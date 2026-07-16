use crate::common::default_shard_amount;
use aliasable::boxed::AliasableBox;
use foldhash::fast::RandomState;
use hashbrown::hash_table::Entry as TableEntry;
use hashbrown::HashTable;
use parking_lot::lock_api::RawMutex as _;
use parking_lot::Mutex;
use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::hash::{BuildHasher, Hash};

/// Per-key entry state without extra link payload (see [`crate::common::State`]).
type State<K, V> = crate::common::State<K, V, ()>;

// ---------------------------------------------------------------------------
// ShardInner – HashTable storage
// ---------------------------------------------------------------------------

struct ShardInner<K, V> {
    table: HashTable<AliasableBox<State<K, V>>>,
}

impl<K, V> ShardInner<K, V> {
    fn with_capacity(capacity: usize) -> Self {
        Self {
            table: HashTable::with_capacity(capacity),
        }
    }
}

// ---------------------------------------------------------------------------
// ShardMap
// ---------------------------------------------------------------------------

struct ShardMap<K, V> {
    inner: Mutex<ShardInner<K, V>>,
}

impl<K, V> ShardMap<K, V> {
    fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Mutex::new(ShardInner::with_capacity(capacity)),
        }
    }

    fn len(&self) -> usize {
        self.inner.lock().table.len()
    }

    fn is_empty(&self) -> bool {
        self.inner.lock().table.is_empty()
    }
}

// ---------------------------------------------------------------------------
// LockMap
// ---------------------------------------------------------------------------

/// A thread-safe hashmap that supports locking entries at the key level.
///
/// `LockMap` provides a concurrent hashmap with fine-grained per-key locking.
/// Each key can be independently locked, so operations on different keys can
/// proceed in parallel. The map is internally sharded to reduce contention on
/// the map structure itself.
///
/// # Storage Design
///
/// The key and its pre-computed hash are stored together in the internal entry
/// state, so each operation hashes the key only once. The full hash is also
/// reused for shard selection and table probing.
///
/// # Examples
///
/// ```
/// use lockmap::LockMap;
///
/// let map = LockMap::<String, u32>::new();
///
/// // Basic operations
/// map.insert("key1".to_string(), 42);
/// assert_eq!(map.get("key1"), Some(42));
///
/// // Entry API for exclusive access
/// {
///     let mut entry = map.entry("key2".to_string());
///     entry.insert(123);
/// }
///
/// // Remove a value
/// assert_eq!(map.remove("key1"), Some(42));
/// assert_eq!(map.get("key1"), None);
/// ```
pub struct LockMap<K, V, S = RandomState> {
    shards: Vec<ShardMap<K, V>>,
    hasher: S,
}

impl<K: Eq + Hash, V, S: BuildHasher + Default> Default for LockMap<K, V, S> {
    fn default() -> Self {
        Self::with_capacity_and_shard_amount_and_hasher(0, default_shard_amount(), S::default())
    }
}

impl<K: Eq + Hash, V> LockMap<K, V> {
    /// Creates a new `LockMap` with the default number of shards.
    pub fn new() -> Self {
        Self::with_capacity_and_shard_amount(0, default_shard_amount())
    }

    /// Creates a new `LockMap` with the specified initial capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_shard_amount(capacity, default_shard_amount())
    }

    /// Creates a new `LockMap` with the specified initial capacity and number of shards.
    pub fn with_capacity_and_shard_amount(capacity: usize, shard_amount: usize) -> Self {
        Self::with_capacity_and_shard_amount_and_hasher(
            capacity,
            shard_amount,
            RandomState::default(),
        )
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> LockMap<K, V, S> {
    /// Creates a new `LockMap` using the given hash builder.
    ///
    /// # Examples
    ///
    /// ```
    /// use lockmap::LockMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let map = LockMap::<String, u32, _>::with_hasher(RandomState::new());
    /// map.insert("key".to_string(), 42);
    /// assert_eq!(map.get("key"), Some(42));
    /// ```
    pub fn with_hasher(hasher: S) -> Self {
        Self::with_capacity_and_shard_amount_and_hasher(0, default_shard_amount(), hasher)
    }

    /// Creates a new `LockMap` with the specified initial capacity, using the
    /// given hash builder.
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S) -> Self {
        Self::with_capacity_and_shard_amount_and_hasher(capacity, default_shard_amount(), hasher)
    }

    /// Creates a new `LockMap` with the specified initial capacity and number
    /// of shards, using the given hash builder.
    pub fn with_capacity_and_shard_amount_and_hasher(
        capacity: usize,
        shard_amount: usize,
        hasher: S,
    ) -> Self {
        assert!(shard_amount > 0, "shard_amount must be greater than 0");
        let per_shard_capacity = capacity.div_ceil(shard_amount);
        Self {
            shards: (0..shard_amount)
                .map(|_| ShardMap::with_capacity(per_shard_capacity))
                .collect(),
            hasher,
        }
    }
}

impl<K, V, S> LockMap<K, V, S> {
    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.shards.iter().map(|s| s.len()).sum()
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.shards.iter().all(|s| s.is_empty())
    }

    // --- shard routing ---

    /// Compute the shard index from the full hash value.
    ///
    /// Uses the upper 32 bits of the hash for shard selection via the
    /// multiply-shift ("fastrange") technique, which avoids an integer modulo
    /// and works for any shard count. The internal `HashTable` uses the lower
    /// bits for bucket selection, so using the upper bits avoids correlation
    /// between shard assignment and bucket placement.
    #[inline(always)]
    fn shard_index(&self, hash: u64) -> usize {
        (((hash >> 32) * self.shards.len() as u64) >> 32) as usize
    }

    /// Rehash closure for `HashTable` growth — reuses the stored hash from
    /// each `State`. This avoids calling the hasher entirely during rehash.
    #[inline(always)]
    fn state_hasher() -> impl Fn(&AliasableBox<State<K, V>>) -> u64 {
        |s| s.hash
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> LockMap<K, V, S> {
    // ------------------------------------------------------------------
    // Public API
    // ------------------------------------------------------------------

    /// Gets exclusive access to an entry in the map.
    ///
    /// The returned [`Entry`] provides exclusive access to the key and its
    /// associated value until it is dropped.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LockMap;
    /// let map = LockMap::<String, u32>::new();
    /// {
    ///     let mut entry = map.entry("key".to_string());
    ///     entry.insert(42);
    /// }
    /// ```
    pub fn entry(&self, key: K) -> Entry<'_, K, V, S> {
        let ptr = self.acquire_state(key);
        self.guard(ptr)
    }

    /// Attempts to get exclusive access to an entry without blocking.
    ///
    /// Returns `None` if another thread currently holds the entry for this key.
    /// Unlike [`entry`](Self::entry), this method never blocks on the per-key
    /// lock (it may still wait briefly on the internal shard lock).
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LockMap;
    /// let map = LockMap::<String, u32>::new();
    /// let entry = map.entry("key".to_string());
    /// // The key is held by `entry`, so `try_entry` fails:
    /// assert!(map.try_entry("key".to_string()).is_none());
    /// drop(entry);
    /// assert!(map.try_entry("key".to_string()).is_some());
    /// ```
    pub fn try_entry(&self, key: K) -> Option<Entry<'_, K, V, S>> {
        let ptr = self.acquire_state(key);
        self.try_guard(ptr)
    }

    /// Acquires (or creates) the state for `key`, incrementing its reference
    /// count. The returned pointer is valid until released via `guard` /
    /// `try_guard` / `release_ref`.
    fn acquire_state(&self, key: K) -> *mut State<K, V> {
        let hash = self.hasher.hash_one(&key);
        let shard = &self.shards[self.shard_index(hash)];
        let mut inner = shard.inner.lock();
        match inner
            .table
            .entry(hash, |s| s.key.borrow() == &key, Self::state_hasher())
        {
            TableEntry::Occupied(occupied) => {
                let ptr = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                unsafe { &*ptr }.inc_ref();
                ptr
            }
            TableEntry::Vacant(vacant) => {
                let state = State::new(key, None, 1, hash);
                let ptr = &*state as *const State<K, V> as *mut State<K, V>;
                vacant.insert(state);
                ptr
            }
        }
    }

    /// Gets exclusive access to an entry by reference.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LockMap;
    /// let map = LockMap::<String, u32>::new();
    /// {
    ///     let mut entry = map.entry_by_ref("key");
    ///     entry.insert(42);
    /// }
    /// ```
    pub fn entry_by_ref<Q>(&self, key: &Q) -> Entry<'_, K, V, S>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let ptr = self.acquire_state_by_ref(key);
        self.guard(ptr)
    }

    /// Attempts to get exclusive access to an entry by reference without blocking.
    ///
    /// Returns `None` if another thread currently holds the entry for this key.
    /// Unlike [`entry_by_ref`](Self::entry_by_ref), this method never blocks on
    /// the per-key lock (it may still wait briefly on the internal shard lock).
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LockMap;
    /// let map = LockMap::<String, u32>::new();
    /// let entry = map.entry_by_ref("key");
    /// assert!(map.try_entry_by_ref("key").is_none());
    /// drop(entry);
    /// assert!(map.try_entry_by_ref("key").is_some());
    /// ```
    pub fn try_entry_by_ref<Q>(&self, key: &Q) -> Option<Entry<'_, K, V, S>>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let ptr = self.acquire_state_by_ref(key);
        self.try_guard(ptr)
    }

    /// By-reference variant of [`acquire_state`](Self::acquire_state).
    fn acquire_state_by_ref<Q>(&self, key: &Q) -> *mut State<K, V>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let shard = &self.shards[self.shard_index(hash)];
        let mut inner = shard.inner.lock();
        match inner
            .table
            .entry(hash, |s| s.key.borrow() == key, Self::state_hasher())
        {
            TableEntry::Occupied(occupied) => {
                let ptr = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                unsafe { &*ptr }.inc_ref();
                ptr
            }
            TableEntry::Vacant(vacant) => {
                let owned_key: K = key.into();
                let state = State::new(owned_key, None, 1, hash);
                let ptr = &*state as *const State<K, V> as *mut State<K, V>;
                vacant.insert(state);
                ptr
            }
        }
    }

    /// Gets the value associated with the given key.
    ///
    /// If other threads are currently accessing the key, this will wait
    /// until exclusive access is available before returning.
    ///
    /// # Performance Note
    ///
    /// When no other thread holds an entry for this key, the `clone()` operation
    /// is performed while holding the shard lock. If `V::clone()` is expensive,
    /// consider using `entry()` or `entry_by_ref()` combined with `Entry::get()`
    /// to avoid blocking other keys in the same shard.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<String, u32>::new();
    /// map.insert("key".to_string(), 42);
    /// assert_eq!(map.get("key"), Some(42));
    /// assert_eq!(map.get("missing"), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
        Q: Eq + Hash + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let shard = &self.shards[self.shard_index(hash)];
        let mut ptr: *mut State<K, V> = std::ptr::null_mut();

        let value = {
            let inner = shard.inner.lock();
            let p = inner
                .table
                .find(hash, |s| s.key.borrow() == key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>)
                .unwrap_or(std::ptr::null_mut());
            if !p.is_null() {
                let state = unsafe { &*p };
                if state.flags().refcnt() == 0 {
                    // SAFETY: refcnt == 0 means no Entry guard exists.
                    unsafe { state.value_ref() }.clone()
                } else {
                    state.inc_ref();
                    ptr = p;
                    None
                }
            } else {
                None
            }
        };

        if ptr.is_null() {
            return value;
        }

        self.guard(ptr).get().clone()
    }

    /// Sets a value in the map, returning the previous value if any.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<String, u32>::new();
    /// assert_eq!(map.insert("key".to_string(), 42), None);
    /// assert_eq!(map.insert("key".to_string(), 123), Some(42));
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let hash = self.hasher.hash_one(&key);
        let shard = &self.shards[self.shard_index(hash)];
        let (ptr, old) = {
            let mut inner = shard.inner.lock();
            match inner
                .table
                .entry(hash, |s| s.key.borrow() == &key, Self::state_hasher())
            {
                TableEntry::Occupied(occupied) => {
                    let p = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                    let state = unsafe { &*p };
                    let flags = state.flags();
                    if flags.refcnt() == 0 {
                        // SAFETY: refcnt == 0 → exclusive.
                        let old = unsafe { state.value_mut() }.replace(value);
                        state.set_value_state(true);
                        (std::ptr::null_mut(), old)
                    } else {
                        state.inc_ref();
                        (p, Some(value))
                    }
                }
                TableEntry::Vacant(vacant) => {
                    let state = State::new(key, Some(value), 0, hash);
                    vacant.insert(state);
                    (std::ptr::null_mut(), None)
                }
            }
        };

        if ptr.is_null() {
            return old;
        }

        self.guard(ptr).swap(old)
    }

    /// Sets a value in the map by reference key.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<String, u32>::new();
    /// map.insert_by_ref("key", 42);
    /// assert_eq!(map.get("key"), Some(42));
    /// ```
    pub fn insert_by_ref<Q>(&self, key: &Q, value: V) -> Option<V>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let shard = &self.shards[self.shard_index(hash)];
        let (ptr, old) = {
            let mut inner = shard.inner.lock();
            match inner
                .table
                .entry(hash, |s| s.key.borrow() == key, Self::state_hasher())
            {
                TableEntry::Occupied(occupied) => {
                    let p = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                    let state = unsafe { &*p };
                    let flags = state.flags();
                    if flags.refcnt() == 0 {
                        let old = unsafe { state.value_mut() }.replace(value);
                        state.set_value_state(true);
                        (std::ptr::null_mut(), old)
                    } else {
                        state.inc_ref();
                        (p, Some(value))
                    }
                }
                TableEntry::Vacant(vacant) => {
                    let owned_key: K = key.into();
                    let state = State::new(owned_key, Some(value), 0, hash);
                    vacant.insert(state);
                    (std::ptr::null_mut(), None)
                }
            }
        };

        if ptr.is_null() {
            return old;
        }

        self.guard(ptr).swap(old)
    }

    /// Checks if the map contains a key.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::new();
    /// map.insert("key", 42);
    /// assert!(map.contains_key("key"));
    /// assert!(!map.contains_key("non_existent_key"));
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let shard = &self.shards[self.shard_index(hash)];
        let mut ptr: *mut State<K, V> = std::ptr::null_mut();

        let found = {
            let inner = shard.inner.lock();
            let p = inner
                .table
                .find(hash, |s| s.key.borrow() == key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>)
                .unwrap_or(std::ptr::null_mut());
            if !p.is_null() {
                let state = unsafe { &*p };
                if state.flags().refcnt() == 0 {
                    unsafe { state.value_ref() }.is_some()
                } else {
                    state.inc_ref();
                    ptr = p;
                    false
                }
            } else {
                false
            }
        };

        if ptr.is_null() {
            return found;
        }

        self.guard(ptr).get().is_some()
    }

    /// Removes a key from the map.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<String, u32>::new();
    /// map.insert("key".to_string(), 42);
    /// assert_eq!(map.remove("key"), Some(42));
    /// assert_eq!(map.get("key"), None);
    /// ```
    pub fn remove<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let shard = &self.shards[self.shard_index(hash)];

        let ptr = {
            let mut inner = shard.inner.lock();
            match inner.table.find_entry(hash, |s| s.key.borrow() == key) {
                Ok(occupied) => {
                    let p = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                    let state = unsafe { &*p };
                    if state.flags().refcnt() == 0 {
                        // SAFETY: refcnt == 0 → exclusive.
                        let value = unsafe { state.value_mut() }.take();
                        let _ = occupied.remove();
                        return value;
                    }
                    state.inc_ref();
                    p
                }
                Err(_) => return None,
            }
        };

        self.guard(ptr).remove()
    }

    /// Acquires exclusive locks for a batch of keys in a deadlock-safe manner.
    ///
    /// Takes a `BTreeSet` of keys, ensuring they are processed and locked
    /// in a consistent, sorted order across all threads.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use lockmap::LockMap;
    /// use std::collections::BTreeSet;
    ///
    /// let map = LockMap::<u32, u32>::new();
    /// map.insert(1, 100);
    /// map.insert(2, 200);
    /// map.insert(3, 300);
    ///
    /// let mut keys = BTreeSet::new();
    /// keys.insert(3);
    /// keys.insert(1);
    /// keys.insert(2);
    ///
    /// let mut locked_entries = map.batch_lock::<std::collections::HashMap<_, _>>(keys);
    ///
    /// locked_entries.get_mut(&1).and_then(|entry| entry.insert(101));
    /// locked_entries.get_mut(&2).and_then(|entry| entry.insert(201));
    /// locked_entries.get_mut(&3).and_then(|entry| entry.insert(301));
    ///
    /// drop(locked_entries);
    ///
    /// assert_eq!(map.get(&1), Some(101));
    /// assert_eq!(map.get(&2), Some(201));
    /// assert_eq!(map.get(&3), Some(301));
    /// ```
    pub fn batch_lock<'a, M>(&'a self, keys: BTreeSet<K>) -> M
    where
        K: Clone,
        M: FromIterator<(K, Entry<'a, K, V, S>)>,
    {
        keys.into_iter()
            .map(|key| (key.clone(), self.entry(key)))
            .collect()
    }
}

impl<K: Eq + Hash, V, S> LockMap<K, V, S> {
    /// Removes all key-value pairs from the map.
    ///
    /// Entries that are currently held by an [`Entry`] guard are cleared by
    /// waiting for the guard to be released, exactly as [`remove`](Self::remove)
    /// would.
    ///
    /// **Locking behaviour:** Deadlock if called when holding any entry of this map.
    ///
    /// # Examples
    ///
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<String, u32>::new();
    /// map.insert("a".to_string(), 1);
    /// map.insert("b".to_string(), 2);
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&self) {
        for shard in &self.shards {
            let mut in_use: Vec<*mut State<K, V>> = Vec::new();
            {
                let mut inner = shard.inner.lock();
                inner.table.retain(|s| {
                    if s.flags().refcnt() == 0 {
                        // SAFETY: refcnt == 0 → no guard exists; safe to drop.
                        false
                    } else {
                        s.inc_ref();
                        in_use.push(&**s as *const State<K, V> as *mut State<K, V>);
                        true
                    }
                });
            }
            // For in-use entries, wait for the holders and remove the values.
            for ptr in in_use {
                self.guard(ptr).remove();
            }
        }
    }

    /// Calls `f` for every key-value pair in the map.
    ///
    /// Entries that are not currently held are visited under the internal shard
    /// lock; entries held by an [`Entry`] guard are visited afterwards by
    /// waiting for the guard to be released. Consequently the iteration is not
    /// an atomic snapshot: entries may be inserted or removed concurrently.
    ///
    /// **Locking behaviour:** Deadlock if `f` accesses this map or if called
    /// when holding any entry of this map.
    ///
    /// # Examples
    ///
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<u32, u32>::new();
    /// map.insert(1, 10);
    /// map.insert(2, 20);
    ///
    /// let mut sum = 0;
    /// map.for_each(|_, v| sum += v);
    /// assert_eq!(sum, 30);
    /// ```
    pub fn for_each<F>(&self, mut f: F)
    where
        F: FnMut(&K, &V),
    {
        for shard in &self.shards {
            let mut in_use: Vec<*mut State<K, V>> = Vec::new();
            {
                let inner = shard.inner.lock();
                for s in inner.table.iter() {
                    if s.flags().refcnt() == 0 {
                        // SAFETY: refcnt == 0 → no guard exists, and none can be
                        // created while the shard lock is held.
                        if let Some(v) = unsafe { s.value_ref() } {
                            f(&s.key, v);
                        }
                    } else {
                        s.inc_ref();
                        in_use.push(&**s as *const State<K, V> as *mut State<K, V>);
                    }
                }
            }
            for ptr in in_use {
                let entry = self.guard(ptr);
                if let Some(v) = entry.get() {
                    f(entry.key(), v);
                }
            }
        }
    }

    /// Retains only the key-value pairs for which `f` returns `true`.
    ///
    /// Entries that are not currently held are visited under the internal shard
    /// lock; entries held by an [`Entry`] guard are visited afterwards by
    /// waiting for the guard to be released.
    ///
    /// **Locking behaviour:** Deadlock if `f` accesses this map or if called
    /// when holding any entry of this map.
    ///
    /// # Examples
    ///
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<u32, u32>::new();
    /// for i in 0..10 {
    ///     map.insert(i, i);
    /// }
    /// map.retain(|_, v| *v % 2 == 0);
    /// assert_eq!(map.len(), 5);
    /// ```
    pub fn retain<F>(&self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        for shard in &self.shards {
            let mut in_use: Vec<*mut State<K, V>> = Vec::new();
            {
                let mut inner = shard.inner.lock();
                inner.table.retain(|s| {
                    if s.flags().refcnt() == 0 {
                        // SAFETY: refcnt == 0 → no guard exists, and none can be
                        // created while the shard lock is held.
                        match unsafe { s.value_mut() } {
                            Some(v) => f(&s.key, v),
                            None => false,
                        }
                    } else {
                        s.inc_ref();
                        in_use.push(&**s as *const State<K, V> as *mut State<K, V>);
                        true
                    }
                });
            }
            for ptr in in_use {
                let mut entry = self.guard(ptr);
                // SAFETY: the key is immutable and lives as long as the guard;
                // borrowing it independently of `entry` lets us pass it to `f`
                // together with the mutable value borrow below.
                let key: &K = unsafe { &(*ptr).key };
                let keep = match entry.get_mut() {
                    Some(v) => f(key, v),
                    None => true,
                };
                if !keep {
                    entry.remove();
                }
            }
        }
    }

    fn guard(&self, ptr: *mut State<K, V>) -> Entry<'_, K, V, S> {
        // SAFETY: ptr is valid (ref-counted) and stable (AliasableBox).
        unsafe { (*ptr).mutex.lock() };
        Entry {
            map: self,
            state: ptr,
        }
    }

    fn try_guard(&self, ptr: *mut State<K, V>) -> Option<Entry<'_, K, V, S>> {
        // SAFETY: ptr is valid (ref-counted) and stable (AliasableBox).
        if unsafe { (*ptr).mutex.try_lock() } {
            Some(Entry {
                map: self,
                state: ptr,
            })
        } else {
            self.release_ref(ptr);
            None
        }
    }

    /// Releases one reference to `state`; if this was the last reference and
    /// the entry holds no value, the entry is removed from its shard.
    ///
    /// The per-key mutex must NOT be held by the caller.
    fn release_ref(&self, state: *mut State<K, V>) {
        let state_ref = unsafe { &*state };

        // Fast path: CAS-decrement unless cleanup is required.
        if !state_ref.release_ref_needs_cleanup() {
            return;
        }

        // Acquire shard lock using the stored hash (no re-hashing).
        let shard = &self.shards[self.shard_index(state_ref.hash)];
        let mut inner = shard.inner.lock();

        // Decrement the reference count again; cleanup if needed.
        let final_flags = state_ref.dec_ref();
        if final_flags.pending_cleanup() {
            let state_ptr = state as *const State<K, V>;
            if let Ok(entry) = inner
                .table
                .find_entry(state_ref.hash, |s| std::ptr::eq(&**s, state_ptr))
            {
                let _ = entry.remove();
            }
        }
    }
}

impl<K, V, S> std::fmt::Debug for LockMap<K, V, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LockMap").finish()
    }
}

// ---------------------------------------------------------------------------
// Entry
// ---------------------------------------------------------------------------

/// An RAII guard providing exclusive access to a key-value pair in the [`LockMap`].
///
/// The key is obtained directly from the internal `State`, so there is no need
/// for separate by-value / by-reference entry types.
///
/// When dropped, this type automatically unlocks the entry and may trigger
/// cleanup of empty entries.
///
/// # Examples
///
/// ```
/// use lockmap::LockMap;
///
/// let map = LockMap::new();
/// {
///     let mut entry = map.entry("key");
///     entry.insert(42);
/// }
/// ```
pub struct Entry<'a, K: Eq + Hash, V, S = RandomState> {
    map: &'a LockMap<K, V, S>,
    state: *mut State<K, V>,
}

// SAFETY: The guard holds a per-key mutex lock and a valid, ref-counted pointer.
// Entry is intentionally !Send — like MutexGuard, it should not be moved across threads.
// For Sync, only K: Sync and V: Sync are needed: sharing &Entry across threads only
// requires shared references (&K, &Option<V>) to be safe to share, not ownership transfer.
unsafe impl<K: Eq + Hash + Sync, V: Sync, S: Sync> Sync for Entry<'_, K, V, S> {}

impl<K: Eq + Hash, V, S> Entry<'_, K, V, S> {
    /// Returns a reference to the entry's key.
    pub fn key(&self) -> &K {
        // SAFETY: The state pointer is valid for the lifetime of this guard
        // and the key is immutable.
        unsafe { &(*self.state).key }
    }

    /// Returns a reference to the entry's value.
    pub fn get(&self) -> &Option<V> {
        unsafe { (*self.state).value_ref() }
    }

    /// Returns a mutable reference to the entry's value.
    pub fn get_mut(&mut self) -> &mut Option<V> {
        unsafe { (*self.state).value_mut() }
    }

    /// Sets the value, returning the old value if any.
    pub fn insert(&mut self, value: V) -> Option<V> {
        self.get_mut().replace(value)
    }

    /// Swaps the value with the provided one, returning the old value.
    pub fn swap(&mut self, mut value: Option<V>) -> Option<V> {
        std::mem::swap(self.get_mut(), &mut value);
        value
    }

    /// Removes the value, returning it if it existed.
    pub fn remove(&mut self) -> Option<V> {
        self.get_mut().take()
    }

    /// Inserts `default` if the entry has no value, then returns a mutable
    /// reference to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LockMap;
    /// let map = LockMap::<&str, u32>::new();
    /// *map.entry("counter").or_insert(0) += 1;
    /// *map.entry("counter").or_insert(0) += 1;
    /// assert_eq!(map.get("counter"), Some(2));
    /// ```
    pub fn or_insert(&mut self, default: V) -> &mut V {
        self.get_mut().get_or_insert(default)
    }

    /// Inserts the value returned by `default` if the entry has no value, then
    /// returns a mutable reference to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LockMap;
    /// let map = LockMap::<&str, Vec<u32>>::new();
    /// map.entry("list").or_insert_with(Vec::new).push(1);
    /// map.entry("list").or_insert_with(Vec::new).push(2);
    /// assert_eq!(map.get("list"), Some(vec![1, 2]));
    /// ```
    pub fn or_insert_with<F: FnOnce() -> V>(&mut self, default: F) -> &mut V {
        self.get_mut().get_or_insert_with(default)
    }
}

impl<K: Eq + Hash + std::fmt::Debug, V: std::fmt::Debug, S> std::fmt::Debug for Entry<'_, K, V, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Entry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

impl<K: Eq + Hash, V, S> Drop for Entry<'_, K, V, S> {
    fn drop(&mut self) {
        // 1. Update value state flag
        let has_value = self.get().is_some();
        let state_ref = unsafe { &*self.state };
        state_ref.set_value_state(has_value);

        // 2. Unlock the entry's mutex
        // SAFETY: We hold the lock (acquired in guard()).
        unsafe { state_ref.mutex.unlock() };

        // 3. Release the reference; removes the entry if it is the last
        //    reference and no value is stored.
        self.map.release_ref(self.state);
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{
        atomic::{AtomicU32, Ordering},
        Arc,
    };

    #[test]
    fn test_lockmap_lock() {
        let map = LockMap::<u32, u32>::new();
        assert!(map.is_empty());
        println!("{:?}", map);
        {
            let mut entry = map.entry(1);
            assert_eq!(*entry.key(), 1);
            assert_eq!(entry.insert(2), None);
            println!("{:?}", entry);
            assert!(!map.is_empty());
            assert_eq!(map.len(), 1);
        }
        {
            let mut entry = map.entry(1);
            assert_eq!(entry.get_mut().unwrap(), 2);
            assert_eq!(entry.remove(), Some(2));
        }
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
        {
            let mut entry = map.entry(1);
            assert!(entry.get_mut().is_none());
        }
        let map = LockMap::<u32, u32>::default();
        {
            let mut entry = map.entry(1);
            assert_eq!(entry.insert(2), None);
        }
        assert!(!map.is_empty());
        assert_eq!(map.len(), 1);
        assert!(map.contains_key(&1));
        assert_eq!(map.remove(&1), Some(2));
        assert!(map.is_empty());
        assert!(!map.contains_key(&1));
        assert_eq!(map.len(), 0);
        assert_eq!(map.remove(&1), None);
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn test_lockmap_lock_by_ref() {
        let map = LockMap::<String, u32>::new();
        println!("{:?}", map);
        {
            let mut entry = map.entry_by_ref("1");
            assert_eq!(entry.key(), "1");
            assert_eq!(entry.insert(2), None);
            println!("{:?}", entry);
        }
        {
            let mut entry = map.entry_by_ref("1");
            assert_eq!(entry.get_mut().unwrap(), 2);
            assert_eq!(entry.remove(), Some(2));
        }
        {
            let mut entry = map.entry_by_ref("1");
            assert!(entry.get_mut().is_none());
        }
    }

    #[test]
    fn test_lockmap_same_key_by_value() {
        let lock_map = Arc::new(LockMap::<usize, usize>::with_capacity(256));
        let current = Arc::new(AtomicU32::default());
        #[cfg(not(miri))]
        const N: usize = 1 << 20;
        #[cfg(miri)]
        const N: usize = 1 << 6;
        const M: usize = 4;

        const S: usize = 0;
        lock_map.insert(S, 0);

        let threads = (0..M)
            .map(|_| {
                let lock_map = lock_map.clone();
                let current = current.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let mut entry = lock_map.entry(S);
                        let now = current.fetch_add(1, Ordering::AcqRel);
                        assert_eq!(now, 0);
                        let v = entry.get_mut().as_mut().unwrap();
                        *v += 1;
                        let now = current.fetch_sub(1, Ordering::AcqRel);
                        assert_eq!(now, 1);
                    }
                })
            })
            .collect::<Vec<_>>();
        threads.into_iter().for_each(|t| t.join().unwrap());

        let mut entry = lock_map.entry(S);
        assert_eq!(*entry.get(), Some(N * M));
        assert_eq!(entry.get_mut().unwrap(), N * M);
    }

    #[test]
    fn test_lockmap_same_key_by_ref() {
        let lock_map = Arc::new(LockMap::<String, usize>::with_capacity(256));
        let current = Arc::new(AtomicU32::default());
        #[cfg(not(miri))]
        const N: usize = 1 << 20;
        #[cfg(miri)]
        const N: usize = 1 << 6;
        const M: usize = 4;

        const S: &str = "hello";
        lock_map.insert_by_ref(S, 0);

        let threads = (0..M)
            .map(|_| {
                let lock_map = lock_map.clone();
                let current = current.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let mut entry = lock_map.entry_by_ref(S);
                        let now = current.fetch_add(1, Ordering::AcqRel);
                        assert_eq!(now, 0);
                        let v = entry.get_mut().as_mut().unwrap();
                        *v += 1;
                        let now = current.fetch_sub(1, Ordering::AcqRel);
                        assert_eq!(now, 1);
                    }
                })
            })
            .collect::<Vec<_>>();
        threads.into_iter().for_each(|t| t.join().unwrap());

        let mut entry = lock_map.entry_by_ref(S);
        println!("{:?}", entry);
        assert_eq!(entry.key(), S);
        assert_eq!(*entry.get(), Some(N * M));
        assert_eq!(entry.insert(0).unwrap(), N * M);
    }

    #[test]
    fn test_lockmap_random_key() {
        let lock_map = Arc::new(LockMap::<u32, u32>::with_capacity_and_shard_amount(256, 16));
        let total = Arc::new(AtomicU32::default());
        #[cfg(not(miri))]
        const N: usize = 1 << 12;
        #[cfg(miri)]
        const N: usize = 1 << 6;
        const M: usize = 8;

        let threads = (0..M)
            .map(|_| {
                let lock_map = lock_map.clone();
                let total = total.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let key = rand::random::<u32>() % 32;
                        let mut entry = lock_map.entry(key);
                        assert!(entry.get_mut().is_none());
                        entry.get_mut().replace(1);
                        total.fetch_add(1, Ordering::AcqRel);
                        entry.get_mut().take();
                    }
                })
            })
            .collect::<Vec<_>>();
        threads.into_iter().for_each(|t| t.join().unwrap());

        assert_eq!(total.load(Ordering::Acquire) as usize, N * M);
    }

    #[test]
    fn test_lockmap_random_batch_lock() {
        let lock_map = Arc::new(LockMap::<u32, u32>::with_capacity_and_shard_amount(256, 16));
        let total = Arc::new(AtomicU32::default());
        #[cfg(not(miri))]
        const N: usize = 1 << 16;
        #[cfg(miri)]
        const N: usize = 1 << 6;
        const M: usize = 8;

        let threads = (0..M)
            .map(|_| {
                let lock_map = lock_map.clone();
                let total = total.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let keys = (0..3).map(|_| rand::random::<u32>() % 32).collect();
                        let mut entries: std::collections::HashMap<_, _> =
                            lock_map.batch_lock(keys);
                        for entry in entries.values_mut() {
                            assert!(entry.get().is_none());
                            entry.insert(1);
                        }
                        total.fetch_add(1, Ordering::AcqRel);
                        for entry in entries.values_mut() {
                            entry.remove();
                        }
                    }
                })
            })
            .collect::<Vec<_>>();
        threads.into_iter().for_each(|t| t.join().unwrap());

        assert_eq!(total.load(Ordering::Acquire) as usize, N * M);
    }

    #[test]
    fn test_lockmap_get_set() {
        let lock_map = Arc::new(LockMap::<u32, u32>::with_capacity_and_shard_amount(256, 16));
        #[cfg(not(miri))]
        const N: usize = 1 << 20;
        #[cfg(miri)]
        const N: usize = 1 << 6;

        let entry_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = rand::random::<u32>() % 32;
                    let value = rand::random::<u32>() % 32;
                    let mut entry = lock_map.entry(key);
                    if value < 16 {
                        entry.get_mut().take();
                    } else {
                        entry.get_mut().replace(value);
                    }
                }
            })
        };

        let set_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = rand::random::<u32>() % 32;
                    let value = rand::random::<u32>() % 32;
                    if value < 16 {
                        lock_map.remove(&key);
                    } else {
                        lock_map.insert(key, value);
                    }
                }
            })
        };

        let get_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = rand::random::<u32>() % 32;
                    let value = lock_map.get(&key);
                    if let Some(v) = value {
                        assert!(v >= 16)
                    }
                }
            })
        };

        entry_thread.join().unwrap();
        set_thread.join().unwrap();
        get_thread.join().unwrap();
    }

    #[test]
    fn test_lockmap_get_set_by_ref() {
        let lock_map = Arc::new(LockMap::<String, u32>::with_capacity_and_shard_amount(
            256, 16,
        ));
        #[cfg(not(miri))]
        const N: usize = 1 << 18;
        #[cfg(miri)]
        const N: usize = 1 << 6;

        let entry_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = (rand::random::<u32>() % 32).to_string();
                    let value = rand::random::<u32>() % 32;
                    let mut entry = lock_map.entry_by_ref(&key);
                    if value < 16 {
                        entry.get_mut().take();
                    } else {
                        entry.get_mut().replace(value);
                    }
                }
            })
        };

        let set_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = (rand::random::<u32>() % 32).to_string();
                    let value = rand::random::<u32>() % 32;
                    if value < 16 {
                        lock_map.remove(&key);
                    } else {
                        lock_map.insert_by_ref(&key, value);
                    }
                }
            })
        };

        let get_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = (rand::random::<u32>() % 32).to_string();
                    let value = lock_map.get(&key);
                    if let Some(v) = value {
                        assert!(v >= 16)
                    }
                }
            })
        };

        entry_thread.join().unwrap();
        set_thread.join().unwrap();
        get_thread.join().unwrap();
    }

    #[test]
    fn test_lockmap_heavy_contention() {
        let lock_map = Arc::new(LockMap::<u32, u32>::new());
        #[cfg(not(miri))]
        const THREADS: usize = 16;
        #[cfg(miri)]
        const THREADS: usize = 4;
        #[cfg(not(miri))]
        const OPS_PER_THREAD: usize = 10000;
        #[cfg(miri)]
        const OPS_PER_THREAD: usize = 10;
        const HOT_KEYS: u32 = 5;

        let counter = Arc::new(AtomicU32::new(0));

        let threads: Vec<_> = (0..THREADS)
            .map(|_| {
                let lock_map = lock_map.clone();
                let counter = counter.clone();
                std::thread::spawn(move || {
                    for _ in 0..OPS_PER_THREAD {
                        let key = rand::random::<u32>() % HOT_KEYS;
                        let mut entry = lock_map.entry(key);

                        // Simulate some work
                        std::thread::sleep(std::time::Duration::from_nanos(10));

                        match entry.get_mut() {
                            Some(value) => {
                                *value = value.wrapping_add(1);
                                counter.fetch_add(1, Ordering::Relaxed);
                            }
                            None => {
                                entry.insert(1);
                                counter.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                        drop(entry);
                        assert!(lock_map.contains_key(&key), "Key {} should exist", key);
                    }
                })
            })
            .collect();

        for thread in threads {
            thread.join().unwrap();
        }

        assert_eq!(
            counter.load(Ordering::Relaxed),
            THREADS as u32 * OPS_PER_THREAD as u32
        );
    }

    #[test]
    fn test_lockmap_try_entry() {
        let map = LockMap::<String, u32>::new();
        {
            let mut entry = map.try_entry("key".to_string()).unwrap();
            entry.insert(1);
            assert!(map.try_entry("key".to_string()).is_none());
            assert!(map.try_entry_by_ref("key").is_none());
        }
        assert_eq!(map.get("key"), Some(1));
        {
            let mut entry = map.try_entry_by_ref("key").unwrap();
            assert_eq!(entry.remove(), Some(1));
        }
        // A failed try_entry on a held, empty key must not leak the entry.
        let held = map.entry("held".to_string());
        assert!(map.try_entry("held".to_string()).is_none());
        drop(held);
        assert!(map.is_empty());
    }

    #[test]
    fn test_lockmap_try_entry_concurrent() {
        let map = Arc::new(LockMap::<u32, u32>::new());
        #[cfg(not(miri))]
        const N: usize = 1 << 12;
        #[cfg(miri)]
        const N: usize = 1 << 6;
        const M: usize = 4;

        map.insert(0, 0);
        let success = Arc::new(AtomicU32::new(0));

        let threads: Vec<_> = (0..M)
            .map(|_| {
                let map = map.clone();
                let success = success.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        if let Some(mut entry) = map.try_entry(0) {
                            *entry.get_mut().as_mut().unwrap() += 1;
                            success.fetch_add(1, Ordering::AcqRel);
                        }
                    }
                })
            })
            .collect();
        threads.into_iter().for_each(|t| t.join().unwrap());

        assert_eq!(map.get(&0), Some(success.load(Ordering::Acquire)));
    }

    #[test]
    fn test_lockmap_clear() {
        let map = LockMap::<u32, u32>::new();
        for i in 0..100 {
            map.insert(i, i);
        }
        assert_eq!(map.len(), 100);
        map.clear();
        assert!(map.is_empty());
        assert_eq!(map.get(&50), None);

        // Clearing an empty map is a no-op.
        map.clear();
        assert!(map.is_empty());
    }

    #[test]
    fn test_lockmap_clear_with_held_entry() {
        let map = Arc::new(LockMap::<u32, u32>::new());
        map.insert(1, 10);

        let mut held = map.entry(2);
        held.insert(20);

        let cleaner = {
            let map = map.clone();
            std::thread::spawn(move || map.clear())
        };

        // Give the cleaner a chance to reach the held entry, then release it.
        std::thread::sleep(std::time::Duration::from_millis(10));
        drop(held);
        cleaner.join().unwrap();

        assert!(map.is_empty());
        assert_eq!(map.get(&1), None);
        assert_eq!(map.get(&2), None);
    }

    #[test]
    fn test_lockmap_custom_hasher() {
        use std::collections::hash_map::RandomState as StdRandomState;

        let map = LockMap::<String, u32, _>::with_hasher(StdRandomState::new());
        map.insert("a".to_string(), 1);
        assert_eq!(map.get("a"), Some(1));
        {
            let mut entry = map.entry("b".to_string());
            entry.insert(2);
        }
        assert_eq!(map.remove("b"), Some(2));
        assert_eq!(map.len(), 1);

        let map = LockMap::<u32, u32, _>::with_capacity_and_hasher(100, StdRandomState::default());
        for i in 0..100 {
            map.insert(i, i);
        }
        assert_eq!(map.len(), 100);

        let map: LockMap<u32, u32, StdRandomState> = LockMap::default();
        map.insert(1, 1);
        assert!(map.contains_key(&1));
    }

    #[test]
    fn test_lockmap_for_each() {
        let map = LockMap::<u32, u32>::new();
        for i in 0..10 {
            map.insert(i, i * 2);
        }

        let mut sum = 0;
        let mut count = 0;
        map.for_each(|k, v| {
            assert_eq!(*v, k * 2);
            sum += *v;
            count += 1;
        });
        assert_eq!(count, 10);
        assert_eq!(sum, (0..10).map(|i| i * 2).sum());
    }

    #[test]
    fn test_lockmap_for_each_with_held_entry() {
        let map = Arc::new(LockMap::<u32, u32>::new());
        map.insert(1, 10);
        let mut held = map.entry(2);
        held.insert(20);

        let visitor = {
            let map = map.clone();
            std::thread::spawn(move || {
                let mut visited = Vec::new();
                map.for_each(|k, v| visited.push((*k, *v)));
                visited.sort();
                visited
            })
        };

        std::thread::sleep(std::time::Duration::from_millis(10));
        drop(held);
        assert_eq!(visitor.join().unwrap(), vec![(1, 10), (2, 20)]);
    }

    #[test]
    fn test_lockmap_retain() {
        let map = LockMap::<u32, u32>::new();
        for i in 0..10 {
            map.insert(i, i);
        }
        map.retain(|_, v| {
            *v += 100;
            *v % 2 == 0
        });
        assert_eq!(map.len(), 5);
        for i in 0..10 {
            if i % 2 == 0 {
                assert_eq!(map.get(&i), Some(i + 100));
            } else {
                assert_eq!(map.get(&i), None);
            }
        }
    }

    #[test]
    fn test_lockmap_retain_with_held_entry() {
        let map = Arc::new(LockMap::<u32, u32>::new());
        map.insert(1, 1);
        let mut held = map.entry(2);
        held.insert(2);

        let retainer = {
            let map = map.clone();
            std::thread::spawn(move || map.retain(|_, v| *v % 2 == 0))
        };

        std::thread::sleep(std::time::Duration::from_millis(10));
        drop(held);
        retainer.join().unwrap();

        assert_eq!(map.get(&1), None);
        assert_eq!(map.get(&2), Some(2));
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn test_lockmap_retain_removes_held_entry() {
        // A held entry for which `f` returns false must be removed via the
        // in-use path (`entry.remove()`), not the shard pass.
        let map = Arc::new(LockMap::<u32, u32>::new());
        map.insert(2, 2);
        let mut held = map.entry(1);
        held.insert(1);

        let retainer = {
            let map = map.clone();
            std::thread::spawn(move || map.retain(|_, v| *v % 2 == 0))
        };

        std::thread::sleep(std::time::Duration::from_millis(10));
        drop(held);
        retainer.join().unwrap();

        assert_eq!(map.get(&1), None);
        assert_eq!(map.get(&2), Some(2));
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn test_lockmap_retain_held_entry_without_value() {
        // A held entry with no value is visited via the in-use path; `f` is
        // not called for it and the entry is kept (cleanup happens when the
        // guard is dropped).
        let map = Arc::new(LockMap::<u32, u32>::new());
        map.insert(1, 1);
        let held = map.entry(2); // held, but no value is ever inserted

        let calls = Arc::new(AtomicU32::new(0));
        let retainer = {
            let map = map.clone();
            let calls = calls.clone();
            std::thread::spawn(move || {
                map.retain(|_, _| {
                    calls.fetch_add(1, Ordering::AcqRel);
                    false
                })
            })
        };

        std::thread::sleep(std::time::Duration::from_millis(10));
        drop(held);
        retainer.join().unwrap();

        // `f` was only called for key 1; the valueless held entry was skipped
        // and cleaned up on guard drop.
        assert_eq!(calls.load(Ordering::Acquire), 1);
        assert!(map.is_empty());
    }

    #[test]
    fn test_lockmap_retain_unheld_entry_without_value() {
        // White-box test: simulate the defensive state of an unheld entry
        // (refcnt == 0) without a value; `retain` must drop it without
        // calling `f`.
        let map = LockMap::<u32, u32>::new();
        map.insert(1, 1);
        map.insert(2, 2);

        for shard in &map.shards {
            let inner = shard.inner.lock();
            for s in inner.table.iter() {
                if s.key == 1 {
                    // SAFETY: the shard lock is held and refcnt == 0, so no
                    // guard exists and none can be created concurrently.
                    unsafe { (*s.value.get()).take() };
                    s.set_value_state(false);
                }
            }
        }

        map.retain(|k, _| {
            assert_ne!(*k, 1, "valueless entry must not be visited");
            true
        });
        assert_eq!(map.len(), 1);
        assert_eq!(map.get(&1), None);
        assert_eq!(map.get(&2), Some(2));
    }

    #[test]
    fn test_lockmap_or_insert() {
        let map = LockMap::<&str, u32>::new();
        *map.entry("counter").or_insert(0) += 1;
        *map.entry("counter").or_insert(0) += 1;
        assert_eq!(map.get("counter"), Some(2));

        let map = LockMap::<&str, Vec<u32>>::new();
        map.entry("list").or_insert_with(Vec::new).push(1);
        map.entry("list").or_insert_with(Vec::new).push(2);
        assert_eq!(map.get("list"), Some(vec![1, 2]));
    }

    #[test]
    fn test_lockmap_grow() {
        let lock_map = Arc::new(LockMap::<u32, u32>::with_capacity(4));
        #[cfg(not(miri))]
        const N: usize = 1 << 12;
        #[cfg(miri)]
        const N: usize = 1 << 6;

        for i in 0..N {
            lock_map.insert(i as u32, i as u32);
        }

        for i in 0..N {
            assert_eq!(lock_map.get(&(i as u32)), Some(i as u32));
        }
    }
}
