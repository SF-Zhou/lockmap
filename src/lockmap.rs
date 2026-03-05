use aliasable::boxed::AliasableBox;
use foldhash::fast::RandomState;
use hashbrown::hash_table::Entry as TableEntry;
use hashbrown::HashTable;
use parking_lot::lock_api::RawMutex as _;
use parking_lot::RawMutex;
use std::borrow::Borrow;
use std::cell::UnsafeCell;
use std::collections::BTreeSet;
use std::hash::{BuildHasher, Hash};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::OnceLock;

// ---------------------------------------------------------------------------
// StateFlags
// ---------------------------------------------------------------------------

struct StateFlags(u32);

impl StateFlags {
    const HAS_VALUE_FLAG: u32 = 1 << 31;
    const REFCNT_MASK: u32 = !Self::HAS_VALUE_FLAG;

    fn new(refcnt: u32, has_value: bool) -> Self {
        let mut val = refcnt & Self::REFCNT_MASK;
        if has_value {
            val |= Self::HAS_VALUE_FLAG;
        }
        Self(val)
    }

    fn refcnt(&self) -> u32 {
        self.0 & Self::REFCNT_MASK
    }

    fn has_value(&self) -> bool {
        (self.0 & Self::HAS_VALUE_FLAG) != 0
    }

    fn pending_cleanup(&self) -> bool {
        self.0 == 0
    }
}

// ---------------------------------------------------------------------------
// State – per-key state with key and pre-computed hash
// ---------------------------------------------------------------------------

struct State<K, V> {
    key: K,
    hash: u64,
    flags: AtomicU32,
    mutex: RawMutex,
    value: UnsafeCell<Option<V>>,
}

impl<K, V> State<K, V> {
    fn new(key: K, value: Option<V>, refcnt: u32, hash: u64) -> AliasableBox<Self> {
        AliasableBox::from_unique(Box::new(Self {
            key,
            hash,
            flags: AtomicU32::new(StateFlags::new(refcnt, value.is_some()).0),
            mutex: RawMutex::INIT,
            value: UnsafeCell::new(value),
        }))
    }

    fn flags(&self) -> StateFlags {
        StateFlags(self.flags.load(Ordering::Acquire))
    }

    /// Increments the reference count.
    ///
    /// # Note
    ///
    /// The reference count uses 31 bits, supporting up to 2^31 concurrent references.
    /// Overflow is not checked; exceeding this limit causes undefined behavior.
    fn inc_ref(&self) -> StateFlags {
        StateFlags(self.flags.fetch_add(1, Ordering::AcqRel) + 1)
    }

    fn dec_ref(&self) -> StateFlags {
        StateFlags(self.flags.fetch_sub(1, Ordering::AcqRel) - 1)
    }

    fn set_value_state(&self, has_value: bool) {
        if has_value {
            self.flags
                .fetch_or(StateFlags::HAS_VALUE_FLAG, Ordering::Release);
        } else {
            self.flags
                .fetch_and(!StateFlags::HAS_VALUE_FLAG, Ordering::Release);
        }
    }

    /// # Safety
    ///
    /// The caller must ensure that the internal `mutex` is locked.
    unsafe fn value_ref(&self) -> &Option<V> {
        &*self.value.get()
    }

    /// # Safety
    ///
    /// The caller must ensure that the internal `mutex` is locked and they have exclusive access.
    #[allow(clippy::mut_from_ref)]
    unsafe fn value_mut(&self) -> &mut Option<V> {
        &mut *self.value.get()
    }
}

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
    inner: std::sync::Mutex<ShardInner<K, V>>,
}

impl<K, V> ShardMap<K, V> {
    fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: std::sync::Mutex::new(ShardInner::with_capacity(capacity)),
        }
    }

    fn len(&self) -> usize {
        self.inner.lock().unwrap().table.len()
    }

    fn is_empty(&self) -> bool {
        self.inner.lock().unwrap().table.is_empty()
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
pub struct LockMap<K, V> {
    shards: Vec<ShardMap<K, V>>,
    hasher: RandomState,
}

fn default_shard_amount() -> usize {
    static DEFAULT_SHARD_AMOUNT: OnceLock<usize> = OnceLock::new();
    *DEFAULT_SHARD_AMOUNT.get_or_init(|| {
        (std::thread::available_parallelism().map_or(1, usize::from) * 4).next_power_of_two()
    })
}

impl<K: Eq + Hash, V> Default for LockMap<K, V> {
    fn default() -> Self {
        Self::new()
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
        assert!(shard_amount > 0, "shard_amount must be greater than 0");
        let per_shard_capacity = capacity.div_ceil(shard_amount);
        Self {
            shards: (0..shard_amount)
                .map(|_| ShardMap::with_capacity(per_shard_capacity))
                .collect(),
            hasher: RandomState::default(),
        }
    }

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
    /// Uses the upper 32 bits of the hash for shard selection. The internal
    /// `HashTable` uses the lower bits for bucket selection, so using the upper
    /// bits avoids correlation between shard assignment and bucket placement.
    #[inline(always)]
    fn shard_index(&self, hash: u64) -> usize {
        ((hash >> 32) as usize) % self.shards.len()
    }

    /// Rehash closure for `HashTable` growth — reuses the stored hash from
    /// each `State`. This avoids calling the hasher entirely during rehash.
    #[inline(always)]
    fn state_hasher() -> impl Fn(&AliasableBox<State<K, V>>) -> u64 {
        |s| s.hash
    }

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
    pub fn entry(&self, key: K) -> Entry<'_, K, V> {
        let hash = self.hasher.hash_one(&key);
        let shard = &self.shards[self.shard_index(hash)];
        let ptr: *mut State<K, V> = {
            let mut inner = shard.inner.lock().unwrap();
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
        };
        self.guard(ptr)
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
    pub fn entry_by_ref<Q>(&self, key: &Q) -> Entry<'_, K, V>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let shard = &self.shards[self.shard_index(hash)];
        let ptr: *mut State<K, V> = {
            let mut inner = shard.inner.lock().unwrap();
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
        };
        self.guard(ptr)
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
            let inner = shard.inner.lock().unwrap();
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
            let mut inner = shard.inner.lock().unwrap();
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
            let mut inner = shard.inner.lock().unwrap();
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
            let inner = shard.inner.lock().unwrap();
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
            let mut inner = shard.inner.lock().unwrap();
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
        M: FromIterator<(K, Entry<'a, K, V>)>,
    {
        keys.into_iter()
            .map(|key| (key.clone(), self.entry(key)))
            .collect()
    }

    fn guard(&self, ptr: *mut State<K, V>) -> Entry<'_, K, V> {
        // SAFETY: ptr is valid (ref-counted) and stable (AliasableBox).
        unsafe { (*ptr).mutex.lock() };
        Entry {
            map: self,
            state: ptr,
        }
    }
}

impl<K, V> std::fmt::Debug for LockMap<K, V> {
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
pub struct Entry<'a, K: Eq + Hash, V> {
    map: &'a LockMap<K, V>,
    state: *mut State<K, V>,
}

// SAFETY: The guard holds a per-key mutex lock and a valid, ref-counted pointer.
unsafe impl<K: Eq + Hash + Send, V: Send> Send for Entry<'_, K, V> {}
unsafe impl<K: Eq + Hash + Send + Sync, V: Send + Sync> Sync for Entry<'_, K, V> {}

impl<K: Eq + Hash, V> Entry<'_, K, V> {
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
}

impl<K: Eq + Hash + std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug for Entry<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Entry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

impl<K: Eq + Hash, V> Drop for Entry<'_, K, V> {
    fn drop(&mut self) {
        // 1. Update value state flag
        let has_value = self.get().is_some();
        let state_ref = unsafe { &*self.state };
        state_ref.set_value_state(has_value);

        // 2. Unlock the entry's mutex
        // SAFETY: We hold the lock (acquired in guard()).
        unsafe { state_ref.mutex.unlock() };

        // 3. CAS loop to decrement reference count
        let mut current = state_ref.flags.load(Ordering::Acquire);
        loop {
            let flags = StateFlags(current);

            // If this is the last guard and no value, proceed to cleanup
            if flags.refcnt() == 1 && !flags.has_value() {
                break;
            }

            let new_flags = StateFlags::new(flags.refcnt() - 1, flags.has_value());
            match state_ref.flags.compare_exchange_weak(
                current,
                new_flags.0,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return, // Not last guard or still has value, return early
                Err(actual) => current = actual,
            }
        }

        // 4. Acquire shard lock using the stored hash (no re-hashing).
        let shard_idx = self.map.shard_index(state_ref.hash);
        let shard = &self.map.shards[shard_idx];
        let mut inner = shard.inner.lock().unwrap();

        // 5. Decrement reference count again; cleanup if needed
        let final_flags = state_ref.dec_ref();
        if final_flags.pending_cleanup() {
            let state_ptr = self.state as *const State<K, V>;
            if let Ok(entry) = inner
                .table
                .find_entry(state_ref.hash, |s| std::ptr::eq(&**s, state_ptr))
            {
                let _ = entry.remove();
            }
        }
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
        let lock_map = Arc::new(LockMap::<String, u32>::with_capacity_and_shard_amount(256, 16));
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
}
