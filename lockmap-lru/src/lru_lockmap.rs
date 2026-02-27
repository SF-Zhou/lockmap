use aliasable::boxed::AliasableBox;
use foldhash::fast::RandomState;
use lockmap_core::Mutex;
use std::borrow::Borrow;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::OnceLock;

// ---------------------------------------------------------------------------
// StateFlags (same design as lockmap)
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
// State – per-key state with intrusive LRU list pointers
// ---------------------------------------------------------------------------

struct State<K, V> {
    key: K,
    flags: AtomicU32,
    mutex: Mutex,
    value: UnsafeCell<Option<V>>,
    // Intrusive doubly-linked list pointers for LRU ordering.
    // These are only accessed while the shard's `std::sync::Mutex` is held.
    prev: UnsafeCell<*mut Self>,
    next: UnsafeCell<*mut Self>,
}

impl<K, V> State<K, V> {
    fn new(key: K, value: Option<V>, refcnt: u32) -> AliasableBox<Self> {
        AliasableBox::from_unique(Box::new(Self {
            key,
            flags: AtomicU32::new(StateFlags::new(refcnt, value.is_some()).0),
            mutex: Mutex::new(),
            value: UnsafeCell::new(value),
            prev: UnsafeCell::new(std::ptr::null_mut()),
            next: UnsafeCell::new(std::ptr::null_mut()),
        }))
    }

    fn flags(&self) -> StateFlags {
        StateFlags(self.flags.load(Ordering::Acquire))
    }

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
// LruShardInner – HashMap + intrusive doubly-linked LRU list
// ---------------------------------------------------------------------------

struct LruShardInner<K, V> {
    map: HashMap<K, AliasableBox<State<K, V>>, RandomState>,
    head: *mut State<K, V>,
    tail: *mut State<K, V>,
    capacity: usize,
}

// SAFETY: The raw pointers (head, tail, prev, next) are only accessed while
// the shard's `std::sync::Mutex` is held, ensuring exclusive access.
unsafe impl<K: Send, V: Send> Send for LruShardInner<K, V> {}

impl<K: Eq + Hash, V> LruShardInner<K, V> {
    fn with_capacity(map_capacity: usize, lru_capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity_and_hasher(map_capacity, RandomState::default()),
            head: std::ptr::null_mut(),
            tail: std::ptr::null_mut(),
            capacity: lru_capacity,
        }
    }

    // --- Intrusive linked-list helpers (all called under shard lock) ---

    /// Detach `node` from the doubly-linked list.
    ///
    /// # Safety
    ///
    /// `node` must be a valid, non-null pointer to a State that is currently in
    /// this shard's linked list. The shard mutex must be held.
    unsafe fn detach(&mut self, node: *mut State<K, V>) {
        let prev = *(*node).prev.get();
        let next = *(*node).next.get();

        if !prev.is_null() {
            *(*prev).next.get() = next;
        } else {
            self.head = next;
        }

        if !next.is_null() {
            *(*next).prev.get() = prev;
        } else {
            self.tail = prev;
        }

        *(*node).prev.get() = std::ptr::null_mut();
        *(*node).next.get() = std::ptr::null_mut();
    }

    /// Push `node` to the front (head) of the doubly-linked list.
    ///
    /// # Safety
    ///
    /// `node` must be a valid, non-null pointer to a State that is NOT currently
    /// in the list (prev/next must be null). The shard mutex must be held.
    unsafe fn push_front(&mut self, node: *mut State<K, V>) {
        *(*node).next.get() = self.head;
        *(*node).prev.get() = std::ptr::null_mut();

        if !self.head.is_null() {
            *(*self.head).prev.get() = node;
        }
        self.head = node;
        if self.tail.is_null() {
            self.tail = node;
        }
    }

    /// Move `node` to the front of the list (mark as most-recently-used).
    ///
    /// # Safety
    ///
    /// `node` must be a valid pointer to a State in this shard's list.
    /// The shard mutex must be held.
    unsafe fn move_to_front(&mut self, node: *mut State<K, V>) {
        if self.head == node {
            return;
        }
        self.detach(node);
        self.push_front(node);
    }

    /// Try to evict the least-recently-used entries until the map size is within capacity.
    ///
    /// Entries that are currently in use (refcnt > 0) are skipped — eviction is
    /// deferred until a future access triggers another eviction pass.
    fn try_evict(&mut self) {
        while self.map.len() > self.capacity && !self.tail.is_null() {
            let tail = self.tail;

            // SAFETY: `tail` is a valid pointer to a State in the list (maintained by push_front/detach).
            let state = unsafe { &*tail };
            if state.flags().refcnt() > 0 {
                // The tail entry is currently in use. Give up for now; a future
                // access will retry eviction.
                break;
            }

            // SAFETY: `tail` is valid and in the list.
            unsafe { self.detach(tail) };

            // Remove from the HashMap. This drops the `AliasableBox` and frees
            // the `State` allocation.
            let _state = self.map.remove(&state.key);
        }
    }
}

// ---------------------------------------------------------------------------
// LruShardMap
// ---------------------------------------------------------------------------

struct LruShardMap<K, V> {
    inner: std::sync::Mutex<LruShardInner<K, V>>,
}

impl<K: Eq + Hash, V> LruShardMap<K, V> {
    fn with_capacity(map_capacity: usize, lru_capacity: usize) -> Self {
        Self {
            inner: std::sync::Mutex::new(LruShardInner::with_capacity(map_capacity, lru_capacity)),
        }
    }

    fn len(&self) -> usize {
        self.inner.lock().unwrap().map.len()
    }

    fn is_empty(&self) -> bool {
        self.inner.lock().unwrap().map.is_empty()
    }
}

// ---------------------------------------------------------------------------
// LruLockMap
// ---------------------------------------------------------------------------

/// A thread-safe LRU cache that supports locking entries at the key level.
///
/// `LruLockMap` extends the per-key locking design of `LockMap` with LRU
/// (Least Recently Used) eviction. The total capacity is divided evenly among
/// internal shards, and each shard independently evicts its least-recently-used
/// entries when it exceeds its share of the capacity.
///
/// # Eviction Policy
///
/// - On every access (get, insert, entry, remove, contains_key), the accessed
///   entry is promoted to the head of its shard's LRU list.
/// - After an access that may increase the shard size, entries are evicted from
///   the tail of the LRU list until the shard is within capacity.
/// - Entries with an active [`LruEntryByVal`] or [`LruEntryByRef`] guard
///   (refcnt > 0) are **not** evicted. Eviction is deferred until a subsequent
///   access triggers another pass.
///
/// # Examples
///
/// ```
/// use lockmap_lru::LruLockMap;
///
/// let cache = LruLockMap::<String, u32>::new(1024);
///
/// cache.insert("a".to_string(), 1);
/// cache.insert("b".to_string(), 2);
///
/// assert_eq!(cache.get("a"), Some(1));
///
/// {
///     let mut entry = cache.entry("c".to_string());
///     entry.insert(3);
/// }
///
/// assert_eq!(cache.remove("b"), Some(2));
/// ```
pub struct LruLockMap<K, V> {
    shards: Vec<LruShardMap<K, V>>,
    hasher: RandomState,
}

fn default_shard_amount() -> usize {
    static DEFAULT_SHARD_AMOUNT: OnceLock<usize> = OnceLock::new();
    *DEFAULT_SHARD_AMOUNT.get_or_init(|| {
        (std::thread::available_parallelism().map_or(1, usize::from) * 4).next_power_of_two()
    })
}

impl<K: Eq + Hash + Clone, V> LruLockMap<K, V> {
    /// Creates a new `LruLockMap` with the given total capacity.
    ///
    /// The capacity is divided evenly among the default number of shards.
    pub fn new(capacity: usize) -> Self {
        Self::with_capacity_and_shard_amount(capacity, default_shard_amount())
    }

    /// Creates a new `LruLockMap` with the given total capacity and number of shards.
    ///
    /// Each shard will have a capacity of `capacity / shard_amount` (rounded up
    /// for the first shard to absorb the remainder).
    pub fn with_capacity_and_shard_amount(capacity: usize, shard_amount: usize) -> Self {
        assert!(shard_amount > 0, "shard_amount must be greater than 0");
        let per_shard = capacity.div_ceil(shard_amount);
        let map_cap = per_shard;
        Self {
            shards: (0..shard_amount)
                .map(|_| LruShardMap::with_capacity(map_cap, per_shard))
                .collect(),
            hasher: RandomState::default(),
        }
    }

    /// Returns the total number of entries across all shards.
    pub fn len(&self) -> usize {
        self.shards.iter().map(|s| s.len()).sum()
    }

    /// Returns `true` if the cache contains no entries.
    pub fn is_empty(&self) -> bool {
        self.shards.iter().all(|s| s.is_empty())
    }

    // --- shard routing ---

    #[inline(always)]
    fn shard<Q>(&self, key: &Q) -> &LruShardMap<K, V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let idx = self.hasher.hash_one(key) as usize % self.shards.len();
        &self.shards[idx]
    }

    // ------------------------------------------------------------------
    // Public API – mirrors lockmap::LockMap
    // ------------------------------------------------------------------

    /// Gets exclusive access to an entry in the cache.
    ///
    /// The returned [`LruEntryByVal`] provides exclusive access to the key and
    /// its associated value until it is dropped. Accessing the entry promotes it
    /// in the LRU list and may trigger eviction of other entries.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap_lru::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// {
    ///     let mut entry = cache.entry("key".to_string());
    ///     entry.insert(42);
    /// }
    /// ```
    pub fn entry(&self, key: K) -> LruEntryByVal<'_, K, V> {
        let shard = self.shard(&key);
        let ptr: *mut State<K, V> = {
            let mut inner = shard.inner.lock().unwrap();
            let p = inner
                .map
                .get(&key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>);
            match p {
                Some(ptr) => {
                    // SAFETY: ptr is valid and ref-counted via AliasableBox.
                    unsafe { &*ptr }.inc_ref();
                    unsafe { inner.move_to_front(ptr) };
                    inner.try_evict();
                    ptr
                }
                None => {
                    let state = State::new(key.clone(), None, 1);
                    let ptr = &*state as *const State<K, V> as *mut State<K, V>;
                    inner.map.insert(key.clone(), state);
                    unsafe { inner.push_front(ptr) };
                    inner.try_evict();
                    ptr
                }
            }
        };
        self.guard_by_val(ptr, key)
    }

    /// Gets exclusive access to an entry by reference.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap_lru::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// {
    ///     let mut entry = cache.entry_by_ref("key");
    ///     entry.insert(42);
    /// }
    /// ```
    pub fn entry_by_ref<'a, 'b, Q>(&'a self, key: &'b Q) -> LruEntryByRef<'a, 'b, K, Q, V>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let shard = self.shard(key);
        let ptr: *mut State<K, V> = {
            let mut inner = shard.inner.lock().unwrap();
            let p = inner
                .map
                .get(key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>);
            match p {
                Some(ptr) => {
                    unsafe { &*ptr }.inc_ref();
                    unsafe { inner.move_to_front(ptr) };
                    inner.try_evict();
                    ptr
                }
                None => {
                    let owned_key: K = key.into();
                    let state = State::new(owned_key.clone(), None, 1);
                    let ptr = &*state as *const State<K, V> as *mut State<K, V>;
                    inner.map.insert(owned_key, state);
                    unsafe { inner.push_front(ptr) };
                    inner.try_evict();
                    ptr
                }
            }
        };
        self.guard_by_ref(ptr, key)
    }

    /// Gets the value associated with the given key.
    ///
    /// Accessing the key promotes it in the LRU list.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap_lru::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// cache.insert("key".to_string(), 42);
    /// assert_eq!(cache.get("key"), Some(42));
    /// assert_eq!(cache.get("missing"), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
        Q: Eq + Hash + ?Sized,
    {
        let shard = self.shard(key);
        let mut ptr: *mut State<K, V> = std::ptr::null_mut();

        let value = {
            let mut inner = shard.inner.lock().unwrap();
            let p = inner
                .map
                .get(key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>);
            match p {
                Some(p) => {
                    unsafe { inner.move_to_front(p) };

                    let state = unsafe { &*p };
                    if state.flags().refcnt() == 0 {
                        // SAFETY: refcnt == 0 means no Entry guard exists.
                        unsafe { state.value_ref() }.clone()
                    } else {
                        state.inc_ref();
                        ptr = p;
                        None
                    }
                }
                None => None,
            }
        };

        if ptr.is_null() {
            return value;
        }

        self.guard_by_ref(ptr, key).get().clone()
    }

    /// Inserts a value into the cache, returning the previous value if any.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap_lru::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// assert_eq!(cache.insert("key".to_string(), 42), None);
    /// assert_eq!(cache.insert("key".to_string(), 123), Some(42));
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let shard = self.shard(&key);
        let (ptr, old) = {
            let mut inner = shard.inner.lock().unwrap();
            let p = inner
                .map
                .get(&key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>);
            match p {
                Some(p) => {
                    unsafe { inner.move_to_front(p) };

                    let state = unsafe { &*p };
                    let flags = state.flags();
                    if flags.refcnt() == 0 {
                        // SAFETY: refcnt == 0 → exclusive.
                        let old = unsafe { state.value_mut() }.replace(value);
                        if !flags.has_value() {
                            state.set_value_state(true);
                        }
                        (std::ptr::null_mut(), old)
                    } else {
                        state.inc_ref();
                        (p, Some(value))
                    }
                }
                None => {
                    let state = State::new(key.clone(), Some(value), 0);
                    let p = &*state as *const State<K, V> as *mut State<K, V>;
                    inner.map.insert(key.clone(), state);
                    unsafe { inner.push_front(p) };
                    inner.try_evict();
                    (std::ptr::null_mut(), None)
                }
            }
        };

        if ptr.is_null() {
            return old;
        }

        self.guard_by_val(ptr, key).swap(old)
    }

    /// Inserts a value by reference key.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap_lru::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// cache.insert_by_ref("key", 42);
    /// assert_eq!(cache.get("key"), Some(42));
    /// ```
    pub fn insert_by_ref<Q>(&self, key: &Q, value: V) -> Option<V>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let shard = self.shard(key);
        let (ptr, old) = {
            let mut inner = shard.inner.lock().unwrap();
            let p = inner
                .map
                .get(key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>);
            match p {
                Some(p) => {
                    unsafe { inner.move_to_front(p) };

                    let state = unsafe { &*p };
                    let flags = state.flags();
                    if flags.refcnt() == 0 {
                        let old = unsafe { state.value_mut() }.replace(value);
                        if !flags.has_value() {
                            state.set_value_state(true);
                        }
                        (std::ptr::null_mut(), old)
                    } else {
                        state.inc_ref();
                        (p, Some(value))
                    }
                }
                None => {
                    let owned_key: K = key.into();
                    let state = State::new(owned_key.clone(), Some(value), 0);
                    let p = &*state as *const State<K, V> as *mut State<K, V>;
                    inner.map.insert(owned_key, state);
                    unsafe { inner.push_front(p) };
                    inner.try_evict();
                    (std::ptr::null_mut(), None)
                }
            }
        };

        if ptr.is_null() {
            return old;
        }

        self.guard_by_ref(ptr, key).swap(old)
    }

    /// Returns `true` if the cache contains the given key.
    ///
    /// Accessing the key promotes it in the LRU list.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap_lru::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// cache.insert("key".to_string(), 42);
    /// assert!(cache.contains_key("key"));
    /// assert!(!cache.contains_key("missing"));
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let shard = self.shard(key);
        let mut ptr: *mut State<K, V> = std::ptr::null_mut();

        let found = {
            let mut inner = shard.inner.lock().unwrap();
            let p = inner
                .map
                .get(key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>);
            match p {
                Some(p) => {
                    unsafe { inner.move_to_front(p) };

                    let state = unsafe { &*p };
                    if state.flags().refcnt() == 0 {
                        unsafe { state.value_ref() }.is_some()
                    } else {
                        state.inc_ref();
                        ptr = p;
                        false
                    }
                }
                None => false,
            }
        };

        if ptr.is_null() {
            return found;
        }

        self.guard_by_ref(ptr, key).get().is_some()
    }

    /// Removes a key from the cache, returning the value if it existed.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap_lru::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// cache.insert("key".to_string(), 42);
    /// assert_eq!(cache.remove("key"), Some(42));
    /// assert_eq!(cache.get("key"), None);
    /// ```
    pub fn remove<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let shard = self.shard(key);
        let mut ptr: *mut State<K, V> = std::ptr::null_mut();

        let value = {
            let mut inner = shard.inner.lock().unwrap();
            let p = inner
                .map
                .get(key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>);
            match p {
                Some(p) => {
                    let state = unsafe { &*p };
                    if state.flags().refcnt() == 0 {
                        // SAFETY: refcnt == 0 → exclusive.
                        let value = unsafe { state.value_mut() }.take();
                        unsafe { inner.detach(p) };
                        inner.map.remove(key);
                        value
                    } else {
                        state.inc_ref();
                        ptr = p;
                        None
                    }
                }
                None => None,
            }
        };

        if ptr.is_null() {
            return value;
        }

        self.guard_by_ref(ptr, key).remove()
    }

    // ------------------------------------------------------------------
    // Internal helpers
    // ------------------------------------------------------------------

    fn try_remove_entry<Q>(&self, key: &Q)
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let shard = self.shard(key);
        let mut inner = shard.inner.lock().unwrap();
        if let Some(state) = inner.map.get(key) {
            if state.flags().pending_cleanup() {
                let p = &**state as *const State<K, V> as *mut State<K, V>;
                // SAFETY: The state is in the linked list and the shard lock is held.
                unsafe { inner.detach(p) };
                inner.map.remove(key);
            }
        }
    }

    fn guard_by_val(&self, ptr: *mut State<K, V>, key: K) -> LruEntryByVal<'_, K, V> {
        // SAFETY: ptr is valid (ref-counted) and stable (AliasableBox).
        unsafe { (*ptr).mutex.lock() };
        LruEntryByVal {
            map: self,
            key,
            state: ptr,
        }
    }

    fn guard_by_ref<'a, 'b, Q>(
        &'a self,
        ptr: *mut State<K, V>,
        key: &'b Q,
    ) -> LruEntryByRef<'a, 'b, K, Q, V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        unsafe { (*ptr).mutex.lock() };
        LruEntryByRef {
            map: self,
            key,
            state: ptr,
        }
    }
}

impl<K: Eq + Hash + Clone, V> Default for LruLockMap<K, V> {
    fn default() -> Self {
        Self::new(0)
    }
}

impl<K, V> std::fmt::Debug for LruLockMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LruLockMap").finish()
    }
}

// ---------------------------------------------------------------------------
// LruEntryByVal
// ---------------------------------------------------------------------------

/// An RAII guard providing exclusive access to a key-value pair in the [`LruLockMap`].
///
/// When dropped, this type automatically unlocks the entry and may trigger
/// cleanup of empty entries.
pub struct LruEntryByVal<'a, K: Eq + Hash + Clone, V> {
    map: &'a LruLockMap<K, V>,
    key: K,
    state: *mut State<K, V>,
}

// SAFETY: The guard holds a per-key mutex lock and a valid, ref-counted pointer.
unsafe impl<K: Eq + Hash + Clone + Send, V: Send> Send for LruEntryByVal<'_, K, V> {}
unsafe impl<K: Eq + Hash + Clone + Send + Sync, V: Send + Sync> Sync for LruEntryByVal<'_, K, V> {}

impl<K: Eq + Hash + Clone, V> LruEntryByVal<'_, K, V> {
    /// Returns a reference to the entry's key.
    pub fn key(&self) -> &K {
        &self.key
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

impl<K: Eq + Hash + Clone + std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug
    for LruEntryByVal<'_, K, V>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LruEntryByVal")
            .field("key", &self.key)
            .field("value", self.get())
            .finish()
    }
}

impl<K: Eq + Hash + Clone, V> Drop for LruEntryByVal<'_, K, V> {
    fn drop(&mut self) {
        unsafe { &*self.state }.set_value_state(self.get().is_some());
        unsafe { &*self.state }.mutex.unlock();

        let flags = unsafe { (*self.state).dec_ref() };
        if flags.pending_cleanup() {
            self.map.try_remove_entry(&self.key);
        }
    }
}

// ---------------------------------------------------------------------------
// LruEntryByRef
// ---------------------------------------------------------------------------

/// An RAII guard providing exclusive access to a key-value pair in the [`LruLockMap`],
/// using a borrowed key reference.
pub struct LruEntryByRef<'a, 'b, K: Eq + Hash + Clone + Borrow<Q>, Q: Eq + Hash + ?Sized, V> {
    map: &'a LruLockMap<K, V>,
    key: &'b Q,
    state: *mut State<K, V>,
}

// SAFETY: Same as LruEntryByVal.
unsafe impl<K: Eq + Hash + Clone + Borrow<Q> + Send, Q: Eq + Hash + ?Sized + Sync, V: Send> Send
    for LruEntryByRef<'_, '_, K, Q, V>
{
}
unsafe impl<
        K: Eq + Hash + Clone + Borrow<Q> + Send + Sync,
        Q: Eq + Hash + ?Sized + Sync,
        V: Send + Sync,
    > Sync for LruEntryByRef<'_, '_, K, Q, V>
{
}

impl<K: Eq + Hash + Clone + Borrow<Q>, Q: Eq + Hash + ?Sized, V> LruEntryByRef<'_, '_, K, Q, V> {
    /// Returns a reference to the entry's key.
    pub fn key(&self) -> &Q {
        self.key
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

impl<K, Q, V> std::fmt::Debug for LruEntryByRef<'_, '_, K, Q, V>
where
    K: Eq + Hash + Clone + Borrow<Q> + std::fmt::Debug,
    Q: Eq + Hash + ?Sized + std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LruEntryByRef")
            .field("key", &self.key)
            .field("value", self.get())
            .finish()
    }
}

impl<K: Eq + Hash + Clone + Borrow<Q>, Q: Eq + Hash + ?Sized, V> Drop
    for LruEntryByRef<'_, '_, K, Q, V>
{
    fn drop(&mut self) {
        unsafe { &*self.state }.set_value_state(self.get().is_some());
        unsafe { &*self.state }.mutex.unlock();

        let flags = unsafe { (*self.state).dec_ref() };
        if flags.pending_cleanup() {
            self.map.try_remove_entry(self.key);
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

    // --- basic operations ---

    #[test]
    fn test_basic_insert_get_remove() {
        let cache = LruLockMap::<String, u32>::new(100);
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);

        cache.insert("a".to_string(), 1);
        assert_eq!(cache.get("a"), Some(1));
        assert!(!cache.is_empty());
        assert_eq!(cache.len(), 1);

        assert_eq!(cache.insert("a".to_string(), 2), Some(1));
        assert_eq!(cache.get("a"), Some(2));

        assert_eq!(cache.remove("a"), Some(2));
        assert_eq!(cache.get("a"), None);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_insert_by_ref() {
        let cache = LruLockMap::<String, u32>::new(100);
        cache.insert_by_ref("key", 42);
        assert_eq!(cache.get("key"), Some(42));
        assert_eq!(cache.insert_by_ref("key", 99), Some(42));
        assert_eq!(cache.get("key"), Some(99));
    }

    #[test]
    fn test_contains_key() {
        let cache = LruLockMap::<String, u32>::new(100);
        assert!(!cache.contains_key("x"));
        cache.insert("x".to_string(), 7);
        assert!(cache.contains_key("x"));
        cache.remove("x");
        assert!(!cache.contains_key("x"));
    }

    #[test]
    fn test_entry_by_val() {
        let cache = LruLockMap::<u32, u32>::new(100);
        {
            let mut entry = cache.entry(1);
            assert_eq!(*entry.key(), 1);
            assert!(entry.get().is_none());
            entry.insert(42);
            assert_eq!(*entry.get(), Some(42));
            println!("{:?}", entry);
        }
        assert_eq!(cache.get(&1), Some(42));
        {
            let mut entry = cache.entry(1);
            assert_eq!(entry.remove(), Some(42));
        }
        assert_eq!(cache.get(&1), None);
    }

    #[test]
    fn test_entry_by_ref() {
        let cache = LruLockMap::<String, u32>::new(100);
        {
            let mut entry = cache.entry_by_ref("key");
            assert_eq!(entry.key(), "key");
            entry.insert(7);
            println!("{:?}", entry);
        }
        assert_eq!(cache.get("key"), Some(7));
        {
            let mut entry = cache.entry_by_ref("key");
            assert_eq!(entry.get_mut().take(), Some(7));
        }
        assert_eq!(cache.get("key"), None);
    }

    #[test]
    fn test_default_and_debug() {
        let cache = LruLockMap::<u32, u32>::default();
        println!("{:?}", cache);
        assert!(cache.is_empty());
    }

    // --- LRU eviction ---

    #[test]
    fn test_lru_eviction_basic() {
        // 1 shard, capacity 3
        let cache = LruLockMap::<u32, u32>::with_capacity_and_shard_amount(3, 1);

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);
        assert_eq!(cache.len(), 3);

        // Inserting a 4th key should evict the LRU entry (key=1)
        cache.insert(4, 40);
        assert_eq!(cache.len(), 3);
        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.get(&2), Some(20));
        assert_eq!(cache.get(&3), Some(30));
        assert_eq!(cache.get(&4), Some(40));
    }

    #[test]
    fn test_lru_access_promotes() {
        // 1 shard, capacity 3
        let cache = LruLockMap::<u32, u32>::with_capacity_and_shard_amount(3, 1);

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        // Access key=1 to promote it
        assert_eq!(cache.get(&1), Some(10));

        // Now key=2 should be the LRU
        cache.insert(4, 40);
        assert_eq!(cache.get(&2), None); // evicted
        assert_eq!(cache.get(&1), Some(10)); // still present (was promoted)
        assert_eq!(cache.get(&3), Some(30));
        assert_eq!(cache.get(&4), Some(40));
    }

    #[test]
    fn test_lru_entry_promotes() {
        let cache = LruLockMap::<u32, u32>::with_capacity_and_shard_amount(3, 1);

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        // Access key=1 via entry to promote it
        {
            let entry = cache.entry(1);
            assert_eq!(*entry.get(), Some(10));
        }

        cache.insert(4, 40);
        assert_eq!(cache.get(&2), None); // evicted
        assert_eq!(cache.get(&1), Some(10)); // promoted
    }

    #[test]
    fn test_lru_skip_in_use_entry() {
        let cache = Arc::new(LruLockMap::<u32, u32>::with_capacity_and_shard_amount(3, 1));

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        // Hold entry for key=1 (the LRU tail after inserting 2 and 3)
        let _entry = cache.entry(1);

        // Insert key=4 — should try to evict key=1 but it's in use, so skip
        // The cache may grow beyond capacity temporarily.
        let cache2 = cache.clone();
        let t = std::thread::spawn(move || {
            cache2.insert(4, 40);
        });
        t.join().unwrap();

        // key=1 should still be present because it was in use
        assert_eq!(*_entry.get(), Some(10));

        // After dropping the entry, cleanup may happen on next access
        drop(_entry);

        // The cache may now have 4 items but future inserts will evict
        assert!(cache.len() <= 4);
    }

    #[test]
    fn test_lru_insert_overwrite_no_evict() {
        let cache = LruLockMap::<u32, u32>::with_capacity_and_shard_amount(3, 1);

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        // Overwriting an existing key should NOT increase count
        cache.insert(2, 200);
        assert_eq!(cache.len(), 3);
        assert_eq!(cache.get(&1), Some(10));
        assert_eq!(cache.get(&2), Some(200));
        assert_eq!(cache.get(&3), Some(30));
    }

    #[test]
    fn test_lru_remove_frees_slot() {
        let cache = LruLockMap::<u32, u32>::with_capacity_and_shard_amount(3, 1);

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        cache.remove(&2);
        assert_eq!(cache.len(), 2);

        // Should be able to add more without evicting
        cache.insert(4, 40);
        assert_eq!(cache.len(), 3);
        assert_eq!(cache.get(&1), Some(10));
        assert_eq!(cache.get(&3), Some(30));
        assert_eq!(cache.get(&4), Some(40));
    }

    #[test]
    fn test_lru_zero_capacity() {
        // With per-shard capacity of 0 (ceil division gives 0), inserts should
        // still work but immediately evict.
        let cache = LruLockMap::<u32, u32>::with_capacity_and_shard_amount(0, 4);
        cache.insert(1, 10);
        // The entry is evicted immediately after insert
        assert_eq!(cache.get(&1), None);
    }

    // --- concurrency tests ---

    #[test]
    fn test_concurrent_same_key() {
        let cache = Arc::new(LruLockMap::<usize, usize>::new(1024));
        let counter = Arc::new(AtomicU32::default());
        #[cfg(not(miri))]
        const N: usize = 1 << 16;
        #[cfg(miri)]
        const N: usize = 1 << 6;
        const M: usize = 4;

        cache.insert(0, 0);

        let threads: Vec<_> = (0..M)
            .map(|_| {
                let cache = cache.clone();
                let counter = counter.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let mut entry = cache.entry(0);
                        let now = counter.fetch_add(1, Ordering::AcqRel);
                        assert_eq!(now, 0);
                        let v = entry.get_mut().as_mut().unwrap();
                        *v += 1;
                        let now = counter.fetch_sub(1, Ordering::AcqRel);
                        assert_eq!(now, 1);
                    }
                })
            })
            .collect();
        threads.into_iter().for_each(|t| t.join().unwrap());

        let entry = cache.entry(0);
        assert_eq!(*entry.get(), Some(N * M));
    }

    #[test]
    fn test_concurrent_same_key_by_ref() {
        let cache = Arc::new(LruLockMap::<String, usize>::new(1024));
        let counter = Arc::new(AtomicU32::default());
        #[cfg(not(miri))]
        const N: usize = 1 << 16;
        #[cfg(miri)]
        const N: usize = 1 << 6;
        const M: usize = 4;

        cache.insert_by_ref("hello", 0);

        let threads: Vec<_> = (0..M)
            .map(|_| {
                let cache = cache.clone();
                let counter = counter.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let mut entry = cache.entry_by_ref("hello");
                        let now = counter.fetch_add(1, Ordering::AcqRel);
                        assert_eq!(now, 0);
                        let v = entry.get_mut().as_mut().unwrap();
                        *v += 1;
                        let now = counter.fetch_sub(1, Ordering::AcqRel);
                        assert_eq!(now, 1);
                    }
                })
            })
            .collect();
        threads.into_iter().for_each(|t| t.join().unwrap());

        let entry = cache.entry_by_ref("hello");
        assert_eq!(*entry.get(), Some(N * M));
    }

    #[test]
    fn test_concurrent_random_keys() {
        let cache = Arc::new(LruLockMap::<u32, u32>::with_capacity_and_shard_amount(
            256, 16,
        ));
        let total = Arc::new(AtomicU32::default());
        #[cfg(not(miri))]
        const N: usize = 1 << 12;
        #[cfg(miri)]
        const N: usize = 1 << 6;
        const M: usize = 8;

        let threads: Vec<_> = (0..M)
            .map(|_| {
                let cache = cache.clone();
                let total = total.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let key = rand::random::<u32>() % 32;
                        let mut entry = cache.entry(key);
                        assert!(entry.get().is_none());
                        entry.insert(1);
                        total.fetch_add(1, Ordering::AcqRel);
                        entry.remove();
                    }
                })
            })
            .collect();
        threads.into_iter().for_each(|t| t.join().unwrap());

        assert_eq!(total.load(Ordering::Acquire) as usize, N * M);
    }

    #[test]
    fn test_concurrent_get_set() {
        let cache = Arc::new(LruLockMap::<u32, u32>::with_capacity_and_shard_amount(
            256, 16,
        ));
        #[cfg(not(miri))]
        const N: usize = 1 << 16;
        #[cfg(miri)]
        const N: usize = 1 << 6;

        let entry_thread = {
            let cache = cache.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = rand::random::<u32>() % 32;
                    let value = rand::random::<u32>() % 32;
                    let mut entry = cache.entry(key);
                    if value < 16 {
                        entry.get_mut().take();
                    } else {
                        entry.get_mut().replace(value);
                    }
                }
            })
        };

        let set_thread = {
            let cache = cache.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = rand::random::<u32>() % 32;
                    let value = rand::random::<u32>() % 32;
                    if value < 16 {
                        cache.remove(&key);
                    } else {
                        cache.insert(key, value);
                    }
                }
            })
        };

        let get_thread = {
            let cache = cache.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = rand::random::<u32>() % 32;
                    let value = cache.get(&key);
                    if let Some(v) = value {
                        assert!(v >= 16);
                    }
                }
            })
        };

        entry_thread.join().unwrap();
        set_thread.join().unwrap();
        get_thread.join().unwrap();
    }

    #[test]
    fn test_concurrent_get_set_by_ref() {
        let cache = Arc::new(LruLockMap::<String, u32>::with_capacity_and_shard_amount(
            256, 16,
        ));
        #[cfg(not(miri))]
        const N: usize = 1 << 14;
        #[cfg(miri)]
        const N: usize = 1 << 6;

        let entry_thread = {
            let cache = cache.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = (rand::random::<u32>() % 32).to_string();
                    let value = rand::random::<u32>() % 32;
                    let mut entry = cache.entry_by_ref(&key);
                    if value < 16 {
                        entry.get_mut().take();
                    } else {
                        entry.get_mut().replace(value);
                    }
                }
            })
        };

        let set_thread = {
            let cache = cache.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = (rand::random::<u32>() % 32).to_string();
                    let value = rand::random::<u32>() % 32;
                    if value < 16 {
                        cache.remove(&key);
                    } else {
                        cache.insert_by_ref(&key, value);
                    }
                }
            })
        };

        let get_thread = {
            let cache = cache.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = (rand::random::<u32>() % 32).to_string();
                    let value = cache.get(&key);
                    if let Some(v) = value {
                        assert!(v >= 16);
                    }
                }
            })
        };

        entry_thread.join().unwrap();
        set_thread.join().unwrap();
        get_thread.join().unwrap();
    }

    #[test]
    fn test_concurrent_with_eviction() {
        // Small capacity to force frequent evictions under contention
        let cache = Arc::new(LruLockMap::<u32, u32>::with_capacity_and_shard_amount(
            32, 4,
        ));
        #[cfg(not(miri))]
        const N: usize = 1 << 14;
        #[cfg(miri)]
        const N: usize = 1 << 6;
        const M: usize = 8;

        let threads: Vec<_> = (0..M)
            .map(|_| {
                let cache = cache.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let key = rand::random::<u32>() % 64;
                        let op = rand::random::<u32>() % 4;
                        match op {
                            0 => {
                                cache.insert(key, key);
                            }
                            1 => {
                                let _ = cache.get(&key);
                            }
                            2 => {
                                let _ = cache.remove(&key);
                            }
                            _ => {
                                let mut entry = cache.entry(key);
                                entry.insert(key);
                                drop(entry);
                            }
                        }
                    }
                })
            })
            .collect();

        for t in threads {
            t.join().unwrap();
        }

        // The cache should not have grown unbounded
        assert!(cache.len() <= 64);
    }

    #[test]
    fn test_swap() {
        let cache = LruLockMap::<u32, u32>::new(100);
        cache.insert(1, 10);
        {
            let mut entry = cache.entry(1);
            let old = entry.swap(Some(20));
            assert_eq!(old, Some(10));
        }
        assert_eq!(cache.get(&1), Some(20));
    }

    #[test]
    fn test_lockmap_same_key_by_ref() {
        let lock_map = Arc::new(LruLockMap::<String, usize>::new(1 << 20));
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
    fn test_lockmap_get_set_by_ref() {
        let lock_map = Arc::new(LruLockMap::<String, u32>::with_capacity_and_shard_amount(
            1 << 20,
            16,
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
        let lock_map = Arc::new(LruLockMap::<u32, u32>::new(1 << 20));
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
