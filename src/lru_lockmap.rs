use crate::common::{default_shard_amount, StateFlags};
use aliasable::boxed::AliasableBox;
use foldhash::fast::RandomState;
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use parking_lot::lock_api::RawMutex as _;
use parking_lot::{Mutex, RawMutex};
use std::borrow::Borrow;
use std::cell::UnsafeCell;
use std::hash::{BuildHasher, Hash};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};

// ---------------------------------------------------------------------------
// State – per-key state with intrusive LRU list pointers
// ---------------------------------------------------------------------------

struct State<K, V> {
    key: K,
    hash: u64,
    flags: AtomicU32,
    mutex: RawMutex,
    value: UnsafeCell<Option<V>>,
    // Intrusive doubly-linked list pointers for LRU ordering.
    // These are only accessed while the shard's `parking_lot::Mutex` is held.
    prev: UnsafeCell<*mut Self>,
    next: UnsafeCell<*mut Self>,
}

impl<K, V> State<K, V> {
    fn new(key: K, value: Option<V>, refcnt: u32, hash: u64) -> AliasableBox<Self> {
        AliasableBox::from_unique(Box::new(Self {
            key,
            hash,
            flags: AtomicU32::new(StateFlags::new(refcnt, value.is_some()).0),
            mutex: RawMutex::INIT,
            value: UnsafeCell::new(value),
            prev: UnsafeCell::new(std::ptr::null_mut()),
            next: UnsafeCell::new(std::ptr::null_mut()),
        }))
    }

    fn flags(&self) -> StateFlags {
        StateFlags(self.flags.load(Ordering::Acquire))
    }

    /// Increments the reference count.
    ///
    /// # Note
    ///
    /// The reference count uses 31 bits, supporting up to 2^31 - 1 concurrent
    /// references. Overflow is checked in debug builds only.
    fn inc_ref(&self) -> StateFlags {
        let old = self.flags.fetch_add(1, Ordering::AcqRel);
        debug_assert!(
            StateFlags(old).refcnt() < StateFlags::REFCNT_MASK,
            "lockmap: reference count overflow"
        );
        StateFlags(old + 1)
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
// LruShardInner – HashTable + intrusive doubly-linked LRU list
//
// Uses `hashbrown::HashTable<AliasableBox<State<K, V>>>`.  The key and its
// pre-computed hash live inside `State`.  There is no per-shard hasher;
// a single `RandomState` owned by `LruLockMap` is used for all hashing.
// ---------------------------------------------------------------------------

struct LruShardInner<K, V> {
    table: HashTable<AliasableBox<State<K, V>>>,
    head: *mut State<K, V>,
    tail: *mut State<K, V>,
    max_size: usize,
    max_evict: usize,
}

// SAFETY: The raw pointers (head, tail, prev, next) are only accessed while
// the shard's `parking_lot::Mutex` is held, ensuring exclusive access.
unsafe impl<K: Send, V: Send> Send for LruShardInner<K, V> {}

impl<K, V> LruShardInner<K, V> {
    fn with_capacity(max_size: usize, capacity: usize) -> Self {
        Self {
            table: HashTable::with_capacity(capacity),
            head: std::ptr::null_mut(),
            tail: std::ptr::null_mut(),
            max_size,
            max_evict: usize::MAX,
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

    /// Try to evict the least-recently-used entries until the table size is within capacity.
    ///
    /// Walks from the tail (LRU end) towards the head (MRU end). Entries that
    /// are currently in use (refcnt > 0) are **skipped** and traversal continues
    /// to the next candidate.
    ///
    /// `current` is the entry that was just accessed or inserted — it must not
    /// be evicted even though it is at the head of the list.
    fn try_evict(&mut self, current: *mut State<K, V>) {
        let mut cursor = self.tail;
        let mut evicted = 0;
        while self.table.len() > self.max_size
            && !cursor.is_null()
            && cursor != current
            && evicted < self.max_evict
        {
            let prev = unsafe { *(*cursor).prev.get() };
            let state = unsafe { &*cursor };

            if state.flags().refcnt() > 0 {
                cursor = prev;
                continue;
            }

            unsafe { self.detach(cursor) };

            let hash = state.hash;
            if let Ok(entry) = self.table.find_entry(hash, |s| std::ptr::eq(&**s, cursor)) {
                let _ = entry.remove();
            }

            evicted += 1;
            cursor = prev;
        }
    }

    /// Removes and returns the least-recently-used entry of this shard.
    ///
    /// Walks from the tail (LRU end) towards the head (MRU end). Entries that
    /// are currently in use (refcnt > 0) are skipped. Returns `None` if no
    /// removable entry exists.
    fn pop_lru(&mut self) -> Option<(K, V)> {
        let mut cursor = self.tail;
        while !cursor.is_null() {
            // SAFETY: cursor is a valid node of this shard's list; the shard
            // mutex is held. `prev` is read before any removal.
            let prev = unsafe { *(*cursor).prev.get() };
            let state = unsafe { &*cursor };

            if state.flags().refcnt() == 0 {
                let hash = state.hash;
                // SAFETY: refcnt == 0 → no guard exists; safe to detach and remove.
                unsafe { self.detach(cursor) };
                if let Ok(entry) = self.table.find_entry(hash, |s| std::ptr::eq(&**s, cursor)) {
                    let (state_box, _) = entry.remove();
                    // SAFETY: the state is no longer shared: it has been removed
                    // from the table and the list, and refcnt == 0.
                    let state = AliasableBox::into_unique(state_box);
                    let State { key, value, .. } = *state;
                    if let Some(value) = value.into_inner() {
                        return Some((key, value));
                    }
                    // Entry without a value; keep scanning.
                }
            }
            cursor = prev;
        }
        None
    }
}

// ---------------------------------------------------------------------------
// LruShardMap
// ---------------------------------------------------------------------------

struct LruShardMap<K, V> {
    inner: Mutex<LruShardInner<K, V>>,
}

impl<K, V> LruShardMap<K, V> {
    fn with_capacity(max_size: usize, capacity: usize) -> Self {
        Self {
            inner: Mutex::new(LruShardInner::with_capacity(max_size, capacity)),
        }
    }

    fn len(&self) -> usize {
        self.inner.lock().table.len()
    }

    fn is_empty(&self) -> bool {
        self.inner.lock().table.is_empty()
    }

    fn max_size(&self) -> usize {
        self.inner.lock().max_size
    }

    fn set_max_size(&self, max_size: usize) {
        self.inner.lock().max_size = max_size;
    }

    fn set_max_evict(&self, max_evict: usize) {
        self.inner.lock().max_evict = max_evict.max(1);
    }
}

// ---------------------------------------------------------------------------
// LruLockMap
// ---------------------------------------------------------------------------

/// A thread-safe LRU cache that supports locking entries at the key level.
///
/// `LruLockMap` extends the per-key locking design of [`LockMap`](crate::LockMap)
/// with LRU (Least Recently Used) eviction. The total capacity is divided evenly
/// among internal shards, and each shard independently evicts its least-recently-used
/// entries when it exceeds its share of the capacity.
///
/// # Eviction Policy
///
/// - On every access (get, insert, entry, remove, contains_key), the accessed
///   entry is promoted to the head of its shard's LRU list.
/// - After an access that may increase the shard size, entries are evicted from
///   the tail of the LRU list until the shard is within capacity.
/// - Entries with an active [`LruEntry`] guard (refcnt > 0) are **skipped**
///   during eviction — traversal continues to the next candidate so that
///   eviction still makes progress even when the tail entry is held.
///
/// # Examples
///
/// ```
/// use lockmap::LruLockMap;
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
    /// Round-robin cursor for [`pop_lru`](Self::pop_lru) shard selection.
    pop_cursor: AtomicUsize,
}

impl<K: Eq + Hash, V> LruLockMap<K, V> {
    /// Creates a new `LruLockMap` with the given total capacity.
    ///
    /// The capacity is divided evenly among the default number of shards.
    pub fn new(max_size: usize) -> Self {
        Self::with_options(max_size, 0, default_shard_amount())
    }

    /// Creates a new `LruLockMap` with the given total capacity and number of shards.
    ///
    /// Each shard will have a capacity of `max_size / shard_amount` (rounded up).
    pub fn with_options(max_size: usize, initial_capacity: usize, shard_amount: usize) -> Self {
        assert!(shard_amount > 0, "shard_amount must be greater than 0");
        let per_shard_max_size = max_size.div_ceil(shard_amount);
        let per_shard_capacity = initial_capacity.div_ceil(shard_amount);
        Self {
            shards: (0..shard_amount)
                .map(|_| LruShardMap::with_capacity(per_shard_max_size, per_shard_capacity))
                .collect(),
            hasher: RandomState::default(),
            pop_cursor: AtomicUsize::new(0),
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

    /// Returns the configured target capacity of the cache, in number of entries.
    ///
    /// This is the total logical capacity across all shards, computed from the
    /// per‑shard limits. The per‑shard limit is derived using
    /// `max_size.div_ceil(shard_amount)`, so the effective total capacity may be
    /// rounded up compared to the value originally passed to
    /// [`with_options`](Self::with_options).
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::with_options(100, 100, 10);
    /// assert_eq!(cache.max_size(), 100);
    /// ```
    pub fn max_size(&self) -> usize {
        let max_size = self.shards.first().map(|s| s.max_size()).unwrap_or(0);
        self.shards.len() * max_size
    }

    /// Sets the maximum number of entries that can be stored in the cache.
    ///
    /// The capacity is divided evenly among all shards. Note that the actual
    /// capacity may be slightly larger than requested due to rounding up when
    /// dividing by number of shards.
    ///
    /// **Eviction behavior:** This operation does not immediately trigger eviction
    /// of excess entries. Eviction will occur lazily on subsequent insertions
    /// and other operations that may increase the cache size.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<u32, u32>::with_options(100, 100, 10);
    /// cache.set_max_size(200);
    /// assert_eq!(cache.max_size(), 200);
    /// ```
    pub fn set_max_size(&self, max_size: usize) {
        let per_shard_max_size = max_size.div_ceil(self.shards.len());
        for shard in &self.shards {
            shard.set_max_size(per_shard_max_size);
        }
    }

    /// Sets the maximum number of entries that can be evicted in a single `try_evict` call.
    ///
    /// The limit is applied **per shard**. The default is `usize::MAX`, meaning
    /// no limit is enforced and eviction continues until the shard is within
    /// capacity or all candidates are exhausted.
    ///
    /// A value of `0` is treated as `1`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<u32, u32>::with_options(10, 10, 1);
    /// cache.set_max_evict(3);
    /// ```
    pub fn set_max_evict(&self, max_evict: usize) {
        for shard in &self.shards {
            shard.set_max_evict(max_evict);
        }
    }

    // --- shard routing ---

    #[inline(always)]
    fn shard_index(&self, hash: u64) -> usize {
        ((hash >> 32) as usize) % self.shards.len()
    }

    #[inline(always)]
    fn state_hasher() -> impl Fn(&AliasableBox<State<K, V>>) -> u64 {
        |s| s.hash
    }

    // ------------------------------------------------------------------
    // Public API
    // ------------------------------------------------------------------

    /// Gets exclusive access to an entry in the cache.
    ///
    /// The returned [`LruEntry`] provides exclusive access to the key and
    /// its associated value until it is dropped. Accessing the entry promotes it
    /// in the LRU list and may trigger eviction of other entries.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// {
    ///     let mut entry = cache.entry("key".to_string());
    ///     entry.insert(42);
    /// }
    /// ```
    pub fn entry(&self, key: K) -> LruEntry<'_, K, V> {
        let ptr = self.acquire_state(key);
        self.guard(ptr)
    }

    /// Attempts to get exclusive access to an entry without blocking.
    ///
    /// Returns `None` if another thread currently holds the entry for this key.
    /// Unlike [`entry`](Self::entry), this method never blocks on the per-key
    /// lock (it may still wait briefly on the internal shard lock). The key is
    /// promoted in the LRU list even if `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// let entry = cache.entry("key".to_string());
    /// // The key is held by `entry`, so `try_entry` fails:
    /// assert!(cache.try_entry("key".to_string()).is_none());
    /// drop(entry);
    /// assert!(cache.try_entry("key".to_string()).is_some());
    /// ```
    pub fn try_entry(&self, key: K) -> Option<LruEntry<'_, K, V>> {
        let ptr = self.acquire_state(key);
        self.try_guard(ptr)
    }

    /// Acquires (or creates) the state for `key`, incrementing its reference
    /// count, promoting it in the LRU list and triggering eviction if needed.
    fn acquire_state(&self, key: K) -> *mut State<K, V> {
        let hash = self.hasher.hash_one(&key);
        let shard = &self.shards[self.shard_index(hash)];
        let mut inner = shard.inner.lock();
        let ptr = match inner
            .table
            .entry(hash, |s| s.key.borrow() == &key, Self::state_hasher())
        {
            Entry::Occupied(occupied) => {
                let ptr = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                unsafe { &*ptr }.inc_ref();
                unsafe { inner.move_to_front(ptr) };
                ptr
            }
            Entry::Vacant(vacant) => {
                let state = State::new(key, None, 1, hash);
                let ptr = &*state as *const State<K, V> as *mut State<K, V>;
                vacant.insert(state);
                unsafe { inner.push_front(ptr) };
                ptr
            }
        };
        inner.try_evict(ptr);
        ptr
    }

    /// Gets exclusive access to an entry by reference.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// {
    ///     let mut entry = cache.entry_by_ref("key");
    ///     entry.insert(42);
    /// }
    /// ```
    pub fn entry_by_ref<Q>(&self, key: &Q) -> LruEntry<'_, K, V>
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
    /// The key is promoted in the LRU list even if `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// let entry = cache.entry_by_ref("key");
    /// assert!(cache.try_entry_by_ref("key").is_none());
    /// drop(entry);
    /// assert!(cache.try_entry_by_ref("key").is_some());
    /// ```
    pub fn try_entry_by_ref<Q>(&self, key: &Q) -> Option<LruEntry<'_, K, V>>
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
        let ptr = match inner
            .table
            .entry(hash, |s| s.key.borrow() == key, Self::state_hasher())
        {
            Entry::Occupied(occupied) => {
                let ptr = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                unsafe { &*ptr }.inc_ref();
                unsafe { inner.move_to_front(ptr) };
                ptr
            }
            Entry::Vacant(vacant) => {
                let owned_key: K = key.into();
                let state = State::new(owned_key, None, 1, hash);
                let ptr = &*state as *const State<K, V> as *mut State<K, V>;
                vacant.insert(state);
                unsafe { inner.push_front(ptr) };
                ptr
            }
        };
        inner.try_evict(ptr);
        ptr
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
    /// # use lockmap::LruLockMap;
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
        let hash = self.hasher.hash_one(key);
        let shard = &self.shards[self.shard_index(hash)];
        let mut ptr: *mut State<K, V> = std::ptr::null_mut();

        let value = {
            let mut inner = shard.inner.lock();
            let p = inner
                .table
                .find(hash, |s| s.key.borrow() == key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>)
                .unwrap_or(std::ptr::null_mut());
            if !p.is_null() {
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
            } else {
                None
            }
        };

        if ptr.is_null() {
            return value;
        }

        self.guard(ptr).get().clone()
    }

    /// Gets the value associated with the given key **without** promoting it
    /// in the LRU list.
    ///
    /// Unlike [`get`](Self::get), calling `peek` does not affect the eviction
    /// order: the entry keeps its current position in the LRU list.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// cache.insert("key".to_string(), 42);
    /// assert_eq!(cache.peek("key"), Some(42));
    /// assert_eq!(cache.peek("missing"), None);
    /// ```
    pub fn peek<Q>(&self, key: &Q) -> Option<V>
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

    /// Inserts a value into the cache, returning the previous value if any.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// assert_eq!(cache.insert("key".to_string(), 42), None);
    /// assert_eq!(cache.insert("key".to_string(), 123), Some(42));
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
                Entry::Occupied(occupied) => {
                    let p = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                    unsafe { inner.move_to_front(p) };
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
                Entry::Vacant(vacant) => {
                    let state = State::new(key, Some(value), 0, hash);
                    let new_ptr = &*state as *const State<K, V> as *mut State<K, V>;
                    vacant.insert(state);
                    unsafe { inner.push_front(new_ptr) };
                    inner.try_evict(new_ptr);
                    (std::ptr::null_mut(), None)
                }
            }
        };

        if ptr.is_null() {
            return old;
        }

        self.guard(ptr).swap(old)
    }

    /// Inserts a value by reference key.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// cache.insert_by_ref("key", 42);
    /// assert_eq!(cache.get("key"), Some(42));
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
                Entry::Occupied(occupied) => {
                    let p = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                    unsafe { inner.move_to_front(p) };
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
                Entry::Vacant(vacant) => {
                    let owned_key: K = key.into();
                    let state = State::new(owned_key, Some(value), 0, hash);
                    let new_ptr = &*state as *const State<K, V> as *mut State<K, V>;
                    vacant.insert(state);
                    unsafe { inner.push_front(new_ptr) };
                    inner.try_evict(new_ptr);
                    (std::ptr::null_mut(), None)
                }
            }
        };

        if ptr.is_null() {
            return old;
        }

        self.guard(ptr).swap(old)
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
    /// # use lockmap::LruLockMap;
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
        let hash = self.hasher.hash_one(key);
        let shard = &self.shards[self.shard_index(hash)];
        let mut ptr: *mut State<K, V> = std::ptr::null_mut();

        let found = {
            let mut inner = shard.inner.lock();
            let p = inner
                .table
                .find(hash, |s| s.key.borrow() == key)
                .map(|s| &**s as *const State<K, V> as *mut State<K, V>)
                .unwrap_or(std::ptr::null_mut());
            if !p.is_null() {
                unsafe { inner.move_to_front(p) };

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

    /// Removes a key from the cache, returning the value if it existed.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
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
        let hash = self.hasher.hash_one(key);
        let shard = &self.shards[self.shard_index(hash)];

        let ptr = {
            let mut inner = shard.inner.lock();
            let p = match inner.table.find_entry(hash, |s| s.key.borrow() == key) {
                Ok(occupied) => {
                    let p = &**occupied.get() as *const State<K, V> as *mut State<K, V>;
                    let state = unsafe { &*p };
                    if state.flags().refcnt() == 0 {
                        // SAFETY: refcnt == 0 → exclusive.
                        let value = unsafe { state.value_mut() }.take();
                        let (state_box, _) = occupied.remove();
                        unsafe { inner.detach(p) };
                        drop(state_box);
                        return value;
                    }
                    state.inc_ref();
                    p
                }
                Err(_) => return None,
            };
            p
        };

        self.guard(ptr).remove()
    }

    /// Removes and returns a least-recently-used entry from the cache.
    ///
    /// Since the LRU order is maintained **per shard**, the returned entry is
    /// the least recently used of a single shard, not necessarily of the whole
    /// cache. Shards are visited in round-robin order across calls so repeated
    /// invocations drain all shards fairly.
    ///
    /// Entries that are currently held by an [`LruEntry`] guard are skipped,
    /// mirroring the eviction policy. Returns `None` if no removable entry
    /// exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<u32, u32>::with_options(10, 10, 1);
    /// cache.insert(1, 10);
    /// cache.insert(2, 20);
    /// cache.get(&1); // promote key=1
    /// assert_eq!(cache.pop_lru(), Some((2, 20)));
    /// assert_eq!(cache.pop_lru(), Some((1, 10)));
    /// assert_eq!(cache.pop_lru(), None);
    /// ```
    pub fn pop_lru(&self) -> Option<(K, V)> {
        let shard_count = self.shards.len();
        let start = self.pop_cursor.fetch_add(1, Ordering::Relaxed) % shard_count;
        for i in 0..shard_count {
            let shard = &self.shards[(start + i) % shard_count];
            if let Some(kv) = shard.inner.lock().pop_lru() {
                return Some(kv);
            }
        }
        None
    }

    /// Removes all key-value pairs from the cache.
    ///
    /// Entries that are currently held by an [`LruEntry`] guard are cleared by
    /// waiting for the guard to be released, exactly as [`remove`](Self::remove)
    /// would.
    ///
    /// **Locking behaviour:** Deadlock if called when holding any entry of this cache.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lockmap::LruLockMap;
    /// let cache = LruLockMap::<String, u32>::new(100);
    /// cache.insert("a".to_string(), 1);
    /// cache.insert("b".to_string(), 2);
    /// cache.clear();
    /// assert!(cache.is_empty());
    /// ```
    pub fn clear(&self) {
        for shard in &self.shards {
            let mut in_use: Vec<*mut State<K, V>> = Vec::new();
            {
                let mut inner = shard.inner.lock();
                let mut cursor = inner.head;
                while !cursor.is_null() {
                    // SAFETY: cursor is a valid node of this shard's list; the
                    // shard mutex is held. `next` is read before any removal.
                    let next = unsafe { *(*cursor).next.get() };
                    let state = unsafe { &*cursor };
                    if state.flags().refcnt() == 0 {
                        // SAFETY: refcnt == 0 → no guard exists; safe to drop.
                        let hash = state.hash;
                        unsafe { inner.detach(cursor) };
                        if let Ok(entry) =
                            inner.table.find_entry(hash, |s| std::ptr::eq(&**s, cursor))
                        {
                            let _ = entry.remove();
                        }
                    } else {
                        state.inc_ref();
                        in_use.push(cursor);
                    }
                    cursor = next;
                }
            }
            // For in-use entries, wait for the holders and remove the values.
            for ptr in in_use {
                self.guard(ptr).remove();
            }
        }
    }

    fn guard(&self, ptr: *mut State<K, V>) -> LruEntry<'_, K, V> {
        // SAFETY: ptr is valid (ref-counted) and stable (AliasableBox).
        unsafe { (*ptr).mutex.lock() };
        LruEntry {
            map: self,
            state: ptr,
        }
    }

    fn try_guard(&self, ptr: *mut State<K, V>) -> Option<LruEntry<'_, K, V>> {
        // SAFETY: ptr is valid (ref-counted) and stable (AliasableBox).
        if unsafe { (*ptr).mutex.try_lock() } {
            Some(LruEntry {
                map: self,
                state: ptr,
            })
        } else {
            self.release_ref(ptr);
            None
        }
    }

    /// Releases one reference to `state`; if this was the last reference and
    /// the entry holds no value, the entry is detached from the LRU list and
    /// removed from its shard.
    ///
    /// The per-key mutex must NOT be held by the caller.
    fn release_ref(&self, state: *mut State<K, V>) {
        let state_ref = unsafe { &*state };

        // CAS loop to decrement the reference count.
        let mut current = state_ref.flags.load(Ordering::Acquire);
        loop {
            let flags = StateFlags(current);

            // If this is the last reference and no value, proceed to cleanup.
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
                Ok(_) => return, // Not the last reference or still has value.
                Err(actual) => current = actual,
            }
        }

        // Acquire shard lock using the stored hash (no re-hashing).
        let shard = &self.shards[self.shard_index(state_ref.hash)];
        let mut inner = shard.inner.lock();

        // Decrement the reference count again; cleanup if needed.
        let final_flags = state_ref.dec_ref();
        if final_flags.pending_cleanup() {
            unsafe { inner.detach(state) };
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

impl<K: Eq + Hash, V> Default for LruLockMap<K, V> {
    fn default() -> Self {
        Self::new(usize::MAX)
    }
}

impl<K, V> std::fmt::Debug for LruLockMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LruLockMap").finish()
    }
}

// ---------------------------------------------------------------------------
// LruEntry
// ---------------------------------------------------------------------------

/// An RAII guard providing exclusive access to a key-value pair in the [`LruLockMap`].
///
/// The key is obtained directly from the internal `State`, so there is no need
/// for separate by-value / by-reference entry types.
///
/// When dropped, this type automatically unlocks the entry and may trigger
/// cleanup of empty entries.
pub struct LruEntry<'a, K: Eq + Hash, V> {
    map: &'a LruLockMap<K, V>,
    state: *mut State<K, V>,
}

// SAFETY: The guard holds a per-key mutex lock and a valid, ref-counted pointer.
// LruEntry is intentionally !Send — like MutexGuard, it should not be moved across threads.
// For Sync, only K: Sync and V: Sync are needed: sharing &LruEntry across threads only
// requires shared references (&K, &Option<V>) to be safe to share, not ownership transfer.
unsafe impl<K: Eq + Hash + Sync, V: Sync> Sync for LruEntry<'_, K, V> {}

impl<K: Eq + Hash, V> LruEntry<'_, K, V> {
    /// Returns a reference to the entry's key.
    pub fn key(&self) -> &K {
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

impl<K: Eq + Hash + std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug for LruEntry<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LruEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

impl<K: Eq + Hash, V> Drop for LruEntry<'_, K, V> {
    fn drop(&mut self) {
        // 1. Update value state flag
        let has_value = self.get().is_some();
        let state_ref = unsafe { &*self.state };
        state_ref.set_value_state(has_value);

        // 2. Unlock the entry's mutex
        // SAFETY: We hold the lock (acquired in guard()).
        unsafe { state_ref.mutex.unlock() };

        // 3. Release the reference; detaches and removes the entry if it is
        //    the last reference and no value is stored.
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

    #[test]
    fn test_lru_zero_capacity() {
        let cache = LruLockMap::<u32, u32>::with_options(0, 0, 1);
        assert!(cache.is_empty());

        assert_eq!(cache.insert(1, 10), None);
        assert_eq!(cache.len(), 1);

        assert_eq!(cache.insert(2, 20), None);
        assert_eq!(cache.len(), 1); // still 1 due to eviction
    }

    #[test]
    fn test_set_max_size() {
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 4);
        assert_eq!(cache.max_size(), 4);
        cache.set_max_size(6);
        assert_eq!(cache.max_size(), 8);
    }

    // --- LRU eviction ---

    #[test]
    fn test_lru_eviction_basic() {
        // 1 shard, capacity 3
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 1);

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
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 1);

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
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 1);

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
        let cache = Arc::new(LruLockMap::<u32, u32>::with_options(3, 3, 1));

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        // Hold entry for key=1 (the LRU tail after inserting 2 and 3)
        let _entry = cache.entry(1);

        // Insert key=4 — should try to evict key=1 but it's in use.
        let cache2 = cache.clone();
        let t = std::thread::spawn(move || {
            cache2.insert(4, 40);
        });
        t.join().unwrap();

        // key=1 should still be present because it was in use
        assert_eq!(*_entry.get(), Some(10));

        // key=2 should have been evicted (it was the next LRU candidate)
        assert_eq!(cache.get(&2), None);

        // key=3 and key=4 should still be present
        assert_eq!(cache.get(&3), Some(30));
        assert_eq!(cache.get(&4), Some(40));

        // After dropping the held entry, cache should be within capacity
        drop(_entry);
        assert!(cache.len() <= 4);
    }

    #[test]
    fn test_lru_evict_skips_multiple_in_use() {
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 1);

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        let _entry1 = cache.entry(1);
        let _entry2 = cache.entry(2);

        cache.insert(4, 40);

        assert_eq!(*_entry1.get(), Some(10));
        assert_eq!(*_entry2.get(), Some(20));

        assert_eq!(cache.get(&3), None);
        assert_eq!(cache.get(&4), Some(40));

        drop(_entry2);
        drop(_entry1);
    }

    #[test]
    fn test_lru_insert_overwrite_no_evict() {
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 1);

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        cache.insert(2, 200);
        assert_eq!(cache.len(), 3);
        assert_eq!(cache.get(&1), Some(10));
        assert_eq!(cache.get(&2), Some(200));
        assert_eq!(cache.get(&3), Some(30));
    }

    #[test]
    fn test_lru_remove_frees_slot() {
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 1);

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        cache.remove(&2);
        assert_eq!(cache.len(), 2);

        cache.insert(4, 40);
        assert_eq!(cache.len(), 3);
        assert_eq!(cache.get(&1), Some(10));
        assert_eq!(cache.get(&3), Some(30));
        assert_eq!(cache.get(&4), Some(40));
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
        let cache = Arc::new(LruLockMap::<u32, u32>::with_options(256, 16, 1));
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
        let cache = Arc::new(LruLockMap::<u32, u32>::with_options(256, 16, 1));
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
        let cache = Arc::new(LruLockMap::<String, u32>::with_options(256, 16, 1));
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
        let cache = Arc::new(LruLockMap::<u32, u32>::with_options(32, 4, 1));
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
        let lock_map = Arc::new(LruLockMap::<String, u32>::with_options(1 << 20, 16, 1));
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
    fn test_lockmap_insert_remove() {
        let lock_map = Arc::new(LruLockMap::<String, u32>::with_options(1 << 20, 16, 1));
        #[cfg(not(miri))]
        const N: usize = 1 << 22;
        #[cfg(miri)]
        const N: usize = 1 << 6;

        let entry_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = (rand::random::<u32>() % 32).to_string();
                    let mut entry = lock_map.entry_by_ref(&key);
                    entry.remove();
                }
            })
        };

        let set_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = (rand::random::<u32>() % 32).to_string();
                    let value = rand::random::<u32>() % 32;
                    lock_map.insert_by_ref(&key, value);
                }
            })
        };

        entry_thread.join().unwrap();
        set_thread.join().unwrap();
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

    // --- max_evict ---

    #[test]
    fn test_max_evict_default_unlimited() {
        let cache = LruLockMap::<u32, u32>::with_options(10, 10, 1);
        for i in 0..5u32 {
            cache.insert(i, i * 10);
        }
        assert_eq!(cache.len(), 5);

        // Shrink max_size to 1 — now 4 entries over capacity
        cache.set_max_size(1);

        // Insert triggers eviction. Default max_evict=usize::MAX should evict all
        // excess entries until within capacity (only the new entry remains).
        cache.insert(5, 50);
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&5), Some(50));
        assert!(cache.get(&0).is_none());
        assert!(cache.get(&1).is_none());
        assert!(cache.get(&2).is_none());
        assert!(cache.get(&3).is_none());
        assert!(cache.get(&4).is_none());
    }

    #[test]
    fn test_max_evict_limited() {
        let cache = LruLockMap::<u32, u32>::with_options(2, 2, 1);
        cache.set_max_evict(1);
        cache.insert(1, 10);
        cache.insert(2, 20);

        // Insert key 3, max_size=2 so we need to evict. max_evict=1 means only 1 can be evicted.
        cache.insert(3, 30);
        // Only key 1 (LRU) should be evicted, key 2 and 3 remain
        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.get(&2), Some(20));
        assert_eq!(cache.get(&3), Some(30));
    }

    #[test]
    fn test_max_evict_zero_treated_as_one() {
        let cache = LruLockMap::<u32, u32>::with_options(2, 2, 1);
        cache.set_max_evict(0); // should be treated as 1
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);
        assert_eq!(cache.get(&1), None); // key 1 evicted
        assert_eq!(cache.get(&2), Some(20));
        assert_eq!(cache.get(&3), Some(30));
    }

    #[test]
    fn test_max_evict_still_respects_in_use() {
        let cache = LruLockMap::<u32, u32>::with_options(1, 1, 1);
        cache.set_max_evict(1);
        cache.insert(1, 10);

        let _entry = cache.entry(1); // refcnt > 0, cannot be evicted

        cache.insert(2, 20); // need to evict key 1 but it's in use, and max_evict=1
        assert_eq!(*_entry.get(), Some(10)); // key 1 still present (in use)
        assert_eq!(cache.get(&2), Some(20));
    }

    #[test]
    fn test_max_evict_after_shrinking_capacity() {
        let cache = LruLockMap::<u32, u32>::with_options(10, 10, 1);
        for i in 0..5u32 {
            cache.insert(i, i * 10);
        }
        assert_eq!(cache.len(), 5);

        // Shrink max_size: 5 entries but max_size=2 → 3 slots over capacity
        cache.set_max_size(2);
        cache.set_max_evict(2);

        // Insert triggers eviction, but only up to max_evict=2
        cache.insert(5, 50);

        // 5 initial + 1 new - 2 evicted = 4 remaining
        assert_eq!(cache.len(), 4);

        // LRU entries 0 and 1 should be evicted
        assert_eq!(cache.get(&0), None);
        assert_eq!(cache.get(&1), None);

        // Remaining entries should still be present
        assert!(cache.get(&2).is_some());
        assert!(cache.get(&3).is_some());
        assert!(cache.get(&4).is_some());
        assert_eq!(cache.get(&5), Some(50));
    }

    // --- try_entry / clear ---

    #[test]
    fn test_lru_try_entry() {
        let cache = LruLockMap::<String, u32>::new(100);
        {
            let mut entry = cache.try_entry("key".to_string()).unwrap();
            entry.insert(1);
            assert!(cache.try_entry("key".to_string()).is_none());
            assert!(cache.try_entry_by_ref("key").is_none());
        }
        assert_eq!(cache.get("key"), Some(1));
        {
            let mut entry = cache.try_entry_by_ref("key").unwrap();
            assert_eq!(entry.remove(), Some(1));
        }
        // A failed try_entry on a held, empty key must not leak the entry.
        let held = cache.entry("held".to_string());
        assert!(cache.try_entry("held".to_string()).is_none());
        drop(held);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_lru_try_entry_promotes() {
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 1);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        // Promote key=1 via try_entry.
        assert!(cache.try_entry(1).is_some());

        cache.insert(4, 40);
        assert_eq!(cache.get(&2), None); // evicted
        assert_eq!(cache.get(&1), Some(10)); // promoted
    }

    #[test]
    fn test_lru_clear() {
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 1);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);
        cache.clear();
        assert!(cache.is_empty());

        // The LRU list must remain consistent after clear: eviction still works.
        cache.insert(4, 40);
        cache.insert(5, 50);
        cache.insert(6, 60);
        cache.insert(7, 70);
        assert_eq!(cache.len(), 3);
        assert_eq!(cache.get(&4), None); // evicted
        assert_eq!(cache.get(&5), Some(50));
        assert_eq!(cache.get(&6), Some(60));
        assert_eq!(cache.get(&7), Some(70));

        // Clearing an empty cache is a no-op.
        cache.clear();
        assert!(cache.is_empty());
    }

    // --- peek / pop_lru ---

    #[test]
    fn test_lru_peek_basic() {
        let cache = LruLockMap::<String, u32>::new(100);
        assert_eq!(cache.peek("missing"), None);
        cache.insert("key".to_string(), 42);
        assert_eq!(cache.peek("key"), Some(42));
        // Peeking does not remove or modify the value.
        assert_eq!(cache.get("key"), Some(42));
    }

    #[test]
    fn test_lru_peek_does_not_promote() {
        let cache = LruLockMap::<u32, u32>::with_options(3, 3, 1);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        // Peek key=1: unlike get, this must NOT promote it.
        assert_eq!(cache.peek(&1), Some(10));

        cache.insert(4, 40);
        assert_eq!(cache.peek(&1), None); // still evicted as LRU
        assert_eq!(cache.peek(&2), Some(20));
        assert_eq!(cache.peek(&3), Some(30));
        assert_eq!(cache.peek(&4), Some(40));
    }

    #[test]
    fn test_lru_peek_held_entry() {
        let cache = Arc::new(LruLockMap::<u32, u32>::new(100));
        cache.insert(1, 10);

        let entry = cache.entry(1);
        let peeker = {
            let cache = cache.clone();
            // peek on a held key blocks until the guard is released.
            std::thread::spawn(move || cache.peek(&1))
        };
        std::thread::sleep(std::time::Duration::from_millis(10));
        drop(entry);
        assert_eq!(peeker.join().unwrap(), Some(10));
    }

    #[test]
    fn test_lru_pop_lru_order() {
        let cache = LruLockMap::<u32, u32>::with_options(10, 10, 1);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        // Promote key=1; LRU order becomes 2, 3, 1.
        assert_eq!(cache.get(&1), Some(10));

        assert_eq!(cache.pop_lru(), Some((2, 20)));
        assert_eq!(cache.pop_lru(), Some((3, 30)));
        assert_eq!(cache.pop_lru(), Some((1, 10)));
        assert_eq!(cache.pop_lru(), None);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_lru_pop_lru_skips_in_use() {
        let cache = LruLockMap::<u32, u32>::with_options(10, 10, 1);
        cache.insert(1, 10);
        cache.insert(2, 20);

        // Hold key=1 (the LRU tail); pop_lru must skip it.
        let held = cache.entry(1);
        assert_eq!(cache.pop_lru(), Some((2, 20)));
        assert_eq!(cache.pop_lru(), None); // only the held entry remains
        drop(held);

        assert_eq!(cache.pop_lru(), Some((1, 10)));
    }

    #[test]
    fn test_lru_pop_lru_skips_empty_entry() {
        let cache = LruLockMap::<u32, u32>::with_options(10, 10, 1);
        // A held entry without a value must not be returned.
        let held = cache.entry(1);
        assert_eq!(cache.pop_lru(), None);
        drop(held);
        assert_eq!(cache.pop_lru(), None);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_lru_pop_lru_multi_shard() {
        let cache = LruLockMap::<u32, u32>::with_options(100, 0, 4);
        for i in 0..10 {
            cache.insert(i, i * 10);
        }

        let mut popped = std::collections::BTreeSet::new();
        while let Some((k, v)) = cache.pop_lru() {
            assert_eq!(v, k * 10);
            assert!(popped.insert(k), "duplicate key {k}");
        }
        assert_eq!(popped.len(), 10);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_lru_pop_lru_concurrent() {
        let cache = Arc::new(LruLockMap::<u32, u32>::with_options(1 << 16, 0, 4));
        #[cfg(not(miri))]
        const N: u32 = 1 << 10;
        #[cfg(miri)]
        const N: u32 = 1 << 5;
        const M: usize = 4;

        for i in 0..N {
            cache.insert(i, i);
        }

        let total = Arc::new(AtomicU32::new(0));
        let threads: Vec<_> = (0..M)
            .map(|_| {
                let cache = cache.clone();
                let total = total.clone();
                std::thread::spawn(move || {
                    while let Some((k, v)) = cache.pop_lru() {
                        assert_eq!(k, v);
                        total.fetch_add(1, Ordering::AcqRel);
                    }
                })
            })
            .collect();
        threads.into_iter().for_each(|t| t.join().unwrap());

        assert_eq!(total.load(Ordering::Acquire), N);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_lru_clear_with_held_entry() {
        let cache = Arc::new(LruLockMap::<u32, u32>::new(100));
        cache.insert(1, 10);

        let mut held = cache.entry(2);
        held.insert(20);

        let cleaner = {
            let cache = cache.clone();
            std::thread::spawn(move || cache.clear())
        };

        // Give the cleaner a chance to reach the held entry, then release it.
        std::thread::sleep(std::time::Duration::from_millis(10));
        drop(held);
        cleaner.join().unwrap();

        assert!(cache.is_empty());
        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.get(&2), None);
    }
}
