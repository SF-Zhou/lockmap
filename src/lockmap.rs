use crate::{Mutex, ShardsMap, SimpleAction, UpdateAction};
use aliasable::boxed::AliasableBox;
use std::borrow::Borrow;
use std::cell::UnsafeCell;
use std::collections::BTreeSet;
use std::hash::Hash;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::OnceLock;

/// Internal state for a key-value pair in the `LockMap`.
///
/// This type manages the stored value, the per-key lock, and a reference count
/// used for both synchronization optimization and memory management.
struct State<V> {
    refcnt: AtomicU32,
    mutex: Mutex,
    value: UnsafeCell<Option<V>>,
}

// SAFETY: `State<V>` is `Sync` if `V` is `Send` because access to the `UnsafeCell<Option<V>>`
// is strictly controlled by the internal `Mutex`. The `refcnt` is an `AtomicU32` which is
// inherently thread-safe.
unsafe impl<V: Send> Sync for State<V> {}

impl<V> State<V> {
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

/// A thread-safe hashmap that supports locking entries at the key level.
pub struct LockMap<K, V> {
    map: ShardsMap<K, AliasableBox<State<V>>>,
}

impl<K: Eq + Hash, V> Default for LockMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

/// Returns the default number of shards to use for the `LockMap`.
fn default_shard_amount() -> usize {
    static DEFAULT_SHARD_AMOUNT: OnceLock<usize> = OnceLock::new();
    *DEFAULT_SHARD_AMOUNT.get_or_init(|| {
        (std::thread::available_parallelism().map_or(1, usize::from) * 4).next_power_of_two()
    })
}

/// The main thread-safe map type providing per-key level locking.
impl<K: Eq + Hash, V> LockMap<K, V> {
    /// Creates a new `LockMap` with the default number of shards.
    ///
    /// # Returns
    ///
    /// A new `LockMap` instance.
    pub fn new() -> Self {
        Self {
            map: ShardsMap::with_capacity_and_shard_amount(0, default_shard_amount()),
        }
    }

    /// Creates a new `LockMap` with the specified initial capacity and the default number of shards.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The initial capacity of the hashmap.
    ///
    /// # Returns
    ///
    /// A new `LockMap` instance.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: ShardsMap::with_capacity_and_shard_amount(capacity, default_shard_amount()),
        }
    }

    /// Creates a new `LockMap` with the specified initial capacity and number of shards.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The initial capacity of the hashmap.
    /// * `shard_amount` - The number of shards to create.
    ///
    /// # Returns
    ///
    /// A new `LockMap` instance.
    pub fn with_capacity_and_shard_amount(capacity: usize, shard_amount: usize) -> Self {
        Self {
            map: ShardsMap::with_capacity_and_shard_amount(capacity, shard_amount),
        }
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Gets exclusive access to an entry in the map.
    ///
    /// The returned `EntryByVal` provides exclusive access to the key and its associated value
    /// until it is dropped.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    /// ```
    /// # use lockmap::LockMap;
    /// let map = LockMap::<String, u32>::new();
    /// {
    ///     let mut entry = map.entry("key".to_string());
    ///     entry.insert(42);
    ///     // let _ = map.get("key".to_string()); // DEADLOCK!
    ///     // map.insert("key".to_string(), 21); // DEADLOCK!
    ///     // map.remove("key".to_string()); // DEADLOCK!
    ///     // let mut entry2 = map.entry("key".to_string()); // DEADLOCK!
    /// }
    /// ```
    pub fn entry(&self, key: K) -> EntryByVal<'_, K, V>
    where
        K: Clone,
    {
        let ptr: *mut State<V> = self.map.update(key.clone(), |s| match s {
            Some(state) => {
                state.refcnt.fetch_add(1, Ordering::AcqRel);
                let ptr = &**state as *const State<V> as *mut State<V>;
                (UpdateAction::Keep, ptr)
            }
            None => {
                let state = AliasableBox::from_unique(Box::new(State {
                    refcnt: AtomicU32::new(1),
                    mutex: Mutex::new(),
                    value: UnsafeCell::new(None),
                }));
                let ptr = &*state as *const State<V> as *mut State<V>;
                (UpdateAction::Replace(state), ptr)
            }
        });

        self.guard_by_val(ptr, key)
    }

    /// Gets exclusive access to an entry in the map.
    ///
    /// The returned `EntryByVal` provides exclusive access to the key and its associated value
    /// until it is dropped.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    /// ```
    /// # use lockmap::LockMap;
    /// let map = LockMap::<String, u32>::new();
    /// {
    ///     let mut entry = map.entry_by_ref("key");
    ///     entry.insert(42);
    ///     // let _ = map.get("key"); // DEADLOCK!
    ///     // map.insert_by_ref("key", 21); // DEADLOCK!
    ///     // map.remove("key"); // DEADLOCK!
    ///     // let mut entry2 = map.entry_by_ref("key"); // DEADLOCK!
    /// }
    /// ```
    pub fn entry_by_ref<'a, 'b, Q>(&'a self, key: &'b Q) -> EntryByRef<'a, 'b, K, Q, V>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let ptr: *mut State<V> = self.map.update_by_ref(key, |s| match s {
            Some(state) => {
                state.refcnt.fetch_add(1, Ordering::AcqRel);
                let ptr = &**state as *const State<V> as *mut State<V>;
                (UpdateAction::Keep, ptr)
            }
            None => {
                let state = AliasableBox::from_unique(Box::new(State {
                    refcnt: AtomicU32::new(1),
                    mutex: Mutex::new(),
                    value: UnsafeCell::new(None),
                }));
                let ptr = &*state as *const State<V> as *mut State<V>;
                (UpdateAction::Replace(state), ptr)
            }
        });

        self.guard_by_ref(ptr, key)
    }

    /// Gets the value associated with the given key.
    ///
    /// If other threads are currently accessing the key, this will wait
    /// until exclusive access is available before returning.
    ///
    /// # Arguments
    /// * `key` - The key to look up
    ///
    /// # Returns
    /// * `Some(V)` if the key exists
    /// * `None` if the key doesn't exist
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<String, u32>::new();
    /// map.insert_by_ref("key", 42);
    /// assert_eq!(map.get("key"), Some(42));
    /// assert_eq!(map.get("missing"), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
        Q: Eq + Hash + ?Sized,
    {
        let mut ptr: *mut State<V> = std::ptr::null_mut();
        let value = self.map.simple_update(key, |s| match s {
            Some(state) => {
                // Use Acquire to ensure we see the latest value if refcnt is 0.
                if state.refcnt.load(Ordering::Acquire) == 0 {
                    // SAFETY: We are inside the map's shard lock, and refcnt is 0,
                    // meaning no other thread can be holding an `Entry` for this key.
                    let value = unsafe { state.value_ref() }.clone();
                    (SimpleAction::Keep, value)
                } else {
                    state.refcnt.fetch_add(1, Ordering::AcqRel);
                    ptr = &**state as *const State<V> as *mut State<V>;
                    (SimpleAction::Keep, None)
                }
            }
            None => (SimpleAction::Keep, None),
        });

        if ptr.is_null() {
            return value;
        }

        self.guard_by_ref(ptr, key).get().clone()
    }

    /// Sets a value in the map.
    ///
    /// If other threads are currently accessing the key, this will wait
    /// until exclusive access is available before updating.
    ///
    /// # Arguments
    /// * `key` - The key to update
    /// * `value` - The value to set
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<String, u32>::new();
    ///
    /// // Set a value
    /// assert_eq!(map.insert("key".to_string(), 42), None);
    ///
    /// // Update existing value
    /// assert_eq!(map.insert("key".to_string(), 123), Some(42));
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<V>
    where
        K: Clone,
    {
        let (ptr, value) = self.map.update(key.clone(), move |s| match s {
            Some(state) => {
                // Use Acquire to ensure we see the latest value if refcnt is 0.
                if state.refcnt.load(Ordering::Acquire) == 0 {
                    // SAFETY: We are inside the map's shard lock, and refcnt is 0,
                    // meaning no other thread can be holding an `Entry` for this key.
                    let value = unsafe { state.value_mut() }.replace(value);
                    (UpdateAction::Keep, (std::ptr::null_mut(), value))
                } else {
                    state.refcnt.fetch_add(1, Ordering::AcqRel);
                    let ptr: *mut State<V> = &**state as *const State<V> as *mut State<V>;
                    (UpdateAction::Keep, (ptr, Some(value)))
                }
            }
            None => {
                let state = AliasableBox::from_unique(Box::new(State {
                    refcnt: AtomicU32::new(0),
                    mutex: Mutex::new(),
                    value: UnsafeCell::new(Some(value)),
                }));
                (UpdateAction::Replace(state), (std::ptr::null_mut(), None))
            }
        });

        if ptr.is_null() {
            return value;
        }

        self.guard_by_val(ptr, key).swap(value)
    }

    /// Sets a value in the map.
    ///
    /// If other threads are currently accessing the key, this will wait
    /// until exclusive access is available before updating.
    ///
    /// # Arguments
    /// * `key` - The key to update
    /// * `value` - The value to set
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<String, u32>::new();
    ///
    /// // Set a value
    /// map.insert_by_ref("key", 42);
    ///
    /// // Update existing value
    /// map.insert_by_ref("key", 123);
    /// ```
    pub fn insert_by_ref<Q>(&self, key: &Q, value: V) -> Option<V>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let (ptr, value) = self.map.update_by_ref(key, move |s| match s {
            Some(state) => {
                // Use Acquire to ensure we see the latest value if refcnt is 0.
                if state.refcnt.load(Ordering::Acquire) == 0 {
                    // SAFETY: We are inside the map's shard lock, and refcnt is 0,
                    // meaning no other thread can be holding an `Entry` for this key.
                    let value = unsafe { state.value_mut() }.replace(value);
                    (UpdateAction::Keep, (std::ptr::null_mut(), value))
                } else {
                    state.refcnt.fetch_add(1, Ordering::AcqRel);
                    let ptr: *mut State<V> = &**state as *const State<V> as *mut State<V>;
                    (UpdateAction::Keep, (ptr, Some(value)))
                }
            }
            None => {
                let state = AliasableBox::from_unique(Box::new(State {
                    refcnt: AtomicU32::new(0),
                    mutex: Mutex::new(),
                    value: UnsafeCell::new(Some(value)),
                }));
                (UpdateAction::Replace(state), (std::ptr::null_mut(), None))
            }
        });

        if ptr.is_null() {
            return value;
        }

        self.guard_by_ref(ptr, key).swap(value)
    }

    /// Checks if the map contains a key.
    ///
    /// If other threads are currently accessing the key, this will wait
    /// until exclusive access is available before checking.
    ///
    /// # Arguments
    /// * `key` - The key to check
    ///
    /// # Returns
    /// * `true` if the key exists
    /// * `false` if the key doesn't exist
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
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
        let mut ptr: *mut State<V> = std::ptr::null_mut();
        let value = self.map.simple_update(key, |s| match s {
            Some(state) => {
                // Use Acquire to ensure we see the latest value if refcnt is 0.
                if state.refcnt.load(Ordering::Acquire) == 0 {
                    // SAFETY: We are inside the map's shard lock, and refcnt is 0,
                    // meaning no other thread can be holding an `Entry` for this key.
                    (SimpleAction::Keep, unsafe { state.value_ref() }.is_some())
                } else {
                    state.refcnt.fetch_add(1, Ordering::AcqRel);
                    ptr = &**state as *const State<V> as *mut State<V>;
                    (SimpleAction::Keep, false)
                }
            }
            None => (SimpleAction::Keep, false),
        });

        if ptr.is_null() {
            return value;
        }

        self.guard_by_ref(ptr, key).get().is_some()
    }

    /// Removes a key from the map.
    ///
    /// If other threads are currently accessing the key, this will wait
    /// until exclusive access is available before removing.
    ///
    /// # Arguments
    /// * `key` - The key to remove
    ///
    /// # Returns
    /// * `Some(V)` if the key exists
    /// * `None` if the key doesn't exist
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
    ///
    /// # Examples
    /// ```
    /// use lockmap::LockMap;
    ///
    /// let map = LockMap::<String, u32>::new();
    /// map.insert_by_ref("key", 42);
    /// assert_eq!(map.remove("key"), Some(42));
    /// assert_eq!(map.get("key"), None);
    /// ```
    pub fn remove<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let mut ptr: *mut State<V> = std::ptr::null_mut();
        let value = self.map.simple_update(key, |s| match s {
            Some(state) => {
                // Use Acquire to ensure we see the latest value if refcnt is 0.
                if state.refcnt.load(Ordering::Acquire) == 0 {
                    // SAFETY: We are inside the map's shard lock, and refcnt is 0,
                    // meaning no other thread can be holding an `Entry` for this key.
                    let value = unsafe { state.value_mut() }.take();
                    (SimpleAction::Remove, value)
                } else {
                    state.refcnt.fetch_add(1, Ordering::AcqRel);
                    ptr = &**state as *const State<V> as *mut State<V>;
                    (SimpleAction::Keep, None)
                }
            }
            None => (SimpleAction::Keep, None),
        });

        if ptr.is_null() {
            return value;
        }

        self.guard_by_ref(ptr, key).remove()
    }

    /// Acquires exclusive locks for a batch of keys in a deadlock-safe manner.
    ///
    /// This function is designed to prevent deadlocks that can occur when multiple threads
    /// try to acquire locks on the same set of keys in different orders. It achieves this
    /// by taking a `BTreeSet` of keys, which ensures the keys are processed and locked
    /// in a consistent, sorted order across all threads.
    ///
    /// The function iterates through the sorted keys, acquiring an exclusive lock for each
    /// key and its associated value. The returned `Vec` contains RAII guards, which
    /// automatically release the locks when they are dropped.
    ///
    /// # Arguments
    ///
    /// * `keys` - The `BTreeSet` of keys to lock. The use of `BTreeSet` is crucial as it
    ///   enforces a global, canonical locking order, thus preventing deadlocks.
    ///
    /// # Returns
    ///
    /// A `Vec<EntryByVal<K, V>>` containing the RAII guards for each locked key.
    ///
    /// **Locking behaviour:** Deadlock if called when holding the same entry.
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
    /// // Create a set of keys to lock. Note that the order in the set doesn't matter
    /// // since BTreeSet will sort them.
    /// let mut keys = BTreeSet::new();
    /// keys.insert(3);
    /// keys.insert(1);
    /// keys.insert(2);
    ///
    /// // Acquire locks for all keys in a deadlock-safe manner
    /// let mut locked_entries = map.batch_lock::<std::collections::HashMap<_, _>>(keys);
    ///
    /// // The locks are held as long as `locked_entries` is in scope
    /// locked_entries.get_mut(&1).and_then(|entry| entry.insert(101));
    /// locked_entries.get_mut(&2).and_then(|entry| entry.insert(201));
    /// locked_entries.get_mut(&3).and_then(|entry| entry.insert(301));
    ///
    /// // When `locked_entries` is dropped, all locks are released
    /// drop(locked_entries);
    ///
    /// assert_eq!(map.get(&1), Some(101));
    /// assert_eq!(map.get(&2), Some(201));
    /// assert_eq!(map.get(&3), Some(301));
    /// ```
    pub fn batch_lock<'a, M>(&'a self, keys: BTreeSet<K>) -> M
    where
        K: Clone,
        M: FromIterator<(K, EntryByVal<'a, K, V>)>,
    {
        keys.into_iter()
            .map(|key| (key.clone(), self.entry(key)))
            .collect()
    }

    /// Attempts to remove an entry from the map if it's no longer needed.
    ///
    /// An entry is considered no longer needed if its reference count is 0
    /// and it contains no value.
    fn try_remove_entry<Q>(&self, key: &Q)
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.simple_update(key, |value| match value {
            Some(state) => {
                // SAFETY: We are inside the map's shard lock. If `refcnt` is 0 here,
                // then no `Entry` is currently held for this key, and no other thread
                // can increment `refcnt` without first acquiring this same shard lock.
                // Therefore, if the stored value is also `None`, it is safe to remove
                // the entry from the map.
                if state.refcnt.load(Ordering::Acquire) == 0
                    && unsafe { state.value_ref() }.is_none()
                {
                    (SimpleAction::Remove, ())
                } else {
                    (SimpleAction::Keep, ())
                }
            }
            // The key might have been removed by another thread (e.g., via `remove`)
            // between the `refcnt` decrement and this call.
            None => (SimpleAction::Keep, ()),
        });
    }

    fn guard_by_val(&self, ptr: *mut State<V>, key: K) -> EntryByVal<'_, K, V> {
        // SAFETY: The pointer `ptr` is valid because it was just retrieved from the map
        // and its reference count was incremented, ensuring it won't be dropped.
        // The `AliasableBox` in the map ensures the `State<V>` remains at a stable
        // memory location.
        unsafe { (*ptr).mutex.lock() };
        EntryByVal {
            map: self,
            key,
            state: ptr,
        }
    }

    fn guard_by_ref<'a, 'b, Q>(
        &'a self,
        ptr: *mut State<V>,
        key: &'b Q,
    ) -> EntryByRef<'a, 'b, K, Q, V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        // SAFETY: Same as `guard_by_val`.
        unsafe { (*ptr).mutex.lock() };
        EntryByRef {
            map: self,
            key,
            state: ptr,
        }
    }
}

impl<K, V> std::fmt::Debug for LockMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LockMap").finish()
    }
}

/// An RAII guard providing exclusive access to a key-value pair in the `LockMap`.
///
/// When dropped, this type automatically unlocks the entry allowing other threads to access it.
///
/// # Type Parameters
/// * `'a` - Lifetime of the `LockMap`
/// * `K` - Key type that must implement `Eq + Hash`
/// * `V` - Value type
///
/// # Examples
/// ```
/// use lockmap::LockMap;
///
/// let map = LockMap::new();
/// {
///     // Get exclusive access to an entry
///     let mut entry = map.entry("key");
///
///     // Modify the value
///     entry.insert(42);
///
///     // EntryByVal is automatically unlocked when dropped
/// }
/// ```
pub struct EntryByVal<'a, K: Eq + Hash, V> {
    map: &'a LockMap<K, V>,
    key: K,
    state: *mut State<V>,
}

// SAFETY: `EntryByVal` is `Send` if `K` and `V` are `Send`. It holds a raw pointer to `State<V>`,
// which is safe to transfer between threads because the entry is locked and the `State`
// itself is `Sync`.
unsafe impl<K: Eq + Hash + Send, V: Send> Send for EntryByVal<'_, K, V> {}

// SAFETY: `EntryByVal` is `Sync` if `K` is `Sync` and `V` is `Sync`. Multiple threads can
// share a reference to `EntryByVal` safely because all access to the underlying value
// is synchronized by the lock held by the entry.
unsafe impl<K: Eq + Hash + Sync, V: Sync> Sync for EntryByVal<'_, K, V> {}

impl<K: Eq + Hash, V> EntryByVal<'_, K, V> {
    /// Returns a reference to the entry's key.
    ///
    /// # Returns
    ///
    /// A reference to the key associated with this entry.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Returns a reference to the entry's value.
    ///
    /// # Returns
    ///
    /// A reference to `Some(V)` if the entry has a value, or `None` if the entry is vacant.
    pub fn get(&self) -> &Option<V> {
        // SAFETY: The entry holds the lock on the `State`, so it is safe to access the value.
        unsafe { (*self.state).value_ref() }
    }

    /// Returns a mutable reference to the entry's value.
    ///
    /// # Returns
    ///
    /// A mutable reference to `Some(V)` if the entry has a value, or `None` if the entry is vacant.
    pub fn get_mut(&mut self) -> &mut Option<V> {
        // SAFETY: The entry holds the lock on the `State`, so it is safe to access the value.
        unsafe { (*self.state).value_mut() }
    }

    /// Sets the value of the entry, returning the old value if it existed.
    ///
    /// # Arguments
    ///
    /// * `value` - The new value to insert
    ///
    /// # Returns
    ///
    /// The previous value if the entry was occupied, or `None` if it was vacant.
    pub fn insert(&mut self, value: V) -> Option<V> {
        self.get_mut().replace(value)
    }

    /// Swaps the value of the entry with the provided value.
    ///
    /// # Arguments
    ///
    /// * `value` - The new value to swap in (wrapped in `Option`)
    ///
    /// # Returns
    ///
    /// The previous value of the entry.
    pub fn swap(&mut self, mut value: Option<V>) -> Option<V> {
        std::mem::swap(self.get_mut(), &mut value);
        value
    }

    /// Removes the value from the entry, returning it if it existed.
    ///
    /// # Returns
    ///
    /// The value that was stored in the entry, or `None` if the entry was vacant.
    pub fn remove(&mut self) -> Option<V> {
        // SAFETY: The entry holds the lock on the `State`, so it is safe to access the value.
        unsafe { (*self.state).value_mut() }.take()
    }
}

impl<K: Eq + Hash + std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug for EntryByVal<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EntryByVal")
            .field("key", &self.key)
            .field("value", self.get())
            .finish()
    }
}

impl<K: Eq + Hash, V> Drop for EntryByVal<'_, K, V> {
    fn drop(&mut self) {
        // SAFETY: The entry holds the lock on the `State`, so it is safe to unlock it.
        unsafe { (*self.state).mutex.unlock() };

        // SAFETY: The pointer `self.state` is valid because it was obtained from the map and its
        // reference count was incremented, ensuring the `State` won't be dropped while we hold it
        let prev = (unsafe { &*self.state })
            .refcnt
            .fetch_sub(1, Ordering::AcqRel);
        if prev == 1 {
            self.map.try_remove_entry(&self.key);
        }
    }
}

/// An RAII guard providing exclusive access to a key-value pair in the `LockMap`.
///
/// When dropped, this type automatically unlocks the entry allowing other threads to access it.
///
/// # Type Parameters
/// * `'a` - Lifetime of the `LockMap`
/// * `'b` - Lifetime of the key reference
/// * `K` - Key type that must implement `Eq + Hash`
/// * `Q` - Query type that can be borrowed from `K`
/// * `V` - Value type
///
/// # Examples
/// ```
/// use lockmap::LockMap;
///
/// let map = LockMap::<String, u32>::new();
/// {
///     // Get exclusive access to an entry
///     let mut entry = map.entry_by_ref("key");
///
///     // Modify the value
///     entry.insert(42);
///
///     // EntryByRef is automatically unlocked when dropped
/// }
/// ```
pub struct EntryByRef<'a, 'b, K: Eq + Hash + Borrow<Q>, Q: Eq + Hash + ?Sized, V> {
    map: &'a LockMap<K, V>,
    key: &'b Q,
    state: *mut State<V>,
}

// SAFETY: `EntryByRef` is `Send` if `K`, `Q` and `V` are `Send`. It holds a raw pointer to `State<V>`,
// which is safe to transfer between threads because the entry is locked and the `State`
// itself is `Sync`.
unsafe impl<K, Q, V> Send for EntryByRef<'_, '_, K, Q, V>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash + ?Sized + Sync,
    V: Send,
{
}

// SAFETY: `EntryByRef` is `Sync` if `K`, `Q` and `V` are `Sync`. Multiple threads can
// share a reference to `EntryByRef` safely because all access to the underlying value
// is synchronized by the lock held by the entry.
unsafe impl<K, Q, V> Sync for EntryByRef<'_, '_, K, Q, V>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash + ?Sized + Sync,
    V: Sync,
{
}

impl<K: Eq + Hash + Borrow<Q>, Q: Eq + Hash + ?Sized, V> EntryByRef<'_, '_, K, Q, V> {
    /// Returns a reference to the entry's key.
    ///
    /// # Returns
    ///
    /// A reference to the key associated with this entry.
    pub fn key(&self) -> &Q {
        self.key
    }

    /// Returns a reference to the entry's value.
    ///
    /// # Returns
    ///
    /// A reference to `Some(V)` if the entry has a value, or `None` if the entry is vacant.
    pub fn get(&self) -> &Option<V> {
        // SAFETY: The entry holds the lock on the `State`, so it is safe to access the value.
        unsafe { (*self.state).value_ref() }
    }

    /// Returns a mutable reference to the entry's value.
    ///
    /// # Returns
    ///
    /// A mutable reference to `Some(V)` if the entry has a value, or `None` if the entry is vacant.
    pub fn get_mut(&mut self) -> &mut Option<V> {
        // SAFETY: The entry holds the lock on the `State`, so it is safe to access the value.
        unsafe { (*self.state).value_mut() }
    }

    /// Sets the value of the entry, returning the old value if it existed.
    ///
    /// # Arguments
    ///
    /// * `value` - The new value to insert
    ///
    /// # Returns
    ///
    /// The previous value if the entry was occupied, or `None` if it was vacant.
    pub fn insert(&mut self, value: V) -> Option<V> {
        self.get_mut().replace(value)
    }

    /// Swaps the value of the entry with the provided value.
    ///
    /// # Arguments
    ///
    /// * `value` - The new value to swap in (wrapped in `Option`)
    ///
    /// # Returns
    ///
    /// The previous value of the entry.
    pub fn swap(&mut self, mut value: Option<V>) -> Option<V> {
        std::mem::swap(self.get_mut(), &mut value);
        value
    }

    /// Removes the value from the entry, returning it if it existed.
    ///
    /// # Returns
    ///
    /// The value that was stored in the entry, or `None` if the entry was vacant.
    pub fn remove(&mut self) -> Option<V> {
        // SAFETY: The entry holds the lock on the `State`, so it is safe to access the value.
        self.get_mut().take()
    }
}

impl<K, Q, V> std::fmt::Debug for EntryByRef<'_, '_, K, Q, V>
where
    K: Eq + Hash + Borrow<Q> + std::fmt::Debug,
    Q: Eq + Hash + ?Sized + std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EntryByRef")
            .field("key", &self.key)
            .field("value", self.get())
            .finish()
    }
}

impl<K: Eq + Hash + Borrow<Q>, Q: Eq + Hash + ?Sized, V> Drop for EntryByRef<'_, '_, K, Q, V> {
    fn drop(&mut self) {
        // SAFETY: The entry holds the lock on the `State`, so it is safe to unlock it.
        unsafe { (*self.state).mutex.unlock() };

        // SAFETY: The pointer `self.state` is valid because it was obtained from the map and its
        // reference count was incremented, ensuring the `State` won't be dropped while we hold it
        let prev = (unsafe { &*self.state })
            .refcnt
            .fetch_sub(1, Ordering::AcqRel);
        if prev == 1 {
            self.map.try_remove_entry(self.key);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        collections::HashMap,
        sync::{
            atomic::{AtomicU32, Ordering},
            Arc,
        },
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
                        let mut entries: HashMap<_, _> = lock_map.batch_lock(keys);
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
}
