use crate::{ShardsMap, SimpleAction, UpdateAction, WaiterPtr};
use std::borrow::Borrow;
use std::collections::LinkedList;
use std::hash::Hash;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::OnceLock;

/// Internal state for a key-value pair in the `LockMap`.
///
/// This type manages both the stored value and the queue of waiting threads
/// for per-key synchronization.
struct State<V> {
    /// The stored value, wrapped in a Box to ensure stable memory location
    value: Box<Option<V>>,
    /// Queue of threads waiting for access to this key
    queue: LinkedList<WaiterPtr>,
}

impl<V> Default for State<V> {
    fn default() -> Self {
        Self {
            value: Default::default(),
            queue: Default::default(),
        }
    }
}

/// A thread-safe hashmap that supports locking entries at the key level.
pub struct LockMap<K, V> {
    map: ShardsMap<K, State<V>>,
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

    /// Gets exclusive access to an entry in the map.
    ///
    /// The returned `Entry` provides exclusive access to the key and its associated value
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
    ///     entry.value.replace(42);
    ///     // let _ = map.get("key".to_string()); // DEADLOCK!
    ///     // map.set("key".to_string(), 21); // DEADLOCK!
    ///     // map.remove("key".to_string()); // DEADLOCK!
    ///     // let mut entry2 = map.entry("key".to_string()); // DEADLOCK!
    /// }
    /// ```
    pub fn entry(&self, key: K) -> Entry<'_, K, V>
    where
        K: Clone,
    {
        let waiter = AtomicU32::new(0);
        let ptr = self.map.update(key.clone(), |value| match value {
            Some(state) => {
                if state.queue.is_empty() {
                    // no need to wait.
                    waiter.store(1, Ordering::Release);
                }
                state.queue.push_back(WaiterPtr::new(&waiter));
                (UpdateAction::Keep, state.value.as_mut() as *mut _)
            }
            None => {
                let mut state = State::default();
                // no need to wait.
                state.queue.push_back(WaiterPtr::new(&waiter));
                let ptr = state.value.as_mut() as *mut _;
                waiter.store(1, Ordering::Release);
                (UpdateAction::Update(state), ptr)
            }
        });

        WaiterPtr::wait(&waiter);

        Entry {
            map: self,
            key,
            value: Self::value_ptr_to_ref(ptr),
        }
    }

    /// Gets exclusive access to an entry in the map.
    ///
    /// The returned `Entry` provides exclusive access to the key and its associated value
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
    ///     entry.value.replace(42);
    ///     // let _ = map.get("key"); // DEADLOCK!
    ///     // map.set_by_ref("key", 21); // DEADLOCK!
    ///     // map.remove("key"); // DEADLOCK!
    ///     // let mut entry2 = map.entry_by_ref("key"); // DEADLOCK!
    /// }
    /// ```
    pub fn entry_by_ref<'a, 'b, Q>(&'a self, key: &'b Q) -> EntryByRef<'a, 'b, K, Q, V>
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let waiter = AtomicU32::new(0);
        let ptr = self.map.update_by_ref(key, |value| match value {
            Some(state) => {
                if state.queue.is_empty() {
                    // no need to wait.
                    waiter.store(1, Ordering::Release);
                }
                state.queue.push_back(WaiterPtr::new(&waiter));
                (UpdateAction::Keep, state.value.as_mut() as *mut _)
            }
            None => {
                let mut state = State::default();
                // no need to wait.
                state.queue.push_back(WaiterPtr::new(&waiter));
                let ptr = state.value.as_mut() as *mut _;
                waiter.store(1, Ordering::Release);
                (UpdateAction::Update(state), ptr)
            }
        });

        WaiterPtr::wait(&waiter);

        EntryByRef {
            map: self,
            key,
            value: Self::value_ptr_to_ref(ptr),
        }
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
    /// map.set_by_ref("key", 42);
    /// assert_eq!(map.get("key"), Some(42));
    /// assert_eq!(map.get("missing"), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
        Q: Eq + Hash + ?Sized,
    {
        let waiter = AtomicU32::new(0);
        let mut ptr: *mut Option<V> = std::ptr::null_mut();
        let value = self.map.simple_update(key, |value| match value {
            Some(state) => {
                if state.queue.is_empty() {
                    // no need to wait.
                    (SimpleAction::Keep, state.value.as_mut().clone())
                } else {
                    // need to wait.
                    state.queue.push_back(WaiterPtr::new(&waiter));
                    ptr = state.value.as_mut() as *mut _;
                    (SimpleAction::Keep, None)
                }
            }
            None => (SimpleAction::Keep, None),
        });

        if ptr.is_null() {
            return value;
        }

        WaiterPtr::wait(&waiter);

        let value = Self::value_ptr_to_ref(ptr).clone();
        self.unlock(key);
        value
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
    /// map.set("key".to_string(), 42);
    ///
    /// // Update existing value
    /// map.set("key".to_string(), 123);
    /// ```
    pub fn set(&self, key: K, value: V)
    where
        K: Clone,
    {
        let waiter = AtomicU32::new(0);
        let mut ptr: *mut Option<V> = std::ptr::null_mut();
        let value = self.map.update(key.clone(), |v| match v {
            Some(state) => {
                if state.queue.is_empty() {
                    // no need to wait.
                    state.value.replace(value);
                    (UpdateAction::Keep, None)
                } else {
                    // need to wait.
                    state.queue.push_back(WaiterPtr::new(&waiter));
                    ptr = state.value.as_mut() as *mut _;
                    (UpdateAction::Keep, Some(value))
                }
            }
            None => {
                // no need to wait.
                let state = State {
                    value: Box::new(Some(value)),
                    queue: Default::default(),
                };
                (UpdateAction::Update(state), None)
            }
        });

        if ptr.is_null() {
            return;
        }

        WaiterPtr::wait(&waiter);

        *Self::value_ptr_to_ref(ptr) = value;
        self.unlock(&key);
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
    /// map.set_by_ref("key", 42);
    ///
    /// // Update existing value
    /// map.set_by_ref("key", 123);
    /// ```
    pub fn set_by_ref<Q>(&self, key: &Q, value: V)
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
    {
        let waiter = AtomicU32::new(0);
        let mut ptr: *mut Option<V> = std::ptr::null_mut();
        let value = self.map.update_by_ref(key, |v| match v {
            Some(state) => {
                if state.queue.is_empty() {
                    // no need to wait.
                    state.value.replace(value);
                    (UpdateAction::Keep, None)
                } else {
                    // need to wait.
                    state.queue.push_back(WaiterPtr::new(&waiter));
                    ptr = state.value.as_mut() as *mut _;
                    (UpdateAction::Keep, Some(value))
                }
            }
            None => {
                // no need to wait.
                let state = State {
                    value: Box::new(Some(value)),
                    queue: Default::default(),
                };
                (UpdateAction::Update(state), None)
            }
        });

        if ptr.is_null() {
            return;
        }

        WaiterPtr::wait(&waiter);

        *Self::value_ptr_to_ref(ptr) = value;
        self.unlock(key);
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
    /// map.set_by_ref("key", 42);
    /// assert_eq!(map.remove("key"), Some(42));
    /// assert_eq!(map.get("key"), None);
    /// ```
    pub fn remove<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let waiter = AtomicU32::new(0);
        let mut ptr: *mut Option<V> = std::ptr::null_mut();
        let value = self.map.simple_update(key, |v| match v {
            Some(state) => {
                if state.queue.is_empty() {
                    // no need to wait.
                    (SimpleAction::Remove, state.value.take())
                } else {
                    // need to wait.
                    state.queue.push_back(WaiterPtr::new(&waiter));
                    ptr = state.value.as_mut() as _;
                    (SimpleAction::Keep, None)
                }
            }
            None => (SimpleAction::Keep, None), // no need to wait.
        });

        if ptr.is_null() {
            return value;
        }

        WaiterPtr::wait(&waiter);

        let value = Self::value_ptr_to_ref(ptr).take();
        self.unlock(key);
        value
    }

    fn unlock<Q>(&self, key: &Q)
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.simple_update(key, |value| match value {
            Some(state) => (Self::wake_up_next_one(state), ()),
            None => panic!("impossible: unlock a non-existent key!"),
        });
    }

    fn wake_up_next_one(state: &mut State<V>) -> SimpleAction {
        state.queue.pop_front();
        match state.queue.front() {
            Some(waiter) => {
                waiter.wake_up();
                SimpleAction::Keep
            }
            None if state.value.is_none() => SimpleAction::Remove,
            None => SimpleAction::Keep,
        }
    }

    fn value_ptr_to_ref<'env>(ptr: *mut Option<V>) -> &'env mut Option<V> {
        unsafe { &mut *ptr }
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
///     entry.value.replace(42);
///
///     // Entry is automatically unlocked when dropped
/// }
/// ```
pub struct Entry<'a, K: Eq + Hash, V> {
    map: &'a LockMap<K, V>,
    pub key: K,
    pub value: &'a mut Option<V>,
}

impl<K: Eq + Hash, V> Drop for Entry<'_, K, V> {
    fn drop(&mut self) {
        self.map.unlock(&self.key);
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
/// let map = LockMap::new();
/// {
///     // Get exclusive access to an entry
///     let mut entry = map.entry("key");
///
///     // Modify the value
///     entry.value.replace(42);
///
///     // Entry is automatically unlocked when dropped
/// }
/// ```
pub struct EntryByRef<'a, 'b, K: Eq + Hash, Q, V>
where
    K: Borrow<Q>,
    Q: Eq + Hash + ?Sized,
{
    map: &'a LockMap<K, V>,
    pub key: &'b Q,
    pub value: &'a mut Option<V>,
}

impl<K: Eq + Hash, Q, V> Drop for EntryByRef<'_, '_, K, Q, V>
where
    K: Borrow<Q>,
    Q: Eq + Hash + ?Sized,
{
    fn drop(&mut self) {
        self.map.unlock(self.key);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{atomic::AtomicUsize, Arc};

    #[test]
    fn test_lockmap_lock() {
        let map = LockMap::<u32, u32>::new();
        {
            let entry = map.entry(1);
            entry.value.replace(2);
        }
        {
            let entry = map.entry(1);
            assert_eq!(entry.value.unwrap(), 2);
            entry.value.take();
        }
        {
            let entry = map.entry(1);
            assert!(entry.value.is_none());
        }
        let map = LockMap::<u32, u32>::default();
        {
            let entry = map.entry(1);
            entry.value.replace(2);
        }
        assert_eq!(map.remove(&1), Some(2));
        assert_eq!(map.remove(&1), None);
    }

    #[test]
    #[should_panic(expected = "impossible: unlock a non-existent key!")]
    fn test_lockmap_invalid_unlock() {
        let map = LockMap::<u32, u32>::new();
        let key = 0xB1;
        let mut dummy = Some(7268);
        let _ = Entry {
            map: &map,
            key,
            value: &mut dummy,
        };
    }

    #[test]
    #[should_panic(expected = "impossible: unlock a non-existent key!")]
    fn test_lockmap_invalid_unlock_by_ref() {
        let map = LockMap::<String, u32>::new();
        let key = "hello";
        let mut dummy = Some(7268);
        let _ = EntryByRef {
            map: &map,
            key,
            value: &mut dummy,
        };
    }

    #[test]
    fn test_lockmap_same_key() {
        let lock_map = Arc::new(LockMap::<String, usize>::with_capacity(256));
        let current = Arc::new(AtomicU32::default());
        const N: usize = 1 << 12;
        const M: usize = 16;

        const S: &str = "hello";
        lock_map.set_by_ref(S, 0);

        let threads = (0..M)
            .map(|_| {
                let lock_map = lock_map.clone();
                let current = current.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let entry = lock_map.entry_by_ref(S);
                        let now = current.fetch_add(1, Ordering::AcqRel);
                        assert_eq!(now, 0);
                        let v = entry.value.as_mut().unwrap();
                        *v += 1;
                        let now = current.fetch_sub(1, Ordering::AcqRel);
                        assert_eq!(now, 1);
                    }
                })
            })
            .collect::<Vec<_>>();
        threads.into_iter().for_each(|t| t.join().unwrap());

        let entry = lock_map.entry_by_ref(S);
        assert_eq!(entry.value.unwrap(), N * M);
    }

    #[test]
    fn test_lockmap_random_key() {
        let lock_map = Arc::new(LockMap::<u32, u32>::with_capacity_and_shard_amount(256, 16));
        let total = Arc::new(AtomicUsize::default());
        const N: usize = 1 << 12;
        const M: usize = 8;

        let threads = (0..M)
            .map(|_| {
                let lock_map = lock_map.clone();
                let total = total.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        let key = rand::random::<u32>() % 32;
                        let entry = lock_map.entry(key);
                        assert!(entry.value.is_none());
                        entry.value.replace(1);
                        total.fetch_add(1, Ordering::AcqRel);
                        entry.value.take();
                    }
                })
            })
            .collect::<Vec<_>>();
        threads.into_iter().for_each(|t| t.join().unwrap());

        assert_eq!(total.load(Ordering::Acquire), N * M);
    }

    #[test]
    fn test_lockmap_get_set() {
        let lock_map = Arc::new(LockMap::<u32, u32>::with_capacity_and_shard_amount(256, 16));
        const N: usize = 1 << 20;

        let entry_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = rand::random::<u32>() % 32;
                    let value = rand::random::<u32>() % 32;
                    let entry = lock_map.entry(key);
                    if value < 16 {
                        entry.value.take();
                    } else {
                        entry.value.replace(value);
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
                        lock_map.set(key, value);
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
        const N: usize = 1 << 18;

        let entry_thread = {
            let lock_map = lock_map.clone();
            std::thread::spawn(move || {
                for _ in 0..N {
                    let key = (rand::random::<u32>() % 32).to_string();
                    let value = rand::random::<u32>() % 32;
                    let entry = lock_map.entry_by_ref(&key);
                    if value < 16 {
                        entry.value.take();
                    } else {
                        entry.value.replace(value);
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
                        lock_map.set_by_ref(&key, value);
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
}
