use crate::{Mutex, ShardsMap, SimpleAction, UpdateAction};
use std::borrow::Borrow;
use std::hash::Hash;
use std::sync::OnceLock;

/// Internal state for a key-value pair in the `LockMap`.
///
/// This type manages both the stored value and the queue of waiting threads
/// for per-key synchronization.
struct State<V> {
    refcnt: u32,
    mutex: Mutex,
    value: Option<V>,
}

/// A thread-safe hashmap that supports locking entries at the key level.
pub struct LockMap<K, V> {
    map: ShardsMap<K, Box<State<V>>>,
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
                state.refcnt += 1;
                let ptr = state.as_mut() as _;
                (UpdateAction::Keep, ptr)
            }
            None => {
                let mut state: Box<_> = Box::new(State {
                    refcnt: 1,
                    mutex: Mutex::new(),
                    value: None,
                });
                let ptr = state.as_mut() as _;
                (UpdateAction::Replace(state), ptr)
            }
        });

        self.guard_by_val(ptr, key.clone())
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
                state.refcnt += 1;
                let ptr = state.as_mut() as _;
                (UpdateAction::Keep, ptr)
            }
            None => {
                let mut state: Box<_> = Box::new(State {
                    refcnt: 1,
                    mutex: Mutex::new(),
                    value: None,
                });
                let ptr = state.as_mut() as _;
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
                if state.refcnt == 0 {
                    let value = state.value.clone();
                    (SimpleAction::Keep, value)
                } else {
                    state.refcnt += 1;
                    ptr = state.as_mut();
                    (SimpleAction::Keep, None)
                }
            }
            None => (SimpleAction::Keep, None),
        });

        if ptr.is_null() {
            return value;
        }

        self.guard_by_ref(ptr, key).state.value.clone()
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
                if state.refcnt == 0 {
                    let value = state.value.replace(value);
                    (UpdateAction::Keep, (std::ptr::null_mut(), value))
                } else {
                    state.refcnt += 1;
                    let ptr: *mut State<V> = state.as_mut();
                    (UpdateAction::Keep, (ptr, Some(value)))
                }
            }
            None => {
                let state: Box<_> = Box::new(State {
                    refcnt: 0,
                    mutex: Mutex::new(),
                    value: Some(value),
                });
                (UpdateAction::Replace(state), (std::ptr::null_mut(), None))
            }
        });

        if ptr.is_null() {
            return value;
        }

        let mut entry = self.guard_by_val(ptr, key.clone());
        std::mem::replace(entry.get_mut(), value)
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
                if state.refcnt == 0 {
                    let value = state.value.replace(value);
                    (UpdateAction::Keep, (std::ptr::null_mut(), value))
                } else {
                    state.refcnt += 1;
                    let ptr: *mut State<V> = state.as_mut();
                    (UpdateAction::Keep, (ptr, Some(value)))
                }
            }
            None => {
                let state: Box<_> = Box::new(State {
                    refcnt: 0,
                    mutex: Mutex::new(),
                    value: Some(value),
                });
                (UpdateAction::Replace(state), (std::ptr::null_mut(), None))
            }
        });

        if ptr.is_null() {
            return value;
        }

        let mut entry = self.guard_by_ref(ptr, key);
        std::mem::replace(entry.get_mut(), value)
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
                if state.refcnt == 0 {
                    let value = state.value.take();
                    (SimpleAction::Remove, value)
                } else {
                    state.refcnt += 1;
                    ptr = state.as_mut();
                    (SimpleAction::Keep, None)
                }
            }
            None => (SimpleAction::Keep, None),
        });

        if ptr.is_null() {
            return value;
        }

        self.guard_by_ref(ptr, key).state.value.take()
    }

    fn unlock<Q>(&self, key: &Q)
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.simple_update(key, |value| match value {
            Some(state) => {
                state.refcnt -= 1;
                if state.value.is_none() && state.refcnt == 0 {
                    (SimpleAction::Remove, ())
                } else {
                    (SimpleAction::Keep, ())
                }
            }
            None => panic!("impossible: unlock a non-existent key!"),
        });
    }

    fn guard_by_val(&self, ptr: *mut State<V>, key: K) -> EntryByVal<K, V> {
        let state = unsafe { &mut *ptr };
        state.mutex.lock();
        EntryByVal {
            map: self,
            key,
            state,
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
        let state = unsafe { &mut *ptr };
        state.mutex.lock();
        EntryByRef {
            map: self,
            key,
            state,
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
    state: &'a mut State<V>,
}

impl<K: Eq + Hash, V> EntryByVal<'_, K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn get(&self) -> &Option<V> {
        &self.state.value
    }

    pub fn get_mut(&mut self) -> &mut Option<V> {
        &mut self.state.value
    }

    pub fn insert(&mut self, value: V) -> Option<V> {
        self.state.value.replace(value)
    }

    pub fn remove(&mut self) -> Option<V> {
        self.state.value.take()
    }
}

impl<K: Eq + Hash + std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug for EntryByVal<'_, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EntryByVal")
            .field("key", &self.key)
            .field("value", &self.state.value)
            .finish()
    }
}

impl<K: Eq + Hash, V> Drop for EntryByVal<'_, K, V> {
    fn drop(&mut self) {
        self.state.mutex.unlock();
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
    state: &'a mut State<V>,
}

impl<K: Eq + Hash + Borrow<Q>, Q: Eq + Hash + ?Sized, V> EntryByRef<'_, '_, K, Q, V> {
    pub fn key(&self) -> &Q {
        self.key
    }

    pub fn get(&self) -> &Option<V> {
        &self.state.value
    }

    pub fn get_mut(&mut self) -> &mut Option<V> {
        &mut self.state.value
    }

    pub fn insert(&mut self, value: V) -> Option<V> {
        self.state.value.replace(value)
    }

    pub fn remove(&mut self) -> Option<V> {
        self.state.value.take()
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
            .field("value", &self.state.value)
            .finish()
    }
}

impl<K: Eq + Hash + Borrow<Q>, Q: Eq + Hash + ?Sized, V> Drop for EntryByRef<'_, '_, K, Q, V> {
    fn drop(&mut self) {
        self.state.mutex.unlock();
        self.map.unlock(self.key);
    }
}

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
        assert_eq!(map.remove(&1), Some(2));
        assert!(map.is_empty());
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
    #[should_panic(expected = "impossible: unlock a non-existent key!")]
    fn test_lockmap_invalid_unlock() {
        let map = LockMap::<u32, u32>::new();
        let mut state = State {
            refcnt: 1,
            mutex: Mutex::new(),
            value: None,
        };
        let _ = EntryByVal {
            map: &map,
            key: 7268,
            state: &mut state,
        };
    }

    #[test]
    fn test_lockmap_same_key_by_value() {
        let lock_map = Arc::new(LockMap::<usize, usize>::with_capacity(256));
        let current = Arc::new(AtomicU32::default());
        const N: usize = 1 << 20;
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
        const N: usize = 1 << 20;
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
        const N: usize = 1 << 12;
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
    fn test_lockmap_get_set() {
        let lock_map = Arc::new(LockMap::<u32, u32>::with_capacity_and_shard_amount(256, 16));
        const N: usize = 1 << 20;

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
        const N: usize = 1 << 18;

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
}
