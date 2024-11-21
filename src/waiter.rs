use std::sync::atomic::{AtomicU32, Ordering};

/// A pointer type used for thread synchronization that provides waiting and waking capabilities.
///
/// This type is used internally by `LockMap` to implement per-key locking behavior. It wraps an
/// `AtomicU32` and provides safe access to waiting and waking operations.
///
/// # Safety
/// This type is both `Send` and `Sync` safe as it only provides controlled access to an atomic value.
pub struct WaiterPtr(*const AtomicU32);

impl WaiterPtr {
    /// Creates a new `WaiterPtr` from a reference to an `AtomicU32`.
    ///
    /// # Arguments
    /// * `w` - Reference to the `AtomicU32` to wrap
    ///
    /// # Safety
    /// The wrapped `AtomicU32` must outlive the `WaiterPtr`.
    pub fn new(w: &AtomicU32) -> Self {
        Self(w as *const _)
    }

    /// Wakes up a single thread waiting on this value.
    ///
    /// Sets the atomic value to 1 and wakes one waiting thread.
    pub fn wake_up(&self) {
        let waiter = unsafe { &*self.0 };
        waiter.store(1, Ordering::Release);
        atomic_wait::wake_one(self.0);
    }

    /// Waits until the atomic value becomes non-zero.
    ///
    /// This will block the current thread until another thread calls `wake_up()`.
    ///
    /// # Arguments
    /// * `w` - The `AtomicU32` to wait on
    pub fn wait(w: &AtomicU32) {
        while w.load(Ordering::Acquire) == 0 {
            atomic_wait::wait(w, 0);
        }
    }
}

// Safety: WaiterPtr can be safely shared between threads
unsafe impl Sync for WaiterPtr {}
unsafe impl Send for WaiterPtr {}
