// Modified from https://github.com/rust-lang/rust/blob/master/library/std/src/sys/sync/mutex/futex.rs
// Copyright (c) The Rust Project Contributors

//! Fast user-space mutex implementation using futex operations.
//!
//! This module provides a lightweight mutex implementation that optimizes for
//! the common case of low contention while gracefully handling high contention
//! scenarios through futex-based blocking.
//!
//! The implementation uses a three-state atomic variable to track lock state:
//! - `UNLOCKED`: No thread holds the lock
//! - `LOCKED`: One thread holds the lock, no others waiting  
//! - `CONTENDED`: One thread holds the lock, others are waiting
//!
//! This design minimizes atomic operations in the fast path while ensuring
//! fair wakeup behavior when contention occurs.

use std::sync::atomic::{
    AtomicU32,
    Ordering::{Acquire, Relaxed, Release},
};

/// A fast user-space mutex implementation using futex operations.
///
/// This mutex is optimized for low contention scenarios by first attempting
/// to acquire the lock using atomic operations before falling back to
/// kernel-level futex operations when contention occurs.
///
/// # Performance Characteristics
/// - Very fast in uncontended cases (single atomic operation)
/// - Efficiently handles contended cases using futex syscalls
/// - Minimal memory overhead (single 32-bit atomic)
///
/// # Safety
/// This mutex does not provide poisoning support unlike `std::sync::Mutex`.
/// If a thread panics while holding the lock, the lock may remain in a locked
/// state permanently.
pub struct Mutex {
    futex: AtomicU32,
}

/// Represents an unlocked mutex state.
const UNLOCKED: u32 = 0;

/// Represents a locked mutex with no waiting threads.
const LOCKED: u32 = 1;

/// Represents a locked mutex with threads waiting for acquisition.
const CONTENDED: u32 = 2;

impl Mutex {
    /// Creates a new mutex in the unlocked state.
    ///
    /// # Returns
    ///
    /// A new `Mutex` instance ready for use.
    #[inline]
    pub const fn new() -> Self {
        Self {
            futex: AtomicU32::new(UNLOCKED),
        }
    }

    /// Attempts to acquire the lock without blocking.
    ///
    /// # Returns
    ///
    /// * `true` if the lock was successfully acquired
    /// * `false` if the lock is currently held by another thread
    #[inline]
    pub fn try_lock(&self) -> bool {
        self.futex
            .compare_exchange(UNLOCKED, LOCKED, Acquire, Relaxed)
            .is_ok()
    }

    /// Acquires the lock, blocking the current thread until it becomes available.
    ///
    /// This function will not return until the lock has been acquired.
    ///
    /// # Panics
    ///
    /// This function may panic if the current thread already holds the lock.
    /// However, this is not guaranteed and should not be relied upon for correctness.
    #[inline]
    pub fn lock(&self) {
        if !self.try_lock() {
            self.lock_contended();
        }
    }

    /// Handles lock acquisition when contention is detected.
    ///
    /// This is the slow path for lock acquisition, used when `try_lock` fails.
    /// It first spins briefly to see if the lock becomes available quickly,
    /// then falls back to using futex operations to block the thread.
    #[cold]
    fn lock_contended(&self) {
        // Spin first to speed things up if the lock is released quickly.
        let mut state = self.spin();

        // If it's unlocked now, attempt to take the lock
        // without marking it as contended.
        if state == UNLOCKED {
            match self
                .futex
                .compare_exchange(UNLOCKED, LOCKED, Acquire, Relaxed)
            {
                Ok(_) => return, // Locked!
                Err(s) => state = s,
            }
        }

        loop {
            // Put the lock in contended state.
            // We avoid an unnecessary write if it as already set to CONTENDED,
            // to be friendlier for the caches.
            if state != CONTENDED && self.futex.swap(CONTENDED, Acquire) == UNLOCKED {
                // We changed it from UNLOCKED to CONTENDED, so we just successfully locked it.
                return;
            }

            // Wait for the futex to change state, assuming it is still CONTENDED.
            atomic_wait::wait(&self.futex, CONTENDED);

            // Spin again after waking up.
            state = self.spin();
        }
    }

    /// Performs a brief spin loop waiting for the lock to become available.
    ///
    /// This reduces the overhead of immediately falling back to futex operations
    /// in cases where the lock is held only briefly.
    ///
    /// # Returns
    ///
    /// The current state of the futex after spinning.
    fn spin(&self) -> u32 {
        let mut spin = 100;
        loop {
            // We only use `load` (and not `swap` or `compare_exchange`)
            // while spinning, to be easier on the caches.
            let state = self.futex.load(Relaxed);

            // We stop spinning when the mutex is UNLOCKED,
            // but also when it's CONTENDED.
            if state != LOCKED || spin == 0 {
                return state;
            }

            std::hint::spin_loop();
            spin -= 1;
        }
    }

    /// Releases the lock.
    ///
    /// # Safety
    ///
    /// This function should only be called by the thread that currently holds the lock.
    /// Calling this function when the lock is not held or from a different thread
    /// may lead to undefined behavior.
    ///
    /// # Panics
    ///
    /// This function may panic if called when the lock is not held, but this
    /// is not guaranteed and should not be relied upon for correctness.
    #[inline]
    pub fn unlock(&self) {
        if self.futex.swap(UNLOCKED, Release) == CONTENDED {
            // We only wake up one thread. When that thread locks the mutex, it
            // will mark the mutex as CONTENDED (see lock_contended above),
            // which makes sure that any other waiting threads will also be
            // woken up eventually.
            self.wake();
        }
    }

    /// Wakes up one waiting thread.
    ///
    /// This is called when releasing a contended lock to notify waiting threads
    /// that the lock is now available.
    #[cold]
    fn wake(&self) {
        atomic_wait::wake_one(&self.futex);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn test_futex() {
        let lock = Arc::new(Mutex::new());
        let current = Arc::new(AtomicU32::new(0));
        const N: usize = 8;
        const M: usize = 1 << 20;

        let mut tasks = vec![];
        for _ in 0..N {
            let lock = lock.clone();
            let current = current.clone();
            tasks.push(std::thread::spawn(move || {
                for _ in 0..M {
                    lock.lock();
                    assert_eq!(current.fetch_add(1, Acquire), 0);
                    current.fetch_sub(1, Acquire);
                    lock.unlock();
                }
            }));
        }
        for task in tasks {
            task.join().unwrap();
        }
    }

    #[test]
    fn test_concurrent() {
        let lock = Arc::new(Mutex::new());
        let counter = Arc::new(AtomicU32::new(0));
        const THREAD_COUNT: usize = 4;
        const ITERATIONS: usize = 10000;

        let mut handles = vec![];

        // Spawn multiple threads that increment and decrement a shared counter
        for _ in 0..THREAD_COUNT {
            let lock = Arc::clone(&lock);
            let counter = Arc::clone(&counter);

            handles.push(std::thread::spawn(move || {
                for _ in 0..ITERATIONS {
                    // Lock and modify shared state
                    lock.lock();
                    let value = counter.load(Relaxed);
                    std::thread::yield_now(); // Force a context switch to increase contention
                    counter.store(value + 1, Relaxed);
                    lock.unlock();

                    // Do some work without the lock
                    std::thread::yield_now();

                    // Lock and modify shared state again
                    lock.lock();
                    let value = counter.load(Relaxed);
                    std::thread::yield_now(); // Force a context switch to increase contention
                    counter.store(value - 1, Relaxed);
                    lock.unlock();
                }
            }));
        }

        // Wait for all threads to complete
        for handle in handles {
            handle.join().unwrap();
        }

        // Verify the final counter value is 0
        assert_eq!(counter.load(Relaxed), 0);
    }
}
