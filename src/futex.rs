// Modified from https://github.com/rust-lang/rust/blob/master/library/std/src/sys/sync/mutex/futex.rs
use std::sync::atomic::{
    AtomicU32,
    Ordering::{Acquire, Relaxed, Release},
};

pub struct Mutex {
    futex: AtomicU32,
}

const UNLOCKED: u32 = 0;
const LOCKED: u32 = 1; // locked, no other threads waiting
const CONTENDED: u32 = 2; // locked, and other threads waiting (contended)

impl Mutex {
    #[inline]
    pub const fn new() -> Self {
        Self {
            futex: AtomicU32::new(UNLOCKED),
        }
    }

    #[inline]
    pub fn try_lock(&self) -> bool {
        self.futex
            .compare_exchange(UNLOCKED, LOCKED, Acquire, Relaxed)
            .is_ok()
    }

    #[inline]
    pub fn lock(&self) {
        if !self.try_lock() {
            self.lock_contended();
        }
    }

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
