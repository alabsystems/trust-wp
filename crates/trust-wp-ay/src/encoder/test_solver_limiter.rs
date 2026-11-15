// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Process-local solver instance limiter for test builds.
//!
//! Encoder instances own substantial solver state. A counting semaphore bounds
//! live encoders within each test process, independently of test-thread count.
//! `TRUST_WP_MAX_TEST_SOLVERS` overrides the default permit limit.
//!
//! Each process owns its synchronization and diagnostics. A forked verifier
//! child must not wait on permits owned by parent threads, or touch a mutex
//! copied while those threads held it. Published states are identified by PID;
//! the child's first use installs fresh state before taking any lock. Permits
//! copied from a parent do not release the child's permits when dropped.
//!
//! This module is excluded from production builds.

use std::sync::{
    atomic::{AtomicPtr, AtomicUsize, Ordering},
    Condvar, Mutex,
};

/// Default maximum concurrent solver instances in test builds.
///
/// Leave room for tests that temporarily hold more than one encoder while
/// still bounding the solver memory used by parallel test threads.
const DEFAULT_MAX_CONCURRENT_SOLVERS: usize = 8;

/// Global state for the solver instance limiter.
struct SolverLimiter {
    /// Forked children cannot wait on a parent thread's copied mutex or count.
    owner_pid: u32,
    /// Maximum concurrent solvers allowed.
    max: usize,
    /// Current number of live solver instances.
    count: Mutex<usize>,
    /// Notified when a solver is dropped (permit released).
    released: Condvar,
    live: AtomicUsize,
    peak: AtomicUsize,
    acquired: AtomicUsize,
}

// Published states live until process exit: a permit may still refer to an old
// state's address after fork. Avoid OnceLock here, because fork may copy it
// while another parent thread is initializing it, just as it may copy a held
// limiter mutex. Only the atomic pointer and immutable PID are read before a
// child replaces inherited state.
static LIMITER: AtomicPtr<SolverLimiter> = AtomicPtr::new(std::ptr::null_mut());

fn get_limiter() -> &'static SolverLimiter {
    let owner_pid = std::process::id();
    loop {
        let current = LIMITER.load(Ordering::Acquire);
        let previous = if current.is_null() {
            None
        } else {
            // SAFETY: every published state is fully initialized before the
            // release store and is never freed; only immutable fields are read.
            Some(unsafe { &*current })
        };
        if let Some(limiter) = previous {
            if limiter.owner_pid == owner_pid {
                return limiter;
            }
        }
        // Preserve the parent's configured limit without consulting copied
        // environment locks in the child. Its live permits belong to parent
        // threads, so the child starts with fresh counters and synchronization.
        let max = previous.map_or_else(
            || {
                std::env::var("TRUST_WP_MAX_TEST_SOLVERS")
                    .ok()
                    .and_then(|v| v.parse::<usize>().ok())
                    .unwrap_or(DEFAULT_MAX_CONCURRENT_SOLVERS)
            },
            |limiter| limiter.max,
        );
        let replacement = Box::into_raw(Box::new(SolverLimiter {
            owner_pid,
            max,
            count: Mutex::new(0),
            released: Condvar::new(),
            live: AtomicUsize::new(0),
            peak: AtomicUsize::new(0),
            acquired: AtomicUsize::new(0),
        }));
        if LIMITER
            .compare_exchange(current, replacement, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            // SAFETY: this state was just published and will never be freed.
            return unsafe { &*replacement };
        }
        // SAFETY: the failed CAS never published replacement, so this thread
        // still exclusively owns it and no permit can refer to it.
        unsafe { drop(Box::from_raw(replacement)) };
    }
}

/// RAII permit for a solver instance. Releases the permit on drop.
///
/// This is stored as a field in `AYEncoder` (test builds only).
/// A permit retains the state it charged. A copied parent permit must never
/// decrement the fresh child count, or lock the inherited parent state.
pub(crate) struct SolverPermit {
    limiter: &'static SolverLimiter,
}

impl Drop for SolverPermit {
    fn drop(&mut self) {
        let limiter = self.limiter;
        if limiter.owner_pid != std::process::id()
            || !std::ptr::eq(limiter, LIMITER.load(Ordering::Acquire))
        {
            return;
        }
        {
            let mut count = limiter.count.lock().expect("solver limiter mutex poisoned");
            *count = count.saturating_sub(1);
            // Keep diagnostics in the same critical section as the permit
            // count. Otherwise an acquire can overtake this decrement and
            // record a peak larger than the actual semaphore limit.
            limiter.live.fetch_sub(1, Ordering::Relaxed);
        }
        limiter.released.notify_one();
    }
}

/// Acquire a solver permit, blocking if the concurrent limit is reached.
///
/// Called from `AYEncoder::from_solver_and_mem_state()` before creating
/// the encoder. The returned `SolverPermit` must be stored in the encoder
/// and will release the permit when the encoder is dropped.
pub(crate) fn acquire_solver_permit() -> SolverPermit {
    let limiter = get_limiter();
    let mut count = limiter.count.lock().expect("solver limiter mutex poisoned");
    while *count >= limiter.max {
        count = limiter
            .released
            .wait(count)
            .expect("solver limiter mutex poisoned during wait");
    }
    *count += 1;
    let new_live = limiter.live.fetch_add(1, Ordering::Relaxed) + 1;
    // Update peak high-water mark (lock-free CAS loop).
    let mut peak = limiter.peak.load(Ordering::Relaxed);
    while new_live > peak {
        match limiter.peak.compare_exchange_weak(
            peak,
            new_live,
            Ordering::Relaxed,
            Ordering::Relaxed,
        ) {
            Ok(_) => break,
            Err(current) => peak = current,
        }
    }
    limiter.acquired.fetch_add(1, Ordering::Relaxed);
    SolverPermit { limiter }
}

/// Returns the current number of live solver permits (for diagnostics).
#[cfg(test)]
pub(crate) fn live_solver_count() -> usize {
    get_limiter().live.load(Ordering::Relaxed)
}

/// Returns the configured maximum concurrent solvers (for diagnostics).
#[cfg(test)]
pub(crate) fn max_concurrent_solvers() -> usize {
    get_limiter().max
}

/// Returns the peak number of concurrent solver permits observed since
/// process start (for diagnostics).
///
/// This high-water mark verifies the limiter is working: after a full
/// test run, `peak_solver_count()` should be `<= max_concurrent_solvers()`.
#[cfg(test)]
pub(crate) fn peak_solver_count() -> usize {
    get_limiter().peak.load(Ordering::Relaxed)
}

/// Returns the total number of solver permits acquired since process start.
///
/// Useful for confirming tests are actually going through the limiter.
/// After a full trust-wp-ay test run, this should be in the thousands.
#[cfg(test)]
pub(crate) fn total_permits_acquired() -> usize {
    get_limiter().acquired.load(Ordering::Relaxed)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: these tests use `>=` / range checks rather than exact equality
    // because other test threads may concurrently acquire/release permits
    // (every AYEncoder::new() in the test suite acquires a permit). The
    // process-local live count is shared across all threads.

    #[cfg(unix)]
    #[test]
    fn forked_child_replaces_locked_parent_limiter_and_ignores_parent_permits() {
        let parent_permit = acquire_solver_permit();
        let parent_limiter = get_limiter();
        // Keep the copied mutex locked until the child finishes. Reusing or
        // resetting it in the child would deadlock even if its count were zero.
        let held = parent_limiter.count.lock().expect("parent limiter lock");
        // SAFETY: the child only exercises the limiter and exits with _exit;
        // the parent reaps exactly this PID and retains all its own state.
        let child = unsafe { libc::fork() };
        assert!(child >= 0, "fork failed");
        if child == 0 {
            let permit = acquire_solver_permit();
            let fresh = get_limiter();
            let independent = !std::ptr::eq(fresh, parent_limiter)
                && fresh.max == parent_limiter.max
                && live_solver_count() == 1
                && total_permits_acquired() == 1;
            drop(parent_permit);
            let inherited_drop_ignored = live_solver_count() == 1;
            drop(permit);
            let released = live_solver_count() == 0;
            // SAFETY: skip destructors for the copied, locked parent state.
            unsafe {
                libc::_exit(i32::from(
                    !(independent && inherited_drop_ignored && released),
                ))
            };
        }
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        let mut status = 0;
        let completed = loop {
            // SAFETY: status is writable and child is the PID from our fork.
            let observed = unsafe { libc::waitpid(child, &raw mut status, libc::WNOHANG) };
            if observed == child {
                break true;
            }
            if observed < 0 || std::time::Instant::now() >= deadline {
                // SAFETY: kill and reap only this test's child on a failure.
                unsafe {
                    libc::kill(child, libc::SIGKILL);
                    libc::waitpid(child, &raw mut status, 0);
                }
                break false;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        };
        drop(held);
        drop(parent_permit);
        assert!(completed, "child blocked on the inherited limiter");
        assert!(
            libc::WIFEXITED(status),
            "child did not exit normally: {status}"
        );
        assert_eq!(
            libc::WEXITSTATUS(status),
            0,
            "child limiter state was not independent"
        );
    }

    #[test]
    fn test_acquire_and_release_permit() {
        let before = total_permits_acquired();
        let permit = acquire_solver_permit();
        // Other threads may release their permits while we acquire ours.
        // The cumulative counter is monotone; a held permit guarantees only
        // that the current live count is positive, not a net increase.
        assert!(total_permits_acquired() > before);
        assert!(live_solver_count() >= 1);
        drop(permit);
    }

    #[test]
    fn test_max_concurrent_solvers_default_or_env() {
        let max = max_concurrent_solvers();
        // Either the default or whatever TRUST_WP_MAX_TEST_SOLVERS is set to.
        assert!(max > 0, "max concurrent solvers must be positive");
    }

    #[test]
    fn test_multiple_permits_increments() {
        if max_concurrent_solvers() < 2 {
            return;
        }

        let p1 = acquire_solver_permit();
        let after_p1 = live_solver_count();
        let p2 = acquire_solver_permit();
        let after_p2 = live_solver_count();
        // p2 should push the count higher than p1 alone (barring exact
        // concurrent drops from other threads, but the count should be >= 2).
        assert!(
            after_p2 >= 2,
            "two permits should result in at least 2 live solvers, got {after_p2}"
        );
        assert!(
            after_p2 > after_p1 || after_p2 >= 2,
            "acquiring a second permit should increase count or maintain >= 2"
        );
        drop(p1);
        drop(p2);
    }

    #[test]
    fn test_peak_count_is_tracked() {
        if max_concurrent_solvers() < 2 {
            return;
        }

        // After acquiring permits, the peak count should be at least as high
        // as the number of permits we held simultaneously.
        let p1 = acquire_solver_permit();
        let p2 = acquire_solver_permit();
        let peak = peak_solver_count();
        // We held 2 simultaneously; the peak must be >= 2 (other tests may
        // have pushed it higher).
        assert!(
            peak >= 2,
            "peak solver count should be >= 2 after holding 2 permits, got {peak}"
        );
        drop(p1);
        drop(p2);
        // Peak should NOT decrease after releasing permits — it is a high-water mark.
        let peak_after = peak_solver_count();
        assert!(
            peak_after >= peak,
            "peak solver count should never decrease: was {peak}, now {peak_after}"
        );
    }

    #[test]
    fn test_total_acquired_increments() {
        let before = total_permits_acquired();
        let _p = acquire_solver_permit();
        let after = total_permits_acquired();
        assert!(
            after > before,
            "total_permits_acquired should increment on acquire: before={before}, after={after}"
        );
    }

    #[test]
    fn test_peak_never_exceeds_max() {
        // This is the core invariant: peak concurrent solvers should never
        // exceed the configured maximum. Because this test runs alongside
        // ~6700 other tests that all acquire permits, the peak count is the
        // true observed maximum across the entire test run.
        let peak = peak_solver_count();
        let max = max_concurrent_solvers();
        assert!(
            peak <= max,
            "peak solver count ({peak}) should never exceed max ({max}) — \
             the limiter is not working correctly"
        );
    }

    #[test]
    fn test_limiter_works_with_real_encoder() {
        // A real encoder must acquire a permit even when other tests release
        // their own encoders concurrently.
        let before = total_permits_acquired();
        let encoder = crate::AYEncoder::new();
        assert!(total_permits_acquired() > before);
        assert!(live_solver_count() >= 1);
        drop(encoder);
    }
}
