// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Global solver instance limiter for test builds.
//!
//! # Problem
//!
//! The trust-wp-ay test suite has ~6700 tests, most of which create at least one
//! `AYEncoder` (and thus a ay-dpll `Solver` instance). Each solver allocates
//! significant memory for its internal clause database, theory solvers, and
//! proof-production state. With Rust's default test parallelism (= CPU count,
//! e.g. 12 on an M2 Max), peak resident memory can hit 26GB, which has caused
//! macOS kernel panics (OOM kills). (#2710)
//!
//! The `.cargo/config.toml` setting `RUST_TEST_THREADS=4` caps test threads,
//! but tests within each thread cycle through many encoders, and some tests
//! create multiple encoders. The thread cap alone does not bound peak solver
//! instance count.
//!
//! # Solution
//!
//! A global counting semaphore limits the number of **live** `AYEncoder`
//! instances across all test threads. When the limit is reached, new
//! `AYEncoder` constructors block until an existing encoder is dropped.
//!
//! The permit is acquired in `AYEncoder::from_solver_and_mem_state()` (the
//! single internal constructor all public constructors funnel through) and
//! released automatically via `Drop for AYEncoder`. This makes the limiter
//! completely transparent to all ~2200 call sites.
//!
//! # Configuration
//!
//! - Default limit: [`DEFAULT_MAX_CONCURRENT_SOLVERS`] (8)
//! - Override via env var: `TRUST_WP_MAX_TEST_SOLVERS=N`
//!
//! The default of 8 is chosen to allow moderate parallelism (tests that create
//! a solver, do a quick check, and drop it benefit from >4 permits even with
//! 4 test threads) while keeping peak RSS well under 16GB.
//!
//! # Production builds
//!
//! This module is `#[cfg(test)]` only. Production solver instances are not
//! throttled — the production pipeline creates at most one solver per
//! verification function, with natural serialization from the driver.

use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Condvar, Mutex, OnceLock,
};

/// Default maximum concurrent solver instances in test builds.
///
/// 8 permits with 4 test threads allows 2 encoders per thread on average,
/// covering tests that create multiple encoders without excessive memory.
/// Peak RSS at 8 concurrent solvers is approximately 8-12GB depending on
/// logic complexity (QF_LIA < QF_AUFLIA < ALL).
const DEFAULT_MAX_CONCURRENT_SOLVERS: usize = 8;

/// Global state for the solver instance limiter.
struct SolverLimiter {
    /// Maximum concurrent solvers allowed.
    max: usize,
    /// Current number of live solver instances.
    count: Mutex<usize>,
    /// Notified when a solver is dropped (permit released).
    released: Condvar,
}

/// Global solver limiter singleton, initialized on first use.
static LIMITER: OnceLock<SolverLimiter> = OnceLock::new();

/// Number of currently live solver permits (for diagnostics/testing).
static LIVE_COUNT: AtomicUsize = AtomicUsize::new(0);

/// High-water mark: peak number of concurrent solver permits observed.
/// Updated on each acquire. Useful for verifying the limiter is actually
/// capping concurrent instances during test runs.
static PEAK_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Total number of solver permits acquired since process start.
/// Useful for verifying that tests are actually going through the limiter.
static TOTAL_ACQUIRED: AtomicUsize = AtomicUsize::new(0);

fn get_limiter() -> &'static SolverLimiter {
    LIMITER.get_or_init(|| {
        let max = std::env::var("TRUST_WP_MAX_TEST_SOLVERS")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(DEFAULT_MAX_CONCURRENT_SOLVERS);

        SolverLimiter {
            max,
            count: Mutex::new(0),
            released: Condvar::new(),
        }
    })
}

/// RAII permit for a solver instance. Releases the permit on drop.
///
/// This is stored as a field in `AYEncoder` (test builds only).
/// The permit is zero-sized in terms of data — it's just a marker that
/// the semaphore count has been incremented. The actual counting is
/// managed by the global `SolverLimiter`.
pub(crate) struct SolverPermit {
    /// Prevent construction outside this module.
    _private: (),
}

impl Drop for SolverPermit {
    fn drop(&mut self) {
        let limiter = get_limiter();
        {
            let mut count = limiter.count.lock().expect("solver limiter mutex poisoned");
            *count = count.saturating_sub(1);
        }
        LIVE_COUNT.fetch_sub(1, Ordering::Relaxed);
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
    let new_live = LIVE_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
    // Update peak high-water mark (lock-free CAS loop).
    let mut peak = PEAK_COUNT.load(Ordering::Relaxed);
    while new_live > peak {
        match PEAK_COUNT.compare_exchange_weak(peak, new_live, Ordering::Relaxed, Ordering::Relaxed)
        {
            Ok(_) => break,
            Err(current) => peak = current,
        }
    }
    TOTAL_ACQUIRED.fetch_add(1, Ordering::Relaxed);
    SolverPermit { _private: () }
}

/// Returns the current number of live solver permits (for diagnostics).
#[cfg(test)]
pub(crate) fn live_solver_count() -> usize {
    LIVE_COUNT.load(Ordering::Relaxed)
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
    PEAK_COUNT.load(Ordering::Relaxed)
}

/// Returns the total number of solver permits acquired since process start.
///
/// Useful for confirming tests are actually going through the limiter.
/// After a full trust-wp-ay test run, this should be in the thousands.
#[cfg(test)]
pub(crate) fn total_permits_acquired() -> usize {
    TOTAL_ACQUIRED.load(Ordering::Relaxed)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: these tests use `>=` / range checks rather than exact equality
    // because other test threads may concurrently acquire/release permits
    // (every AYEncoder::new() in the test suite acquires a permit). The
    // global LIVE_COUNT is shared across all threads.

    #[test]
    fn test_acquire_and_release_permit() {
        let before = live_solver_count();
        let permit = acquire_solver_permit();
        // Count must have increased (at least by 1, possibly more from
        // other threads).
        assert!(
            live_solver_count() > before,
            "acquiring a permit should increase the live count"
        );
        drop(permit);
        // After dropping our permit, the count should be <= what it was
        // right after we acquired (could be less if other threads also dropped).
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
        // Verify that AYEncoder instances actually go through the limiter.
        // Creating a AYEncoder should increase the live count.
        let before = live_solver_count();
        let encoder = crate::AYEncoder::new();
        let during = live_solver_count();
        assert!(
            during > before,
            "creating a AYEncoder should acquire a solver permit: \
             before={before}, during={during}"
        );
        drop(encoder);
        // After dropping, count should decrease (barring exact-concurrent
        // activity from other test threads).
    }
}
