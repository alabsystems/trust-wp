// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    ptr::NonNull,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};

use ntest::timeout;

use super::{ResolveContinuation, UnknownReason, VerificationResult};
use crate::encoder::AYEncoder;

fn resolve_verified(_: &mut AYEncoder) -> VerificationResult {
    VerificationResult::Verified(None)
}

struct DropTracker(Arc<AtomicBool>);

impl Drop for DropTracker {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

struct OwnedTestBox<T>(NonNull<T>);

impl<T> OwnedTestBox<T> {
    fn from_box(boxed: Box<T>) -> Self {
        Self(NonNull::from(Box::leak(boxed)))
    }
}

impl<T> Drop for OwnedTestBox<T> {
    fn drop(&mut self) {
        // SAFETY: `OwnedTestBox` owns this leaked allocation exclusively
        // for the duration of the test helper's lifetime.
        unsafe {
            drop(Box::from_raw(self.0.as_ptr()));
        }
    }
}

// SAFETY: the test helper moves exclusive ownership of `T` through a
// channel; the pointed-to allocation is not aliased.
unsafe impl<T: Send> Send for OwnedTestBox<T> {}

#[test]
#[timeout(30000)]
fn dropping_unread_channel_payload_reclaims_owned_box() {
    let dropped = Arc::new(AtomicBool::new(false));
    let payload = OwnedTestBox::from_box(Box::new(DropTracker(Arc::clone(&dropped))));
    let (send, recv) = std::sync::mpsc::channel();

    send.send(payload)
        .expect("payload send should succeed while receiver is alive");
    drop(recv);

    assert!(
        dropped.load(Ordering::SeqCst),
        "dropping an unread channel payload should drop the owned box instead of leaking it"
    );
}

#[test]
#[timeout(30000)]
fn spawn_boundary_wrapper_has_no_drop_but_channel_payload_does() {
    assert!(
        !std::mem::needs_drop::<super::SendEncoderPtr>(),
        "spawn-boundary wrapper must stay drop-free so spawn failure cannot reclaim the encoder before caller recovery"
    );
    assert!(
        std::mem::needs_drop::<super::OwnedEncoderPtr>(),
        "channel payload wrapper must keep ownership semantics so unread worker returns still reclaim the encoder"
    );
}

#[test]
#[timeout(30000)]
fn reserve_slot_increments_and_drop_decrements_live_worker_count() {
    let _serial = super::hard_timeout_test_serial_guard_for_test();
    let _isolated = super::isolated_hard_timeout_limiter_for_test();
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));

    let guard = super::reserve_hard_timeout_worker_slot(Duration::ZERO)
        .expect("slot reservation should succeed when slots are available");
    assert_eq!(
        super::live_hard_timeout_worker_count_for_test(),
        1,
        "reserving a hard-timeout worker slot should increment the live-worker count"
    );

    drop(guard);
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));
}

#[test]
#[timeout(30000)]
fn exhausted_wait_budget_returns_none_instead_of_oversubscribing() {
    let _serial = super::hard_timeout_test_serial_guard_for_test();
    let _isolated = super::isolated_hard_timeout_limiter_for_test();
    // ay v0.2.0 solver takes longer; parallel tests may hold slots.
    // Increased wait budget from 1s to 5s to avoid flaky failures.
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(5));

    let max_workers = super::max_hard_timeout_workers();
    let guards: Vec<_> = (0..max_workers)
        .map(|_| {
            super::reserve_hard_timeout_worker_slot(Duration::ZERO)
                .expect("slot reservation should succeed when filling limiter")
        })
        .collect();
    assert_eq!(
        super::live_hard_timeout_worker_count_for_test(),
        max_workers,
        "filling the worker limiter should track every reserved slot"
    );

    let refused = super::reserve_hard_timeout_worker_slot(Duration::ZERO);
    assert!(
        refused.is_none(),
        "exhausted wait budget should return None instead of oversubscribing"
    );
    assert_eq!(
        super::live_hard_timeout_worker_count_for_test(),
        max_workers,
        "refusing to oversubscribe should not change the live worker count"
    );

    drop(guards);
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(5));
}

// --- hard_timeout_for unit tests ---

#[test]
#[timeout(30000)]
fn hard_timeout_for_with_solver_timeout_returns_1_5x_plus_grace() {
    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(Duration::from_secs(20)));

    let result = super::hard_timeout_for(&encoder);
    // 1.5 * 20s + 100ms grace = 30.1s (#2674: reduced from 1.75x to 1.5x)
    let expected = Duration::from_secs(30) + super::HARD_TIMEOUT_GRACE;
    assert_eq!(
        result, expected,
        "hard_timeout_for should compute 1.5x solver timeout + grace period (#2674)"
    );
}

#[test]
#[timeout(30000)]
fn hard_timeout_for_without_solver_timeout_returns_default_plus_grace() {
    let encoder = AYEncoder::new();
    // No solver timeout set → uses DEFAULT_HARD_TIMEOUT + grace

    let result = super::hard_timeout_for(&encoder);
    let expected = super::DEFAULT_HARD_TIMEOUT + super::HARD_TIMEOUT_GRACE;
    assert_eq!(
        result, expected,
        "hard_timeout_for with no solver timeout should use default + grace"
    );
}

#[test]
#[timeout(30000)]
fn hard_timeout_for_with_very_small_timeout() {
    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(Duration::from_millis(1)));

    let result = super::hard_timeout_for(&encoder);
    // 1.5 * 1ms + 100ms grace = 1ms + 0.5ms + 100ms = 101.5ms
    // (#2674: reduced from 1.75x to 1.5x)
    let t = Duration::from_millis(1);
    let expected = t + t / 2 + super::HARD_TIMEOUT_GRACE;
    assert_eq!(
        result, expected,
        "hard_timeout_for should work with very small solver timeouts"
    );
}

#[test]
#[timeout(30000)]
fn hard_timeout_for_with_zero_timeout() {
    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(Duration::ZERO));

    let result = super::hard_timeout_for(&encoder);
    // 1.5 * 0 + 100ms = 100ms (#2674: unchanged, zero case)
    assert_eq!(
        result,
        super::HARD_TIMEOUT_GRACE,
        "hard_timeout_for with zero solver timeout should return just the grace period"
    );
}

// --- hard_timeout_worker_wait_budget unit tests ---

#[test]
#[timeout(30000)]
fn worker_wait_budget_clamped_to_default_for_large_timeout() {
    let large = Duration::from_mins(5);
    let budget = super::hard_timeout_worker_wait_budget(large);
    assert_eq!(
        budget,
        super::DEFAULT_HARD_TIMEOUT,
        "wait budget should be clamped to DEFAULT_HARD_TIMEOUT for large outer timeouts"
    );
}

#[test]
#[timeout(30000)]
fn worker_wait_budget_uses_outer_timeout_when_smaller_than_default() {
    let small = Duration::from_millis(100);
    let budget = super::hard_timeout_worker_wait_budget(small);
    assert_eq!(
        budget, small,
        "wait budget should use the outer timeout when it is smaller than DEFAULT_HARD_TIMEOUT"
    );
}

// --- run_with_hard_timeout success path ---

#[test]
#[timeout(30000)]
fn run_with_hard_timeout_success_restores_encoder_state() {
    let _serial = super::hard_timeout_test_serial_guard_for_test();
    let _isolated = super::isolated_hard_timeout_limiter_for_test();
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));

    let mut encoder = AYEncoder::new();
    let timeout_val = Duration::from_millis(50);
    encoder.set_timeout(Some(timeout_val));

    let result = super::run_with_hard_timeout(&mut encoder, resolve_verified);
    assert!(
        matches!(
            result,
            ResolveContinuation::Continue(VerificationResult::Verified(_))
        ),
        "successful resolve should continue with Verified: {result:?}"
    );
    assert_eq!(
        encoder.solver().timeout(),
        Some(timeout_val),
        "encoder should be fully restored after successful hard-timeout resolution"
    );

    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));
}

// --- Disconnected channel path ---

#[test]
#[timeout(30000)]
fn run_with_hard_timeout_worker_panic_returns_solver_panic_abort() {
    let _serial = super::hard_timeout_test_serial_guard_for_test();
    let _isolated = super::isolated_hard_timeout_limiter_for_test();
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));

    fn resolve_panic(_: &mut AYEncoder) -> VerificationResult {
        panic!("simulated solver crash in worker thread");
    }

    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(Duration::from_millis(50)));

    let result = super::run_with_hard_timeout(&mut encoder, resolve_panic);
    // Worker panics → channel disconnects before sending → Disconnected path
    assert!(
        matches!(
            result,
            ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::SolverPanic(_)))
        ),
        "worker panic should produce Abort(Unknown(SolverPanic)): {result:?}"
    );

    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(5));
}

// --- OwnedEncoderPtr round-trip ---

#[test]
#[timeout(30000)]
fn owned_encoder_ptr_round_trip_preserves_allocation() {
    let encoder = Box::new(AYEncoder::new());
    let ptr = super::OwnedEncoderPtr::from_box(encoder);
    // Round-trip: from_box → into_box should return a valid encoder.
    let recovered = ptr.into_box();
    // Verify the recovered encoder is functional.
    assert!(
        recovered.solver().timeout().is_none(),
        "round-tripped encoder should have default state (no timeout)"
    );
}

// --- Constants ---

#[test]
#[timeout(30000)]
#[allow(clippy::assertions_on_constants)] // compile-time range check on const, intentional
fn default_max_hard_timeout_workers_is_reasonable() {
    assert!(
        super::DEFAULT_MAX_HARD_TIMEOUT_WORKERS >= 2,
        "limiter should allow at least 2 concurrent workers"
    );
    assert!(
        super::DEFAULT_MAX_HARD_TIMEOUT_WORKERS <= 32,
        "limiter should not allow unreasonable concurrency"
    );
}

#[test]
#[timeout(30000)]
fn max_hard_timeout_workers_reads_env_override() {
    let result = super::max_hard_timeout_workers_from_raw(Some("64"));
    assert_eq!(
        result, 64,
        "max_hard_timeout_workers should respect TRUST_WP_MAX_HARD_TIMEOUT_WORKERS"
    );
}

#[test]
#[timeout(30000)]
fn max_hard_timeout_workers_ignores_invalid_or_zero_env() {
    assert_eq!(
        super::max_hard_timeout_workers_from_raw(Some("0")),
        super::DEFAULT_MAX_HARD_TIMEOUT_WORKERS,
        "zero worker cap should fall back to default"
    );
    assert_eq!(
        super::max_hard_timeout_workers_from_raw(Some("not-a-number")),
        super::DEFAULT_MAX_HARD_TIMEOUT_WORKERS,
        "invalid worker cap should fall back to default"
    );
}

#[test]
#[timeout(30000)]
fn default_hard_timeout_is_at_least_10_seconds() {
    assert!(
        super::DEFAULT_HARD_TIMEOUT >= Duration::from_secs(10),
        "default hard timeout should be at least 10 seconds: {:?}",
        super::DEFAULT_HARD_TIMEOUT
    );
}

#[test]
#[timeout(30000)]
fn hard_timeout_grace_is_positive() {
    assert!(
        super::HARD_TIMEOUT_GRACE > Duration::ZERO,
        "grace period must be positive to avoid zero-duration recv_timeout"
    );
}

#[test]
#[timeout(30000)]
fn moved_guard_releases_slot_when_worker_thread_exits() {
    let _serial = super::hard_timeout_test_serial_guard_for_test();
    let _isolated = super::isolated_hard_timeout_limiter_for_test();
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));

    let guard = super::reserve_hard_timeout_worker_slot(Duration::ZERO)
        .expect("slot reservation should succeed when slots are available");
    assert_eq!(super::live_hard_timeout_worker_count_for_test(), 1);

    std::thread::spawn(move || {
        let _guard = guard;
    })
    .join()
    .expect("worker thread should exit cleanly");

    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));
}

#[test]
#[timeout(30000)]
fn panicking_worker_thread_still_releases_slot() {
    let _serial = super::hard_timeout_test_serial_guard_for_test();
    let _isolated = super::isolated_hard_timeout_limiter_for_test();
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));

    let guard = super::reserve_hard_timeout_worker_slot(Duration::ZERO)
        .expect("slot reservation should succeed when slots are available");
    assert_eq!(super::live_hard_timeout_worker_count_for_test(), 1);

    let panic_result = std::thread::spawn(move || {
        let _guard = guard;
        panic!("simulated hard-timeout worker panic");
    })
    .join();
    assert!(
        panic_result.is_err(),
        "panic regression test should propagate the simulated worker panic"
    );

    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));
}

#[test]
#[timeout(30000)]
fn forced_hard_timeout_eventually_releases_worker_slot() {
    let _serial = super::hard_timeout_test_serial_guard_for_test();
    let _isolated = super::isolated_hard_timeout_limiter_for_test();
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));

    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(Duration::from_millis(1)));
    let _force_guard = super::force_hard_timeout_for_test();

    let result = super::run_with_hard_timeout(&mut encoder, resolve_verified);
    assert!(
        matches!(
            result,
            ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout))
        ),
        "forced hard-timeout path should still abort with Unknown(timeout): {result:?}"
    );
    assert_eq!(
        super::live_hard_timeout_worker_count_for_test(),
        1,
        "timed-out worker should stay counted until its thread exits and drops the guard"
    );

    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));
}

#[test]
#[timeout(30000)]
fn saturated_limiter_returns_resource_out_without_inline_solve() {
    let _serial = super::hard_timeout_test_serial_guard_for_test();
    let _isolated = super::isolated_hard_timeout_limiter_for_test();
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));

    let max_workers = super::max_hard_timeout_workers();
    let guards: Vec<_> = (0..max_workers)
        .map(|_| {
            super::reserve_hard_timeout_worker_slot(Duration::ZERO)
                .expect("slot reservation should succeed when filling limiter")
        })
        .collect();

    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(Duration::from_millis(20)));

    // With all slots occupied, run_with_hard_timeout should fail closed
    // without spawning a thread or running an uninterruptible inline solve.
    let start = Instant::now();
    let result = super::run_with_hard_timeout(&mut encoder, resolve_verified);
    let elapsed = start.elapsed();

    assert!(
        matches!(
            result,
            ResolveContinuation::Continue(VerificationResult::Unknown(UnknownReason::ResourceOut))
        ),
        "saturated limiter should return Unknown(ResourceOut): {result:?}"
    );
    // ResourceOut should be fast — no thread spawn, no inline solve.
    assert!(
        elapsed <= Duration::from_secs(5),
        "saturated limiter fail-closed path should complete quickly: elapsed {elapsed:?}"
    );
    // Worker count should not have changed — no thread was spawned.
    assert_eq!(
        super::live_hard_timeout_worker_count_for_test(),
        max_workers,
        "resource-out path should not affect the live worker count"
    );

    drop(guards);
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));
}

// --- RSS memory guard tests ---

#[test]
#[timeout(30000)]
fn get_process_rss_bytes_returns_nonzero() {
    let rss = super::get_process_rss_bytes();
    assert!(
        rss > 0,
        "get_process_rss_bytes should return a positive value for a running process"
    );
    // Sanity: a running Rust test process should be at least 1 MB.
    assert!(
        rss >= 1024 * 1024,
        "RSS should be at least 1 MB for a running test process, got {rss} bytes"
    );
}

#[test]
#[timeout(30000)]
fn default_max_rss_bytes_is_12_gb() {
    assert_eq!(
        super::DEFAULT_MAX_RSS_BYTES,
        12 * 1024 * 1024 * 1024,
        "default RSS limit should be 12 GB"
    );
}

#[test]
#[timeout(30000)]
fn max_rss_bytes_returns_default_when_env_unset() {
    let result = super::max_rss_bytes_from_raw(None);
    assert_eq!(
        result,
        super::DEFAULT_MAX_RSS_BYTES,
        "max_rss_bytes should return default when TRUST_WP_MAX_RSS_BYTES is unset"
    );
}

#[test]
#[timeout(30000)]
fn max_rss_bytes_reads_env_override() {
    let result = super::max_rss_bytes_from_raw(Some("4294967296")); // 4 GB
    assert_eq!(
        result, 4_294_967_296,
        "max_rss_bytes should respect TRUST_WP_MAX_RSS_BYTES env var"
    );
}

#[test]
#[timeout(30000)]
fn max_rss_bytes_ignores_invalid_env() {
    let result = super::max_rss_bytes_from_raw(Some("not_a_number"));
    assert_eq!(
        result,
        super::DEFAULT_MAX_RSS_BYTES,
        "max_rss_bytes should fall back to default for non-numeric env"
    );
}

#[test]
#[timeout(30000)]
fn rss_guard_allows_normal_operation_below_limit() {
    // This test verifies that run_with_hard_timeout works normally when
    // RSS is below the explicit limit (i.e., the guard does not false-trigger).
    let _serial = super::hard_timeout_test_serial_guard_for_test();

    let _isolated = super::isolated_hard_timeout_limiter_for_test();
    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));

    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(Duration::from_millis(50)));

    let result = super::run_with_hard_timeout_with_rss_limit(
        &mut encoder,
        resolve_verified,
        64 * 1024 * 1024 * 1024,
    );

    assert!(
        matches!(
            result,
            ResolveContinuation::Continue(VerificationResult::Verified(_))
        ),
        "run_with_hard_timeout should succeed normally when RSS is below limit: {result:?}"
    );

    super::wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));
}

#[test]
#[timeout(30000)]
fn rss_guard_fails_closed_when_limit_exceeded() {
    // Pass an absurdly low RSS limit (1 byte) to force the guard to trigger.
    let _serial = super::hard_timeout_test_serial_guard_for_test();

    let mut encoder = AYEncoder::new();
    encoder.set_timeout(Some(Duration::from_millis(50)));

    let result = super::run_with_hard_timeout_with_rss_limit(&mut encoder, resolve_verified, 1);

    // Running inline here can bypass the hard-timeout envelope when the process
    // is already under memory pressure. Fail closed instead.
    assert!(
        matches!(
            result,
            ResolveContinuation::Continue(VerificationResult::Unknown(UnknownReason::ResourceOut))
        ),
        "RSS guard should fail closed with ResourceOut: {result:?}"
    );
}
