// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    ptr::NonNull,
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc::RecvTimeoutError,
    },
    time::{Duration, Instant},
};

use super::{UnknownReason, VerificationResult};
use crate::encoder::{unsoundness, AYEncoder};

const DEFAULT_HARD_TIMEOUT: Duration = Duration::from_mins(1);
const HARD_TIMEOUT_GRACE: Duration = Duration::from_millis(100);
const HARD_TIMEOUT_WORKER_POLL_INTERVAL: Duration = Duration::from_millis(50);
// Keep the default pool bounded, but large enough that a handful of
// non-interruptible solver timeouts in a serial full-suite run do not poison
// unrelated tests. The cap can be raised for controlled full-suite dependency
// gates via `TRUST_WP_MAX_HARD_TIMEOUT_WORKERS`.
const DEFAULT_MAX_HARD_TIMEOUT_WORKERS: usize = 16;

/// Default RSS limit: 12 GB. Configurable via `TRUST_WP_MAX_RSS_BYTES`.
const DEFAULT_MAX_RSS_BYTES: u64 = 12 * 1024 * 1024 * 1024;

/// Stack size for the spawned solver/replay worker threads: 256 MiB.
///
/// The native base-replay decodes a serialized assertion stack by recursively
/// walking its exported term forest; on tests with large replays (e.g.
/// cc/collections' `into_iter` contract) the default ~2–8 MiB worker stack
/// overflows, which aborts the whole PROCESS (SIGABRT) rather than failing the
/// one obligation — a crash class that can strand any large-replay test. A
/// worker thread does not commit this reservation up front (it is virtual
/// address space, faulted in lazily), so the generous size is effectively free
/// unless the deep walk actually needs it. Mirrors the demonstrated
/// `RUST_MIN_STACK=256MiB` fix, but scoped to the worker threads that need it.
const REPLAY_WORKER_STACK_BYTES: usize = 256 * 1024 * 1024;

static LIVE_HARD_TIMEOUT_WORKERS: AtomicUsize = AtomicUsize::new(0);
static PROCESS_ISOLATION_FORKED_CHILD: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Abandoned worker threads from timed-out solves. We try to join these
/// before spawning new workers to reclaim memory from completed stuck threads.
static ABANDONED_WORKERS: std::sync::Mutex<Vec<std::thread::JoinHandle<()>>> =
    std::sync::Mutex::new(Vec::new());

/// Try to join completed abandoned workers to reclaim their memory.
/// Retains only threads that are still running.
fn try_reclaim_abandoned_workers() {
    if PROCESS_ISOLATION_FORKED_CHILD.load(Ordering::SeqCst) {
        return;
    }
    let mut workers = match ABANDONED_WORKERS.lock() {
        Ok(guard) => guard,
        Err(poisoned) => poisoned.into_inner(),
    };
    workers.retain(|handle| !handle.is_finished());
}

/// Store a timed-out worker's `JoinHandle` for later cleanup.
fn abandon_worker(handle: std::thread::JoinHandle<()>) {
    if PROCESS_ISOLATION_FORKED_CHILD.load(Ordering::SeqCst) {
        drop(handle);
        return;
    }
    let mut workers = match ABANDONED_WORKERS.lock() {
        Ok(guard) => guard,
        Err(poisoned) => poisoned.into_inner(),
    };
    workers.push(handle);
}

#[cfg(unix)]
pub(super) fn reset_after_process_isolation_fork() {
    // After `fork`, only the calling thread exists in the child process. The
    // copied worker count and abandoned JoinHandles describe parent-process
    // threads that the child cannot join or wait on.
    PROCESS_ISOLATION_FORKED_CHILD.store(true, Ordering::SeqCst);
    LIVE_HARD_TIMEOUT_WORKERS.store(0, Ordering::SeqCst);
}

#[derive(Debug)]
pub(crate) enum ResolveContinuation {
    Continue(VerificationResult),
    Abort(VerificationResult),
}

/// Drop-safe wrapper for encoder pointer payloads (channel, worker return).
///
/// `OwnedEncoderPtr` owns the leaked `Box<AYEncoder>` allocation and will
/// deallocate it on `Drop`. Used for channel payloads so unread messages
/// do not leak the encoder (#2431).
#[derive(Debug)]
struct OwnedEncoderPtr(NonNull<AYEncoder>);

impl OwnedEncoderPtr {
    fn from_box(boxed: Box<AYEncoder>) -> Self {
        Self(NonNull::from(Box::leak(boxed)))
    }

    fn into_box(self) -> Box<AYEncoder> {
        let ptr = self.0.as_ptr();
        std::mem::forget(self);
        // SAFETY: `OwnedEncoderPtr` owns this allocation exclusively unless
        // `into_box` has already consumed it.
        unsafe { Box::from_raw(ptr) }
    }
}

impl Drop for OwnedEncoderPtr {
    fn drop(&mut self) {
        // SAFETY: `OwnedEncoderPtr` owns this allocation exclusively unless
        // `into_box` consumed it and `mem::forget(self)` suppressed `Drop`.
        unsafe {
            drop(Box::from_raw(self.0.as_ptr()));
        }
    }
}

// SAFETY: `OwnedEncoderPtr` carries the same exclusive `AYEncoder` ownership
// transfer this module previously implemented with a raw `usize`. `mem::take`
// removes the caller's live encoder, the worker thread becomes the sole owner,
// and ownership only returns through the channel or is dropped by `OwnedEncoderPtr`.
// No alias to the moved encoder remains on the caller thread during the handoff.
unsafe impl Send for OwnedEncoderPtr {}

/// Send-only wrapper for the spawn boundary — NO `Drop` impl. (#2435)
///
/// On spawn failure the closure is dropped. If the closure captured an
/// `OwnedEncoderPtr` (which has `Drop`), that drop would deallocate the
/// encoder. The spawn-failure recovery path then does `Box::from_raw` on
/// the same pointer → double-free / UB.
///
/// `SendEncoderPtr` carries the pointer across the `Send` boundary without
/// a `Drop` impl, so spawn failure just discards the wrapper harmlessly.
/// Ownership is reconstituted inside the closure via `Box::from_raw`.
struct SendEncoderPtr(NonNull<AYEncoder>);

impl SendEncoderPtr {
    /// Reconstitute the owned `Box<AYEncoder>` from the raw pointer.
    ///
    /// # Safety
    /// Caller must have exclusive ownership of the allocation.
    unsafe fn into_box(self) -> Box<AYEncoder> {
        // SAFETY: required by the `unsafe fn` contract above; ownership of
        // this allocation is exclusive when the worker reconstructs it.
        unsafe { Box::from_raw(self.0.as_ptr()) }
    }
}

// SAFETY: exclusive ownership is transferred to the spawned thread.
// The caller retains a Copy of the raw NonNull only for the spawn-failure
// recovery path, which is unreachable when the thread starts successfully.
unsafe impl Send for SendEncoderPtr {}

type ChannelPayload = (
    OwnedEncoderPtr,
    VerificationResult,
    unsoundness::Snapshot,
    Option<super::solver_tail::PreferredVerifiedSolveDiagnostics>,
);

struct HardTimeoutWorkerGuard;

impl Drop for HardTimeoutWorkerGuard {
    fn drop(&mut self) {
        let previous = LIVE_HARD_TIMEOUT_WORKERS.fetch_sub(1, Ordering::SeqCst);
        debug_assert!(
            previous > 0,
            "hard-timeout worker guard dropped without a reserved slot"
        );
    }
}

/// Query the current process RSS (resident set size) in bytes.
///
/// Uses `ps -o rss= -p <pid>` which returns RSS in kilobytes. This is
/// called once per `run_with_hard_timeout` invocation (before spawning the
/// worker thread), so the subprocess overhead (~1ms) is negligible compared
/// to solver execution time.
///
/// Returns 0 on any failure (conservative — never blocks verification on
/// a monitoring error).
fn get_process_rss_bytes() -> u64 {
    let pid = std::process::id();
    std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.trim().parse::<u64>().ok())
        .map(|kb| kb * 1024)
        .unwrap_or(0)
}

/// Read the RSS ceiling from `TRUST_WP_MAX_RSS_BYTES`, falling back to
/// [`DEFAULT_MAX_RSS_BYTES`] (12 GB).
fn max_rss_bytes() -> u64 {
    let raw = std::env::var("TRUST_WP_MAX_RSS_BYTES").ok();
    max_rss_bytes_from_raw(raw.as_deref())
}

fn max_rss_bytes_from_raw(raw: Option<&str>) -> u64 {
    raw.and_then(|value| value.parse().ok())
        .unwrap_or(DEFAULT_MAX_RSS_BYTES)
}

fn max_hard_timeout_workers() -> usize {
    let raw = std::env::var("TRUST_WP_MAX_HARD_TIMEOUT_WORKERS").ok();
    max_hard_timeout_workers_from_raw(raw.as_deref())
}

fn max_hard_timeout_workers_from_raw(raw: Option<&str>) -> usize {
    raw.and_then(|value| value.parse().ok())
        .filter(|value| *value > 0)
        .unwrap_or(DEFAULT_MAX_HARD_TIMEOUT_WORKERS)
}

/// Attempt to reserve a hard-timeout worker slot within `wait_budget`.
///
/// Returns `Some(guard)` if a slot was acquired, `None` if all slots are
/// occupied by stuck (non-interruptible) solver threads after the wait
/// budget expires. The caller must fail closed when `None` is returned,
/// avoiding both unbounded worker growth and an uninterruptible inline solve.
fn reserve_hard_timeout_worker_slot(wait_budget: Duration) -> Option<HardTimeoutWorkerGuard> {
    // Try to reclaim finished zombie workers before checking slot availability.
    try_reclaim_abandoned_workers();
    let start = Instant::now();
    loop {
        let max_workers = max_hard_timeout_workers();
        let live_workers = LIVE_HARD_TIMEOUT_WORKERS.load(Ordering::SeqCst);
        if live_workers < max_workers {
            if LIVE_HARD_TIMEOUT_WORKERS
                .compare_exchange_weak(
                    live_workers,
                    live_workers + 1,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                )
                .is_ok()
            {
                return Some(HardTimeoutWorkerGuard);
            }
            continue;
        }

        let elapsed = start.elapsed();
        if elapsed >= wait_budget {
            tracing::warn!(
                live_workers,
                max_workers,
                ?wait_budget,
                "hard-timeout worker limiter saturated; refusing to oversubscribe"
            );
            return None;
        }

        let remaining = wait_budget.saturating_sub(elapsed);
        std::thread::sleep(HARD_TIMEOUT_WORKER_POLL_INTERVAL.min(remaining));
    }
}

/// Run a resolve helper behind an outer hard-timeout envelope.
///
/// When the inner solve completes normally, the live encoder is restored to the
/// caller and the result is returned as [`ResolveContinuation::Continue`].
///
/// When the outer deadline expires, the helper interrupts the live solver and
/// returns [`ResolveContinuation::Abort`] because the live encoder is still
/// owned by the worker thread and the caller must not use the placeholder
/// encoder left behind by `mem::take`.
///
/// When all worker slots are occupied by stuck (non-interruptible) solver
/// threads, the helper returns a structured resource exhaustion result instead
/// of running inline. Inline fallback can overrun the caller's wall-clock
/// budget when the underlying solver phase ignores its soft timeout.
pub(crate) fn run_with_hard_timeout(
    encoder: &mut AYEncoder,
    resolve: fn(&mut AYEncoder) -> VerificationResult,
) -> ResolveContinuation {
    run_with_hard_timeout_with_rss_limit(encoder, resolve, max_rss_bytes())
}

fn run_with_hard_timeout_with_rss_limit(
    encoder: &mut AYEncoder,
    resolve: fn(&mut AYEncoder) -> VerificationResult,
    rss_limit: u64,
) -> ResolveContinuation {
    // RSS memory guard: refuse to spawn a new solver worker when the
    // process is already consuming too much memory.  This prevents the
    // OOM cascade that caused a macOS kernel panic (100% compressed
    // pages, 59 swap files).  On failure to read RSS we get 0 which
    // safely passes the check.
    let current_rss = get_process_rss_bytes();
    if current_rss > 0 && current_rss > rss_limit {
        tracing::warn!(
            current_rss_mb = current_rss / (1024 * 1024),
            max_rss_mb = rss_limit / (1024 * 1024),
            "RSS memory limit exceeded; refusing to spawn hard-timeout worker"
        );
        return ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::ResourceOut,
        ));
    }
    #[cfg(test)]
    let _serial = hard_timeout_test_serial_guard_for_test();
    // In production, start the envelope timer before slot reservation so
    // that slot-wait time counts against the hard-timeout budget (#2607).
    #[cfg(not(test))]
    let envelope_start = Instant::now();
    let outer_timeout = hard_timeout_for(encoder);
    let worker_guard =
        reserve_hard_timeout_worker_slot(hard_timeout_worker_wait_budget(outer_timeout));

    // If all worker slots are occupied by stuck threads, fail closed. Running
    // inline here can bypass the hard-timeout envelope and trip outer test or
    // request watchdogs.
    let worker_guard = match worker_guard {
        Some(guard) => guard,
        None => {
            tracing::info!("hard-timeout worker slots saturated; returning resource-out");
            return ResolveContinuation::Continue(VerificationResult::Unknown(
                UnknownReason::ResourceOut,
            ));
        }
    };

    // In test mode, start the envelope timer AFTER slot reservation so that
    // test-infrastructure overhead (serial guard + slot contention from
    // parallel test threads) does not steal time from the solver recv
    // timeout.  This prevents ~32 borderline tests from timing out when
    // the full suite runs in parallel (#2607).
    #[cfg(test)]
    let envelope_start = Instant::now();
    #[cfg(test)]
    let force_hard_timeout = force_hard_timeout_enabled();
    let owned = Box::new(std::mem::take(encoder));
    let interrupt = owned.solver().interrupt_handle();
    let owned_ptr = NonNull::from(Box::leak(owned));
    // Use SendEncoderPtr (no Drop) across the spawn boundary to avoid
    // double-free on spawn failure (#2435). OwnedEncoderPtr (with Drop)
    // is only created inside the closure for channel payload safety.
    let sendable_ptr = SendEncoderPtr(owned_ptr);
    let (send, recv) = std::sync::mpsc::channel::<ChannelPayload>();
    // Thread-local proof-assert authority does not automatically cross the
    // worker boundary. Propagate both lane identity and an already-certified
    // core that a subsequent base-SAT recheck must not erase.
    let proof_assert_mode = super::solver_tail::in_proof_assert_mode();
    let proof_assert_slice_identity = super::solver_tail::active_proof_assert_slice_identity();
    let inherited_proof_assert_diagnostics = proof_assert_mode
        .then(super::solver_tail::clone_preferred_verified_solve_diagnostics)
        .flatten();

    let spawn_result = std::thread::Builder::new()
        .name("trust-wp-hard-timeout".to_string())
        .stack_size(REPLAY_WORKER_STACK_BYTES)
        .spawn(move || {
            let _worker_guard = worker_guard;
            let _proof_assert_guard =
                proof_assert_mode.then(super::solver_tail::ProofAssertModeGuard::enter);
            let _proof_assert_slice_guard = proof_assert_slice_identity
                .map(super::solver_tail::ProofAssertSliceClaimGuard::enter);
            if proof_assert_mode {
                super::solver_tail::replace_preferred_verified_solve_diagnostics(
                    inherited_proof_assert_diagnostics,
                );
            }
            // SAFETY: exclusive ownership transferred to this thread.
            let mut owned = unsafe { sendable_ptr.into_box() };
            #[cfg(test)]
            if force_hard_timeout {
                std::thread::sleep(
                    outer_timeout
                        .checked_add(HARD_TIMEOUT_GRACE)
                        .unwrap_or(outer_timeout),
                );
            }

            let result = resolve(&mut owned);
            let proof_assert_diagnostics = proof_assert_mode
                .then(super::solver_tail::take_preferred_verified_solve_diagnostics)
                .flatten();
            let worker_snapshot = unsoundness::snapshot();
            let returned_ptr = OwnedEncoderPtr::from_box(owned);
            let _ = send.send((
                returned_ptr,
                result,
                worker_snapshot,
                proof_assert_diagnostics,
            ));
        });

    let worker = match spawn_result {
        Ok(worker) => worker,
        Err(err) => {
            // SAFETY: spawn failed → closure dropped → SendEncoderPtr has no Drop
            // → the leaked allocation is still valid. Reconstruct the Box.
            let owned = unsafe { Box::from_raw(owned_ptr.as_ptr()) };
            *encoder = *owned;
            return ResolveContinuation::Continue(VerificationResult::Unknown(
                UnknownReason::SolverMessage(format!("failed to spawn hard-timeout worker: {err}")),
            ));
        }
    };

    let remaining_timeout = outer_timeout.saturating_sub(envelope_start.elapsed());

    match recv.recv_timeout(remaining_timeout) {
        Ok((returned_ptr, result, worker_snapshot, proof_assert_diagnostics)) => {
            let returned_encoder = returned_ptr.into_box();
            *encoder = *returned_encoder;
            if proof_assert_mode {
                super::solver_tail::replace_preferred_verified_solve_diagnostics(
                    proof_assert_diagnostics,
                );
            }
            unsoundness::apply_delta(&worker_snapshot);
            ResolveContinuation::Continue(result)
        }
        Err(RecvTimeoutError::Timeout) => {
            interrupt.store(true, Ordering::Relaxed);
            tracing::warn!(
                ?outer_timeout,
                ?remaining_timeout,
                "hard timeout expired while waiting for solver result; \
                 abandoning worker for later cleanup"
            );
            // Store the worker handle for later cleanup instead of dropping
            // it (which detaches the thread). This gives us a chance to join
            // completed zombies before spawning new workers.
            abandon_worker(worker);
            // The worker still owns its thread-local counters on timeout, so
            // there is no safe snapshot to merge here yet. This remains a
            // conservative limitation of the abort path.
            ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout))
        }
        Err(RecvTimeoutError::Disconnected) => {
            tracing::warn!("hard-timeout worker disconnected before returning encoder");
            ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::SolverPanic(
                "hard-timeout worker disconnected before returning encoder".to_string(),
            )))
        }
    }
}

fn hard_timeout_worker_wait_budget(outer_timeout: Duration) -> Duration {
    outer_timeout.min(DEFAULT_HARD_TIMEOUT)
}

/// Outcome of a detached (encoder-less) base-stack replay solve.
#[derive(Debug)]
pub(crate) enum DetachedReplayOutcome {
    /// The worker finished within the envelope. `None` means the replay
    /// artifact failed to parse/rebuild — treat as inconclusive.
    Completed(Option<ay_dpll::api::SolveDetails>),
    /// The envelope expired: the base solve is pathological (its soft timeout
    /// was not honored). The worker was abandoned — but it owned only the
    /// exported replay JSON, so the caller's live encoder is untouched.
    TimedOut,
    /// No worker could run (RSS guard, slot saturation, or spawn failure).
    Unavailable,
}

/// Maximum concurrent detached replay workers.
///
/// Detached replay workers deliberately live in their OWN small pool, fully
/// separate from the `LIVE_HARD_TIMEOUT_WORKERS` limiter: a hung
/// (non-interruptible) replay solve occupies its slot until the thread
/// finishes, and sharing the main pool would let leaked replay workers starve
/// PRIMARY solves into `ResourceOut` Unknowns (observed as mass
/// SAT-expected-got-Unknown unit-test failures plus a memory-pressure
/// SIGKILL of the test binary). When this pool is full the detached phase is
/// simply SKIPPED — never waited on. Kept very small because an abandoned
/// hung replay spins on a core until its solve loop notices the interrupt
/// flag (which some ay phases never do); the per-obligation pathology latch
/// in `run_base_recheck_preserving_encoder` means one pathological obligation
/// leaks at most one worker.
const MAX_DETACHED_REPLAY_WORKERS: usize = 2;

static LIVE_DETACHED_REPLAY_WORKERS: AtomicUsize = AtomicUsize::new(0);

struct DetachedReplayWorkerGuard;

impl Drop for DetachedReplayWorkerGuard {
    fn drop(&mut self) {
        LIVE_DETACHED_REPLAY_WORKERS.fetch_sub(1, Ordering::SeqCst);
    }
}

/// Try to reserve a detached replay worker slot WITHOUT waiting.
///
/// Non-blocking by design: the detached phase is a best-effort optimization,
/// so pool exhaustion (e.g. pathological bases leaking hung replay threads)
/// must cost nothing — the caller immediately falls back to the classic
/// recheck path.
fn try_reserve_detached_replay_worker_slot() -> Option<DetachedReplayWorkerGuard> {
    try_reclaim_abandoned_workers();
    loop {
        let live = LIVE_DETACHED_REPLAY_WORKERS.load(Ordering::SeqCst);
        if live >= MAX_DETACHED_REPLAY_WORKERS {
            return None;
        }
        if LIVE_DETACHED_REPLAY_WORKERS
            .compare_exchange_weak(live, live + 1, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            return Some(DetachedReplayWorkerGuard);
        }
    }
}

/// Run a fresh native-replay re-solve of an exported assertion stack behind a
/// hard-timeout envelope, WITHOUT ever giving up the live encoder (#2414
/// non-fatal base recheck).
///
/// `run_with_hard_timeout` must `mem::take` the caller's encoder, so an
/// expired envelope permanently costs the live encoder (and with it, every
/// remaining obligation slice). This runner instead ships only the exported
/// replay JSON to the worker: an expired envelope abandons the worker thread
/// and its private fresh solver, and the caller keeps solving with its intact
/// incremental encoder. The cached native replay is flushed (exported) by the
/// caller BEFORE the worker could ever be abandoned.
pub(crate) fn run_detached_replay_solve_with_hard_timeout(
    replay_json: String,
    outer_timeout: Duration,
) -> DetachedReplayOutcome {
    // Same RSS memory guard as `run_with_hard_timeout`: never spawn another
    // solver worker when the process is already memory-constrained.
    let current_rss = get_process_rss_bytes();
    let rss_limit = max_rss_bytes();
    if current_rss > 0 && current_rss > rss_limit {
        tracing::warn!(
            current_rss_mb = current_rss / (1024 * 1024),
            max_rss_mb = rss_limit / (1024 * 1024),
            "RSS memory limit exceeded; refusing to spawn detached replay worker"
        );
        return DetachedReplayOutcome::Unavailable;
    }
    let Some(worker_guard) = try_reserve_detached_replay_worker_slot() else {
        tracing::debug!("detached replay worker pool full; skipping detached replay solve");
        return DetachedReplayOutcome::Unavailable;
    };

    let (send, recv) = std::sync::mpsc::channel::<Option<ay_dpll::api::SolveDetails>>();
    let spawn_result = std::thread::Builder::new()
        .name("trust-wp-base-replay".to_string())
        .stack_size(REPLAY_WORKER_STACK_BYTES)
        .spawn(move || {
            let _worker_guard = worker_guard;
            let details = ay_dpll::api::Solver::replay_native_replay_json_str(&replay_json).ok();
            let _ = send.send(details);
        });

    let worker = match spawn_result {
        Ok(worker) => worker,
        Err(err) => {
            tracing::warn!("failed to spawn detached replay worker: {err}");
            return DetachedReplayOutcome::Unavailable;
        }
    };

    match recv.recv_timeout(outer_timeout) {
        Ok(details) => {
            let _ = worker.join();
            DetachedReplayOutcome::Completed(details)
        }
        Err(RecvTimeoutError::Timeout) => {
            tracing::warn!(
                ?outer_timeout,
                "detached replay solve exceeded its envelope; abandoning worker \
                 (live encoder unaffected)"
            );
            abandon_worker(worker);
            DetachedReplayOutcome::TimedOut
        }
        Err(RecvTimeoutError::Disconnected) => {
            tracing::warn!("detached replay worker disconnected before returning a result");
            DetachedReplayOutcome::Completed(None)
        }
    }
}

/// Compute the hard-timeout envelope for a solver call.
///
/// Previously used 3× solver timeout + grace (#1342), then 2× + grace,
/// then 1.75× + grace, now reduced to 1.5× + grace (#2674). The worst-case
/// wall-clock for a single `resolve_*` call is:
///   tiered probe (10s) + full solve (T) = 10 + T
/// For T=60s: 70s. The 1.5× + grace envelope (90.1s) provides 20s of
/// margin for thread scheduling, scope push/pop overhead, the 500ms
/// axiom-free probe, and the base recheck (in its own tight 26s envelope).
/// The tiered solve path skips the retry after a probe + full solve
/// sequence (#2674), so the worst case is probe + full without retry.
///
/// The base recheck has its own tight envelope via
/// `run_base_recheck_with_tight_timeout` (1.5× × 15s + grace = 22.6s),
/// so it does not eat into the main solve's hard-timeout budget.
///
/// Non-tiered paths (solver timeout < 15s) still use check_sat_with_retry,
/// where the worst case is T + T/2 = 1.5T. For T=14s: 21s, within
/// the 1.5 × 14 + 0.1 = 21.1s envelope.
fn hard_timeout_for(encoder: &AYEncoder) -> Duration {
    match encoder.solver().timeout() {
        // 1.5× + grace: T + T/2 + grace
        Some(timeout) => timeout
            .checked_add(timeout / 2)
            .and_then(|value| value.checked_add(HARD_TIMEOUT_GRACE))
            .unwrap_or(timeout),
        // TRUST_WP_HARD_TIMEOUT_SECS: watchdog-cap override for solves that
        // run without an encoder timeout. A larger cap only grants compute —
        // it can never change a verdict (the watchdog aborts to Unknown).
        None => std::env::var("TRUST_WP_HARD_TIMEOUT_SECS")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .map(Duration::from_secs)
            .unwrap_or(DEFAULT_HARD_TIMEOUT)
            .checked_add(HARD_TIMEOUT_GRACE)
            .unwrap_or(DEFAULT_HARD_TIMEOUT),
    }
}

#[cfg(test)]
thread_local! {
    static FORCE_HARD_TIMEOUT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
thread_local! {
    static HOLDING_HARD_TIMEOUT_TEST_LOCK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct HardTimeoutTestSerialGuard(Option<std::sync::MutexGuard<'static, ()>>);

#[cfg(test)]
fn hard_timeout_test_mutex() -> &'static std::sync::Mutex<()> {
    static TEST_MUTEX: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
    TEST_MUTEX.get_or_init(|| std::sync::Mutex::new(()))
}

#[cfg(test)]
fn hard_timeout_test_serial_guard_for_test() -> HardTimeoutTestSerialGuard {
    if PROCESS_ISOLATION_FORKED_CHILD.load(Ordering::SeqCst) {
        return HardTimeoutTestSerialGuard(None);
    }

    let already_holding = HOLDING_HARD_TIMEOUT_TEST_LOCK.with(|flag| {
        if flag.get() {
            true
        } else {
            flag.set(true);
            false
        }
    });

    if already_holding {
        return HardTimeoutTestSerialGuard(None);
    }

    let guard = hard_timeout_test_mutex()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    HardTimeoutTestSerialGuard(Some(guard))
}

#[cfg(test)]
impl Drop for HardTimeoutTestSerialGuard {
    fn drop(&mut self) {
        if let Some(guard) = self.0.take() {
            drop(guard);
            HOLDING_HARD_TIMEOUT_TEST_LOCK.with(|flag| flag.set(false));
        }
    }
}

#[cfg(test)]
pub(crate) struct ForceHardTimeoutGuard;

#[cfg(test)]
pub(crate) fn force_hard_timeout_for_test() -> ForceHardTimeoutGuard {
    FORCE_HARD_TIMEOUT.with(|flag| {
        assert!(
            !flag.replace(true),
            "force_hard_timeout_for_test must not be nested on the same thread"
        );
    });
    ForceHardTimeoutGuard
}

#[cfg(test)]
impl Drop for ForceHardTimeoutGuard {
    fn drop(&mut self) {
        FORCE_HARD_TIMEOUT.with(|flag| flag.set(false));
    }
}

#[cfg(test)]
fn force_hard_timeout_enabled() -> bool {
    FORCE_HARD_TIMEOUT.with(std::cell::Cell::get)
}

#[cfg(test)]
fn live_hard_timeout_worker_count_for_test() -> usize {
    LIVE_HARD_TIMEOUT_WORKERS.load(Ordering::SeqCst)
}

#[cfg(test)]
fn wait_for_live_hard_timeout_worker_count_for_test(expected: usize, wait_budget: Duration) {
    let start = Instant::now();
    loop {
        let live_workers = live_hard_timeout_worker_count_for_test();
        if live_workers == expected {
            return;
        }
        assert!(
            start.elapsed() < wait_budget,
            "expected {expected} live hard-timeout workers, found {live_workers} after {:?}",
            wait_budget
        );
        let remaining = wait_budget.saturating_sub(start.elapsed());
        std::thread::sleep(Duration::from_millis(10).min(remaining));
    }
}

#[cfg(test)]
fn isolated_hard_timeout_limiter_for_test() -> HardTimeoutTestSerialGuard {
    let guard = hard_timeout_test_serial_guard_for_test();
    wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));
    guard
}

#[cfg(test)]
pub(super) fn with_saturated_hard_timeout_slots_for_test<T>(f: impl FnOnce() -> T) -> T {
    let _serial = hard_timeout_test_serial_guard_for_test();
    wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));

    let max_workers = max_hard_timeout_workers();
    let guards: Vec<_> = (0..max_workers)
        .map(|_| {
            reserve_hard_timeout_worker_slot(Duration::ZERO)
                .expect("slot reservation should succeed when filling limiter")
        })
        .collect();

    let result = f();
    drop(guards);
    wait_for_live_hard_timeout_worker_count_for_test(0, Duration::from_secs(1));
    result
}

#[cfg(test)]
mod tests;
