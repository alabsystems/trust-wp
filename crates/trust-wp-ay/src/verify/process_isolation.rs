// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Process isolation for verifier entrypoints.
//!
//! The hard-timeout path can abandon a non-interruptible solver worker thread.
//! Running the verifier body in a short-lived child process lets the parent keep
//! the structured outcome while the child process exit tears down any abandoned
//! solver workers.

use std::{cell::Cell, time::Duration};
#[cfg(unix)]
use std::{
    io,
    os::fd::RawFd,
    panic::{self, AssertUnwindSafe},
    time::Instant,
};

#[cfg(unix)]
use super::process_wire::{WireChildMessage, WireLoopChildMessage};
use super::{LoopVerificationOutcome, UnknownReason, VerificationOutcome, VerificationResult};
use crate::error::EncodingError;

const FRAME_PREFIX_BYTES: usize = 8;
const CHILD_POLL_INTERVAL: Duration = Duration::from_millis(10);
#[cfg(unix)]
const PARENT_LIVENESS_POLL_INTERVAL: Duration = Duration::from_millis(25);
const DEFAULT_PROCESS_WATCHDOG_GRACE: Duration = Duration::from_secs(5);
const DEFAULT_PROCESS_WATCHDOG_MULTIPLIER: u32 = 4;
const DEFAULT_VERIFIER_STACK_BYTES: usize = 64 * 1024 * 1024;
const MIN_VERIFIER_STACK_BYTES: usize = 4 * 1024 * 1024;

thread_local! {
    static IN_ISOLATED_CHILD: Cell<bool> = const { Cell::new(false) };
}

/// Run a verifier outcome closure in a forked child process when enabled.
///
/// Process isolation is enabled by default, including in test builds, so a
/// timed-out hard-timeout worker cannot remain alive in the parent test
/// process and poison later checks. Set `TRUST_WP_PROCESS_ISOLATION=0` to force
/// inline execution. Set `TRUST_WP_PROCESS_ISOLATION_WATCHDOG_MS=0` to disable
/// the parent watchdog. Set `TRUST_WP_VERIFIER_STACK_BYTES` to override the
/// verifier stack budget.
pub(crate) fn run_outcome_in_child<F>(
    request_timeout: Option<Duration>,
    f: F,
) -> Result<VerificationOutcome, EncodingError>
where
    F: FnOnce() -> Result<VerificationOutcome, EncodingError>,
{
    run_outcome_in_child_with_policy(process_isolation_enabled(), request_timeout, f)
}

fn run_outcome_in_child_with_policy<F>(
    isolation_enabled: bool,
    request_timeout: Option<Duration>,
    f: F,
) -> Result<VerificationOutcome, EncodingError>
where
    F: FnOnce() -> Result<VerificationOutcome, EncodingError>,
{
    if !isolation_enabled || in_isolated_child() {
        return run_with_verifier_stack(f);
    }

    #[cfg(unix)]
    return run_outcome_in_child_unix(request_timeout, f);
    // Windows has no fork(2), so the copy-the-address-space child that carries
    // the in-memory verification context cannot exist there. Run inline on the
    // dedicated verifier stack — exactly the supported
    // `TRUST_WP_PROCESS_ISOLATION=0` opt-out path. Outcomes are identical; the
    // only loss is the child-exit teardown of abandoned hard-timeout workers.
    #[cfg(not(unix))]
    {
        let _ = request_timeout;
        run_with_verifier_stack(f)
    }
}

/// Run a loop verifier outcome closure in a forked child process when enabled.
pub(crate) fn run_loop_outcome_in_child<F>(
    request_timeout: Option<Duration>,
    f: F,
) -> Result<LoopVerificationOutcome, EncodingError>
where
    F: FnOnce() -> Result<LoopVerificationOutcome, EncodingError>,
{
    if !process_isolation_enabled() || in_isolated_child() {
        return run_with_verifier_stack(f);
    }

    #[cfg(unix)]
    return run_loop_outcome_in_child_unix(request_timeout, f);
    // See run_outcome_in_child: no fork(2) on Windows, so run inline like the
    // `TRUST_WP_PROCESS_ISOLATION=0` opt-out.
    #[cfg(not(unix))]
    {
        let _ = request_timeout;
        run_with_verifier_stack(f)
    }
}

fn process_isolation_enabled() -> bool {
    let raw = std::env::var("TRUST_WP_PROCESS_ISOLATION").ok();
    process_isolation_enabled_from_env(raw.as_deref(), cfg!(test))
}

fn process_isolation_enabled_from_env(raw: Option<&str>, _test_build: bool) -> bool {
    match raw {
        Some("0" | "false" | "FALSE" | "off" | "OFF") => false,
        Some("1" | "true" | "TRUE" | "on" | "ON") => true,
        _ => true,
    }
}

#[cfg(test)]
fn process_isolation_enabled_from_test_env(raw: Option<&str>) -> bool {
    process_isolation_enabled_from_env(raw, true)
}

#[cfg(test)]
fn process_isolation_enabled_from_production_env(raw: Option<&str>) -> bool {
    process_isolation_enabled_from_env(raw, false)
}

fn in_isolated_child() -> bool {
    IN_ISOLATED_CHILD.with(Cell::get)
}

fn run_with_verifier_stack<R, F>(f: F) -> R
where
    F: FnOnce() -> R,
{
    stacker::grow(verifier_stack_bytes(), f)
}

fn verifier_stack_bytes() -> usize {
    std::env::var("TRUST_WP_VERIFIER_STACK_BYTES")
        .ok()
        .and_then(|raw| raw.parse::<usize>().ok())
        .filter(|bytes| *bytes >= MIN_VERIFIER_STACK_BYTES)
        .unwrap_or(DEFAULT_VERIFIER_STACK_BYTES)
}

#[cfg(unix)]
fn run_outcome_in_child_unix<F>(
    request_timeout: Option<Duration>,
    f: F,
) -> Result<VerificationOutcome, EncodingError>
where
    F: FnOnce() -> Result<VerificationOutcome, EncodingError>,
{
    let mut verifier = Some(f);
    let mut fds = [0; 2];
    if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
        return Err(solver_error(format!(
            "failed to create process-isolation pipe: {}",
            io::Error::last_os_error()
        )));
    }
    let read_fd = fds[0];
    let write_fd = fds[1];
    if let Err(error) = set_nonblocking(read_fd) {
        close_fd(read_fd);
        close_fd(write_fd);
        return Err(solver_error(format!(
            "failed to configure process-isolation pipe: {error}"
        )));
    }

    let parent_pid = unsafe { libc::getpid() };
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        close_fd(read_fd);
        close_fd(write_fd);
        return Err(solver_error(format!(
            "failed to fork process-isolated verifier: {}",
            io::Error::last_os_error()
        )));
    }

    if pid == 0 {
        let child_verifier = verifier
            .take()
            .expect("process-isolation child verifier closure already consumed");
        run_child(write_fd, read_fd, parent_pid, child_verifier);
    }

    close_fd(write_fd);
    let parent_result = read_child_message(pid, read_fd, process_watchdog(request_timeout));
    close_fd(read_fd);
    match parent_result {
        Err(error) if should_retry_inline_after_child_error(&error) => {
            tracing::warn!(
                "process-isolated verifier child trapped before producing an outcome; retrying inline"
            );
            verifier
                .take()
                .expect("process-isolation parent verifier closure already consumed")()
        }
        result => result,
    }
}

#[cfg(unix)]
fn should_retry_inline_after_child_error(error: &EncodingError) -> bool {
    matches!(
        error,
        EncodingError::SolverError { message, .. }
            if message.contains("process-isolated verifier exited without an outcome: signal 5")
    )
}

#[cfg(unix)]
fn run_loop_outcome_in_child_unix<F>(
    request_timeout: Option<Duration>,
    f: F,
) -> Result<LoopVerificationOutcome, EncodingError>
where
    F: FnOnce() -> Result<LoopVerificationOutcome, EncodingError>,
{
    let mut fds = [0; 2];
    if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
        return Err(solver_error(format!(
            "failed to create process-isolation pipe: {}",
            io::Error::last_os_error()
        )));
    }
    let read_fd = fds[0];
    let write_fd = fds[1];
    if let Err(error) = set_nonblocking(read_fd) {
        close_fd(read_fd);
        close_fd(write_fd);
        return Err(solver_error(format!(
            "failed to configure process-isolation pipe: {error}"
        )));
    }

    let parent_pid = unsafe { libc::getpid() };
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        close_fd(read_fd);
        close_fd(write_fd);
        return Err(solver_error(format!(
            "failed to fork process-isolated verifier: {}",
            io::Error::last_os_error()
        )));
    }

    if pid == 0 {
        run_loop_child(write_fd, read_fd, parent_pid, f);
    }

    close_fd(write_fd);
    let parent_result = read_loop_child_message(pid, read_fd, process_watchdog(request_timeout));
    close_fd(read_fd);
    parent_result
}

#[cfg(unix)]
fn run_child<F>(write_fd: RawFd, read_fd: RawFd, parent_pid: libc::pid_t, f: F) -> !
where
    F: FnOnce() -> Result<VerificationOutcome, EncodingError>,
{
    IN_ISOLATED_CHILD.with(|flag| flag.set(true));
    close_fd(read_fd);
    establish_isolated_process_group();
    install_parent_liveness_watchdog(parent_pid);
    super::hard_timeout::reset_after_process_isolation_fork();

    let baseline = crate::encoder::unsoundness::snapshot();
    let message = match panic::catch_unwind(AssertUnwindSafe(|| run_with_verifier_stack(f))) {
        Ok(result) => WireChildMessage::from_result(result, &baseline),
        Err(payload) => WireChildMessage::from_panic(panic_payload_to_string(payload), &baseline),
    };

    let exit_code = match write_child_message(write_fd, &message) {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("trust-wp process isolation child write failed: {error}");
            2
        }
    };
    close_fd(write_fd);
    unsafe { libc::_exit(exit_code) }
}

#[cfg(unix)]
fn run_loop_child<F>(write_fd: RawFd, read_fd: RawFd, parent_pid: libc::pid_t, f: F) -> !
where
    F: FnOnce() -> Result<LoopVerificationOutcome, EncodingError>,
{
    IN_ISOLATED_CHILD.with(|flag| flag.set(true));
    close_fd(read_fd);
    establish_isolated_process_group();
    install_parent_liveness_watchdog(parent_pid);
    super::hard_timeout::reset_after_process_isolation_fork();

    let baseline = crate::encoder::unsoundness::snapshot();
    let message = match panic::catch_unwind(AssertUnwindSafe(|| run_with_verifier_stack(f))) {
        Ok(result) => WireLoopChildMessage::from_result(result, &baseline),
        Err(payload) => {
            WireLoopChildMessage::from_panic(panic_payload_to_string(payload), &baseline)
        }
    };

    let exit_code = match write_loop_child_message(write_fd, &message) {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("trust-wp process isolation child write failed: {error}");
            2
        }
    };
    close_fd(write_fd);
    unsafe { libc::_exit(exit_code) }
}

#[cfg(unix)]
fn read_child_message(
    pid: libc::pid_t,
    read_fd: RawFd,
    watchdog: Option<Duration>,
) -> Result<VerificationOutcome, EncodingError> {
    let start = Instant::now();
    let mut bytes = Vec::new();
    let mut child_done = false;
    let mut child_status = 0;
    let mut saw_eof = false;

    loop {
        saw_eof |= read_available(read_fd, &mut bytes)?;

        if !child_done {
            let mut status = 0;
            let wait_result = unsafe { libc::waitpid(pid, &raw mut status, libc::WNOHANG) };
            if wait_result == pid {
                child_done = true;
                child_status = status;
            } else if wait_result < 0 {
                return Err(solver_error(format!(
                    "process-isolated verifier waitpid failed: {}",
                    io::Error::last_os_error()
                )));
            }
        }

        if child_done && saw_eof {
            break;
        }

        if let Some(limit) = watchdog {
            if start.elapsed() >= limit {
                kill_child_process_group(pid);
                let mut status = 0;
                unsafe {
                    libc::waitpid(pid, &raw mut status, 0);
                }
                tracing::warn!(
                    ?limit,
                    "process-isolated verifier watchdog expired; killed child"
                );
                return Ok(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(UnknownReason::Timeout),
                ));
            }
        }

        std::thread::sleep(CHILD_POLL_INTERVAL);
    }

    if bytes.is_empty() {
        return Err(solver_error(format!(
            "process-isolated verifier exited without an outcome: {}",
            format_wait_status(child_status)
        )));
    }

    decode_child_message(&bytes)
}

#[cfg(unix)]
fn read_loop_child_message(
    pid: libc::pid_t,
    read_fd: RawFd,
    watchdog: Option<Duration>,
) -> Result<LoopVerificationOutcome, EncodingError> {
    let start = Instant::now();
    let mut bytes = Vec::new();
    let mut child_done = false;
    let mut child_status = 0;
    let mut saw_eof = false;

    loop {
        saw_eof |= read_available(read_fd, &mut bytes)?;

        if !child_done {
            let mut status = 0;
            let wait_result = unsafe { libc::waitpid(pid, &raw mut status, libc::WNOHANG) };
            if wait_result == pid {
                child_done = true;
                child_status = status;
            } else if wait_result < 0 {
                return Err(solver_error(format!(
                    "process-isolated loop verifier waitpid failed: {}",
                    io::Error::last_os_error()
                )));
            }
        }

        if child_done && saw_eof {
            break;
        }

        if let Some(limit) = watchdog {
            if start.elapsed() >= limit {
                kill_child_process_group(pid);
                let mut status = 0;
                unsafe {
                    libc::waitpid(pid, &raw mut status, 0);
                }
                tracing::warn!(
                    ?limit,
                    "process-isolated loop verifier watchdog expired; killed child"
                );
                return Ok(timeout_loop_outcome());
            }
        }

        std::thread::sleep(CHILD_POLL_INTERVAL);
    }

    if bytes.is_empty() {
        return Err(solver_error(format!(
            "process-isolated loop verifier exited without an outcome: {}",
            format_wait_status(child_status)
        )));
    }

    decode_loop_child_message(&bytes)
}

#[cfg(unix)]
fn decode_child_message(bytes: &[u8]) -> Result<VerificationOutcome, EncodingError> {
    if bytes.len() < FRAME_PREFIX_BYTES {
        return Err(solver_error(format!(
            "process-isolated verifier frame too short: {} bytes",
            bytes.len()
        )));
    }
    let mut len_bytes = [0u8; FRAME_PREFIX_BYTES];
    len_bytes.copy_from_slice(&bytes[..FRAME_PREFIX_BYTES]);
    let expected_len = u64::from_be_bytes(len_bytes) as usize;
    let payload = &bytes[FRAME_PREFIX_BYTES..];
    if payload.len() != expected_len {
        return Err(solver_error(format!(
            "process-isolated verifier frame length mismatch: expected {expected_len}, got {}",
            payload.len()
        )));
    }

    let message: WireChildMessage = serde_json::from_slice(payload).map_err(|error| {
        solver_error(format!(
            "failed to decode process-isolated verifier outcome: {error}"
        ))
    })?;
    if matches!(
        message,
        WireChildMessage::Outcome { .. } | WireChildMessage::Error { .. }
    ) {
        apply_child_unsoundness_delta(message.delta(), "process-isolated unsoundness counters")?;
    }

    match message {
        WireChildMessage::Outcome { outcome, .. } => outcome.into_outcome().map_err(|error| {
            solver_error(format!(
                "failed to convert process-isolated verifier outcome: {error}"
            ))
        }),
        WireChildMessage::Error { error, .. } => Err(error.into_error().map_err(|error| {
            solver_error(format!(
                "failed to convert process-isolated verifier error: {error}"
            ))
        })?),
        WireChildMessage::Panic { message, .. } => {
            if super::panic_boundary::is_ay_panic(&message) {
                Ok(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(UnknownReason::SolverPanic(message)),
                ))
            } else {
                panic::panic_any(message);
            }
        }
    }
}

#[cfg(unix)]
fn decode_loop_child_message(bytes: &[u8]) -> Result<LoopVerificationOutcome, EncodingError> {
    if bytes.len() < FRAME_PREFIX_BYTES {
        return Err(solver_error(format!(
            "process-isolated loop verifier frame too short: {} bytes",
            bytes.len()
        )));
    }
    let mut len_bytes = [0u8; FRAME_PREFIX_BYTES];
    len_bytes.copy_from_slice(&bytes[..FRAME_PREFIX_BYTES]);
    let expected_len = u64::from_be_bytes(len_bytes) as usize;
    let payload = &bytes[FRAME_PREFIX_BYTES..];
    if payload.len() != expected_len {
        return Err(solver_error(format!(
            "process-isolated loop verifier frame length mismatch: expected {expected_len}, got {}",
            payload.len()
        )));
    }

    let message: WireLoopChildMessage = serde_json::from_slice(payload).map_err(|error| {
        solver_error(format!(
            "failed to decode process-isolated loop verifier outcome: {error}"
        ))
    })?;
    if matches!(
        message,
        WireLoopChildMessage::Outcome { .. } | WireLoopChildMessage::Error { .. }
    ) {
        apply_child_unsoundness_delta(
            message.delta(),
            "process-isolated loop unsoundness counters",
        )?;
    }

    match message {
        WireLoopChildMessage::Outcome { outcome, .. } => outcome.into_outcome().map_err(|error| {
            solver_error(format!(
                "failed to convert process-isolated loop verifier outcome: {error}"
            ))
        }),
        WireLoopChildMessage::Error { error, .. } => Err(error.into_error().map_err(|error| {
            solver_error(format!(
                "failed to convert process-isolated loop verifier error: {error}"
            ))
        })?),
        WireLoopChildMessage::Panic { message, .. } => {
            if super::panic_boundary::is_ay_panic(&message) {
                Ok(loop_panic_outcome(message))
            } else {
                panic::panic_any(message);
            }
        }
    }
}

#[cfg(unix)]
fn apply_child_unsoundness_delta(
    delta: Result<crate::encoder::unsoundness::Snapshot, String>,
    context: &str,
) -> Result<(), EncodingError> {
    let delta =
        delta.map_err(|error| solver_error(format!("failed to decode {context}: {error}")))?;
    crate::encoder::unsoundness::apply_delta(&delta);
    Ok(())
}

#[cfg(unix)]
fn write_child_message(fd: RawFd, message: &WireChildMessage) -> io::Result<()> {
    let payload = serde_json::to_vec(message).map_err(io::Error::other)?;
    let len = u64::try_from(payload.len())
        .map_err(|_| io::Error::other("process-isolation payload too large"))?;
    write_all_fd(fd, &len.to_be_bytes())?;
    write_all_fd(fd, &payload)
}

#[cfg(unix)]
fn write_loop_child_message(fd: RawFd, message: &WireLoopChildMessage) -> io::Result<()> {
    let payload = serde_json::to_vec(message).map_err(io::Error::other)?;
    let len = u64::try_from(payload.len())
        .map_err(|_| io::Error::other("process-isolation payload too large"))?;
    write_all_fd(fd, &len.to_be_bytes())?;
    write_all_fd(fd, &payload)
}

fn timeout_loop_outcome() -> LoopVerificationOutcome {
    let timeout = VerificationOutcome::without_provenance(VerificationResult::Unknown(
        UnknownReason::Timeout,
    ));
    LoopVerificationOutcome {
        initialization: timeout.clone(),
        preservation: timeout.clone(),
        postcondition: timeout,
        variant_nonneg: None,
        variant_decrease: None,
        entry_may_execute: None,
    }
}

fn loop_panic_outcome(message: String) -> LoopVerificationOutcome {
    let panic = VerificationOutcome::without_provenance(VerificationResult::Unknown(
        UnknownReason::SolverPanic(message),
    ));
    LoopVerificationOutcome {
        initialization: panic.clone(),
        preservation: panic.clone(),
        postcondition: panic,
        variant_nonneg: None,
        variant_decrease: None,
        entry_may_execute: None,
    }
}

#[cfg(unix)]
fn write_all_fd(fd: RawFd, mut bytes: &[u8]) -> io::Result<()> {
    while !bytes.is_empty() {
        let written = unsafe { libc::write(fd, bytes.as_ptr().cast(), bytes.len()) };
        if written < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        if written == 0 {
            return Err(io::Error::new(
                io::ErrorKind::WriteZero,
                "process-isolation pipe write returned zero",
            ));
        }
        bytes = &bytes[usize::try_from(written).unwrap_or(0)..];
    }
    Ok(())
}

#[cfg(unix)]
fn read_available(fd: RawFd, out: &mut Vec<u8>) -> Result<bool, EncodingError> {
    let mut buf = [0u8; 16 * 1024];
    loop {
        let read = unsafe { libc::read(fd, buf.as_mut_ptr().cast(), buf.len()) };
        if read > 0 {
            let read = usize::try_from(read).unwrap_or(0);
            out.extend_from_slice(&buf[..read]);
            continue;
        }
        if read == 0 {
            return Ok(true);
        }
        let error = io::Error::last_os_error();
        match error.kind() {
            io::ErrorKind::Interrupted => continue,
            io::ErrorKind::WouldBlock => return Ok(false),
            _ => {
                return Err(solver_error(format!(
                    "failed to read process-isolated verifier outcome: {error}"
                )));
            }
        }
    }
}

#[cfg(unix)]
fn set_nonblocking(fd: RawFd) -> io::Result<()> {
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

#[cfg(unix)]
fn close_fd(fd: RawFd) {
    unsafe {
        libc::close(fd);
    }
}

#[cfg(unix)]
fn kill_child_process_group(pid: libc::pid_t) {
    let killed_group = unsafe { libc::killpg(pid, libc::SIGKILL) == 0 };
    if !killed_group {
        unsafe {
            libc::kill(pid, libc::SIGKILL);
        }
    }
}

#[cfg(unix)]
fn establish_isolated_process_group() {
    let pid = unsafe { libc::getpid() };
    let established = unsafe { libc::setpgid(0, 0) == 0 || libc::getpgrp() == pid };
    if !established {
        eprintln!(
            "trust-wp could not establish isolated process group: {}",
            io::Error::last_os_error()
        );
        unsafe { libc::_exit(3) }
    }
}

/// Ensure an externally terminated caller cannot strand its isolated verifier.
///
/// The normal parent path owns the process-group watchdog and reaps `pid`.
/// Test runners and build orchestration can themselves be killed, however. In
/// that case this child is reparented while it may still be inside a
/// non-interruptible solver phase. Because the child deliberately moved into
/// its own process group, a shell-level kill of the former parent would not
/// reach it. Keep one tiny in-child watcher which kills the whole isolated
/// process group as soon as the original parent disappears.
#[cfg(unix)]
fn install_parent_liveness_watchdog(parent_pid: libc::pid_t) {
    if let Err(error) = std::thread::Builder::new()
        .name("trust-wp-parent-liveness".to_string())
        .spawn(move || loop {
            if unsafe { libc::getppid() } != parent_pid {
                unsafe {
                    // The isolated child called `setpgid(0, 0)` before this
                    // watcher was installed, so group 0 is exactly this
                    // verifier and any descendants it created.
                    libc::kill(0, libc::SIGKILL);
                    libc::_exit(128 + libc::SIGKILL);
                }
            }
            std::thread::sleep(PARENT_LIVENESS_POLL_INTERVAL);
        })
    {
        eprintln!("trust-wp could not install parent-liveness watchdog: {error}");
        unsafe { libc::_exit(3) }
    }
}

#[cfg(unix)]
fn process_watchdog(request_timeout: Option<Duration>) -> Option<Duration> {
    if let Ok(raw) = std::env::var("TRUST_WP_PROCESS_ISOLATION_WATCHDOG_MS") {
        if let Ok(ms) = raw.parse::<u64>() {
            return (ms > 0).then(|| Duration::from_millis(ms));
        }
    }

    let base = request_timeout.unwrap_or(Duration::from_mins(1));
    base.checked_mul(DEFAULT_PROCESS_WATCHDOG_MULTIPLIER)
        .and_then(|value| value.checked_add(DEFAULT_PROCESS_WATCHDOG_GRACE))
        .or(Some(DEFAULT_PROCESS_WATCHDOG_GRACE))
}

#[cfg(unix)]
fn panic_payload_to_string(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else if let Some(message) = payload.downcast_ref::<&'static str>() {
        (*message).to_string()
    } else {
        "non-string panic payload".to_string()
    }
}

#[cfg(unix)]
fn format_wait_status(status: i32) -> String {
    if libc::WIFEXITED(status) {
        format!("exit status {}", libc::WEXITSTATUS(status))
    } else if libc::WIFSIGNALED(status) {
        format!("signal {}", libc::WTERMSIG(status))
    } else {
        format!("raw status {status}")
    }
}

fn solver_error(message: String) -> EncodingError {
    EncodingError::SolverError {
        message,
        span: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // Only the fork/child unsoundness-delta tests below touch these, and those
    // are `#[cfg(unix)]`; without the gate Windows builds warn on the unused
    // import.
    #[cfg(unix)]
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    #[cfg(unix)]
    #[test]
    fn process_isolated_child_returns_timeout_outcome() {
        let outcome = run_outcome_in_child_unix(Some(Duration::from_millis(50)), || {
            Ok(VerificationOutcome::without_provenance(
                VerificationResult::Unknown(UnknownReason::Timeout),
            ))
        })
        .expect("child outcome");

        assert!(matches!(
            outcome.result,
            VerificationResult::Unknown(UnknownReason::Timeout)
        ));
    }

    #[cfg(unix)]
    #[test]
    fn process_isolated_child_exit_does_not_wait_for_detached_thread() {
        let start = Instant::now();
        let outcome = run_outcome_in_child_unix(Some(Duration::from_millis(50)), || {
            std::thread::spawn(|| std::thread::sleep(Duration::from_secs(30)));
            Ok(VerificationOutcome::without_provenance(
                VerificationResult::Unknown(UnknownReason::Timeout),
            ))
        })
        .expect("child outcome");

        assert!(
            start.elapsed() < Duration::from_secs(2),
            "child process should exit without waiting for detached worker thread"
        );
        assert!(matches!(
            outcome.result,
            VerificationResult::Unknown(UnknownReason::Timeout)
        ));
    }

    #[cfg(unix)]
    #[test]
    fn process_isolated_child_dies_when_its_parent_is_killed() {
        let mut fds = [0; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
        let read_fd = fds[0];
        let write_fd = fds[1];

        let middle = unsafe { libc::fork() };
        assert!(middle >= 0, "forking the simulated caller must succeed");
        if middle == 0 {
            close_fd(read_fd);
            let _ = run_outcome_in_child_unix(Some(Duration::from_secs(30)), || {
                let child_pid = unsafe { libc::getpid() };
                write_all_fd(write_fd, &child_pid.to_ne_bytes())
                    .expect("reporting isolated child pid");
                std::thread::sleep(Duration::from_secs(30));
                Ok(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(UnknownReason::Timeout),
                ))
            });
            close_fd(write_fd);
            unsafe { libc::_exit(0) }
        }

        close_fd(write_fd);
        set_nonblocking(read_fd).expect("configure pid-report pipe");
        let start = Instant::now();
        let mut bytes = Vec::new();
        while bytes.len() < std::mem::size_of::<libc::pid_t>()
            && start.elapsed() < Duration::from_secs(2)
        {
            read_available(read_fd, &mut bytes).expect("read isolated child pid");
            std::thread::sleep(Duration::from_millis(10));
        }
        close_fd(read_fd);
        assert_eq!(
            bytes.len(),
            std::mem::size_of::<libc::pid_t>(),
            "isolated child must report its pid before caller termination"
        );
        let child_pid = libc::pid_t::from_ne_bytes(
            bytes
                .as_slice()
                .try_into()
                .expect("pid report has the exact native width"),
        );

        unsafe {
            libc::kill(middle, libc::SIGKILL);
            libc::waitpid(middle, std::ptr::null_mut(), 0);
        }

        let deadline = Instant::now() + Duration::from_secs(2);
        let mut child_gone = false;
        while Instant::now() < deadline {
            let exists = unsafe { libc::kill(child_pid, 0) == 0 };
            if !exists && io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH) {
                child_gone = true;
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        if !child_gone {
            // Cleanup before failing so the regression itself can never leave
            // the orphan it is designed to detect.
            kill_child_process_group(child_pid);
        }
        assert!(
            child_gone,
            "isolated verifier {child_pid} survived termination of caller {middle}"
        );
    }

    #[test]
    fn process_isolation_env_policy_defaults_enabled_in_unit_tests() {
        assert!(process_isolation_enabled_from_test_env(None));
        assert!(!process_isolation_enabled_from_test_env(Some("0")));
        assert!(process_isolation_enabled_from_test_env(Some("1")));
        assert!(process_isolation_enabled_from_production_env(None));
        assert!(!process_isolation_enabled_from_production_env(Some("off")));
        assert!(process_isolation_enabled_from_production_env(Some("on")));
    }

    #[test]
    fn process_isolation_disabled_policy_runs_inline_in_unit_tests() {
        let parent_side_effect = Cell::new(false);
        let outcome =
            run_outcome_in_child_with_policy(false, Some(Duration::from_millis(50)), || {
                parent_side_effect.set(true);
                Ok(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(UnknownReason::Timeout),
                ))
            })
            .expect("inline outcome");

        assert!(
            parent_side_effect.get(),
            "disabled process isolation should force inline verifier execution"
        );
        assert!(matches!(
            outcome.result,
            VerificationResult::Unknown(UnknownReason::Timeout)
        ));
    }

    #[cfg(unix)]
    #[test]
    fn process_isolation_default_path_runs_in_child_in_unit_tests() {
        let parent_side_effect = Cell::new(false);
        let outcome =
            run_outcome_in_child_with_policy(true, Some(Duration::from_millis(50)), || {
                parent_side_effect.set(true);
                Ok(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(UnknownReason::Timeout),
                ))
            })
            .expect("child outcome");

        assert!(
            !parent_side_effect.get(),
            "test builds should default to child-process verifier execution"
        );
        assert!(matches!(
            outcome.result,
            VerificationResult::Unknown(UnknownReason::Timeout)
        ));
    }

    #[cfg(unix)]
    #[test]
    fn process_isolation_default_path_does_not_wait_for_detached_worker_in_unit_tests() {
        let start = Instant::now();
        let outcome =
            run_outcome_in_child_with_policy(true, Some(Duration::from_millis(50)), || {
                std::thread::spawn(|| std::thread::sleep(Duration::from_secs(30)));
                Ok(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(UnknownReason::Timeout),
                ))
            })
            .expect("child outcome");

        assert!(
            start.elapsed() < Duration::from_secs(2),
            "default test-build process isolation should not wait for detached child workers"
        );
        assert!(matches!(
            outcome.result,
            VerificationResult::Unknown(UnknownReason::Timeout)
        ));
    }

    /// Windows twin of the default-path tests above: with no fork(2), the
    /// default path must run the verifier inline (the
    /// `TRUST_WP_PROCESS_ISOLATION=0` behavior) rather than pretending to
    /// isolate.
    #[cfg(not(unix))]
    #[test]
    fn process_isolation_default_path_runs_inline_without_fork() {
        let parent_side_effect = Cell::new(false);
        let outcome =
            run_outcome_in_child_with_policy(true, Some(Duration::from_millis(50)), || {
                parent_side_effect.set(true);
                Ok(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(UnknownReason::Timeout),
                ))
            })
            .expect("inline outcome");

        assert!(
            parent_side_effect.get(),
            "without fork(2) the default path must run the verifier inline"
        );
        assert!(matches!(
            outcome.result,
            VerificationResult::Unknown(UnknownReason::Timeout)
        ));
    }

    #[cfg(unix)]
    #[test]
    fn process_isolated_child_ay_panic_returns_solver_panic_unknown_without_unsoundness_delta() {
        unsoundness::reset();
        let outcome = run_outcome_in_child_unix(Some(Duration::from_secs(1)), || {
            unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);
            panic!("BUG: mk_eq sort mismatch");
        })
        .expect("child outcome");

        match outcome.result {
            VerificationResult::Unknown(UnknownReason::SolverPanic(message)) => {
                assert_eq!(message, "BUG: mk_eq sort mismatch");
            }
            result => panic!("ay child panic should become SolverPanic Unknown: {result:?}"),
        }

        assert!(
            unsoundness::snapshot().is_empty(),
            "panic messages must not apply child unsoundness deltas"
        );
    }

    #[cfg(unix)]
    #[test]
    fn process_isolated_child_non_ay_panic_repanics_in_parent() {
        let panic_result = panic::catch_unwind(|| {
            let _ = run_outcome_in_child_unix(Some(Duration::from_secs(1)), || {
                panic!("called `Option::unwrap()` on a `None` value");
            });
        });

        let payload = panic_result.expect_err("non-ay child panic should re-panic in parent");
        let message = panic_payload_to_string(payload);
        assert_eq!(message, "called `Option::unwrap()` on a `None` value");
    }

    #[cfg(unix)]
    #[test]
    fn process_isolated_child_resets_inherited_hard_timeout_slots() {
        let outcome =
            super::super::hard_timeout::with_saturated_hard_timeout_slots_for_test(|| {
                run_outcome_in_child_unix(Some(Duration::from_secs(1)), || {
                    let mut encoder = crate::encoder::AYEncoder::new();
                    encoder.set_timeout(Some(Duration::from_secs(1)));

                    let result = match super::super::hard_timeout::run_with_hard_timeout(
                        &mut encoder,
                        |_| VerificationResult::Verified(None),
                    ) {
                        super::super::hard_timeout::ResolveContinuation::Continue(result)
                        | super::super::hard_timeout::ResolveContinuation::Abort(result) => result,
                    };

                    Ok(VerificationOutcome::without_provenance(result))
                })
            })
            .expect("child outcome");

        assert!(
            matches!(outcome.result, VerificationResult::Verified(None)),
            "child should not inherit saturated parent hard-timeout slots: {outcome:?}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn process_isolation_enabled_path_resets_inherited_hard_timeout_slots() {
        let outcome =
            super::super::hard_timeout::with_saturated_hard_timeout_slots_for_test(|| {
                run_outcome_in_child_with_policy(true, Some(Duration::from_secs(1)), || {
                    let mut encoder = crate::encoder::AYEncoder::new();
                    encoder.set_timeout(Some(Duration::from_secs(1)));

                    let result = match super::super::hard_timeout::run_with_hard_timeout(
                        &mut encoder,
                        |_| VerificationResult::Verified(None),
                    ) {
                        super::super::hard_timeout::ResolveContinuation::Continue(result)
                        | super::super::hard_timeout::ResolveContinuation::Abort(result) => result,
                    };

                    Ok(VerificationOutcome::without_provenance(result))
                })
            });

        let outcome = outcome.expect("child outcome");
        assert!(
            matches!(outcome.result, VerificationResult::Verified(None)),
            "enabled child should not inherit saturated parent hard-timeout slots: {outcome:?}"
        );
    }
}
