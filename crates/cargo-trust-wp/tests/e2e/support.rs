// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared harness helpers for cargo-trust-wp end-to-end tests.

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::{Arc, Mutex, OnceLock},
};

use tempfile::TempDir;
use trust_wp_test_utils::{
    copy_cargo_trust_wp_bin, copy_dir_all, copy_trust_wp_rustc_bin, fixture_dir,
    rewrite_trust_wp_path,
};

pub(crate) fn shared_target_dir() -> &'static PathBuf {
    static TARGET_DIR: OnceLock<PathBuf> = OnceLock::new();
    TARGET_DIR.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!(
            "trust-wp-cargo-trust-wp-e2e-target-{}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).expect("create shared target dir");
        dir
    })
}

pub(crate) fn cargo_trust_wp_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

/// Check if a directory contains a cargo wrapper script (as opposed to the real
/// cargo binary). The wrapper is a small shell script (~5KB) containing the
/// repository-local cargo wrapper identifier string.
pub(crate) fn is_cargo_wrapper_dir(dir: &std::path::Path) -> bool {
    let cargo_path = dir.join("cargo");
    // Real cargo is a >1MB Mach-O/ELF binary; the wrapper is a ~5KB shell script.
    // Check file size first (fast), then verify by reading the shebang line.
    let Ok(metadata) = cargo_path.metadata() else {
        return false;
    };
    if metadata.len() > 50_000 {
        return false; // Real binary, not a wrapper script.
    }
    // Small file — read the first line to confirm it's a shell script.
    let Ok(content) = fs::read_to_string(&cargo_path) else {
        return false;
    };
    content.contains("cargo wrapper") || content.contains("cargo_wrapper")
}

/// Build a PATH for E2E child processes with cargo wrapper directories removed.
///
/// Filters out the repository-local wrapper bin and any directory
/// containing a cargo wrapper script (e.g., `~/.local/bin`). Prepends `bin_dir`
/// so the test's own cargo-trust-wp and trust-wp-rustc binaries take priority.
/// (#572, #2085)
pub(crate) fn build_e2e_path(bin_dir: PathBuf) -> std::ffi::OsString {
    let mut path_entries = vec![bin_dir];
    if let Some(path) = std::env::var_os("PATH") {
        path_entries.extend(std::env::split_paths(&path).filter(|p| {
            let s = p.to_string_lossy();
            !is_repo_local_wrapper_bin_path(&s) && !is_cargo_wrapper_dir(p)
        }));
    }
    std::env::join_paths(path_entries).expect("join PATH")
}

fn is_repo_local_wrapper_bin_path(path: &str) -> bool {
    let wrapper_dir = ["ai", "_template_scripts", "/bin"].concat();
    path.contains(&wrapper_dir)
}

pub(crate) fn run_cargo_trust_wp(fixture: &str, filter: &str) -> Output {
    run_cargo_trust_wp_with_fixture_edit(fixture, filter, |_| {})
}

pub(crate) fn run_cargo_trust_wp_with_fixture_edit(
    fixture: &str,
    filter: &str,
    edit_fixture: impl FnOnce(&Path),
) -> Output {
    let _run_guard = cargo_trust_wp_lock()
        .lock()
        .expect("lock cargo-trust-wp e2e runner");

    let temp_dir = TempDir::new().expect("temp dir");
    let fixture_src = fixture_dir(fixture);
    let fixture_dst = temp_dir.path().join("fixture");
    copy_dir_all(&fixture_src, &fixture_dst).expect("copy fixture");
    rewrite_trust_wp_path(&fixture_dst).expect("rewrite trust-wp path");
    edit_fixture(&fixture_dst);

    let bin_dir = temp_dir.path().join("bin");
    fs::create_dir_all(&bin_dir).expect("bin dir");
    let cargo_trust_wp = copy_cargo_trust_wp_bin(&bin_dir).expect("copy cargo-trust-wp");
    copy_trust_wp_rustc_bin(&bin_dir).expect("copy trust-wp-rustc");

    let joined_path = build_e2e_path(bin_dir);

    let mut cmd = Command::new(cargo_trust_wp);
    cmd.arg("--verbose")
        .arg("--filter")
        .arg(filter)
        .arg("--offline")
        .current_dir(&fixture_dst)
        .env("PATH", joined_path)
        .env("CARGO_NET_OFFLINE", "true")
        // Reuse one target dir for the whole e2e suite to avoid recompiling
        // dependencies for each fixture temp directory.
        .env("CARGO_TARGET_DIR", shared_target_dir())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());

    // Place the child in its own process group so we can kill the entire tree
    // (cargo-trust-wp → cargo check → trust-wp-rustc) with a single signal.
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
    }

    let child = cmd.spawn().expect("spawn cargo-trust-wp");

    // Watchdog: kill the child process group after E2E_TIMEOUT_SECS.
    //
    // ntest's #[timeout] runs the test body on a *spawned* thread. When the
    // timeout fires, ntest panics the *original* thread but the spawned thread
    // (and its child processes) continue running. A Drop-based guard on the
    // spawned thread never fires because that thread is not panicked —
    // std::process::Child::drop is a no-op anyway.
    //
    // Instead, we record the child's PID (= PGID since we set process_group(0))
    // and spawn a watchdog that kills the entire group after a timeout. When the
    // child exits normally, we signal the watchdog to stop. (#583)
    const E2E_TIMEOUT_SECS: u64 = 120;
    let child_pid = child.id();
    let done = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let done_clone = done.clone();
    std::thread::spawn(move || {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(E2E_TIMEOUT_SECS);
        while std::time::Instant::now() < deadline {
            if done_clone.load(std::sync::atomic::Ordering::Acquire) {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis(500));
        }
        if !done_clone.load(std::sync::atomic::Ordering::Acquire) {
            // Kill the entire process group rooted at the child.
            // The negative PID argument to kill(1) targets the PGID, which
            // matches the child's PID because we set process_group(0) above.
            #[cfg(unix)]
            {
                let pgid = format!("-{child_pid}");
                let _ = std::process::Command::new("kill")
                    .args(["-9", &pgid])
                    .output();
            }
        }
    });

    let output = child.wait_with_output().expect("wait for cargo-trust-wp");
    done.store(true, std::sync::atomic::Ordering::Release);
    output
}

pub(crate) fn stderr_string(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

pub(crate) fn status_code(output: &Output) -> i32 {
    // None means the process was killed by a signal (e.g., SIGKILL from the
    // watchdog). Return -1 so tests that assert specific exit codes (1, 2, 3)
    // don't spuriously pass when the child was actually killed by timeout.
    output.status.code().unwrap_or(-1)
}

pub(crate) fn assert_function_status(stderr: &str, function: &str, status: &str) {
    // Use the full status marker with Unicode symbol for stronger matching:
    // "verified ✓" prevents false positives from summary lines like "0 verified, 0 failed".
    // "FAILED ✗" ensures we match the per-function failure line, not a substring.
    let marker = match status {
        "verified" => "verified ✓",
        "FAILED" => "FAILED ✗",
        other => other,
    };
    // Match any line starting with "trust-wp: " that contains the function name
    // (as a whole identifier, not a substring of a longer name) and the status
    // marker. This handles qualified paths like `<Type as Trait>::method` and
    // closure paths like `parent::{closure#0}` while preventing "count" from
    // matching inside "generic_count".
    let found = stderr.lines().any(|line| {
        if !line.starts_with("trust-wp: ") || !line.contains(marker) {
            return false;
        }
        // Find function name and check it's not a substring of a longer identifier.
        // The character after the match must be a non-identifier char (space, ':', etc.)
        // or the function must be at the end of a token.
        if let Some(pos) = line.find(function) {
            let after = pos + function.len();
            after >= line.len()
                || !line.as_bytes()[after].is_ascii_alphanumeric() && line.as_bytes()[after] != b'_'
        } else {
            false
        }
    });
    assert!(
        found,
        "no 'trust-wp:' line contains '{function}' (as whole identifier) and '{marker}' in output: {stderr}"
    );
}

pub(crate) fn assert_trusted_non_proof(output: &Output, function: &str) {
    let stderr = stderr_string(output);
    assert_eq!(
        status_code(output),
        2,
        "trusted functions are accepted as Rust code but are not clean proofs: {output:?}"
    );
    assert_function_status(&stderr, function, "trusted (skipped)");
}

pub(crate) fn assert_exact_trust_wp_line_count(
    stderr: &str,
    expected_line: &str,
    expected_count: usize,
) {
    let count = stderr.lines().filter(|line| *line == expected_line).count();
    assert_eq!(
        count, expected_count,
        "expected exact trust-wp line {expected_line:?} {expected_count} time(s), got {count}: {stderr}"
    );
}
