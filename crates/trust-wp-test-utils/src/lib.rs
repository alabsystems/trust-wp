// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub
)]

//! Shared test utilities for the trust-wp workspace.
//!
//! This crate provides common utilities for integration and end-to-end tests
//! across the trust-wp workspace, reducing duplication and ensuring consistency.
//!
//! # Usage
//!
//! Add to your crate's `[dev-dependencies]`:
//! ```toml
//! [dev-dependencies]
//! trust-wp-test-utils = { workspace = true }
//! ```
//!
//! Then use in tests:
//! ```rust
//! use trust_wp_test_utils::{cargo_trust_wp_bin, workspace_root};
//! let root = workspace_root();
//! assert!(root.exists());
//! ```

use std::{
    ffi::OsStr,
    fmt::Write as _,
    fs::{self, File},
    io::{self, Read as _},
    path::{Path, PathBuf},
    process::Command,
    time::UNIX_EPOCH,
};

use sha2::{Digest as _, Sha256};

mod freshness;

const TRYBUILD_CHILD_TEST_ENV: &str = "TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_CHILD";
const TRYBUILD_WRAPPER_ENV: &str = "TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_WRAPPER";
const TRYBUILD_TARGO_ENV: &str = "TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_TARGO";
const TRYBUILD_TARGO_SHA256_ENV: &str = "TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_TARGO_SHA256";
const TARGO_NESTED_UNVERIFIED_BROKER_ENV: &str = "TRUST_TARGO_NESTED_UNVERIFIED_BROKER";

const VERIFIED_TARGO_AUTHORITY_ENVS: &[&str] = &[
    "TRUST_TARGO_VERIFY",
    "TRUST_TARGO_TEST_EXECUTE_FRESH_SESSION",
    "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
    "TRUST_TARGO_TEST_MONITOR_SESSION",
];

/// Enters a trybuild test without relying on ambient nested-Targo authority.
///
/// On Linux, a live Targo broker already authenticates an outer command's
/// explicit `--unverified` decision, so the test runs normally. On platforms
/// without that broker, this function runs the current test once in a child
/// process whose `CARGO` is a private wrapper around an immutable snapshot of
/// the exact outer Targo executable. The wrapper spells `--unverified` on each
/// trybuild compilation command while leaving authority-neutral commands such
/// as `metadata` and `clean` unmodified; it does not inherit or synthesize a
/// proof claim.
///
/// This is deliberately an **unverified UI-test lane**. Its results must never
/// be cited as verified Targo, certified-monitor, release, or proof evidence.
/// A test reached from an authenticated verified session fails closed instead
/// of silently changing that session's authority.
///
/// Returns `true` when the caller should execute its trybuild body. Returns
/// `false` only in the parent after the isolated child has completed the body.
///
/// # Panics
///
/// Panics if branded Targo state is inconsistent, a verified authority marker
/// is present, the private harness cannot be authenticated, or the child test
/// fails.
pub fn enter_explicit_unverified_trybuild_test(test_name: &str) -> bool {
    assert!(
        !test_name.is_empty(),
        "trybuild test name must not be empty"
    );

    if let Some(selected_test) = std::env::var_os(TRYBUILD_CHILD_TEST_ENV) {
        assert_eq!(
            selected_test,
            OsStr::new(test_name),
            "explicit-unverified trybuild child selected a different test"
        );
        validate_explicit_unverified_trybuild_child()
            .expect("authenticate explicit-unverified trybuild child");
        return true;
    }

    let Some(outer_targo) =
        unbrokered_outer_targo().expect("identify the Cargo/Targo frontend for trybuild")
    else {
        return true;
    };

    let verified_markers: Vec<&str> = VERIFIED_TARGO_AUTHORITY_ENVS
        .iter()
        .copied()
        .filter(|name| std::env::var_os(name).is_some())
        .collect();
    assert!(
        verified_markers.is_empty(),
        "trybuild fixture compilation is an explicitly unverified UI-test lane and cannot run under verified Targo authority; present markers: {}",
        verified_markers.join(", ")
    );

    let harness = ExplicitUnverifiedTrybuildHarness::create(&outer_targo)
        .expect("create explicit-unverified trybuild harness");
    let current_test = std::env::current_exe().expect("locate current test executable");
    let status = Command::new(current_test)
        .args(["--exact", test_name, "--nocapture", "--test-threads=1"])
        .env("CARGO", &harness.wrapper)
        .env(TRYBUILD_CHILD_TEST_ENV, test_name)
        .env(TRYBUILD_WRAPPER_ENV, &harness.wrapper)
        .env(TRYBUILD_TARGO_ENV, &harness.targo)
        .env(TRYBUILD_TARGO_SHA256_ENV, &harness.targo_sha256)
        .env_remove(TARGO_NESTED_UNVERIFIED_BROKER_ENV)
        .status();
    harness.unlock_for_cleanup();
    let status = status.expect("launch explicit-unverified trybuild child");
    assert!(
        status.success(),
        "explicit-unverified trybuild child `{test_name}` failed with {status}"
    );
    false
}

fn unbrokered_outer_targo() -> Result<Option<PathBuf>, String> {
    let trust_frontend =
        std::env::var_os("TRUST_TARGO_FRONTEND").as_deref() == Some(OsStr::new("1"));
    let Some(cargo) = std::env::var_os("CARGO").map(PathBuf::from) else {
        if trust_frontend {
            return Err("TRUST_TARGO_FRONTEND=1 reached a test without an exact CARGO path".into());
        }
        return Ok(None);
    };

    let named_targo = executable_path_is_named(&cargo, "targo");
    if !named_targo {
        if trust_frontend {
            return Err(format!(
                "TRUST_TARGO_FRONTEND=1 supplied a non-Targo CARGO path: {}",
                cargo.display()
            ));
        }
        return Ok(None);
    }

    let metadata = fs::symlink_metadata(&cargo)
        .map_err(|error| format!("inspect outer Targo {}: {error}", cargo.display()))?;
    if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
        return Err(format!(
            "outer Targo CARGO path is not a plain regular file: {}",
            cargo.display()
        ));
    }
    ensure_targo_brand(&cargo)?;

    if std::env::var_os(TARGO_NESTED_UNVERIFIED_BROKER_ENV).is_some() {
        return Ok(None);
    }
    Ok(Some(cargo))
}

fn executable_path_is_named(path: &Path, expected: &str) -> bool {
    let Some(name) = path.file_name().and_then(OsStr::to_str) else {
        return false;
    };
    #[cfg(windows)]
    return name.eq_ignore_ascii_case(&format!("{expected}.exe"));
    #[cfg(not(windows))]
    return name == expected;
}

fn ensure_targo_brand(path: &Path) -> Result<(), String> {
    let output = Command::new(path)
        .arg("--version")
        .output()
        .map_err(|error| format!("execute Targo identity probe {}: {error}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "Targo identity probe {} failed with {}: {}",
            path.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    if !output.stdout.starts_with(b"targo ") {
        return Err(format!(
            "CARGO path {} did not identify itself as branded Targo: {}",
            path.display(),
            String::from_utf8_lossy(&output.stdout)
        ));
    }
    Ok(())
}

struct ExplicitUnverifiedTrybuildHarness {
    directory: tempfile::TempDir,
    wrapper: PathBuf,
    targo: PathBuf,
    targo_sha256: String,
}

impl ExplicitUnverifiedTrybuildHarness {
    fn create(outer_targo: &Path) -> io::Result<Self> {
        let directory = tempfile::Builder::new()
            .prefix("trust-wp-explicit-unverified-trybuild-")
            .tempdir()?;
        #[cfg(unix)]
        set_mode(directory.path(), 0o700)?;

        let targo = directory
            .path()
            .join(format!("targo{}", std::env::consts::EXE_SUFFIX));
        fs::copy(outer_targo, &targo)?;
        #[cfg(unix)]
        set_mode(&targo, 0o500)?;

        let wrapper = directory.path().join(if cfg!(windows) {
            "targo-explicit-unverified.cmd"
        } else {
            "targo-explicit-unverified"
        });
        fs::write(&wrapper, explicit_unverified_wrapper_contents())?;
        #[cfg(unix)]
        set_mode(&wrapper, 0o500)?;

        let targo_sha256 = sha256_file(&targo)?;
        ensure_targo_brand(&targo).map_err(io::Error::other)?;
        #[cfg(unix)]
        set_mode(directory.path(), 0o500)?;

        Ok(Self {
            directory,
            wrapper,
            targo,
            targo_sha256,
        })
    }

    fn unlock_for_cleanup(&self) {
        #[cfg(unix)]
        set_mode(self.directory.path(), 0o700)
            .expect("unlock explicit-unverified trybuild harness for cleanup");
    }
}

fn explicit_unverified_wrapper_contents() -> &'static [u8] {
    #[cfg(unix)]
    return b"#!/bin/sh\nset -eu\nunset TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_CHILD TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_WRAPPER TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_TARGO TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_TARGO_SHA256 TRUST_TARGO_NESTED_UNVERIFIED_BROKER\nfor argument in \"$@\"; do\n    case \"$argument\" in\n        build|check|fix|clippy|miri|test|run|bench|doc|rustc|rustdoc|install|package|publish)\n            exec \"${0%/*}/targo\" --unverified \"$@\"\n            ;;\n    esac\ndone\nexec \"${0%/*}/targo\" \"$@\"\n";
    #[cfg(windows)]
    return b"@echo off\r\nset TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_CHILD=\r\nset TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_WRAPPER=\r\nset TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_TARGO=\r\nset TRUST_WP_TRYBUILD_EXPLICIT_UNVERIFIED_TARGO_SHA256=\r\nset TRUST_TARGO_NESTED_UNVERIFIED_BROKER=\r\nfor %%A in (%*) do (\r\n    for %%C in (build check fix clippy miri test run bench doc rustc rustdoc install package publish) do (\r\n        if \"%%~A\"==\"%%C\" goto explicit_unverified\r\n    )\r\n)\r\n\"%~dp0targo.exe\" %*\r\nexit /b %errorlevel%\r\n:explicit_unverified\r\n\"%~dp0targo.exe\" --unverified %*\r\n";
}

fn validate_explicit_unverified_trybuild_child() -> Result<(), String> {
    let wrapper = required_path_env(TRYBUILD_WRAPPER_ENV)?;
    let targo = required_path_env(TRYBUILD_TARGO_ENV)?;
    let cargo = required_path_env("CARGO")?;
    if cargo != wrapper {
        return Err(format!(
            "trybuild child CARGO {} does not match its private wrapper {}",
            cargo.display(),
            wrapper.display()
        ));
    }
    if wrapper.parent() != targo.parent() {
        return Err("trybuild wrapper and private Targo are not in one harness directory".into());
    }
    let directory = wrapper
        .parent()
        .ok_or_else(|| "trybuild wrapper has no parent directory".to_owned())?;
    ensure_plain_file(&wrapper, "trybuild wrapper")?;
    ensure_plain_file(&targo, "private Targo")?;
    let wrapper_contents = fs::read(&wrapper)
        .map_err(|error| format!("read trybuild wrapper {}: {error}", wrapper.display()))?;
    if wrapper_contents != explicit_unverified_wrapper_contents() {
        return Err(
            "private trybuild wrapper does not spell the reviewed explicit-unverified command"
                .into(),
        );
    }

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        let mode = fs::symlink_metadata(directory)
            .map_err(|error| format!("inspect trybuild harness directory: {error}"))?
            .permissions()
            .mode();
        if mode & 0o022 != 0 {
            return Err(format!(
                "trybuild harness directory is group/other writable: mode {:#o}",
                mode & 0o777
            ));
        }
    }

    let expected_sha256 = std::env::var(TRYBUILD_TARGO_SHA256_ENV)
        .map_err(|error| format!("read {TRYBUILD_TARGO_SHA256_ENV}: {error}"))?;
    let actual_sha256 = sha256_file(&targo)
        .map_err(|error| format!("hash private Targo {}: {error}", targo.display()))?;
    if actual_sha256 != expected_sha256 {
        return Err(format!(
            "private Targo digest changed: expected {expected_sha256}, got {actual_sha256}"
        ));
    }
    ensure_targo_brand(&targo)
}

fn required_path_env(name: &str) -> Result<PathBuf, String> {
    std::env::var_os(name)
        .filter(|value| !value.is_empty())
        .map(PathBuf::from)
        .ok_or_else(|| format!("explicit-unverified trybuild child is missing {name}"))
}

fn ensure_plain_file(path: &Path, description: &str) -> Result<(), String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("inspect {description} {}: {error}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
        return Err(format!(
            "{description} is not a plain regular file: {}",
            path.display()
        ));
    }
    Ok(())
}

fn sha256_file(path: &Path) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut digest = Sha256::new();
    let mut buffer = vec![0_u8; 64 * 1024].into_boxed_slice();
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        digest.update(&buffer[..read]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

#[cfg(unix)]
fn set_mode(path: &Path, mode: u32) -> io::Result<()> {
    use std::os::unix::fs::PermissionsExt as _;
    fs::set_permissions(path, fs::Permissions::from_mode(mode))
}

/// Returns the trust-wp workspace root directory.
///
/// Runtime discovery is preferred over `CARGO_MANIFEST_DIR`: Cargo can reuse a
/// dependency artifact across parallel worktrees, and embedding the compiling
/// worktree's path would then point a later test process at a deleted checkout.
/// An explicit `TRUST_WP_WORKSPACE_ROOT` wins, followed by the current working
/// directory and its ancestors. The compile-time manifest path is only the
/// final compatibility fallback.
///
/// # Panics
///
/// Panics if an explicit root is invalid, or if neither runtime discovery nor
/// the compiled fallback identifies a live trust-wp checkout.
pub fn workspace_root() -> PathBuf {
    if let Some(explicit) = std::env::var_os("TRUST_WP_WORKSPACE_ROOT") {
        let explicit = PathBuf::from(explicit);
        assert!(
            is_workspace_root(&explicit),
            "TRUST_WP_WORKSPACE_ROOT is not a trust-wp checkout: {}",
            explicit.display()
        );
        return explicit;
    }

    if let Ok(current) = std::env::current_dir() {
        if let Some(root) = find_workspace_root_from(&current) {
            return root;
        }
    }

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let fallback = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root should exist")
        .to_path_buf();
    assert!(
        is_workspace_root(&fallback),
        "compiled trust-wp workspace no longer exists; set TRUST_WP_WORKSPACE_ROOT: {}",
        fallback.display()
    );
    fallback
}

fn find_workspace_root_from(start: &Path) -> Option<PathBuf> {
    start
        .ancestors()
        .find(|candidate| is_workspace_root(candidate))
        .map(Path::to_path_buf)
}

fn is_workspace_root(candidate: &Path) -> bool {
    candidate.join("Cargo.toml").is_file()
        && candidate
            .join("crates")
            .join("trust-wp-test-utils")
            .join("Cargo.toml")
            .is_file()
}

/// Returns the path to the cargo-trust-wp binary.
///
/// The binary is expected to be in `target/debug/` after `cargo build`.
/// When `CARGO_TARGET_DIR` is set, the active target directory is used instead.
/// This function returns the expected path without checking for existence; the
/// caller is responsible for building the binary before use.
pub fn cargo_trust_wp_bin() -> PathBuf {
    workspace_target_debug_bin("cargo-trust-wp")
}

/// Returns the path to the trust-wp-rustc binary.
///
/// The binary is expected to be in `target/debug/` after `cargo build`.
/// When `CARGO_TARGET_DIR` is set, the active target directory is used instead.
/// This function returns the expected path without checking for existence; the
/// caller is responsible for building the binary before use.
pub fn trust_wp_rustc_bin() -> PathBuf {
    workspace_target_debug_bin("trust-wp-rustc")
}

/// Returns the path to the trust-wp-rustc binary, building it if necessary.
///
/// Unlike [`trust_wp_rustc_bin`], this function ensures the binary exists and is
/// newer than the driver workspace sources by running
/// `cargo build -p trust-wp-driver --bin trust-wp-rustc` when the binary is
/// missing or stale.
///
/// # Panics
///
/// Panics if the build fails or the binary still doesn't exist after building.
pub fn trust_wp_rustc_path() -> PathBuf {
    let path = trust_wp_rustc_bin();
    if freshness::trust_wp_rustc_needs_build(&path).expect("check trust-wp-rustc freshness") {
        let status = Command::new("cargo")
            .current_dir(workspace_root())
            .args(["build", "-p", "trust-wp-driver", "--bin", "trust-wp-rustc"])
            .status()
            .expect("failed to run cargo build");
        assert!(
            status.success(),
            "cargo build -p trust-wp-driver --bin trust-wp-rustc failed"
        );
    }
    assert!(
        path.exists(),
        "trust-wp-rustc binary missing: {}",
        path.display()
    );
    path
}

/// Returns a target directory for fixture projects that invoke `trust-wp-rustc`.
///
/// Cargo does not include `RUSTC_WRAPPER` binary contents in fixture crate
/// fingerprints. Include the wrapper binary fingerprint in the target path so
/// fixture outputs cannot be reused across trust-wp/ay wrapper rebuilds.
pub fn trust_wp_rustc_fixture_target_dir(name: &str) -> PathBuf {
    let wrapper = trust_wp_rustc_path();
    let metadata = fs::metadata(&wrapper)
        .unwrap_or_else(|err| panic!("failed to stat {}: {err}", wrapper.display()));
    let modified = metadata
        .modified()
        .ok()
        .and_then(|mtime| mtime.duration_since(UNIX_EPOCH).ok())
        .map_or(0, |duration| duration.as_nanos());
    let fingerprint = format!("{:x}-{modified:x}", metadata.len());
    workspace_root()
        .join("target")
        .join(format!("{name}-{fingerprint}"))
}

fn workspace_target_dir() -> PathBuf {
    let target_dir = std::env::var_os("CARGO_TARGET_DIR");
    workspace_target_dir_from_raw(target_dir.as_deref())
}

fn workspace_target_dir_from_raw(target_dir: Option<&OsStr>) -> PathBuf {
    match target_dir {
        Some(target_dir) => {
            let target_dir = PathBuf::from(target_dir);
            if target_dir.is_absolute() {
                target_dir
            } else {
                workspace_root().join(target_dir)
            }
        }
        None => workspace_root().join("target"),
    }
}

fn workspace_target_debug_bin(name: &str) -> PathBuf {
    workspace_target_dir()
        .join("debug")
        .join(format!("{name}{}", std::env::consts::EXE_SUFFIX))
}

#[cfg(test)]
fn workspace_target_debug_bin_from_raw(name: &str, target_dir: Option<&OsStr>) -> PathBuf {
    workspace_target_dir_from_raw(target_dir)
        .join("debug")
        .join(format!("{name}{}", std::env::consts::EXE_SUFFIX))
}

/// Returns the path to a test fixture directory.
///
/// Fixtures are expected to be in `tests/fixtures/<name>/`.
///
/// # Arguments
///
/// * `name` - The fixture directory name
pub fn fixture_dir(name: &str) -> PathBuf {
    workspace_root().join("tests").join("fixtures").join(name)
}

/// Recursively copies a directory and all its contents.
///
/// # Arguments
///
/// * `src` - Source directory path
/// * `dst` - Destination directory path
///
/// # Errors
///
/// Returns an error if any file operation fails.
pub fn copy_dir_all(src: &Path, dst: &Path) -> std::io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());
        if ty.is_dir() {
            copy_dir_all(&src_path, &dst_path)?;
        } else {
            fs::copy(&src_path, &dst_path)?;
        }
    }
    Ok(())
}

/// Rewrites the trust-wp dependency paths in a fixture's Cargo.toml.
///
/// This is needed because fixture projects use relative paths that don't
/// work when the fixture is copied to a temp directory.
///
/// # Arguments
///
/// * `fixture_dir` - Path to the copied fixture directory
///
/// # Errors
///
/// Returns an error if the Cargo.toml cannot be read or written.
pub fn rewrite_trust_wp_path(fixture_dir: &Path) -> std::io::Result<()> {
    let manifest_path = fixture_dir.join("Cargo.toml");
    let mut contents = fs::read_to_string(&manifest_path)?;

    // Rewrite trust-wp path
    let old_trust_wp = "trust-wp = { path = \"../../../crates/trust-wp\" }";
    let new_trust_wp = format!(
        "trust-wp = {{ path = \"{}\" }}",
        workspace_root().join("crates").join("trust-wp").display()
    );
    if contents.contains(old_trust_wp) {
        contents = contents.replace(old_trust_wp, &new_trust_wp);
    }

    // Rewrite trust-wp-std path
    let old_std = "trust-wp-std = { path = \"../../../crates/trust-wp-std\" }";
    let new_std = format!(
        "trust-wp-std = {{ path = \"{}\" }}",
        workspace_root()
            .join("crates")
            .join("trust-wp-std")
            .display()
    );
    if contents.contains(old_std) {
        contents = contents.replace(old_std, &new_std);
    }

    fs::write(&manifest_path, contents)?;
    Ok(())
}

/// Creates a wrapper script for trust-wp-rustc in the given bin directory.
///
/// This is used by cargo-trust-wp end-to-end tests to set up the `RUSTC_WRAPPER`.
///
/// # Arguments
///
/// * `bin_dir` - Directory where the wrapper script should be created
///
/// # Returns
///
/// The path to the created wrapper script.
///
/// # Errors
///
/// Returns an error if the script cannot be created.
#[cfg(unix)]
pub fn write_trust_wp_rustc_wrapper(bin_dir: &Path) -> std::io::Result<PathBuf> {
    use std::os::unix::fs::PermissionsExt;

    let wrapper_path = bin_dir.join("trust-wp-rustc");
    let script_path = workspace_root()
        .join("scripts")
        .join("run-trust-wp-rustc.sh");
    let contents = format!(
        "#!/bin/bash\nset -e\n\"{}\" \"$@\"\n",
        script_path.display()
    );
    fs::write(&wrapper_path, contents)?;
    let mut perms = fs::metadata(&wrapper_path)?.permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&wrapper_path, perms)?;
    Ok(wrapper_path)
}

/// Creates a wrapper script for trust-wp-rustc (Windows version).
#[cfg(windows)]
pub fn write_trust_wp_rustc_wrapper(bin_dir: &Path) -> std::io::Result<PathBuf> {
    let wrapper_path = bin_dir.join("trust-wp-rustc.bat");
    let script_path = workspace_root()
        .join("scripts")
        .join("run-trust-wp-rustc.bat");
    let contents = format!("@echo off\n\"{}\" %*\n", script_path.display());
    fs::write(&wrapper_path, contents)?;
    Ok(wrapper_path)
}

/// Copies the cargo-trust-wp binary to the given bin directory.
///
/// # Arguments
///
/// * `bin_dir` - Directory where the binary should be copied
///
/// # Returns
///
/// The path to the copied binary.
///
/// # Errors
///
/// Returns an error if the binary cannot be copied.
#[cfg(unix)]
pub fn copy_cargo_trust_wp_bin(bin_dir: &Path) -> std::io::Result<PathBuf> {
    use std::os::unix::fs::PermissionsExt;

    let src = cargo_trust_wp_bin();
    let dst = bin_dir.join("cargo-trust-wp");
    fs::copy(&src, &dst)?;
    let mut perms = fs::metadata(&dst)?.permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&dst, perms)?;
    Ok(dst)
}

/// Copies the trust-wp-rustc binary to the given bin directory, rebuilding it if
/// missing or stale.
///
/// This is used by end-to-end tests so `cargo-trust-wp` can find a sibling
/// `trust-wp-rustc` binary without spending the child-process watchdog window
/// building the driver on demand.
#[cfg(unix)]
pub fn copy_trust_wp_rustc_bin(bin_dir: &Path) -> std::io::Result<PathBuf> {
    use std::os::unix::fs::PermissionsExt;

    let src = trust_wp_rustc_path();
    let dst = bin_dir.join("trust-wp-rustc");
    fs::copy(&src, &dst)?;
    let mut perms = fs::metadata(&dst)?.permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&dst, perms)?;
    Ok(dst)
}

/// Copies the trust-wp-rustc binary to the given bin directory (Windows
/// version), building it if necessary.
#[cfg(windows)]
pub fn copy_trust_wp_rustc_bin(bin_dir: &Path) -> std::io::Result<PathBuf> {
    let src = trust_wp_rustc_path();
    let dst = bin_dir.join(format!("trust-wp-rustc{}", std::env::consts::EXE_SUFFIX));
    fs::copy(&src, &dst)?;
    Ok(dst)
}

/// Copies the cargo-trust-wp binary (Windows version).
#[cfg(windows)]
pub fn copy_cargo_trust_wp_bin(bin_dir: &Path) -> std::io::Result<PathBuf> {
    let src = cargo_trust_wp_bin();
    let dst = bin_dir.join("cargo-trust-wp.exe");
    fs::copy(&src, &dst)?;
    Ok(dst)
}

/// Runs a dir-based integration test fixture through `cargo check` with trust-wp-rustc.
///
/// # Arguments
///
/// * `fixture_name` - Fixture directory name under `tests/fixtures/`
/// * `target_dir_suffix` - Suffix appended to `<workspace>/target/` for isolation
/// * `bin` - Binary target name passed to `--bin`
/// * `trust_wp_args` - Optional value for the `TRUST_WP_ARGS` environment variable
pub fn run_dir_fixture(
    fixture_name: &str,
    target_dir_suffix: &str,
    bin: &str,
    trust_wp_args: Option<&str>,
) -> std::process::Output {
    let target_dir = workspace_root().join("target").join(target_dir_suffix);
    let mut cmd = Command::new("cargo");
    cmd.current_dir(fixture_dir(fixture_name))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["check", "--quiet", "--bin", bin]);
    if let Some(args) = trust_wp_args {
        cmd.env("TRUST_WP_ARGS", args);
    }
    cmd.output()
        .expect("failed to run cargo check for dir fixture")
}

/// Runs an inline-source integration test fixture through `cargo check` with trust-wp-rustc.
///
/// Creates a temporary Cargo project with the given source, compiles it through
/// trust-wp-rustc, and cleans up the temp directory afterward.
///
/// # Arguments
///
/// * `pkg_name` - Package name for the generated Cargo.toml
/// * `target_dir_suffix` - Suffix appended to `<workspace>/target/` for isolation
/// * `trust_wp_args` - Value for the `TRUST_WP_ARGS` environment variable
/// * `needs_trust_wp_std` - Whether to include `trust-wp-std` as a dependency
/// * `source` - Rust source code written to `src/main.rs`
pub fn run_inline_fixture(
    pkg_name: &str,
    target_dir_suffix: &str,
    trust_wp_args: &str,
    needs_trust_wp_std: bool,
    source: &str,
) -> std::process::Output {
    use std::time::{SystemTime, UNIX_EPOCH};

    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-{pkg_name}-{}-{unique}",
        std::process::id()
    ));
    let src_dir = fixture_dir.join("src");
    fs::create_dir_all(&src_dir).expect("failed to create temp fixture directory");

    let root = workspace_root();
    let trust_wp_path = root.join("crates").join("trust-wp");

    let mut deps = format!("trust-wp = {{ path = \"{}\" }}\n", trust_wp_path.display());
    if needs_trust_wp_std {
        let trust_wp_std_path = root.join("crates").join("trust-wp-std");
        writeln!(
            deps,
            "trust_wp_std = {{ package = \"trust-wp-std\", path = \"{}\" }}",
            trust_wp_std_path.display()
        )
        .unwrap();
    }

    fs::write(
        fixture_dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{pkg_name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\n{deps}"
        ),
    )
    .expect("failed to write temp Cargo.toml");

    fs::write(src_dir.join("main.rs"), source).expect("failed to write temp main.rs");

    let target_dir = root.join("target").join(target_dir_suffix);

    let output = Command::new("cargo")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", trust_wp_args)
        .args(["check", "--quiet"])
        .output()
        .expect("failed to run cargo check for inline fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[cfg(test)]
mod tests {
    use tempfile::TempDir;

    use super::*;

    #[test]
    fn test_workspace_root_exists() {
        let root = workspace_root();
        assert!(
            root.exists(),
            "workspace root should exist: {}",
            root.display()
        );
        assert!(
            root.join("Cargo.toml").exists(),
            "workspace Cargo.toml should exist"
        );
    }

    #[test]
    fn runtime_workspace_discovery_walks_from_nested_checkout_path() {
        let temp = TempDir::new().unwrap();
        let root = temp.path().join("live-worktree");
        let nested = root.join("target").join("debug").join("deps");
        fs::create_dir_all(root.join("crates").join("trust-wp-test-utils")).unwrap();
        fs::create_dir_all(&nested).unwrap();
        fs::write(root.join("Cargo.toml"), "[workspace]\n").unwrap();
        fs::write(
            root.join("crates")
                .join("trust-wp-test-utils")
                .join("Cargo.toml"),
            "[package]\nname = \"trust-wp-test-utils\"\nversion = \"0.0.0\"\n",
        )
        .unwrap();

        assert_eq!(find_workspace_root_from(&nested), Some(root));
    }

    #[test]
    fn runtime_workspace_discovery_rejects_unrelated_cargo_project() {
        let temp = TempDir::new().unwrap();
        fs::write(
            temp.path().join("Cargo.toml"),
            "[package]\nname = \"other\"\n",
        )
        .unwrap();

        assert_eq!(find_workspace_root_from(temp.path()), None);
    }

    #[test]
    fn test_fixture_dir() {
        // Just test the path construction, not that the fixture exists
        let dir = fixture_dir("example");
        assert!(dir.ends_with("tests/fixtures/example"));
    }

    #[test]
    fn test_copy_dir_all() {
        let temp = TempDir::new().unwrap();
        let src = temp.path().join("src");
        let dst = temp.path().join("dst");

        // Create source structure
        fs::create_dir_all(src.join("subdir")).unwrap();
        fs::write(src.join("file.txt"), "content").unwrap();
        fs::write(src.join("subdir").join("nested.txt"), "nested").unwrap();

        // Copy and verify
        copy_dir_all(&src, &dst).unwrap();
        assert!(dst.join("file.txt").exists());
        assert!(dst.join("subdir").join("nested.txt").exists());
        assert_eq!(fs::read_to_string(dst.join("file.txt")).unwrap(), "content");
        assert_eq!(
            fs::read_to_string(dst.join("subdir").join("nested.txt")).unwrap(),
            "nested"
        );
    }

    #[test]
    fn cargo_trust_wp_bin_defaults_to_workspace_target_debug() {
        assert_eq!(
            workspace_target_debug_bin_from_raw("cargo-trust-wp", None),
            workspace_root()
                .join("target")
                .join("debug")
                .join(format!("cargo-trust-wp{}", std::env::consts::EXE_SUFFIX))
        );
    }

    #[test]
    fn trust_wp_rustc_bin_honors_relative_cargo_target_dir() {
        assert_eq!(
            workspace_target_debug_bin_from_raw(
                "trust-wp-rustc",
                Some(Path::new("target/worker_1").as_os_str()),
            ),
            workspace_root()
                .join("target")
                .join("worker_1")
                .join("debug")
                .join(format!("trust-wp-rustc{}", std::env::consts::EXE_SUFFIX))
        );
    }

    #[test]
    fn cargo_trust_wp_bin_honors_absolute_cargo_target_dir() {
        let temp = TempDir::new().unwrap();
        assert_eq!(
            workspace_target_debug_bin_from_raw("cargo-trust-wp", Some(temp.path().as_os_str()),),
            temp.path()
                .join("debug")
                .join(format!("cargo-trust-wp{}", std::env::consts::EXE_SUFFIX))
        );
    }
}
