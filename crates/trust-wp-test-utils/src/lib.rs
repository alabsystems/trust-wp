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
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::UNIX_EPOCH,
};

mod freshness;

/// Returns the trust-wp workspace root directory.
///
/// This uses `CARGO_MANIFEST_DIR` to navigate up to the workspace root.
/// Works correctly when called from any crate within the workspace.
///
/// # Panics
///
/// Panics if `CARGO_MANIFEST_DIR` is not set (should only happen outside cargo).
pub fn workspace_root() -> PathBuf {
    // In tests, CARGO_MANIFEST_DIR points to the crate's directory
    // We need to navigate up to find the workspace root
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // trust-wp-test-utils is at crates/trust-wp-test-utils, so parent.parent gives workspace
    manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root should exist")
        .to_path_buf()
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
