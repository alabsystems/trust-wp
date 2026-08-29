// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks};

pub(super) const TEST_CRATE_NAME: &str = "trust_wp_struct_field_map_test";
static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

fn dependency_dir() -> PathBuf {
    std::env::current_exe()
        .expect("current test executable path")
        .parent()
        .expect("test executable should live under deps/")
        .to_path_buf()
}

fn dependency_artifact(crate_name: &str, extensions: &[&str]) -> PathBuf {
    let prefix = format!("lib{crate_name}-");
    let mut candidates: Vec<_> = fs::read_dir(dependency_dir())
        .expect("read dependency dir")
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            let file_name = path.file_name()?.to_string_lossy();
            if !file_name.starts_with(&prefix) {
                return None;
            }
            match path.extension().and_then(|ext| ext.to_str()) {
                Some(ext) if extensions.contains(&ext) => Some(path),
                _ => None,
            }
        })
        .collect();
    // Sort by: 1) prefer rlib over rmeta, 2) most recently modified first.
    // With stale build artifacts, the newest matching the current compilation
    // is the correct one.
    candidates.sort_by_key(|path| {
        let ext_priority: u8 = match path.extension().and_then(|ext| ext.to_str()) {
            Some("rlib") => 0,
            Some("rmeta") => 1,
            _ => 2,
        };
        let mtime = fs::metadata(path)
            .and_then(|m| m.modified())
            .unwrap_or(std::time::SystemTime::UNIX_EPOCH);
        (ext_priority, std::cmp::Reverse(mtime))
    });
    candidates
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("missing dependency artifact for {crate_name}"))
}

pub(super) fn trust_wp_probe_args() -> Vec<String> {
    let deps_dir = dependency_dir();
    // Artifacts are named with underscores (`libtrust_wp-*.rmeta`) — rustc
    // crate names are valid Rust identifiers, so the hyphenated package name
    // `trust-wp` maps to crate name `trust_wp`. Same for `--cfg` and `--extern`
    // which both consume crate-name form, not package-name form.
    let trust_wp_artifact = dependency_artifact("trust_wp", &["rmeta", "rlib"]);
    let trust_wp_std_artifact = dependency_artifact("trust_wp_std", &["rmeta", "rlib"]);
    vec![
        "--cfg".to_string(),
        "trust_wp".to_string(),
        "-L".to_string(),
        format!("dependency={}", deps_dir.display()),
        "--extern".to_string(),
        format!("trust_wp={}", trust_wp_artifact.display()),
        "--extern".to_string(),
        format!("trust_wp_std={}", trust_wp_std_artifact.display()),
    ]
}

pub(super) fn run_test_compiler_with_args(
    source: &str,
    temp_prefix: &str,
    extra_args: &[String],
    callbacks: &mut (impl Callbacks + Send),
) {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir =
        std::env::temp_dir().join(format!("{temp_prefix}_{}_{}", std::process::id(), unique));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let mut args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        TEST_CRATE_NAME.to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    args.extend(extra_args.iter().cloned());

    run_compiler(&args, callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);
}

pub(super) fn run_test_compiler(
    source: &str,
    temp_prefix: &str,
    callbacks: &mut (impl Callbacks + Send),
) {
    run_test_compiler_with_args(source, temp_prefix, &[], callbacks);
}
