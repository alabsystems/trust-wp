// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks};

pub(super) const TEST_CRATE_NAME: &str = "trust_wp_struct_field_map_test";
static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

pub(super) fn trust_wp_probe_args() -> Vec<String> {
    let units = trust_wp_test_utils::unit_dirs::UnitDirs::of_current_exe();
    // Artifacts are named with underscores (`libtrust_wp-*.rmeta`) — rustc
    // crate names are valid Rust identifiers, so the hyphenated package name
    // `trust-wp` maps to crate name `trust_wp`. Same for `--cfg` and `--extern`
    // which both consume crate-name form, not package-name form.
    let trust_wp_artifact = units.artifact("trust_wp", &["rmeta", "rlib"]);
    let trust_wp_std_artifact = units.artifact("trust_wp_std", &["rmeta", "rlib"]);
    let mut args = vec![
        "--cfg".to_string(),
        "trust_wp".to_string(),
        "--extern".to_string(),
        format!("trust_wp={}", trust_wp_artifact.display()),
        "--extern".to_string(),
        format!("trust_wp_std={}", trust_wp_std_artifact.display()),
    ];
    args.extend(units.search_args());
    args
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
