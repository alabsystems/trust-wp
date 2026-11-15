// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #2316: `snapshot!` blocks that bind local predicate
//! closures and return `seq!(...)` must preserve the logical `Seq<Mapping<_, bool>>`
//! value for verification instead of collapsing to `Snapshot::new_phantom()`.
//!
//! The proof_assert must verify, and preserving the captured sequence must not
//! leave sort mismatches, solver panics or the phantom capture behind.

use std::{
    fs,
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::{nested_cargo, trust_wp_rustc_path};

fn run_fixture() -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-snapshot-seq-mapping-{}-{unique}",
        std::process::id()
    ));
    let src_dir = fixture_dir.join("src");
    fs::create_dir_all(&src_dir).expect("failed to create temp fixture directory");

    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("failed to resolve workspace root");
    let trust_wp_path = workspace_root.join("crates/trust-wp");
    let trust_wp_std_path = workspace_root.join("crates/trust-wp-std");

    fs::write(
        fixture_dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"snapshot-seq-mapping-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\ntrust_wp_std = {{ package = \"trust-wp-std\", path = \"{}\" }}\n",
            trust_wp_path.display(),
            trust_wp_std_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    fs::write(
        src_dir.join("main.rs"),
        r#"#![allow(unexpected_cfgs)]

use trust_wp::{logic::{Mapping, Seq}, *};

#[ensures(true)]
fn snapshot_block_seq_mapping_closure_preserves_len() {
    let preds: Snapshot<Seq<Mapping<u32, bool>>> = snapshot! {
        let pred0 = |z: u32| z@ % 2 == 0;
        let pred1 = |z: u32| z@ % 2 == 1;
        seq!(pred0, pred1)
    };

    proof_assert!(preds.len() == 2);
}

fn main() {
    snapshot_block_seq_mapping_closure_preserves_len();
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/snapshot_block_seq_mapping_closure_tests");

    let output = nested_cargo("check")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet"])
        .output()
        .expect("failed to run targo check for snapshot fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn snapshot_block_seq_mapping_closure_verifies() {
    let output = run_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "proof_assert should verify the captured seq length; stderr: {stderr}"
    );
    // The function's own verdict is demoted, not verified: in this spelling
    // the block runs as MIR, and the calls it makes to build the sequence
    // (`Mapping::from_closure`, `Seq::singleton`, `Seq::push_back`) have no
    // spec, so each is an opaque call, which owes `requires(false)` and
    // demotes its caller. The creusot_std spelling of the block (`seq![..]`)
    // verifies. The cost is this function's verdict; the captured value the
    // assertion reads is unaffected. The TRUE program is the xfail control
    // snapshot_block_local_closures_seq_trust_wp_spelling_control.rs.
    assert!(
        stderr.contains(
            "trust-wp: snapshot_block_seq_mapping_closure_preserves_len unknown (demoted: encoding approximations may affect soundness: opaque_call_true_assumption(4))"
        ) && stderr.contains("trust-wp: 0 verified, 0 failed, 1 errors, 1 demoted"),
        "expected the function demoted on its four opaque calls; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("Snapshot::<T>::new_phantom"),
        "regression should avoid the old new_phantom capture path; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("sort mismatch"),
        "capturing Seq<Mapping<_, bool>> should not reintroduce sort mismatches; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("ay solver panic"),
        "capturing Seq<Mapping<_, bool>> should not panic the solver; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("error[E"),
        "fixture should compile; stderr: {stderr}"
    );
}
