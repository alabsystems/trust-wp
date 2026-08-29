// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    time::{SystemTime, UNIX_EPOCH},
};

use ay_dpll::api::{
    Logic, NativeReplayArtifact, NativeReplayMetadata, NativeReplaySymbolKind, Solver, Sort,
};

fn tool_bin() -> &'static str {
    env!("CARGO_BIN_EXE_trust-wp-ay-native-replay")
}

fn temp_dir(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock before Unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust-wp-ay-native-replay-tool-{name}-{}-{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

fn write_unsat_artifact_with_redundant_assertion() -> (PathBuf, NativeReplayArtifact) {
    let dir = temp_dir("unsat");
    let path = dir.join("input.ay-native-replay.json");

    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);

    let y_ge_zero = solver.try_ge(y, zero).expect("y >= 0");
    solver
        .try_assert_named(y_ge_zero, "irrelevant-y-lower-bound")
        .expect("assert irrelevant");
    let x_ge_zero = solver.try_ge(x, zero).expect("x >= 0");
    solver
        .try_assert_named(x_ge_zero, "x-lower-bound")
        .expect("assert lower");
    let x_lt_zero = solver.try_lt(x, zero).expect("x < 0");
    solver
        .try_assert_named(x_lt_zero, "x-upper-bound")
        .expect("assert upper");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_unsat());
    let mut metadata = NativeReplayMetadata::default();
    metadata.consumer = Some("trust-wp".to_string());
    metadata.fixture_path = Some("native_replay_tool.rs".to_string());
    metadata.obligation_kind = Some("ensures".to_string());
    let artifact = solver.export_native_replay_artifact(metadata, Some(&details));

    fs::write(&path, artifact.to_pretty_json()).expect("write artifact");
    (path, artifact)
}

fn run_tool(args: &[&str]) -> Output {
    let output = Command::new(tool_bin())
        .args(args)
        .output()
        .expect("run trust-wp-ay-native-replay");
    assert!(
        output.status.success(),
        "tool failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

#[test]
fn replay_command_accepts_trust_wp_native_replay_json() {
    let (path, artifact) = write_unsat_artifact_with_redundant_assertion();

    let output = run_tool(&["replay", path.to_str().expect("utf-8 path")]);
    let stdout = String::from_utf8(output.stdout).expect("utf-8 stdout");

    assert!(stdout.contains("status=ok command=replay"), "{stdout}");
    assert!(stdout.contains("stored=unsat"), "{stdout}");
    assert!(stdout.contains("replay=unsat"), "{stdout}");
    assert!(stdout.contains(&format!("assertions={}", artifact.assertions.len())));
}

#[test]
fn shrink_command_removes_redundant_assertion_and_preserves_replay_status() {
    let (path, artifact) = write_unsat_artifact_with_redundant_assertion();
    let out_path = path
        .parent()
        .expect("artifact has parent")
        .join("minimized.ay-native-replay.json");

    let output = run_tool(&[
        "shrink",
        path.to_str().expect("utf-8 path"),
        "--output",
        out_path.to_str().expect("utf-8 output path"),
    ]);
    let stdout = String::from_utf8(output.stdout).expect("utf-8 stdout");
    assert!(stdout.contains("status=ok command=shrink"), "{stdout}");
    assert!(stdout.contains("target=unsat"), "{stdout}");
    assert!(stdout.contains("final=unsat"), "{stdout}");
    assert!(stdout.contains("assertions=3->2"), "{stdout}");

    let minimized_json = fs::read_to_string(&out_path).expect("read minimized artifact");
    let minimized =
        NativeReplayArtifact::from_json_str(&minimized_json).expect("parse minimized artifact");
    assert_eq!(minimized.assertions.len(), 2);
    assert!(
        minimized
            .assertions
            .iter()
            .all(|assertion| { assertion.name.as_deref() != Some("irrelevant-y-lower-bound") }),
        "minimized artifact should drop the irrelevant assertion"
    );
    assert!(
        minimized.terms.len() < artifact.terms.len(),
        "term pruning should remove the irrelevant y-side term DAG"
    );
    let replay = Solver::replay_native_replay_artifact(&minimized).expect("replay minimized");
    assert!(replay.result.result().is_unsat());

    let replay_output = run_tool(&["replay", out_path.to_str().expect("utf-8 output path")]);
    let replay_stdout = String::from_utf8(replay_output.stdout).expect("utf-8 replay stdout");
    assert!(
        replay_stdout.contains("status=ok command=replay"),
        "{replay_stdout}"
    );
}

/// An artifact shaped like the ones trust-wp actually writes: several constants
/// and an uninterpreted function, with most of the constants reachable only
/// from assertions the reducer will drop.
fn write_sat_artifact_with_prunable_declarations() -> PathBuf {
    let dir = temp_dir("prunable");
    let path = dir.join("input.ay-native-replay.json");

    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let a = solver.declare_const("a", Sort::Int);
    let b = solver.declare_const("b", Sort::Int);
    let spare_one = solver.declare_const("spare_one", Sort::Int);
    let spare_two = solver.declare_const("spare_two", Sort::Int);
    let quotient = solver.declare_fun("quotient", &[Sort::Int, Sort::Int], Sort::Int);
    let zero = solver.int_const(0);

    // The assertion worth keeping: it mentions a, b and the function.
    let applied = solver.try_apply(&quotient, &[a, b]).expect("apply");
    let kept = solver.try_ge(applied, zero).expect("quotient >= 0");
    solver.try_assert_named(kept, "kept").expect("assert kept");

    // ...and two the reducer can drop, which are the only users of the spares.
    for (spare, name) in [(spare_one, "spare-one"), (spare_two, "spare-two")] {
        let bound = solver.try_ge(spare, zero).expect("spare >= 0");
        solver.try_assert_named(bound, name).expect("assert spare");
    }

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_sat());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_eq!(
        artifact.symbol_identities.len(),
        artifact.declarations.len() + artifact.function_declarations.len(),
        "the fixture must carry a populated identity table, or it cannot pin this"
    );

    fs::write(&path, artifact.to_pretty_json()).expect("write artifact");
    path
}

/// A reduced artifact has to still LOAD.
///
/// ay validates that the identity table has exactly one row per declaration,
/// per function declaration and per datatype member, and fails the artifact
/// closed otherwise. The reducer pruned declarations without pruning their
/// rows, so every reduction that actually removed a declaration produced an
/// artifact ay refused to read — `native replay identity table has N rows,
/// expected M`. The reducer's whole purpose is to hand someone a smaller input
/// they can run, so an unloadable output is a total failure, not a blemish.
#[test]
fn shrink_output_stays_loadable_when_declarations_are_pruned() {
    let path = write_sat_artifact_with_prunable_declarations();
    let out_path = path
        .parent()
        .expect("artifact has parent")
        .join("minimized.ay-native-replay.json");

    let output = run_tool(&[
        "shrink",
        "--expect",
        "sat",
        path.to_str().expect("utf-8 path"),
        "--output",
        out_path.to_str().expect("utf-8 output path"),
    ]);
    let stdout = String::from_utf8(output.stdout).expect("utf-8 stdout");
    assert!(stdout.contains("status=ok command=shrink"), "{stdout}");

    let minimized_json = fs::read_to_string(&out_path).expect("read minimized artifact");
    let minimized =
        NativeReplayArtifact::from_json_str(&minimized_json).expect("parse minimized artifact");

    // The reduction has to have actually removed a declaration, or the test
    // would pass without exercising anything.
    assert!(
        minimized.declarations.len() < 4,
        "expected the spare constants to be pruned, got {} declarations",
        minimized.declarations.len()
    );

    // The invariant ay enforces, restated here so a future change to the
    // reducer fails on this line rather than deep inside a replay.
    let non_datatype_rows = minimized
        .symbol_identities
        .iter()
        .filter(|identity| {
            matches!(
                identity.kind,
                NativeReplaySymbolKind::Uninterpreted | NativeReplaySymbolKind::Theory
            )
        })
        .count();
    assert_eq!(
        non_datatype_rows,
        minimized.declarations.len() + minimized.function_declarations.len(),
        "identity rows must track the declarations that survived"
    );

    // ...and the real check: ay accepts it.
    let replay = Solver::replay_native_replay_artifact(&minimized).expect("replay minimized");
    assert!(replay.result.result().is_sat());

    let replay_output = run_tool(&[
        "replay",
        "--expect",
        "sat",
        out_path.to_str().expect("utf-8"),
    ]);
    let replay_stdout = String::from_utf8(replay_output.stdout).expect("utf-8 replay stdout");
    assert!(
        replay_stdout.contains("status=ok command=replay"),
        "{replay_stdout}"
    );
}
