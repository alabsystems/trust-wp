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

//! Integration tests for the `trust-wp` binary.
//!
//! Everything here runs the real executable and needs **no engine, no sysroot
//! and no network**: help, usage errors, the in-process verbs (`contract`,
//! `bundle`, `result`) and the `--json` contract. Every fixture is hand-written
//! and synthetic — no transcript, dry-run echo or report is ever captured from
//! a real run, so nothing machine-specific can leak into the tree.

use std::{
    fs,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

use ntest::timeout;
use serde_json::Value;
use tempfile::TempDir;

/// The binary under test, as built by this crate.
fn trust_wp() -> Command {
    Command::new(env!("CARGO_BIN_EXE_trust-wp"))
}

/// Run the binary and return `(exit code, stdout, stderr)`.
fn run_in(dir: Option<&Path>, args: &[&str], stdin: Option<&str>) -> (i32, String, String) {
    let mut command = trust_wp();
    command.args(args);
    if let Some(dir) = dir {
        command.current_dir(dir);
    }
    command.stdin(if stdin.is_some() {
        Stdio::piped()
    } else {
        Stdio::null()
    });
    command.stdout(Stdio::piped()).stderr(Stdio::piped());

    let mut child = command.spawn().expect("trust-wp should start");
    if let Some(text) = stdin {
        child
            .stdin
            .take()
            .expect("stdin was piped")
            .write_all(text.as_bytes())
            .expect("stdin should accept the transcript");
    }
    let output = child.wait_with_output().expect("trust-wp should finish");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

fn run(args: &[&str]) -> (i32, String, String) {
    run_in(None, args, None)
}

/// Run with one extra environment variable set **on the child**. This process
/// keeps its own environment, which is why this is allowed where
/// `std::env::set_var` is not: nothing here is global state.
fn run_with_env(key: &str, value: &str, args: &[&str]) -> (i32, String, String) {
    let output = trust_wp()
        .args(args)
        .env(key, value)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("trust-wp should run");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// Parse stdout as exactly one JSON document — the `--json` promise.
fn json_of(stdout: &str) -> Value {
    serde_json::from_str(stdout)
        .unwrap_or_else(|err| panic!("stdout should be one JSON document ({err}): {stdout:?}"))
}

/// A `--json` run: assert the envelope and hand back the document.
fn json_run(args: &[&str], expected_exit: i32) -> Value {
    let (code, stdout, stderr) = run(args);
    assert_eq!(code, expected_exit, "args {args:?}, stderr: {stderr}");
    let value = json_of(&stdout);
    assert_eq!(value["schema"], "trust-wp.cli-report.v1", "args {args:?}");
    assert_eq!(value["tool"]["name"], "trust-wp");
    assert!(
        value["tool"]["version"].is_string(),
        "the report names the tool version"
    );
    value
}

// ---------------------------------------------------------------------------
// Help and version: pure, and work with nothing installed
// ---------------------------------------------------------------------------

#[test]
#[timeout(30_000)]
fn help_is_available_under_every_spelling() {
    for args in [&["--help"][..], &["-h"][..], &["help"][..]] {
        let (code, stdout, stderr) = run(args);
        assert_eq!(code, 0, "{args:?}: {stderr}");
        assert!(stdout.starts_with("trust-wp "), "{args:?}: {stdout}");
        for command in [
            "verify", "contract", "bundle", "result", "doctor", "example",
        ] {
            assert!(stdout.contains(command), "{args:?} omits `{command}`");
        }
        assert!(stdout.contains("trust-wp example > demo.rs && trust-wp demo.rs"));
    }
}

#[test]
#[timeout(30_000)]
fn short_help_fits_a_terminal_and_points_at_the_full_page() {
    let (_, brief, _) = run(&["-h"]);
    let (_, full, _) = run(&["--help"]);
    // `-h` exists to be readable without scrolling; `--help` exists to be
    // complete. If they ever converge, one of the two has stopped doing its
    // job — this test is what noticed the first time they were identical.
    assert!(
        brief.lines().count() <= 24,
        "-h is {} lines:\n{brief}",
        brief.lines().count()
    );
    assert!(brief.lines().all(|l| l.chars().count() <= 88), "{brief}");
    assert!(
        full.lines().count() > brief.lines().count() * 2,
        "--help ({}) is not meaningfully fuller than -h ({})",
        full.lines().count(),
        brief.lines().count()
    );
    assert!(brief.contains("--help"), "-h must say where the rest is");
    // Every option the short page advertises has to be real, and documented
    // in full exactly once.
    for flag in ["--filter", "--timeout", "--quiet", "--json", "--dry-run"] {
        assert!(full.contains(flag), "--help omits `{flag}` that -h offers");
        assert_eq!(
            full.lines()
                .filter(|l| l.trim_start().starts_with(flag)
                    || l.trim_start().starts_with(&format!("-q, {flag}")))
                .count(),
            1,
            "`{flag}` is not documented exactly once in --help:\n{full}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn quiet_is_a_presentation_flag_and_never_reaches_the_engine() {
    let dir = TempDir::new().unwrap();
    let demo = dir.path().join("demo.rs");
    assert_eq!(run(&["example", "-o", demo.to_str().unwrap()]).0, 0);
    let demo_arg = demo.to_str().unwrap();

    for spelling in ["-q", "--quiet"] {
        let (code, stdout, stderr) = run(&["--dry-run", spelling, demo_arg]);
        // With no engine installed the dry run reports that instead; either
        // way the flag must be accepted rather than refused as unknown.
        assert_ne!(
            code, 3,
            "{spelling} was rejected as a bad command line: {stderr}"
        );
        // Quiet changes what this process prints. The engine's command line is
        // what it would have been, so a quiet run and a loud one prove the
        // same thing.
        assert!(
            !stdout.contains("'-q'") && !stdout.contains("'--quiet'"),
            "{spelling} leaked into the engine command:\n{stdout}"
        );
    }
    let (_, loud, _) = run(&["--dry-run", demo_arg]);
    let (_, quiet, _) = run(&["--dry-run", "-q", demo_arg]);
    assert_eq!(
        strip_tempdir(&loud),
        strip_tempdir(&quiet),
        "-q changed the engine invocation"
    );
}

/// Blank out the per-run temporary directory so two dry runs compare equal.
fn strip_tempdir(text: &str) -> String {
    text.split_whitespace()
        .map(|word| {
            if word.contains("trust-wp-") && !word.ends_with(".rs") {
                "<tmp>".to_string()
            } else {
                word.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
#[timeout(30_000)]
fn every_command_has_its_own_help_page() {
    for topic in [
        "verify", "contract", "bundle", "result", "doctor", "example",
    ] {
        let (code, stdout, stderr) = run(&["help", topic]);
        assert_eq!(code, 0, "help {topic}: {stderr}");
        assert!(
            stdout.starts_with(&format!("trust-wp {topic}")),
            "help {topic} should lead with the verb: {stdout}"
        );
        // `trust-wp <verb> --help` is the same page.
        let (code, via_flag, _) = run(&[topic, "--help"]);
        assert_eq!(code, 0);
        assert_eq!(
            via_flag, stdout,
            "`{topic} --help` should match `help {topic}`"
        );
    }
    // The verify page documents the flags and the status vocabulary.
    let (_, verify_help, _) = run(&["help", "verify"]);
    assert!(verify_help.contains("--strict-obligations"));
    assert!(verify_help.contains("no_obligations"));
    assert!(verify_help.contains("soundness_gap"));
    // The bundle page is honest about the absent solver.
    let (_, bundle_help, _) = run(&["help", "bundle"]);
    assert!(bundle_help.contains("No SMT solver is involved"));
}

#[test]
#[timeout(30_000)]
fn unknown_help_topics_are_refused() {
    let (code, _, stderr) = run(&["help", "frobnicate"]);
    assert_eq!(code, 3);
    assert!(stderr.contains("no help topic `frobnicate`"), "{stderr}");
}

#[test]
#[timeout(30_000)]
fn version_is_available_under_every_spelling() {
    for args in [&["--version"][..], &["-V"][..], &["version"][..]] {
        let (code, stdout, stderr) = run(args);
        assert_eq!(code, 0, "{args:?}: {stderr}");
        assert!(stdout.starts_with("trust-wp "), "{args:?}: {stdout}");
    }
    let value = json_run(&["--json", "version"], 0);
    assert_eq!(value["command"], "version");
    assert!(value["repository"].is_string());

    // Built from a checkout, the version has to name the commit: the package
    // version is shared by every build between two minor bumps, so on its own
    // it cannot tell anyone which tree a bug report came from. Built from a
    // tarball there is no commit to name, and the bare version is correct.
    let (_, text, _) = run(&["--version"]);
    match value.get("build").and_then(|b| b.as_str()) {
        Some(build) => {
            assert!(
                build.starts_with('g'),
                "build metadata should be the documented `g<sha>` form, got `{build}`"
            );
            assert!(
                text.contains(&format!("+{build}")),
                "--version ({text}) and the JSON report ({build}) disagree"
            );
        }
        None => assert!(
            !text.contains('+'),
            "no build metadata reported, but --version carries some: {text}"
        ),
    }
}

#[test]
#[timeout(30_000)]
fn completions_are_emitted_for_every_shell_and_refused_for_others() {
    for shell in ["bash", "zsh", "fish"] {
        let (code, stdout, stderr) = run(&["completions", shell]);
        assert_eq!(code, 0, "completions {shell}: {stderr}");
        assert!(stdout.contains("trust-wp"), "{shell}: {stdout}");
        // The script is the whole of stdout, so it can be redirected straight
        // into the shell's completion directory.
        assert!(stdout.lines().count() > 10, "{shell} script is a stub");
        assert!(
            stdout.contains("--filter") || stdout.contains("-l filter"),
            "{shell} omits --filter"
        );
    }
    // A shell with no generator is refused by name, and told which exist.
    let (code, _, stderr) = run(&["completions", "tcsh"]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("tcsh"), "{stderr}");
    assert!(stderr.contains("bash"), "{stderr}");

    let (code, _, stderr) = run(&["completions"]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("needs a shell"), "{stderr}");

    // `--json` owns stdout; a shell script is not a report.
    let (code, _, stderr) = run(&["--json", "completions", "bash"]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("does not apply"), "{stderr}");
}

#[test]
#[timeout(60_000)]
fn an_ignored_trust_wp_home_is_reported_rather_than_discarded() {
    let dir = TempDir::new().unwrap();
    let not_a_checkout = dir.path().to_str().unwrap();

    // `doctor` names it, and refuses to call itself ready: an environment
    // that points at the wrong place is a problem even when the run happens
    // to succeed from somewhere else.
    let (code, stdout, _) = run_with_env("TRUST_WP_HOME", not_a_checkout, &["doctor"]);
    assert!(
        stdout.contains("TRUST_WP_HOME") && stdout.contains("IGNORED"),
        "doctor said nothing about an ignored TRUST_WP_HOME:\n{stdout}"
    );
    assert!(stdout.contains(not_a_checkout), "{stdout}");
    assert_ne!(code, 0, "doctor called itself ready anyway:\n{stdout}");
    // And it must not tell someone reading doctor's output to run doctor.
    let line = stdout
        .lines()
        .find(|l| l.contains("IGNORED"))
        .expect("the line exists");
    assert!(
        !line.contains("trust-wp doctor"),
        "doctor points at itself: {line}"
    );

    // Set to a real checkout, there is nothing to report.
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .unwrap();
    let (_, stdout, _) = run_with_env("TRUST_WP_HOME", root.to_str().unwrap(), &["doctor"]);
    assert!(!stdout.contains("IGNORED"), "{stdout}");
}

#[test]
#[timeout(30_000)]
fn the_manual_page_is_emitted_and_is_roff() {
    let (code, stdout, stderr) = run(&["man"]);
    assert_eq!(code, 0, "man: {stderr}");
    assert!(stdout.starts_with(".TH "), "not a man page:\n{stdout}");
    assert!(stdout.contains(".SH NAME"), "{stdout}");
    assert!(stdout.contains(".SH OPTIONS"), "{stdout}");
    assert!(stdout.contains(".SH EXIT STATUS"), "{stdout}");
    // Hyphens are escaped so a copied flag pastes back into a shell as ASCII.
    assert!(stdout.contains("\\-\\-filter"), "{stdout}");

    // Running it twice must give the same bytes: the page is dated by commit,
    // not by build, so an installed page does not churn on every rebuild.
    let (_, again, _) = run(&["man"]);
    assert_eq!(stdout, again, "the manual page is not reproducible");

    // It takes no arguments, and does not pretend to be a report.
    let (code, _, stderr) = run(&["man", "extra"]);
    assert_eq!(code, 3, "{stderr}");
    let (code, _, stderr) = run(&["--json", "man"]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("does not apply"), "{stderr}");
}

#[test]
#[timeout(120_000)]
fn a_loop_placed_invariant_compiles_without_the_user_gating_a_feature() {
    // Creusot writes `#[invariant(...)]` on the loop, and trust-wp advertises
    // compatibility with that syntax. An attribute in expression position is
    // gated behind `proc_macro_hygiene`, so without help this file does not
    // compile and rustc tells the reader to add a feature attribute to their
    // own source — for a requirement that is an artifact of how trust-wp
    // compiles a single file, not of anything they wrote.
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("loopinv.rs");
    fs::write(
        &path,
        "use trust_wp::{ensures, invariant, requires};\n\
         #[requires(n >= 2)]\n\
         #[ensures(result >= 0)]\n\
         pub fn sum_inv(n: i32) -> i32 {\n\
         let mut total = 0; let mut i = 0;\n\
         #[invariant(i >= 0 && total >= 0)]\n\
         while i < n { total += i; i += 1; }\n\
         total\n\
         }\n",
    )
    .unwrap();

    let (code, _, stderr) = run(&[path.to_str().unwrap()]);
    // With no engine installed this cannot verify; the point is that it must
    // never fail with the feature-gate error.
    assert!(
        !stderr.contains("proc_macro_hygiene") && !stderr.contains("E0658"),
        "loop-placed invariant hit the feature gate:\n{stderr}"
    );
    if code == 0 {
        assert!(stderr.contains("sum_inv"), "{stderr}");
    }

    // The flag is a compile-position concession, not a verification one: it
    // must not appear in the engine command when the caller set their own.
    let (_, mine, _) = run(&["--dry-run", path.to_str().unwrap()]);
    if mine.contains("crate-attr") {
        assert_eq!(
            mine.matches("crate-attr").count(),
            1,
            "the flag was added twice:\n{mine}"
        );
    }
}

#[test]
#[timeout(180_000)]
fn a_false_contract_over_a_mutated_reference_is_never_reported_verified() {
    // This is a soundness pin, not a feature test.
    //
    // A deref-store `*p = <rhs>` was lowered to an assumption `*p == <rhs>`,
    // and under the RustHorn encoding `*p` on the left is the ENTRY carrier —
    // so the hypothesis said "the caller's input already equals <rhs>". When
    // <rhs> reads `*p` and the store sits under a branch, that hypothesis is
    // contradictory, the branch goes vacuous, and EVERY postcondition closes
    // on it. Both functions below are false at v = -1 (they reach -2), and the
    // verifier reported `✓ verified` for both.
    //
    // What makes this worth a permanent test rather than a changelog line: the
    // wrong answer was invisible for as long as an unrelated completeness gap
    // happened to withhold the verdict. When that gap was closed, the false
    // "verified" surfaced. A test is the only thing that keeps the two
    // independent.
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("false_contract.rs");
    fs::write(
        &path,
        "use trust_wp::*;\n\
         #[ensures(^v >= 0)]\n\
         pub fn bad_sub(v: &mut i32) { if *v < 0 { *v = *v - 1; } }\n\
         #[ensures(^v >= 0)]\n\
         pub fn bad_mul(v: &mut i32) { if *v < 0 { *v = *v * 2; } }\n",
    )
    .unwrap();

    let (code, _, stderr) = run(&[path.to_str().unwrap()]);
    // Exit 0 means "everything verified", and nothing here is true.
    assert_ne!(
        code, 0,
        "a false contract over a mutated reference was reported verified:\n{stderr}"
    );
    for name in ["bad_sub", "bad_mul"] {
        assert!(
            !stderr.contains(&format!("{name} verified")),
            "`{name}` is false at v = -1 and must never verify:\n{stderr}"
        );
    }
}

// ---------------------------------------------------------------------------
// example
// ---------------------------------------------------------------------------

#[test]
#[timeout(30_000)]
fn example_writes_a_contracted_file() {
    let (code, stdout, _) = run(&["example"]);
    assert_eq!(code, 0);
    assert!(stdout.contains("#[requires(x > 0)]"), "{stdout}");
    assert!(stdout.contains("#[ensures(result > x)]"));

    let dir = TempDir::new().unwrap();
    let path = dir.path().join("demo.rs");
    let (code, stdout, stderr) = run(&["example", "-o", path.to_str().unwrap()]);
    assert_eq!(code, 0, "{stderr}");
    assert!(stdout.is_empty(), "the file is the product: {stdout}");
    assert!(stderr.contains("next:"), "{stderr}");
    let written = fs::read_to_string(&path).unwrap();
    assert!(written.contains("pub fn increment(x: i32) -> i32"));
}

#[test]
#[timeout(30_000)]
fn example_refuses_json_because_it_writes_source() {
    for args in [
        &["example", "--json"][..],
        &["--json", "bundle", "example"][..],
    ] {
        let (code, _, stderr) = run(args);
        assert_eq!(code, 3, "{args:?}");
        assert!(stderr.contains("`--json` does not apply"), "{stderr}");
    }
}

// ---------------------------------------------------------------------------
// Usage errors: refused, never ignored
// ---------------------------------------------------------------------------

#[test]
#[timeout(30_000)]
fn bad_command_lines_exit_three_and_say_why() {
    let cases: &[(&[&str], &str)] = &[
        (&["demo"], "unknown command `demo`"),
        (&["--frobnicate"], "unrecognized option"),
        (
            &["--verify-fn", "increment"],
            "`--verify-fn` is not a trust-wp option",
        ),
        (&["--format", "json"], "`--format` is not a trust-wp option"),
        (&["--timeout"], "`--timeout` needs a value"),
        (&["--track", "sideways"], "unknown --track level"),
        (&["a.rs", "b.rs"], "one file per run"),
        (&["doctor", "extra"], "takes no arguments"),
        (&["contract"], "needs a subcommand"),
        (&["bundle", "nope"], "unknown `trust-wp bundle` subcommand"),
        (&["bundle", "verify"], "needs a request file"),
        (&["--json", "--emit-smt", "demo.rs"], "both want stdout"),
        // Each verb explains that IT runs no other tool, which is more useful
        // than a generic "verify only".
        (&["doctor", "--", "x"], "nowhere to go"),
    ];
    for (args, expected) in cases {
        let (code, stdout, stderr) = run(args);
        assert_eq!(code, 3, "args {args:?} stderr: {stderr}");
        assert!(
            stderr.contains(expected),
            "args {args:?} should explain `{expected}`, got: {stderr}"
        );
        if args.contains(&"--json") {
            // `--json` still owes the caller a report; every other path is silent.
            json_of(&stdout);
        } else {
            assert!(
                stdout.is_empty(),
                "args {args:?} printed to stdout: {stdout}"
            );
        }
    }
}

#[test]
#[timeout(30_000)]
fn rejected_flags_name_the_trust_wp_alternative() {
    let (_, _, stderr) = run(&["--unwind=5"]);
    assert!(stderr.contains("#[invariant"), "{stderr}");
    let (_, _, stderr) = run(&["--solver", "z3"]);
    assert!(stderr.contains("--emit-smt"), "{stderr}");
}

#[test]
#[timeout(30_000)]
fn usage_errors_still_produce_a_json_report() {
    // `--json` promises exactly one document on stdout on every exit — a
    // rejected command line included, so a CI parser never sees nothing.
    let value = json_run(&["--json", "--frobnicate"], 3);
    assert_eq!(value["command"], "usage");
    assert_eq!(value["status"], "error");
    assert_eq!(value["error"]["kind"], "usage");
    assert!(
        value["error"]["message"]
            .as_str()
            .unwrap()
            .contains("--frobnicate"),
        "{value}"
    );
    assert!(!value["error"]["help"].as_array().unwrap().is_empty());
}

// ---------------------------------------------------------------------------
// verify: the paths that need no engine
// ---------------------------------------------------------------------------

#[test]
#[timeout(30_000)]
fn verify_rejects_targets_it_cannot_read() {
    let dir = TempDir::new().unwrap();
    let missing = dir.path().join("nope.rs");
    let (code, _, stderr) = run(&["verify", missing.to_str().unwrap()]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("cannot read"), "{stderr}");

    let not_rust = dir.path().join("notes.txt");
    fs::write(&not_rust, "hello").unwrap();
    let (code, _, stderr) = run(&["verify", not_rust.to_str().unwrap()]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("expected a `.rs` file"), "{stderr}");
}

#[test]
#[timeout(30_000)]
fn crate_mode_without_a_manifest_says_so() {
    let dir = TempDir::new().unwrap();
    let (code, _, stderr) = run_in(Some(dir.path()), &["--filter", "increment"], None);
    // Either there is no manifest here (3), or this machine has no engine (2).
    assert!(code == 3 || code == 2, "unexpected exit {code}: {stderr}");
    if code == 3 {
        assert!(stderr.contains("no Cargo.toml"), "{stderr}");
    } else {
        assert!(
            stderr.contains("cannot find the trust-wp engine"),
            "{stderr}"
        );
    }
}

// ---------------------------------------------------------------------------
// contract
// ---------------------------------------------------------------------------

#[test]
#[timeout(30_000)]
fn contract_parse_normalizes_an_expression() {
    let (code, stdout, stderr) = run(&["contract", "parse", "x > 0 && result == x + 1"]);
    assert_eq!(code, 0, "{stderr}");
    assert!(!stdout.trim().is_empty(), "a normalized form is printed");

    let value = json_run(&["--json", "contract", "parse", "x > 0"], 0);
    assert_eq!(value["command"], "contract parse");
    assert_eq!(value["ok"], true);
    assert_eq!(value["input"], "x > 0");
    assert!(value["normalized"].is_string());
    assert_eq!(value["error"], Value::Null);
}

#[test]
#[timeout(30_000)]
fn contract_parse_reports_the_error_position() {
    let (code, _, stderr) = run(&["contract", "parse", "x >"]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("error:"), "{stderr}");

    let value = json_run(&["--json", "contract", "parse", "x >"], 3);
    assert_eq!(value["ok"], false);
    assert_eq!(value["error"]["kind"], "contract_parse");
    assert!(
        value["error"]["position"].is_number(),
        "the position is machine-readable: {value}"
    );
}

#[test]
#[timeout(30_000)]
fn contract_parse_reads_a_file_or_stdin() {
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("contract.txt");
    fs::write(&path, "result == x\n").unwrap();
    let (code, stdout, stderr) = run(&["contract", "parse", "--file", path.to_str().unwrap()]);
    assert_eq!(code, 0, "{stderr}");
    assert!(!stdout.trim().is_empty());

    let (code, stdout, stderr) = run_in(None, &["contract", "parse", "--stdin"], Some("x >= 0"));
    assert_eq!(code, 0, "{stderr}");
    assert!(!stdout.trim().is_empty());

    // A bare `-` is stdin, the same as it is for `trust-wp result`. It used to
    // fall through to the inline arm and be parsed AS the expression, so a
    // pipeline answered "parse error at position 1: expected expression | -",
    // which describes the dash rather than the input.
    let (code, dash, stderr) = run_in(None, &["contract", "parse", "-"], Some("x >= 0"));
    assert_eq!(code, 0, "`-` should read stdin: {stderr}");
    let (_, flag, _) = run_in(None, &["contract", "parse", "--stdin"], Some("x >= 0"));
    assert_eq!(dash, flag, "`-` and `--stdin` must agree");

    // An expression that genuinely starts with `-` is still refused by name,
    // rather than being mistaken for a stdin request.
    let (code, _, stderr) = run(&["contract", "parse", "-x"]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("does not accept `-x`"), "{stderr}");

    let missing = dir.path().join("nope.txt");
    let (code, _, stderr) = run(&["contract", "parse", "--file", missing.to_str().unwrap()]);
    assert_eq!(code, 3);
    assert!(stderr.contains("cannot read"), "{stderr}");
}

#[test]
#[timeout(30_000)]
fn contract_vc_emits_smt_lib() {
    let (code, stdout, stderr) = run(&[
        "contract",
        "vc",
        "--name",
        "increment",
        "--requires",
        "x > 0",
        "--ensures",
        "result > x",
        "--result",
        "x + 1",
    ]);
    assert_eq!(code, 0, "{stderr}");
    assert!(stdout.contains("increment"), "{stdout}");
    assert!(stdout.contains("(check-sat)"), "{stdout}");

    let value = json_run(
        &[
            "--json",
            "contract",
            "vc",
            "--requires",
            "x > 0",
            "--ensures",
            "result > x",
        ],
        0,
    );
    assert_eq!(value["command"], "contract vc");
    assert_eq!(value["ok"], true);
    assert!(value["smt"].as_str().unwrap().contains("(check-sat)"));
    assert_eq!(value["requires"].as_array().unwrap().len(), 1);
    assert_eq!(value["ensures"].as_array().unwrap().len(), 1);
}

#[test]
#[timeout(30_000)]
fn contract_vc_names_the_clause_that_failed() {
    let (code, _, stderr) = run(&[
        "contract",
        "vc",
        "--requires",
        "x > 0",
        "--ensures",
        "result >",
    ]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("--ensures `result >`"), "{stderr}");

    // A contract with no clauses at all is a usage error, not an empty VC.
    let (code, _, stderr) = run(&["contract", "vc", "--name", "f"]);
    assert_eq!(code, 3);
    assert!(stderr.contains("at least one"), "{stderr}");
}

// ---------------------------------------------------------------------------
// bundle: the in-process prover, end to end
// ---------------------------------------------------------------------------

#[test]
#[timeout(60_000)]
fn bundle_round_trips_from_example_to_replay() {
    let dir = TempDir::new().unwrap();
    let request = dir.path().join("request.json");
    let result = dir.path().join("result.json");
    let request_arg = request.to_str().unwrap();
    let result_arg = result.to_str().unwrap();

    // example -> a request that is valid by construction
    let (code, _, stderr) = run(&["bundle", "example", "-o", request_arg]);
    assert_eq!(code, 0, "{stderr}");
    let text = fs::read_to_string(&request).unwrap();
    let parsed: Value = serde_json::from_str(&text).unwrap();
    assert_eq!(parsed["api_version"], "trust-wp.verify-bundle.v1");

    // validate
    let (code, _, stderr) = run(&["bundle", "validate", request_arg]);
    assert_eq!(code, 0, "{stderr}");
    let value = json_run(&["--json", "bundle", "validate", request_arg], 0);
    assert_eq!(value["command"], "bundle validate");
    assert_eq!(value["status"], "valid");
    assert_eq!(value["diagnostics"].as_array().unwrap().len(), 0);
    assert_eq!(value["error"], Value::Null);

    // verify -o FILE: the result document is written, the report names it
    let (code, _, stderr) = run(&["bundle", "verify", request_arg, "-o", result_arg]);
    assert_eq!(code, 0, "{stderr}");
    let written: Value = serde_json::from_str(&fs::read_to_string(&result).unwrap()).unwrap();
    assert_eq!(written["status"], "verified");
    assert_eq!(written["obligation_results"].as_array().unwrap().len(), 1);

    let value = json_run(
        &["--json", "bundle", "verify", request_arg, "-o", result_arg],
        0,
    );
    assert_eq!(value["status"], "verified");
    assert_eq!(value["obligations"]["verified"], 1);
    assert_eq!(value["result_path"], result_arg);
    assert!(value["result"].is_null(), "-o names the file instead");

    // verify with no -o: the result document is the product...
    let (code, stdout, stderr) = run(&["bundle", "verify", request_arg]);
    assert_eq!(code, 0, "{stderr}");
    let bare = json_of(&stdout);
    assert_eq!(bare["status"], "verified");
    assert_eq!(bare["obligation_results"].as_array().unwrap().len(), 1);

    // ...but under --json stdout is the report, with the result embedded.
    let value = json_run(&["--json", "bundle", "verify", request_arg], 0);
    assert_eq!(value["command"], "bundle verify");
    assert_eq!(value["result"]["status"], "verified");
    assert!(value["result_path"].is_null());

    // replay: the evidence re-checks independently of the run that made it
    let (code, _, stderr) = run(&["bundle", "replay", request_arg, result_arg]);
    assert_eq!(code, 0, "{stderr}");
    let value = json_run(&["--json", "bundle", "replay", request_arg, result_arg], 0);
    assert_eq!(value["status"], "replayed");
    assert_eq!(value["error"], Value::Null);
}

#[test]
#[timeout(60_000)]
fn tampered_evidence_does_not_replay() {
    let dir = TempDir::new().unwrap();
    let request = dir.path().join("request.json");
    let result = dir.path().join("result.json");
    let request_arg = request.to_str().unwrap();
    let result_arg = result.to_str().unwrap();

    assert_eq!(run(&["bundle", "example", "-o", request_arg]).0, 0);
    assert_eq!(
        run(&["bundle", "verify", request_arg, "-o", result_arg]).0,
        0
    );

    // Rewrite the recorded bundle id: the evidence no longer belongs to this
    // request, and replay must refuse it rather than trust the status word.
    let mut document: Value = serde_json::from_str(&fs::read_to_string(&result).unwrap()).unwrap();
    document["bundle_id"] = Value::from("not-the-same-bundle");
    fs::write(&result, serde_json::to_string_pretty(&document).unwrap()).unwrap();

    let (code, _, stderr) = run(&["bundle", "replay", request_arg, result_arg]);
    assert_eq!(code, 2, "{stderr}");
    assert!(stderr.contains("did NOT replay"), "{stderr}");
    let value = json_run(&["--json", "bundle", "replay", request_arg, result_arg], 2);
    assert_eq!(value["status"], "not_replayed");
    assert_eq!(value["error"]["kind"], "invalid_bundle");
    assert!(value["error"]["code"].is_string(), "{value}");
}

#[test]
#[timeout(30_000)]
fn unusable_bundle_inputs_are_refused() {
    let dir = TempDir::new().unwrap();

    let missing = dir.path().join("nope.json");
    let (code, _, stderr) = run(&["bundle", "verify", missing.to_str().unwrap()]);
    assert_eq!(code, 3);
    assert!(stderr.contains("cannot read the request"), "{stderr}");

    let garbage = dir.path().join("garbage.json");
    fs::write(&garbage, "this is not json").unwrap();
    let (code, _, stderr) = run(&["bundle", "verify", garbage.to_str().unwrap()]);
    assert_eq!(code, 3);
    assert!(stderr.contains("cannot decode the request"), "{stderr}");

    // Structurally decodable, but not a valid request: no obligations.
    let empty = dir.path().join("empty.json");
    fs::write(
        &empty,
        r#"{
            "api_version": "trust-wp.verify-bundle.v1",
            "bundle_id": "empty-1",
            "producer": {"name": "test"},
            "target": {"crate_name": "demo_crate"},
            "obligations": [],
            "options": {"require_proof_evidence": true}
        }"#,
    )
    .unwrap();
    let empty_arg = empty.to_str().unwrap();
    let (code, _, stderr) = run(&["bundle", "validate", empty_arg]);
    assert_eq!(code, 3, "{stderr}");
    let value = json_run(&["--json", "bundle", "validate", empty_arg], 3);
    assert_eq!(value["status"], "invalid");
    assert!(!value["diagnostics"].as_array().unwrap().is_empty());
    assert_eq!(run(&["bundle", "verify", empty_arg]).0, 3);

    let json_value = json_run(
        &["--json", "bundle", "verify", missing.to_str().unwrap()],
        3,
    );
    assert_eq!(json_value["error"]["kind"], "invalid_bundle");
}

#[test]
#[timeout(60_000)]
fn a_false_postcondition_fails_and_an_opaque_one_is_unsupported() {
    let dir = TempDir::new().unwrap();

    // The prover settles what it can and refuses to guess at the rest: a claim
    // it can disprove fails, and an open predicate it cannot settle is
    // `unsupported` — never silently "verified".
    for (name, claim, expected_exit, expected_status) in [
        ("false", "false", 1, "failed"),
        ("opaque", "x > 0", 2, "unsupported"),
    ] {
        let path = dir.path().join(format!("{name}.json"));
        fs::write(
            &path,
            format!(
                r#"{{
                    "api_version": "trust-wp.verify-bundle.v1",
                    "bundle_id": "{name}-1",
                    "producer": {{"name": "test"}},
                    "target": {{"crate_name": "demo_crate"}},
                    "obligations": [
                        {{
                            "id": "post-1",
                            "kind": "postcondition",
                            "function": "demo::f",
                            "claim": {{
                                "format": "trust_wp_pure_expr_v1",
                                "payload": "{claim}",
                                "digest": {{"algorithm": "sha256", "value": "{name}-digest"}}
                            }}
                        }}
                    ],
                    "options": {{"require_proof_evidence": true}}
                }}"#
            ),
        )
        .unwrap();
        let arg = path.to_str().unwrap();
        assert_eq!(
            run(&["bundle", "validate", arg]).0,
            0,
            "{name} should validate"
        );
        let value = json_run(&["--json", "bundle", "verify", arg], expected_exit);
        assert_eq!(value["status"], expected_status, "{name}: {value}");
    }
}

// ---------------------------------------------------------------------------
// result: decoding a transcript
// ---------------------------------------------------------------------------

/// A synthetic `TRUST_WP_RESULT:v1` line. Every key the parser requires is
/// present; the caller overrides the counters it cares about.
fn wire_line(overrides: &[(&str, u64)]) -> String {
    let mut fields: Vec<(&str, u64)> = vec![
        ("verified", 0),
        ("failed", 0),
        ("errors", 0),
        ("warnings", 0),
        ("assumed", 0),
        ("trusted", 0),
        ("skipped", 0),
        ("verified_with_axiom_deps", 0),
        ("unverified_axioms", 0),
        ("vacuous", 0),
        ("evidence_gaps", 0),
        ("proof_assert_failed", 0),
        ("proof_assert_errors", 0),
        ("panics", 0),
        ("demoted", 0),
        ("parse_errors", 0),
        ("termination_errors", 0),
        ("logic_recursion_errors", 0),
        ("erasure_errors", 0),
    ];
    for (key, value) in overrides {
        for field in &mut fields {
            if field.0 == *key {
                field.1 = *value;
            }
        }
    }
    let body: Vec<String> = fields
        .iter()
        .map(|(key, value)| format!("{key}={value}"))
        .collect();
    format!("TRUST_WP_RESULT:v1 base_exit_code=0 {}", body.join(" "))
}

/// A synthetic transcript: human chatter, one aggregate line, one diagnostic.
fn transcript(overrides: &[(&str, u64)], with_diagnostic: bool) -> String {
    let mut text = String::from("   Compiling demo v0.1.0 (/work/demo)\n");
    if with_diagnostic {
        text.push_str(
            "TRUST_WP_DIAGNOSTIC:v1 def_path=demo::increment kind=function_contract \
             status=failed reason=counterexample solve_time_ms=3 assertions=7 \
             timeout_ms=60000 ay_result=sat accepted_for_consumer=true \
             model_validated=true unsat_proof_available=false \
             verification_level=FullyVerified replay_present=false replay_bytes=0 \
             replay_sha256=none native_replay_present=false native_replay_bytes=0 \
             native_replay_sha256=none native_replay_schema=none native_replay_path=none \
             native_replay_write_error=none\n",
        );
        text.push_str("trust-wp: demo::increment FAILED \u{2717}\n");
    }
    text.push_str(&wire_line(overrides));
    text.push('\n');
    text
}

#[test]
#[timeout(30_000)]
fn result_decodes_a_transcript_from_stdin_or_a_file() {
    let clean = transcript(&[("verified", 2)], false);
    let (code, stdout, stderr) = run_in(None, &["result"], Some(&clean));
    assert_eq!(code, 0, "{stderr}");
    assert!(stdout.contains("verified"), "{stdout}");

    let dir = TempDir::new().unwrap();
    let path = dir.path().join("run.log");
    fs::write(&path, &clean).unwrap();
    let (code, stdout, stderr) = run(&["result", path.to_str().unwrap()]);
    assert_eq!(code, 0, "{stderr}");
    assert!(stdout.contains("2 verified"), "{stdout}");

    // `-` is stdin, spelled explicitly.
    let (code, _, _) = run_in(None, &["result", "-"], Some(&clean));
    assert_eq!(code, 0);
}

#[test]
#[timeout(30_000)]
fn result_exit_code_follows_the_decoded_verdict() {
    /// One decoded transcript: the counters to set, and what they should mean.
    struct Case {
        counters: &'static [(&'static str, u64)],
        exit_code: i32,
        status: &'static str,
    }
    let cases = [
        Case {
            counters: &[("verified", 1)],
            exit_code: 0,
            status: "verified",
        },
        Case {
            counters: &[("failed", 1)],
            exit_code: 1,
            status: "failed",
        },
        Case {
            counters: &[("errors", 1)],
            exit_code: 2,
            status: "error",
        },
        Case {
            counters: &[("trusted", 1)],
            exit_code: 2,
            status: "soundness_gap",
        },
        Case {
            counters: &[("parse_errors", 1)],
            exit_code: 3,
            status: "parse_error",
        },
        // An all-zero summary means the engine examined no obligation. A live
        // run fails closed on that, so decoding its transcript must agree.
        Case {
            counters: &[],
            exit_code: 2,
            status: "no_obligations",
        },
    ];
    for case in cases {
        let text = transcript(case.counters, false);
        let (code, stdout, stderr) = run_in(None, &["--json", "result"], Some(&text));
        assert_eq!(code, case.exit_code, "{:?}: {stderr}", case.counters);
        let value = json_of(&stdout);
        assert_eq!(value["command"], "result");
        assert_eq!(value["mode"], "transcript");
        assert_eq!(value["status"], case.status, "{:?}", case.counters);
    }
}

#[test]
#[timeout(30_000)]
fn result_reports_diagnostics_and_fails_closed_without_a_summary() {
    let text = transcript(&[("failed", 1)], true);
    let (code, stdout, stderr) = run_in(None, &["--json", "result"], Some(&text));
    assert_eq!(code, 1, "{stderr}");
    let value = json_of(&stdout);
    assert_eq!(value["status"], "failed");
    assert_eq!(value["summary"]["failed"], 1);
    assert_eq!(value["diagnostics_scope"], "non_clean_obligations");
    let diagnostics = value["diagnostics"].as_array().unwrap();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0]["def_path"], "demo::increment");
    assert_eq!(diagnostics[0]["classification"], "failed");
    assert_eq!(diagnostics[0]["solve_time_ms"], 3);
    // `none` decodes to null, not to the literal string.
    assert_eq!(diagnostics[0]["replay"]["sha256"], Value::Null);
    // Reserved until the engine sends them.
    assert_eq!(diagnostics[0]["location"], Value::Null);
    assert_eq!(diagnostics[0]["counterexample"], Value::Null);

    // A transcript with no result line proved nothing: fail closed.
    let (code, stdout, stderr) = run_in(
        None,
        &["--json", "result"],
        Some("   Compiling demo v0.1.0 (/work/demo)\nwarning: unused variable\n"),
    );
    assert_eq!(code, 2, "{stderr}");
    let value = json_of(&stdout);
    assert_eq!(value["status"], "no_verdict");
    assert_eq!(value["summary"], Value::Null);
}

#[test]
#[timeout(30_000)]
fn result_refuses_a_transcript_it_cannot_read() {
    let dir = TempDir::new().unwrap();
    let missing = dir.path().join("nope.log");
    let (code, _, stderr) = run(&["result", missing.to_str().unwrap()]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("cannot read"), "{stderr}");

    let value = json_run(&["--json", "result", missing.to_str().unwrap()], 3);
    assert_eq!(value["error"]["kind"], "io");
}

// ---------------------------------------------------------------------------
// doctor
// ---------------------------------------------------------------------------

#[test]
#[timeout(60_000)]
fn doctor_reports_readiness_either_way() {
    // Whether this machine has an engine is not this test's business; that the
    // report is well formed is.
    let (code, stdout, stderr) = run(&["--json", "doctor"]);
    assert!(code == 0 || code == 2, "unexpected exit {code}: {stderr}");
    let value = json_of(&stdout);
    assert_eq!(value["command"], "doctor");
    assert!(value["ready"].is_boolean());
    let checks = value["checks"].as_array().unwrap();
    assert!(checks.len() >= 5, "{value}");
    for check in checks {
        assert!(check["name"].is_string());
        assert!(check["ok"].is_boolean());
        assert!(check["detail"].is_string());
    }
    assert_eq!(value["ready"].as_bool().unwrap(), code == 0);

    let (human_code, human_stdout, _) = run(&["doctor"]);
    assert_eq!(human_code, code);
    assert!(human_stdout.starts_with("trust-wp "), "{human_stdout}");
    assert!(human_stdout.contains("active sysroot"), "{human_stdout}");
}

// ---------------------------------------------------------------------------
// --json is exactly one document, on every path that takes it
// ---------------------------------------------------------------------------

#[test]
#[timeout(60_000)]
fn json_mode_prints_exactly_one_document() {
    let dir = TempDir::new().unwrap();
    let request = dir.path().join("request.json");
    assert_eq!(
        run(&["bundle", "example", "-o", request.to_str().unwrap()]).0,
        0
    );
    let request_arg = request.to_str().unwrap();

    let cases: &[&[&str]] = &[
        &["--json", "version"],
        &["--json", "doctor"],
        &["--json", "contract", "parse", "x > 0"],
        &["--json", "contract", "parse", "x >"],
        &["--json", "contract", "vc", "--ensures", "result > 0"],
        &["--json", "bundle", "validate", request_arg],
        &["--json", "bundle", "verify", request_arg],
        &["--json", "bundle", "replay", request_arg, request_arg],
        &["--json", "--frobnicate"],
    ];
    for args in cases {
        let (_, stdout, stderr) = run(args);
        let value = json_of(&stdout);
        assert_eq!(
            value["schema"], "trust-wp.cli-report.v1",
            "args {args:?} stderr: {stderr}"
        );
        // Exactly one: a second document would leave trailing input.
        assert!(
            stdout.trim_end().ends_with('}'),
            "args {args:?} printed more than the report: {stdout}"
        );
    }
}

// ---------------------------------------------------------------------------
// The engine-facing path, without depending on a built engine
// ---------------------------------------------------------------------------

#[test]
#[timeout(60_000)]
fn dry_run_describes_the_engine_command_it_would_run() {
    let dir = TempDir::new().unwrap();
    let demo = dir.path().join("demo.rs");
    assert_eq!(run(&["example", "-o", demo.to_str().unwrap()]).0, 0);
    let demo_arg = demo.to_str().unwrap();

    let (code, stdout, stderr) = run(&["--dry-run", demo_arg]);
    if code == 0 {
        // An engine was found: the command is printed, and nothing ran.
        assert!(stdout.contains("TRUST_WP_ARGS="), "{stdout}");
        assert!(stdout.contains("--force"), "{stdout}");
        assert!(stdout.contains("--crate-type"), "{stdout}");
    } else {
        // No engine on this machine: say exactly that, and how to fix it.
        assert_eq!(code, 2, "{stderr}");
        assert!(
            stderr.contains("cannot find the trust-wp engine"),
            "{stderr}"
        );
        return;
    }

    // Under --json the command is reported, not echoed: stdout stays one document.
    let value = json_run(&["--json", "--dry-run", demo_arg], 0);
    assert_eq!(value["status"], "dry_run");
    assert_eq!(value["mode"], "file");
    assert!(value["dry_run"]["program"].is_string());
    assert!(value["dry_run"]["args"].as_array().unwrap().len() >= 4);
    assert!(value["dry_run"]["env"]["TRUST_WP_ARGS"]
        .as_str()
        .unwrap()
        .contains("--force"));
}

#[test]
#[timeout(60_000)]
fn an_unusable_engine_is_reported_as_such_in_json() {
    let dir = TempDir::new().unwrap();
    let demo = dir.path().join("demo.rs");
    assert_eq!(run(&["example", "-o", demo.to_str().unwrap()]).0, 0);

    // A plain file passes the "is it there" check and then fails to execute,
    // which is the shape of a driver that cannot run on this machine. (A
    // missing engine cannot be forced in a built tree: discovery finds the
    // real binary next to this test executable.)
    let not_executable = dir.path().join("trust-wp-rustc");
    fs::write(&not_executable, "not an executable").unwrap();

    let mut command = trust_wp();
    command
        .args(["--json", demo.to_str().unwrap()])
        .env("TRUST_WP_RUSTC", &not_executable);
    let output = command.output().expect("trust-wp should run");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let value = json_of(&stdout);
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(value["schema"], "trust-wp.cli-report.v1");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("cannot run the trust-wp engine"),
        "the human path still explains it"
    );
}

// ---------------------------------------------------------------------------
// Colour follows the usual contract
// ---------------------------------------------------------------------------

#[test]
#[timeout(30_000)]
fn color_is_off_when_piped_and_refuses_bad_values() {
    // These tests capture output, so stderr is never a terminal: `auto` must
    // produce plain bytes. Anything else and every piped log fills with escapes.
    let (_, _, stderr) = run(&["--color", "auto", "help"]);
    assert!(
        !stderr.contains('\u{1b}'),
        "auto must not colour a pipe: {stderr:?}"
    );

    let (code, _, stderr) = run(&["--color", "technicolor", "demo.rs"]);
    assert_eq!(code, 3, "{stderr}");
    assert!(stderr.contains("unknown --color value"), "{stderr}");
    assert!(stderr.contains("auto, always, never"), "{stderr}");
}

#[test]
#[timeout(60_000)]
fn engine_output_is_presented_without_the_tool_prefix() {
    // The engine prefixes every human line with `trust-wp: `; the front door
    // strips it, because the user knows which tool they ran.
    let dir = TempDir::new().unwrap();
    let demo = dir.path().join("demo.rs");
    assert_eq!(run(&["example", "-o", demo.to_str().unwrap()]).0, 0);

    let (code, _, stderr) = run(&["--color", "never", demo.to_str().unwrap()]);
    if code == 2 && stderr.contains("cannot find the trust-wp engine") {
        return; // no engine on this machine; the presentation is unit-tested
    }
    assert!(
        !stderr.contains("trust-wp: "),
        "prefix should be stripped: {stderr}"
    );
    assert!(
        !stderr.contains('\u{1b}'),
        "--color never means no escapes: {stderr:?}"
    );
    if code == 0 {
        assert!(
            stderr.contains("verified, "),
            "the counts summary survives: {stderr}"
        );
        assert!(
            stderr.contains("finished in "),
            "the run reports its duration: {stderr}"
        );
    }
}
