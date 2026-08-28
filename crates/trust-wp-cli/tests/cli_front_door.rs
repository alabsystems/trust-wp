// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Process-level tests for the `trust-wp` front-door binary.
//!
//! The in-file `#[cfg(test)] mod tests` in `src/main.rs` covers `parse_cli` and
//! the exit-code decision as pure functions. Nothing there runs the binary, so
//! nothing there can catch a regression in what a user actually sees: the exit
//! code the process returns, which stream each message goes to, or whether the
//! advertised first-run recipe still works.
//!
//! Two tiers:
//!
//! * **Pure** — `--help`, `--version`, `example`, and every rejected command
//!   line. These touch no sysroot, no solver and no engine binary, so they run
//!   everywhere and are the bulk of the file.
//! * **Engine-backed** — the `example` → verify round trip. This needs a built
//!   `trust-wp-rustc` and `libtrust_wp.rlib`, so it reports and returns when
//!   they are absent rather than failing a checkout that has not built them.
//!   (`trust-wp-ay/tests/strict_proof_trust_gate.rs` uses the same shape for
//!   its `AY_BIN` gate.)

use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
};

use ntest::timeout;

/// Exit codes, mirroring `src/main.rs`.
const EXIT_OK: i32 = 0;
const EXIT_VERIFICATION_FAILURE: i32 = 1;
const EXIT_ENCODING_ERROR: i32 = 2;
const EXIT_USAGE: i32 = 3;

fn trust_wp() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_trust-wp"));
    // A developer's shell may point any of these somewhere else; a test must
    // measure the binary, not the shell it happens to run in.
    for var in [
        "TRUST_WP_HOME",
        "TRUST_WP_RUSTC",
        "TRUST_WP_CARGO",
        "TRUST_WP_ARGS",
        "TRUST_WP_RESULT_PROTOCOL",
        "TRUST_WP_LOG",
        "TRUST_WP_DEBUG",
    ] {
        command.env_remove(var);
    }
    command
}

fn run(args: &[&str]) -> Output {
    trust_wp()
        .args(args)
        .output()
        .expect("the trust-wp front door must be spawnable")
}

fn code(output: &Output) -> i32 {
    output.status.code().expect("process must exit normally")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// The cargo profile directory holding the binary under test.
fn artifact_dir() -> PathBuf {
    Path::new(env!("CARGO_BIN_EXE_trust-wp"))
        .parent()
        .expect("the test binary path has a parent directory")
        .to_path_buf()
}

/// A scratch directory unique to one test.
fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust-wp-cli-test-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("scratch directory must be creatable");
    dir
}

// ---------------------------------------------------------------------------
// Pure: no engine, no sysroot, no solver
// ---------------------------------------------------------------------------

/// `--help` and `--version` are the two things that must work on a machine
/// where nothing else is installed, so they must not reach for an engine.
#[test]
#[timeout(30_000)]
fn help_and_version_are_pure_and_go_to_stdout() {
    let help = run(&["--help"]);
    assert_eq!(code(&help), EXIT_OK);
    assert!(stderr(&help).is_empty(), "help must not write to stderr");
    let text = stdout(&help);
    assert!(text.contains("trust-wp example > demo.rs && trust-wp demo.rs"));
    assert!(text.contains("EXIT CODES:"));
    // Every option the help lists must be one the parser accepts; --wide-pointers
    // was listed for a flag the engine hard-errors on.
    assert!(!text.contains("--wide-pointers"));

    let version = run(&["--version"]);
    assert_eq!(code(&version), EXIT_OK);
    assert!(stdout(&version).starts_with("trust-wp "));
    assert!(stderr(&version).is_empty());

    // Help wins over anything else on the line, and still touches nothing.
    let mixed = run(&["missing.rs", "--filter", "f", "--help"]);
    assert_eq!(code(&mixed), EXIT_OK);
}

/// The recipe the help prints as the first thing to try has to produce a file
/// that parses as the contracts it advertises.
#[test]
#[timeout(30_000)]
fn example_writes_a_contracted_file_to_stdout_and_to_a_path() {
    let piped = run(&["example"]);
    assert_eq!(code(&piped), EXIT_OK);
    let source = stdout(&piped);
    assert!(source.contains("use trust_wp::{ensures, requires};"));
    assert!(source.contains("#[requires(x > 0)]"));
    assert!(source.contains("#[ensures(result > x)]"));

    let dir = scratch("example");
    let path = dir.join("demo.rs");
    let written = run(&["example", "-o", path.to_str().unwrap()]);
    assert_eq!(code(&written), EXIT_OK);
    // The note about where it landed is progress output, not the artifact.
    assert!(stdout(&written).is_empty());
    assert!(stderr(&written).contains("wrote"));
    assert_eq!(
        std::fs::read_to_string(&path).expect("example file must exist"),
        source
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// `example` and `doctor` run no other tool, so a `--` tail has nowhere to go.
/// Swallowing it would contradict the help's "refused, never ignored".
#[test]
#[timeout(30_000)]
fn verbs_reject_arguments_they_cannot_honour() {
    let example = run(&["example", "--", "--cfg", "foo"]);
    assert_eq!(code(&example), EXIT_USAGE);
    assert!(stderr(&example).contains("nowhere to go"));

    let doctor = run(&["doctor", "extra"]);
    assert_eq!(code(&doctor), EXIT_USAGE);
    assert!(stderr(&doctor).contains("takes no arguments"));

    let unknown_example_flag = run(&["example", "--nope"]);
    assert_eq!(code(&unknown_example_flag), EXIT_USAGE);
}

/// Every rejected command line exits 3 and says what to type instead. The
/// engine is never consulted, so these hold on a bare checkout.
#[test]
#[timeout(30_000)]
fn bad_command_lines_are_refused_with_the_alternative_named() {
    let cases: &[(&[&str], &str)] = &[
        (&["--frobnicate"], "unrecognized option"),
        (&["--unwind", "5"], "#[invariant"),
        (&["--verify-fn", "increment"], "--filter"),
        (&["--solver", "z3"], "there is no solver switch"),
        // `--json` is implemented now, so the flag other verifiers spell
        // `--format` is what points at it.
        (&["--format", "json"], "`--json`"),
        // The engine raises a fatal diagnostic on this one; accepting it here
        // would be accept-and-fail.
        (&["--wide-pointers"], "not implemented"),
        (&["a.rs", "b.rs"], "one file per run"),
        (&["--timeout"], "needs a value"),
        (&["--timeout", "soon"], "positive whole number"),
        (&["--timeout=0"], "positive whole number"),
        (&["--track", "sideways"], "valid levels are"),
        (&["--edition", "1999"], "valid editions are"),
        (&["--edition", "2021"], "single-file mode only"),
        (&["Cargo.toml"], "expected a `.rs` file"),
    ];
    for (args, expected) in cases {
        let output = run(args);
        assert_eq!(
            code(&output),
            EXIT_USAGE,
            "`trust-wp {}` should exit {EXIT_USAGE}; stderr was:\n{}",
            args.join(" "),
            stderr(&output)
        );
        assert!(
            stderr(&output).contains(expected),
            "`trust-wp {}` should mention {expected:?}; stderr was:\n{}",
            args.join(" "),
            stderr(&output)
        );
    }
}

/// A value that is plainly the source file is a forgotten flag value, and
/// taking it would silently verify the surrounding crate instead of the file.
#[test]
#[timeout(30_000)]
fn a_forgotten_flag_value_does_not_swallow_the_source_file() {
    let dir = scratch("forgotten");
    let path = dir.join("demo.rs");
    std::fs::write(&path, "pub fn f() {}\n").expect("scratch file must be writable");

    let output = trust_wp()
        .args(["--filter", path.to_str().unwrap()])
        .output()
        .expect("spawnable");
    assert_eq!(code(&output), EXIT_USAGE);
    assert!(stderr(&output).contains("was given the source file"));
    let _ = std::fs::remove_dir_all(&dir);
}

/// A file that does not exist is a command-line error, not a proof failure,
/// and the message points at something the reader can run right now.
#[test]
#[timeout(30_000)]
fn a_missing_file_is_a_usage_error_with_a_way_forward() {
    let output = run(&["definitely-not-here.rs"]);
    assert_eq!(code(&output), EXIT_USAGE);
    let text = stderr(&output);
    assert!(text.contains("cannot read"));
    assert!(text.contains("trust-wp example > demo.rs"));
}

/// `doctor` is a readiness report: it always writes its findings to stdout, and
/// its exit code states whether the tool can actually run.
#[test]
#[timeout(120_000)]
fn doctor_reports_on_stdout_and_states_readiness_in_its_exit_code() {
    let output = run(&["doctor"]);
    let report = stdout(&output);
    assert!(report.starts_with("trust-wp "));
    for row in ["checkout", "trust-wp-rustc", "trust_wp", "active sysroot"] {
        assert!(
            report.contains(row),
            "doctor should report {row}:\n{report}"
        );
    }
    match code(&output) {
        EXIT_OK => assert!(report.contains("ready. try:")),
        EXIT_ENCODING_ERROR => assert!(report.contains("not ready")),
        other => panic!("doctor must exit 0 or 2, got {other}:\n{report}"),
    }
}

/// `--dry-run` must print a command a shell reproduces exactly. Collapsing the
/// newline-delimited engine-argument block to spaces changes how the driver
/// parses it, so the printed command would not stand for the real one.
#[test]
#[timeout(60_000)]
fn dry_run_prints_a_faithful_shell_command() {
    if !engine_present() {
        eprintln!("skipping: no trust-wp-rustc next to the binary under test");
        return;
    }
    let dir = scratch("dryrun");
    let path = dir.join("demo.rs");
    std::fs::write(&path, "pub fn f() {}\n").expect("scratch file must be writable");

    let output = trust_wp()
        .args([
            path.to_str().unwrap(),
            "--emit-smt-dir",
            "/tmp/a directory with spaces",
            "--dry-run",
        ])
        .output()
        .expect("spawnable");
    assert_eq!(code(&output), EXIT_OK);
    let line = stdout(&output);
    assert!(line.contains("TRUST_WP_ARGS='--force\n--emit-smt-dir\n/tmp/a directory with spaces'"));
    assert!(line.contains("TRUST_WP_RESULT_PROTOCOL=1"));
    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Engine-backed
// ---------------------------------------------------------------------------

fn engine_present() -> bool {
    artifact_dir().join("trust-wp-rustc").is_file()
}

fn contract_crate_present() -> bool {
    artifact_dir().join("libtrust_wp.rlib").is_file()
}

/// The advertised first run, end to end: write the sample, verify it, get 0.
///
/// This is the one claim the whole front door is built around — `--help` prints
/// it as the thing to try first — so it is worth a real process.
#[test]
#[timeout(300_000)]
fn the_advertised_first_run_verifies_and_exits_zero() {
    if !engine_present() || !contract_crate_present() {
        eprintln!(
            "skipping: needs a built engine and contract crate in {}",
            artifact_dir().display()
        );
        return;
    }
    let dir = scratch("firstrun");
    let path = dir.join("demo.rs");
    assert_eq!(
        code(&run(&["example", "-o", path.to_str().unwrap()])),
        EXIT_OK
    );

    let output = run(&[path.to_str().unwrap()]);
    let report = stderr(&output);
    assert_eq!(
        code(&output),
        EXIT_OK,
        "the sample `trust-wp example` writes must verify:\n{report}"
    );
    assert!(
        report.contains("2 verified, 0 failed, 0 errors"),
        "{report}"
    );
    // Machine output stays off unless asked for.
    assert!(!report.contains("TRUST_WP_RESULT:"), "{report}");
    assert!(!report.contains("TRUST_WP_DIAGNOSTIC:"), "{report}");
    // Warnings that are artifacts of compiling a lone file as a library are
    // not the user's business.
    assert!(!report.contains("is never used"), "{report}");
    assert!(!report.contains("stmt_expr_attributes"), "{report}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A false postcondition exits 1 and hands back the input that breaks it —
/// and the counterexample names the user's variables, not the encoder's.
#[test]
#[timeout(300_000)]
fn a_false_contract_exits_one_with_a_readable_counterexample() {
    if !engine_present() || !contract_crate_present() {
        eprintln!("skipping: needs a built engine and contract crate");
        return;
    }
    let dir = scratch("counterexample");
    let path = dir.join("wrong.rs");
    std::fs::write(
        &path,
        "use trust_wp::{ensures, requires};\n\
         #[requires(x > 0)]\n\
         #[ensures(result > x)]\n\
         pub fn decrement(x: i32) -> i32 { x - 1 }\n",
    )
    .expect("scratch file must be writable");

    let output = run(&[path.to_str().unwrap()]);
    let report = stderr(&output);
    assert_eq!(code(&output), EXIT_VERIFICATION_FAILURE, "{report}");
    assert!(report.contains("FAILED"), "{report}");
    assert!(report.contains("counterexample:"), "{report}");
    assert!(report.contains("x ="), "{report}");
    assert!(!report.contains("__trust_wp"), "{report}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// Fail closed. A file with no contracts proved nothing, and a verifier that
/// reports success for it is worse than no verifier.
#[test]
#[timeout(300_000)]
fn a_run_that_proves_nothing_does_not_exit_zero() {
    if !engine_present() {
        eprintln!("skipping: needs a built engine");
        return;
    }
    let dir = scratch("empty");
    let path = dir.join("bare.rs");
    std::fs::write(&path, "pub fn untouched(x: i32) -> i32 { x }\n")
        .expect("scratch file must be writable");

    let output = run(&[path.to_str().unwrap()]);
    let report = stderr(&output);
    assert_eq!(code(&output), EXIT_ENCODING_ERROR, "{report}");
    assert!(report.contains("nothing was verified"), "{report}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// ...but a file whose only obligations are `proof_assert!` HAS proved
/// something, and must not be swept up by the fail-closed rule.
///
/// The wire record carries a failure counter for `proof_assert` and, until this
/// was fixed, no success counter — so a run that proved every assertion emitted
/// an all-zero summary and looked exactly like a run that examined nothing.
#[test]
#[timeout(300_000)]
fn a_proof_assert_only_run_still_exits_zero() {
    if !engine_present() || !contract_crate_present() {
        eprintln!("skipping: needs a built engine and contract crate");
        return;
    }
    let dir = scratch("proofassert");
    let path = dir.join("pa.rs");
    std::fs::write(
        &path,
        "use trust_wp::proof_assert;\n\
         pub fn f(x: i32) -> i32 {\n\
         \x20   let y = x;\n\
         \x20   proof_assert!(y == x);\n\
         \x20   y\n\
         }\n",
    )
    .expect("scratch file must be writable");

    let output = run(&[path.to_str().unwrap()]);
    let report = stderr(&output);
    assert!(report.contains("proof_assert"), "{report}");
    assert_eq!(code(&output), EXIT_OK, "{report}");
    assert!(!report.contains("nothing was verified"), "{report}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// The emitted SMT-LIB2 must declare every symbol it goes on to use, or it is
/// text no solver will read — which defeats the point of the flag.
#[test]
#[timeout(300_000)]
fn emitted_smt_declares_every_symbol_it_mentions() {
    if !engine_present() || !contract_crate_present() {
        eprintln!("skipping: needs a built engine and contract crate");
        return;
    }
    let dir = scratch("emitsmt");
    let path = dir.join("demo.rs");
    assert_eq!(
        code(&run(&["example", "-o", path.to_str().unwrap()])),
        EXIT_OK
    );

    let output = run(&[
        "--emit-smt",
        "--filter",
        "increment",
        path.to_str().unwrap(),
    ]);
    assert_eq!(code(&output), EXIT_OK, "{}", stderr(&output));
    let query = stdout(&output);
    assert!(query.contains("(check-sat)"), "{query}");

    // `x@` (the mathematical view of an i32 parameter) is what the injected
    // range preconditions constrain. It used to be asserted about but never
    // declared, which made the query unparseable.
    assert!(query.contains("x_view"), "{query}");
    // Naming every offender at once beats failing on whichever happens to be
    // first. (Moving this file into a linted crate surfaced the old
    // `for … { panic!() }`, which never loops.)
    let undeclared = undeclared_symbols(&query);
    assert!(
        undeclared.is_empty(),
        "emitted SMT uses {undeclared:?} without declaring them:\n{query}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// Every symbol the query mentions that nothing declares or binds.
///
/// Syntactic, and deliberately biased toward *silence*: a name that any
/// `declare-*`, `let` or quantifier introduces anywhere in the query counts as
/// known, wherever it is used. That cannot prove a query well-scoped, but it
/// does catch the failure this test exists for — a symbol the printer emits
/// that the declaration block never mentions — without inventing failures on
/// binder-introduced names.
fn undeclared_symbols(query: &str) -> Vec<String> {
    // SMT-LIB core and Ints, plus the two sorts this emitter declares.
    const BUILTINS: &[&str] = &[
        "set-logic",
        "declare-const",
        "declare-fun",
        "declare-sort",
        "define-fun",
        "assert",
        "check-sat",
        "get-model",
        "exit",
        "not",
        "and",
        "or",
        "=>",
        "xor",
        "=",
        "distinct",
        "ite",
        "let",
        "forall",
        "exists",
        "+",
        "-",
        "*",
        "/",
        "div",
        "mod",
        "abs",
        "<",
        "<=",
        ">",
        ">=",
        "Int",
        "Bool",
        "Real",
        "Seq",
        "true",
        "false",
        "!",
        "ALL",
    ];

    let mut known: Vec<String> = Vec::new();
    for line in query.lines() {
        let line = line.trim();
        for form in ["(declare-const ", "(declare-fun ", "(declare-sort "] {
            if let Some(rest) = line.strip_prefix(form) {
                if let Some(name) = rest.split_whitespace().next() {
                    known.push(name.to_string());
                }
            }
        }
        // `(let ((name value) ...))` and `(forall ((name Sort) ...) ...)` both
        // introduce names as the first token after a doubled open paren.
        let mut rest = line;
        while let Some(at) = rest.find("((") {
            rest = &rest[at + 2..];
            if let Some(name) = rest
                .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
                .next()
            {
                if !name.is_empty() {
                    known.push(name.to_string());
                }
            }
        }
        // ...and each subsequent binding in the same list: `) (name ...`.
        for chunk in line.split(") (").skip(1) {
            if let Some(name) = chunk.split(|c: char| c.is_whitespace() || c == ')').next() {
                if !name.is_empty() {
                    known.push(name.to_string());
                }
            }
        }
    }

    let mut missing = Vec::new();
    for line in query.lines() {
        let line = line.trim();
        if line.starts_with(';') || line.starts_with("(declare") || line.starts_with("(set-") {
            continue;
        }
        for token in line.replace(['(', ')'], " ").split_whitespace() {
            let numeric = !token.is_empty()
                && token
                    .chars()
                    .all(|c| c.is_ascii_digit() || c == '.' || c == '#' || c.is_ascii_hexdigit());
            if numeric
                || BUILTINS.contains(&token)
                || known.iter().any(|name| name == token)
                || missing.iter().any(|name| name == token)
            {
                continue;
            }
            missing.push(token.to_string());
        }
    }
    missing
}

/// The checker has to notice the defect it exists for, and stay quiet on a
/// query that is fine — including one with binders, whose names nothing
/// declares.
#[test]
fn undeclared_symbols_finds_the_gap_and_tolerates_binders() {
    let broken = "(declare-const x Int)\n(assert (>= x_view 0))\n(check-sat)\n";
    assert_eq!(undeclared_symbols(broken), vec!["x_view".to_string()]);

    let sound = "(declare-const n Int)\n\
                 (assert (forall ((k Int)) (>= k n)))\n\
                 (assert (= n (let ((_tw_a 2)) _tw_a)))\n\
                 (check-sat)\n";
    assert!(
        undeclared_symbols(sound).is_empty(),
        "{:?}",
        undeclared_symbols(sound)
    );
}
