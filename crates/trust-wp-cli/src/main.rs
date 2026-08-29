// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub,
    // `tcx.get_all_attrs` is deprecated in favor of `find_attr!`, but trust-wp
    // reads CUSTOM proof-marker attributes (#[logic]/#[trusted]/...) that are
    // not parsed built-ins -- exactly the use the deprecation note sanctions.
    deprecated
)]
// A front-door CLI is mostly help text and argument plumbing: the long
// functions below are printers and dispatchers, not logic. Matching on
// `Option` with a multi-line "here is how to fix it" arm reads better than
// `if let`/`else`, and the stderr relay's symptom flags are plain booleans —
// the same allowances `src/rustc_driver.rs` makes.
#![allow(
    clippy::too_many_lines,
    clippy::single_match_else,
    clippy::struct_excessive_bools
)]

//! `trust-wp` — the front door to the trust-wp weakest-precondition verifier.
//!
//! **This binary contains no verification logic.** Every proof obligation is
//! produced and discharged by machinery that already exists in this workspace;
//! `trust-wp` only picks the right engine, hands it the right arguments, and
//! turns its structured result into an exit code:
//!
//! * **crate mode** (`trust-wp` in a directory with a `Cargo.toml`) runs
//!   `cargo-trust-wp`, which sets `RUSTC_WRAPPER` and shells `cargo check`.
//! * **single-file mode** (`trust-wp file.rs`) runs `trust-wp-rustc` — the
//!   rustc driver in this very crate (`src/rustc_driver.rs`) — directly, the
//!   way `scripts/run-trust-wp-rustc.sh` does, so no Cargo project is needed.
//! * the exit code comes from the engine's own wire protocol,
//!   [`trust_wp_core::result_protocol`], not from re-derived local judgement.
//!
//! `--help`, `--version` and `example` are pure: they touch no sysroot, no
//! solver and no network, and work on a machine where nothing is installed.

mod bundle;
mod completions;
mod contract;
mod man;
mod report;
mod style;

use std::{
    env,
    ffi::OsStr,
    fs,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
    time::Instant,
};

pub(crate) use bundle::BundleCommand;
pub(crate) use contract::ContractCommand;
use trust_wp_core::{
    result_protocol::{
        StructuredVerificationResult, VerificationDiagnosticRecord, DIAGNOSTIC_WIRE_PREFIX,
        RESULT_PROTOCOL_ENV, WIRE_PREFIX,
    },
    tracing_init::trust_wp_log_help,
};

/// `println!` that treats a closed stdout as the end of output rather than a
/// panic.
///
/// Rust ignores `SIGPIPE`, so `trust-wp --help | head -2` reaches a `println!`
/// whose write fails with `EPIPE` and aborts with "failed printing to stdout"
/// and status 101 — an internal-error code for a reader that simply stopped
/// reading. Stopping quietly is what every other Unix tool does.
/// Set once stdout stops accepting writes, so later `out!` calls are cheap
/// no-ops instead of repeated failures.
static STDOUT_CLOSED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

macro_rules! out {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        use std::sync::atomic::Ordering;
        if !STDOUT_CLOSED.load(Ordering::Relaxed) {
            let mut stdout = std::io::stdout().lock();
            if writeln!(stdout, $($arg)*).is_err() {
                // Stop writing, but let the command finish and report its own
                // result: `trust-wp doctor | head` must still exit 2 when the
                // tool is not ready. Exiting here would answer "ready" on
                // behalf of a report the reader truncated.
                STDOUT_CLOSED.store(true, Ordering::Relaxed);
            }
        }
    }};
}

/// All contracts proved.
const EXIT_OK: i32 = 0;
/// At least one contract failed (a counterexample exists).
const EXIT_VERIFICATION_FAILURE: i32 = 1;
/// Encoding error, solver error, or a soundness gap the engine refuses to hide.
const EXIT_ENCODING_ERROR: i32 = 2;
/// Contract parse error — and, matching `cargo-trust-wp`, CLI misuse.
const EXIT_USAGE: i32 = 3;

/// The rustc driver that does the real work.
///
/// Two names again: the Trust-native `trust-wp-driver` and the back-compat
/// alias `trust-wp-rustc`. `DRIVER_BIN` is the alias because that is the name
/// `cargo-trust-wp`, `scripts/run-trust-wp-rustc.sh` and `$TRUST_WP_RUSTC` all
/// resolve, so it is the one a fix line should name.
pub(crate) const DRIVER_BIN: &str = "trust-wp-rustc";
/// Every name the driver ships under, searched in order per location.
pub(crate) const DRIVER_BINS: [&str; 2] = [DRIVER_BIN, "trust-wp-driver"];
/// The cargo front end that does the real work for whole crates.
///
/// The package ships two identical bins: the Trust-native primary
/// `targo-trust-wp` and the back-compat alias `cargo-trust-wp`. Look for the
/// primary first so a Trust bundle that only exposes the native name still
/// resolves, and fall back to the alias for older checkouts.
pub(crate) const CARGO_FRONT_BIN: &str = "targo-trust-wp";
/// Back-compat spelling of [`CARGO_FRONT_BIN`], searched second.
const CARGO_FRONT_BIN_ALIAS: &str = "cargo-trust-wp";

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    let code = run(&args);
    ExitCode::from(u8::try_from(code).unwrap_or(101))
}

fn run(args: &[String]) -> i32 {
    let cli = match parse_cli(args) {
        Ok(cli) => cli,
        Err(err) => {
            err.report();
            // `--json` promises exactly one report on stdout on every exit the
            // CLI itself returns — a rejected command line included, so a CI
            // parser never gets nothing.
            if wants_json(args) {
                report::print_json(&report::usage_report(&err));
            }
            return EXIT_USAGE;
        }
    };

    match cli.mode.clone() {
        Mode::Help { topic, brief } => {
            out!("{}", render_help(topic.as_deref(), brief));
            EXIT_OK
        }
        Mode::Version => {
            if cli.json {
                report::print_json(&report::version_report());
            } else {
                out!("{}", render_version());
            }
            EXIT_OK
        }
        Mode::Example { out } => write_example(out.as_deref()),
        Mode::Doctor => run_doctor(cli.json),
        Mode::File(path) => run_single_file(&cli, &path),
        Mode::Crate => run_crate(&cli),
        Mode::Contract(command) => contract::run(&command, cli.json),
        Mode::Bundle(command) => bundle::run(&command, cli.json),
        Mode::Result { input } => report::decode_transcript(input.as_deref(), cli.json),
        Mode::Man => {
            out!("{}", man::render());
            EXIT_OK
        }
        Mode::Completions { shell } => {
            // The script goes to stdout so it can be redirected into the
            // shell's completion directory; nothing else may share it.
            out!(
                "{}",
                completions::render(&shell).expect("shell validated at parse time")
            );
            EXIT_OK
        }
    }
}

// ---------------------------------------------------------------------------
// Command line
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Mode {
    /// `--help`, or `help [TOPIC]` for one verb's page.
    Help {
        topic: Option<String>,
        /// `-h` wants the summary; `--help` and `help` want the full page.
        /// This is the split rustc and cargo use, and the reason is the same:
        /// the full page is 90-odd lines, which scrolls a first-time `-h` off
        /// the top of an 80x24 terminal.
        brief: bool,
    },
    Version,
    Example {
        out: Option<PathBuf>,
    },
    Doctor,
    File(PathBuf),
    Crate,
    /// Parse a contract expression, or emit a weakest-precondition VC.
    Contract(ContractCommand),
    /// Verify, validate or replay a `trust-wp.verify-bundle.v1` request.
    Bundle(BundleCommand),
    /// Decode a saved result-protocol transcript.
    Result {
        input: Option<PathBuf>,
    },
    /// Print a shell completion script.
    Completions {
        shell: String,
    },
    /// Print the roff manual page.
    Man,
}

/// Verbs that name a command rather than a file to verify.
const COMMAND_WORDS: [&str; 10] = [
    "verify",
    "contract",
    "bundle",
    "result",
    "doctor",
    "example",
    "completions",
    "man",
    "help",
    "version",
];

/// A parsed `trust-wp` invocation.
#[derive(Debug, Clone)]
struct Cli {
    mode: Mode,
    /// Verifier options, already normalized to the engine's own spelling.
    /// Handed to `trust-wp-rustc` through `TRUST_WP_ARGS` and to
    /// `cargo-trust-wp` as ordinary flags — both accept exactly these forms.
    engine_args: Vec<String>,
    /// Everything after `--`: given to cargo (crate mode) or rustc
    /// (single-file mode) untouched.
    passthrough: Vec<String>,
    /// Wrapper-local policy (`cargo-trust-wp` implements it the same way):
    /// promote dropped-obligation warnings to an error exit.
    strict_obligations: bool,
    /// Single-file mode only; a crate takes its edition from its manifest.
    edition: String,
    /// Print the exact engine command instead of running it.
    dry_run: bool,
    /// Print one `trust-wp.cli-report.v1` document on stdout instead of the
    /// human summary. Human output stays on stderr; exit codes are unchanged.
    json: bool,
    /// When to colourise the engine's output.
    color: style::ColorChoice,
    /// Print only what went wrong, plus the summary.
    quiet: bool,
}

impl Cli {
    fn with_mode(mode: Mode) -> Self {
        Self {
            mode,
            engine_args: Vec::new(),
            passthrough: Vec::new(),
            strict_obligations: false,
            edition: "2021".to_string(),
            dry_run: false,
            json: false,
            color: style::ColorChoice::default(),
            quiet: false,
        }
    }

    /// True when the run is expected to produce a verification verdict.
    ///
    /// Emit-only and no-verify runs legitimately produce none, so the
    /// fail-closed "no summary" check must not fire for them.
    ///
    /// `--stop-after-analysis` is deliberately NOT in this set: it tells rustc
    /// to stop before codegen, *after* trust-wp has already verified
    /// (`callbacks/mod.rs` returns `Compilation::Stop` only once verification
    /// has run). Treating it as analysis-only would silence the fail-closed
    /// check on a run that does produce a verdict.
    fn verify_mode(&self) -> bool {
        let analysis_only = self.engine_args.iter().any(|a| a == "--no-verify");
        let emit_only = self
            .engine_args
            .iter()
            .any(|a| a == "--emit-smt" || a == "--emit-smt-dir")
            && !self.engine_args.iter().any(|a| a == "--verify");
        !analysis_only && !emit_only
    }
}

/// A CLI misuse, with the alternative spelled out. Never silently ignored.
#[derive(Debug)]
struct UsageError {
    message: String,
    help: Vec<String>,
}

impl UsageError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            help: Vec::new(),
        }
    }

    fn with_help(mut self, line: impl Into<String>) -> Self {
        self.help.push(line.into());
        self
    }

    fn report(&self) {
        eprintln!("error: {}", self.message);
        for line in &self.help {
            eprintln!("help: {line}");
        }
    }
}

/// Options users of comparable Rust verifiers reach for that trust-wp does not
/// have. Rule: name the flag, name the alternative, exit non-zero — never
/// accept-and-ignore.
const EXIT_CODES: &str = "EXIT CODES:
    0    everything verified
    1    at least one contract failed (a counterexample exists)
    2    encoding/solver error, soundness gap, or the engine could not run
    3    contract parse error, invalid input, or bad command line
    101  internal error (panic)";

/// Editions `rustc --edition` accepts. Checked here so a typo is a command-line
/// error with the list attached rather than a compiler error about a flag the
/// user never typed.
const EDITIONS: [&str; 4] = ["2015", "2018", "2021", "2024"];

const REJECTED_FLAGS: &[(&str, &str)] = &[
    (
        "--verify-fn",
        "trust-wp selects functions with `--filter <NAME>`",
    ),
    (
        "--function",
        "trust-wp selects functions with `--filter <NAME>`",
    ),
    (
        "--focus-on-function",
        "trust-wp selects functions with `--filter <NAME>`",
    ),
    (
        "--harness",
        "trust-wp proves the contracts written on the functions themselves; there are no harnesses. Narrow a run with `--filter <NAME>`",
    ),
    (
        "--unwind",
        "trust-wp is a deductive (unbounded) verifier, so loops take `#[invariant(...)]` (and `#[variant(...)]` for termination) rather than an unwind bound",
    ),
    (
        "--tests",
        "trust-wp proves contracts, it does not run tests; use `cargo test` for those",
    ),
    (
        "--solver",
        "verification conditions are discharged on the built-in `ay` solver; there is no solver switch. Inspect the queries with `--emit-smt` or `--emit-smt-dir <DIR>`",
    ),
    (
        "--backend",
        "trust-wp has one backend (`ay`); use `--emit-smt` / `--emit-smt-dir <DIR>` to see what it is asked",
    ),
    (
        "--output-dir",
        "SMT artifacts are written with `--emit-smt-dir <DIR>`",
    ),
    (
        "--format",
        "machine-readable output is `--json` (one trust-wp.cli-report.v1 document on stdout); there are no other formats",
    ),
    // Accepting this and letting the engine hard-error two seconds later
    // (callbacks/mod.rs raises a fatal diagnostic and stops) is the
    // accept-and-fail shape this table exists to prevent.
    (
        "--wide-pointers",
        "wide-pointer support is not implemented (tracking issue #419); there is nothing this flag can turn on yet",
    ),
];

/// True when `--json` appears in the front segment (before any bare `--`).
///
/// Read separately from [`parse_cli`] so a rejected command line can still be
/// reported as JSON.
fn wants_json(args: &[String]) -> bool {
    let (front, _) = split_passthrough(args);
    front.iter().any(|a| a == "--json")
}

fn parse_cli(args: &[String]) -> Result<Cli, UsageError> {
    let (front, passthrough) = split_passthrough(args);

    // `--json` is global: it may appear anywhere before `--`.
    let json = front.iter().any(|a| a == "--json");
    let front: Vec<String> = front.into_iter().filter(|a| a != "--json").collect();

    if front.iter().any(|a| a == "-h" || a == "--help") {
        let topic = front
            .first()
            .filter(|word| COMMAND_WORDS.contains(&word.as_str()) && *word != "help")
            .cloned();
        let brief = topic.is_none() && !front.iter().any(|a| a == "--help");
        return finish(Cli::with_mode(Mode::Help { topic, brief }), json);
    }
    if front.iter().any(|a| a == "-V" || a == "--version") {
        return finish(Cli::with_mode(Mode::Version), json);
    }

    match front.first().map(String::as_str) {
        Some("help") => {
            let topic = match front.get(1) {
                None => None,
                Some(word) if COMMAND_WORDS.contains(&word.as_str()) => Some(word.clone()),
                Some(other) => {
                    return Err(UsageError::new(format!("no help topic `{other}`"))
                        .with_help(format!("topics: {}", COMMAND_WORDS.join(", "))));
                }
            };
            if let Some(extra) = front.get(2) {
                return Err(UsageError::new(format!(
                    "`trust-wp help` takes one topic, got `{extra}` as well"
                )));
            }
            reject_passthrough("help", &passthrough)?;
            return finish(
                Cli::with_mode(Mode::Help {
                    topic,
                    brief: false,
                }),
                json,
            );
        }
        Some("version") => {
            if let Some(extra) = front.get(1) {
                return Err(UsageError::new(format!(
                    "`trust-wp version` takes no arguments, got `{extra}`"
                )));
            }
            reject_passthrough("version", &passthrough)?;
            return finish(Cli::with_mode(Mode::Version), json);
        }
        Some("contract") => {
            reject_passthrough("contract", &passthrough)?;
            let command = contract::parse(&front[1..])?;
            return finish(Cli::with_mode(Mode::Contract(command)), json);
        }
        Some("bundle") => {
            reject_passthrough("bundle", &passthrough)?;
            let command = bundle::parse(&front[1..])?;
            return finish(Cli::with_mode(Mode::Bundle(command)), json);
        }
        Some("result") => {
            reject_passthrough("result", &passthrough)?;
            let input = parse_result_input(&front[1..])?;
            return finish(Cli::with_mode(Mode::Result { input }), json);
        }
        Some("verify") => {
            // The explicit spelling of the two compat forms below.
            let mut cli = parse_verify(&front[1..], passthrough.clone())?;
            cli.json = json;
            return finish(cli, json);
        }
        // A bare word that carries no extension and names nothing on disk was
        // meant as a verb, so say which verbs exist. Anything with an
        // extension (or an actual path) is a file the user meant to verify,
        // and `canonical_source` gives the better "expected a `.rs` file".
        Some(word)
            if !word.starts_with('-')
                && !COMMAND_WORDS.contains(&word)
                && Path::new(word).extension().is_none()
                && !Path::new(word).exists() =>
        {
            return Err(UsageError::new(format!("unknown command `{word}`"))
                .with_help(format!("commands: {}", COMMAND_WORDS.join(", ")))
                .with_help(
                    "to verify a file, name it with its `.rs` extension: \
                     `trust-wp demo.rs`; to verify the crate here, run \
                     `trust-wp` with no command",
                ));
        }
        Some("example") => {
            // `--` exists to forward options to cargo or rustc; neither runs
            // here, so anything after it would be silently dropped. The help
            // promises unknown options are refused, never ignored.
            reject_passthrough("example", &passthrough)?;
            return finish(parse_example(&front[1..])?, json);
        }
        Some("doctor") => {
            if let Some(extra) = front.get(1) {
                return Err(UsageError::new(format!(
                    "`trust-wp doctor` takes no arguments, got `{extra}`"
                )));
            }
            reject_passthrough("doctor", &passthrough)?;
            return finish(Cli::with_mode(Mode::Doctor), json);
        }
        Some("man") => {
            if let Some(extra) = front.get(1) {
                return Err(UsageError::new(format!(
                    "`trust-wp man` takes no arguments, got `{extra}`"
                ))
                .with_help("`trust-wp man > trust-wp.1` writes the page"));
            }
            reject_passthrough("man", &passthrough)?;
            return finish(Cli::with_mode(Mode::Man), json);
        }
        Some("completions") => {
            let Some(shell) = front.get(1) else {
                return Err(UsageError::new("`trust-wp completions` needs a shell")
                    .with_help(format!("one of: {}", completions::SHELLS.join(", "))));
            };
            if completions::render(shell).is_none() {
                return Err(
                    UsageError::new(format!("no completion script for `{shell}`")).with_help(
                        format!("supported shells: {}", completions::SHELLS.join(", ")),
                    ),
                );
            }
            if let Some(extra) = front.get(2) {
                return Err(UsageError::new(format!(
                    "`trust-wp completions` takes one shell, got `{extra}` as well"
                )));
            }
            reject_passthrough("completions", &passthrough)?;
            return finish(
                Cli::with_mode(Mode::Completions {
                    shell: shell.clone(),
                }),
                json,
            );
        }
        _ => {}
    }

    let mut cli = parse_verify(&front, passthrough.clone())?;
    cli.json = json;
    finish(cli, json)
}

/// Cross-cutting rules that apply once the verb is known.
fn finish(mut cli: Cli, json: bool) -> Result<Cli, UsageError> {
    cli.json = json;
    if json {
        match &cli.mode {
            Mode::Help { .. } => {
                return Err(UsageError::new("`--json` does not apply to help")
                    .with_help("help is text; every other command accepts `--json`"));
            }
            Mode::Completions { .. } | Mode::Man => {
                return Err(
                    UsageError::new("`--json` does not apply to `completions` or `man`")
                        .with_help("both write a document to stdout, not a report"),
                );
            }
            Mode::Example { .. } | Mode::Bundle(BundleCommand::Example { .. }) => {
                return Err(UsageError::new("`--json` does not apply to `example`")
                    .with_help("`example` writes source to start from, not a report"));
            }
            _ if cli.engine_args.iter().any(|a| a == "--emit-smt") => {
                return Err(UsageError::new(
                    "`--json` cannot be combined with `--emit-smt`: both want stdout",
                )
                .with_help("write the queries to files instead: `--emit-smt-dir <DIR> --json`"));
            }
            _ => {}
        }
    }
    Ok(cli)
}

/// The two compat forms and the explicit `verify` verb share this body.
fn parse_verify(front: &[String], passthrough: Vec<String>) -> Result<Cli, UsageError> {
    let mut cli = Cli::with_mode(Mode::Crate);
    cli.passthrough = passthrough;

    let mut file: Option<PathBuf> = None;
    let mut edition_given = false;
    let mut i = 0;
    while i < front.len() {
        let arg = front[i].clone();
        let (name, inline) = split_inline_value(&arg);

        if let Some((flag, alternative)) = REJECTED_FLAGS.iter().find(|(f, _)| *f == name) {
            return Err(
                UsageError::new(format!("`{flag}` is not a trust-wp option"))
                    .with_help((*alternative).to_string())
                    .with_help("run `trust-wp --help` for the full option list"),
            );
        }

        match name {
            // --- verifier options, forwarded verbatim to the engine ---
            "-v" | "-vv" | "--verbose" => cli.engine_args.push("--verbose".to_string()),
            "--emit-smt" => cli.engine_args.push("--emit-smt".to_string()),
            "--strict-axioms" => cli.engine_args.push("--strict-axioms".to_string()),
            "--strict-trust" => cli.engine_args.push("--strict-trust".to_string()),
            "--no-strict-trust" => cli.engine_args.push("--no-strict-trust".to_string()),
            "--stop-after-analysis" => cli.engine_args.push("--stop-after-analysis".to_string()),
            "--verify" => cli.engine_args.push("--verify".to_string()),
            "--no-verify" => cli.engine_args.push("--no-verify".to_string()),
            "--filter" | "--emit-smt-dir" => {
                let value = take_value(name, inline, front, &mut i)?;
                cli.engine_args.push(name.to_string());
                cli.engine_args.push(value);
            }
            "--timeout" => {
                let value = take_value(name, inline, front, &mut i)?;
                // The engine parses this with `str::parse` and silently keeps
                // its 60s default when the parse fails, so a typo would look
                // like it took effect. Refuse it here instead.
                if value.parse::<u64>().map_or(true, |secs| secs == 0) {
                    return Err(UsageError::new(format!(
                        "`--timeout` wants a positive whole number of seconds, got `{value}`"
                    ))
                    .with_help("for example: `--timeout 60`"));
                }
                cli.engine_args.push(name.to_string());
                cli.engine_args.push(value);
            }
            "--track" => {
                let value = take_value(name, inline, front, &mut i)?;
                if !matches!(value.as_str(), "auto" | "reg" | "ptr" | "mem") {
                    return Err(UsageError::new(format!("unknown --track level `{value}`"))
                        .with_help("valid levels are: auto, reg, ptr, mem"));
                }
                // The driver spells this one `--track=<level>`.
                cli.engine_args.push(format!("--track={value}"));
            }
            "-q" | "--quiet" => cli.quiet = true,
            "--color" => {
                let value = take_value(name, inline, front, &mut i)?;
                cli.color = style::ColorChoice::parse(&value).ok_or_else(|| {
                    UsageError::new(format!("unknown --color value `{value}`")).with_help(format!(
                        "valid values are: {}",
                        style::ColorChoice::VALUES.join(", ")
                    ))
                })?;
            }
            // --- wrapper-local options ---
            "--strict-obligations" => cli.strict_obligations = true,
            "--dry-run" => cli.dry_run = true,
            "--edition" => {
                let value = take_value(name, inline, front, &mut i)?;
                if !EDITIONS.contains(&value.as_str()) {
                    return Err(UsageError::new(format!("unknown edition `{value}`"))
                        .with_help(format!("valid editions are: {}", EDITIONS.join(", "))));
                }
                cli.edition = value;
                edition_given = true;
            }
            // --- positionals ---
            _ if arg.starts_with('-') => {
                return Err(UsageError::new(format!("unrecognized option `{arg}`"))
                    .with_help("run `trust-wp --help` for the full option list")
                    .with_help(
                        "to hand an option to the underlying tool unchanged, put it after `--`: \
                         `trust-wp -- <cargo options>` in a crate, \
                         `trust-wp file.rs -- <rustc options>` for a single file",
                    ));
            }
            _ => {
                if let Some(previous) = file.as_ref() {
                    return Err(UsageError::new(format!(
                        "trust-wp verifies one file per run, got `{}` and `{arg}`",
                        previous.display()
                    ))
                    .with_help(
                        "for a whole crate, run `trust-wp` with no file in the crate directory",
                    ));
                }
                file = Some(PathBuf::from(&arg));
            }
        }
        i += 1;
    }

    if let Some(path) = file {
        cli.mode = Mode::File(path);
    } else if edition_given {
        return Err(
            UsageError::new("--edition applies to single-file mode only")
                .with_help("a crate takes its edition from its Cargo.toml"),
        );
    }

    Ok(cli)
}

/// `trust-wp result [FILE | -]` — the transcript to decode, or stdin.
fn parse_result_input(args: &[String]) -> Result<Option<PathBuf>, UsageError> {
    let mut input: Option<PathBuf> = None;
    for arg in args {
        if arg.starts_with('-') && arg != "-" {
            return Err(
                UsageError::new(format!("`trust-wp result` does not accept `{arg}`"))
                    .with_help("usage: trust-wp result [FILE | -]   (default: read stdin)"),
            );
        }
        if input.is_some() {
            return Err(UsageError::new(format!(
                "`trust-wp result` decodes one transcript per run, got `{arg}` as well"
            )));
        }
        input = Some(PathBuf::from(arg));
    }
    Ok(input.filter(|path| path != Path::new("-")))
}

/// Refuse a `-- <options>` tail on a verb that runs no underlying tool.
fn reject_passthrough(verb: &str, passthrough: &[String]) -> Result<(), UsageError> {
    if passthrough.is_empty() {
        return Ok(());
    }
    let tail = passthrough.join(" ");
    Err(UsageError::new(format!(
        "`trust-wp {verb}` runs no other tool, so `-- {tail}` \
             has nowhere to go"
    ))
    .with_help(
        "`--` forwards options to cargo (crate mode) or rustc (single-file mode); \
             neither runs here",
    ))
}

fn parse_example(args: &[String]) -> Result<Cli, UsageError> {
    let mut out: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].clone();
        let (name, inline) = split_inline_value(&arg);
        match name {
            "-o" | "--out" => {
                let value = take_value(name, inline, args, &mut i)?;
                out = Some(PathBuf::from(value));
            }
            _ => {
                return Err(
                    UsageError::new(format!("`trust-wp example` does not accept `{arg}`"))
                        .with_help("usage: trust-wp example [-o FILE]  (default: write to stdout)"),
                );
            }
        }
        i += 1;
    }
    Ok(Cli::with_mode(Mode::Example { out }))
}

/// Split `--flag=value` into (`--flag`, `Some(value)`).
pub(crate) fn split_inline_value(arg: &str) -> (&str, Option<&str>) {
    match arg.split_once('=') {
        Some((name, value)) if name.starts_with('-') => (name, Some(value)),
        _ => (arg, None),
    }
}

/// Read a flag's value from either `--flag=value` or the next argument.
pub(crate) fn take_value(
    name: &str,
    inline: Option<&str>,
    args: &[String],
    i: &mut usize,
) -> Result<String, UsageError> {
    if let Some(value) = inline {
        if value.is_empty() {
            return Err(UsageError::new(format!("`{name}=` needs a value")));
        }
        return Ok(value.to_string());
    }
    match args.get(*i + 1) {
        // An empty value would be accepted here and then vanish in transit:
        // engine args travel as newline-joined text, so `--filter ""` reaches
        // the driver as a blank line and shifts every later argument by one.
        Some(value) if value.is_empty() => Err(UsageError::new(format!(
            "`{name}` was given an empty value"
        ))
        .with_help(format!("for example: `{name} {}`", example_value_for(name)))),
        // `trust-wp --filter demo.rs` is a forgotten value, not a function
        // named `demo.rs`: taking it would silently drop the file and verify
        // the surrounding crate instead.
        //
        // Only for flags whose value is a NAME. `-o` and `--emit-smt-dir` take
        // paths, and `trust-wp example -o demo.rs` run twice in the same
        // directory is the documented first-run recipe — the second run must
        // overwrite, not be refused.
        Some(value)
            if takes_a_name(name)
                && Path::new(value).extension() == Some(OsStr::new("rs"))
                && Path::new(value).is_file() =>
        {
            Err(
                UsageError::new(format!("`{name}` was given the source file `{value}`")).with_help(
                    format!(
                        "`{name}` takes a value of its own; did you mean `{name} {} {value}`?",
                        example_value_for(name)
                    ),
                ),
            )
        }
        Some(value) if !value.starts_with('-') => {
            *i += 1;
            Ok(value.clone())
        }
        _ => Err(UsageError::new(format!("`{name}` needs a value"))
            .with_help(format!("for example: `{name} {}`", example_value_for(name)))),
    }
}

/// True for options whose value is a name rather than a filesystem path.
fn takes_a_name(flag: &str) -> bool {
    matches!(flag, "--filter" | "--track" | "--timeout" | "--edition")
}

fn example_value_for(name: &str) -> &'static str {
    match name {
        "--filter" => "increment",
        "--emit-smt-dir" => "./smt-out",
        "--timeout" => "60",
        "--track" => "reg",
        "--edition" => "2021",
        "-o" | "--out" => "demo.rs",
        _ => "<VALUE>",
    }
}

/// Split at the first bare `--`.
fn split_passthrough(args: &[String]) -> (Vec<String>, Vec<String>) {
    match args.iter().position(|a| a == "--") {
        Some(pos) => (args[..pos].to_vec(), args[pos + 1..].to_vec()),
        None => (args.to_vec(), Vec::new()),
    }
}

// ---------------------------------------------------------------------------
// Finding the engine
// ---------------------------------------------------------------------------

/// A located engine program, plus a human note about where it came from.
#[derive(Debug, Clone)]
pub(crate) struct Engine {
    program: PathBuf,
    origin: String,
}

/// Why an engine binary could not be found, and exactly how to fix it.
struct EngineMissing {
    binary: &'static str,
    searched: Vec<String>,
    fixes: Vec<String>,
}

impl EngineMissing {
    /// Fixes worth printing from inside `doctor`, which already reports the
    /// toolchain state and is itself the thing being suggested elsewhere.
    /// One line naming what could not be found, for the `--json` report.
    fn summary(&self) -> String {
        format!(
            "cannot find `{}` (searched: {})",
            self.binary,
            self.searched.join(", ")
        )
    }

    pub(crate) fn actionable_fixes(&self) -> impl Iterator<Item = &String> {
        self.fixes
            .iter()
            .filter(|fix| !fix.contains("trust-wp doctor") && !fix.contains("rustup toolchain"))
    }

    fn report(&self) {
        eprintln!(
            "error: cannot find the trust-wp engine binary `{}`",
            self.binary
        );
        eprintln!("note: searched");
        for line in &self.searched {
            eprintln!("        {line}");
        }
        eprintln!("help: to fix this, one of");
        for line in &self.fixes {
            eprintln!("        {line}");
        }
        eprintln!(
            "note: `{DRIVER_BIN}` links rustc_private and needs a Trust toolchain sysroot at \
             runtime; it cannot simply be copied from another machine."
        );
    }
}

/// The trust-wp checkout this front door belongs to.
///
/// `$TRUST_WP_HOME` wins; otherwise walk up from this binary (the usual
/// `target/<profile>/trust-wp` layout); otherwise fall back to the path baked
/// in at build time. The baked path is honest here — the engine is not
/// relocatable anyway (see `[workspace.metadata.atpkg]` in the root manifest).
pub(crate) fn repo_root() -> Option<PathBuf> {
    if let Some(home) = env::var_os("TRUST_WP_HOME") {
        let path = PathBuf::from(home);
        if path.join("crates").join("trust-wp-driver").is_dir() {
            return Some(path);
        }
    }
    if let Ok(exe) = env::current_exe() {
        for dir in exe.ancestors() {
            if dir.join("scripts").join("run-trust-wp-rustc.sh").is_file() {
                return Some(dir.to_path_buf());
            }
        }
    }
    let baked = Path::new(env!("CARGO_MANIFEST_DIR")).parent()?.parent()?;
    baked
        .join("crates")
        .join("trust-wp-driver")
        .is_dir()
        .then(|| baked.to_path_buf())
}

/// Say once, on stderr, that `$TRUST_WP_HOME` is being ignored.
///
/// Not routed through `--quiet`: quiet drops clean per-function verdicts, and
/// this is the opposite of routine — it says the run may not be using the
/// checkout the caller intended.
fn warn_about_trust_wp_home() {
    if let Some(complaint) = trust_wp_home_complaint() {
        eprintln!("warning: {complaint};");
        eprintln!(
            "         the engine and libraries are coming from somewhere else \
             — `trust-wp doctor` says where"
        );
    }
}

/// A complaint about `$TRUST_WP_HOME`, if it is set but not usable.
///
/// `repo_root` accepts the variable only when it points at something that
/// looks like a checkout, and otherwise falls through to the next candidate.
/// That fallback is right — a bad value should not be fatal — but discarding
/// an explicitly set variable in silence is not: the tool then resolves the
/// driver, the libraries and the sysroot from a *different* checkout than the
/// one it was told to use, and nothing says so. `--help` already promises that
/// unknown options are "refused, never ignored"; a stale or mistyped
/// `TRUST_WP_HOME` deserves the same courtesy.
pub(crate) fn trust_wp_home_complaint() -> Option<String> {
    complaint_for_home(env::var_os("TRUST_WP_HOME").as_deref())
}

/// The complaint for one value, so the rule can be tested without touching
/// the process environment — which the workspace lints forbid, for good
/// reason: it is global state shared with every other test in the binary.
fn complaint_for_home(home: Option<&OsStr>) -> Option<String> {
    let home = home?;
    // Unset and set-to-empty mean the same thing to a shell user, and neither
    // is an instruction to use a particular checkout.
    if home.is_empty() {
        return None;
    }
    let path = Path::new(home);
    if path.join("crates").join("trust-wp-driver").is_dir() {
        return None;
    }
    let why = if path.is_dir() {
        "no crates/trust-wp-driver there"
    } else {
        "no such directory"
    };
    Some(format!(
        "$TRUST_WP_HOME is set to `{}` but is being ignored ({why})",
        path.display()
    ))
}

/// Directory holding this binary — also the cargo profile dir holding its siblings.
fn exe_dir() -> Option<PathBuf> {
    env::current_exe()
        .ok()
        .and_then(|exe| exe.parent().map(Path::to_path_buf))
}

fn which(name: &str) -> Option<PathBuf> {
    let path = env::var_os("PATH")?;
    env::split_paths(&path)
        .map(|dir| dir.join(name))
        .find(|candidate| candidate.is_file())
}

/// Candidate profile directories that may hold engine binaries and rlibs.
fn engine_search_dirs() -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    if let Some(dir) = exe_dir() {
        dirs.push(dir);
    }
    if let Some(root) = repo_root() {
        for profile in ["release", "debug"] {
            let dir = root.join("target").join(profile);
            if !dirs.contains(&dir) {
                dirs.push(dir);
            }
        }
    }
    dirs
}

/// Find an engine binary, trying every name it ships under.
///
/// Precedence is by *location*, not by name: the environment override, then
/// every local build directory, then `$PATH`. Searching all of `$PATH` for the
/// first name before looking at the second name locally would let a stale
/// bundle-installed `targo-trust-wp` win over the `cargo-trust-wp` sitting
/// next to this binary — the opposite of what a developer in a checkout means.
pub(crate) fn find_engine(
    names: &[&'static str],
    env_override: &str,
) -> Result<Engine, EngineMissing> {
    let mut searched = Vec::new();

    match env::var_os(env_override) {
        Some(value) => {
            let path = PathBuf::from(&value);
            if path.is_file() {
                return Ok(Engine {
                    program: path,
                    origin: format!("${env_override}"),
                });
            }
            searched.push(format!("${env_override} = {} (not a file)", path.display()));
        }
        None => searched.push(format!("${env_override} (not set)")),
    }

    for dir in engine_search_dirs() {
        for name in names {
            let candidate = dir.join(name);
            if candidate.is_file() {
                return Ok(Engine {
                    program: candidate,
                    origin: dir.display().to_string(),
                });
            }
            searched.push(candidate.display().to_string());
        }
    }

    for name in names {
        if let Some(found) = which(name) {
            return Ok(Engine {
                program: found,
                origin: "$PATH".to_string(),
            });
        }
        searched.push(format!("$PATH ({name})"));
    }

    Err(EngineMissing {
        // Report against the primary name: it is the one the fix line builds.
        binary: names[0],
        searched,
        fixes: build_fixes(names[0], env_override),
    })
}

/// Locate the cargo front end under either of its two shipped names.
///
/// The package ships `targo-trust-wp` and the byte-identical back-compat alias
/// `cargo-trust-wp`; a checkout, a `$PATH` install and a Trust bundle may each
/// expose only one of them.
pub(crate) fn find_cargo_front() -> Result<Engine, EngineMissing> {
    find_engine(&[CARGO_FRONT_BIN, CARGO_FRONT_BIN_ALIAS], "TRUST_WP_CARGO")
}

fn build_fixes(binary: &'static str, env_override: &str) -> Vec<String> {
    let root = repo_root().map_or_else(
        || "/path/to/trust-wp".to_string(),
        |root| root.display().to_string(),
    );
    // Package names, not binary names: the cargo front end's *package* was
    // renamed to `targo-trust-wp`; `cargo-trust-wp` survives only as a
    // back-compat [[bin]] alias inside it, so `-p cargo-trust-wp` no longer
    // resolves.
    let package = if binary == DRIVER_BIN {
        "-p trust-wp-driver --bin trust-wp-rustc"
    } else {
        "-p targo-trust-wp"
    };
    vec![
        format!("build it:  cd {root} && cargo build --release {package}"),
        format!("point at an existing one:  {env_override}=/path/to/{binary} trust-wp ..."),
        "check the Trust toolchain is usable:  rustup toolchain list && rustc --print sysroot"
            .to_string(),
        "run `trust-wp doctor` for a full readiness report".to_string(),
    ]
}

/// The two contract crates a lone `.rs` file may import.
///
/// `trust_wp` is the native surface; `creusot_contracts` is the compat shim
/// this workspace ships (`crates/creusot-contracts`) and which the help sells.
/// Each entry is (crate name as written in `use`, rlib file name, the cargo
/// package that builds it).
pub(crate) const CONTRACT_CRATES: [(&str, &str, &str); 2] = [
    ("trust_wp", "libtrust_wp.rlib", "trust-wp"),
    (
        "creusot_contracts",
        "libcreusot_contracts.rlib",
        "creusot-contracts",
    ),
];

/// Locate a compiled contract crate, so a lone `.rs` file can say
/// `use trust_wp::{ensures, requires};` with no Cargo project around it.
///
/// Returns the rlib and the sibling `deps` directory rustc needs in order to
/// resolve the proc-macro and std-spec crates behind it.
///
/// Two places, and the newest wins. `target/<profile>/libtrust_wp.rlib` is the
/// uplifted copy, which cargo refreshes only when someone names the package
/// (`cargo build -p trust-wp`); `target/<profile>/deps/libtrust_wp-<hash>.rlib`
/// is written whenever anything depends on it. Preferring whichever is newer
/// is what keeps single-file mode working after an ordinary workspace build
/// instead of failing with a bare `can't find crate for trust_wp` against a
/// copy left over from an older compiler or an older `trust-wp-core`.
pub(crate) fn find_contract_rlib(rlib_name: &str) -> Option<(PathBuf, PathBuf)> {
    for dir in engine_search_dirs() {
        let deps = dir.join("deps");
        let mut candidates: Vec<PathBuf> = Vec::new();

        let uplifted = dir.join(rlib_name);
        if uplifted.is_file() {
            candidates.push(uplifted);
        }
        // `libtrust_wp.rlib` -> ("libtrust_wp-", ".rlib")
        if let Some(stem) = rlib_name.strip_suffix(".rlib") {
            let hashed_prefix = format!("{stem}-");
            if let Ok(entries) = fs::read_dir(&deps) {
                candidates.extend(entries.flatten().map(|entry| entry.path()).filter(|path| {
                    path.extension() == Some(OsStr::new("rlib"))
                        && path
                            .file_stem()
                            .and_then(OsStr::to_str)
                            .is_some_and(|name| name.starts_with(&hashed_prefix))
                }));
            }
        }

        let newest = candidates.into_iter().max_by_key(|path| {
            fs::metadata(path)
                .and_then(|meta| meta.modified())
                .unwrap_or(std::time::UNIX_EPOCH)
        });
        if let Some(rlib) = newest {
            return Some((rlib, deps));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Single-file mode
// ---------------------------------------------------------------------------

fn run_single_file(cli: &Cli, file: &Path) -> i32 {
    warn_about_trust_wp_home();
    let Some(path) = canonical_source(file) else {
        return EXIT_USAGE;
    };

    let engine = match find_engine(&DRIVER_BINS, "TRUST_WP_RUSTC") {
        Ok(engine) => engine,
        Err(missing) => {
            missing.report();
            emit_json_failure(
                cli,
                "file",
                file.display().to_string(),
                EXIT_ENCODING_ERROR,
                (report::ErrorKind::EngineMissing, missing.summary()),
            );
            return EXIT_ENCODING_ERROR;
        }
    };

    // Process id alone repeats after a wrap-around, and a stale directory left
    // by a killed run would then be reused and deleted under a live one. The
    // source path's hash pins it to this input as well.
    let out_dir = env::temp_dir().join(format!(
        "trust-wp-{}-{:x}",
        std::process::id(),
        scratch_tag(&path)
    ));
    if let Err(err) = fs::create_dir_all(&out_dir) {
        eprintln!(
            "error: cannot create the scratch output directory {}: {err}",
            out_dir.display()
        );
        return EXIT_ENCODING_ERROR;
    }

    // rustc accumulates `--crate-type` and refuses a repeated `--edition`, so a
    // caller who set either after `--` must win outright rather than have ours
    // added alongside.
    let passthrough_sets = |flag: &str| {
        cli.passthrough
            .iter()
            .any(|a| a == flag || a.starts_with(&format!("{flag}=")))
    };
    let mut rustc_args = vec![
        path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        crate_name_for(&path),
    ];
    if !passthrough_sets("--crate-type") {
        rustc_args.push("--crate-type".to_string());
        rustc_args.push("lib".to_string());
    }
    if !passthrough_sets("--edition") {
        rustc_args.push(format!("--edition={}", cli.edition));
    }
    rustc_args.extend([
        "--out-dir".to_string(),
        out_dir.to_string_lossy().into_owned(),
        // Single-file mode compiles the file as a library purely to reach its
        // MIR. Nothing links against that library, so rustc reports every
        // contracted function — and any `fn main` — as dead code. Those
        // warnings are an artifact of how trust-wp compiles the file, not of
        // anything the user wrote, and they bury the verification result under
        // a wall of noise. Real diagnostics still come through untouched, and
        // a caller who wants the lint back can say so after `--`, which lands
        // later on the command line and therefore wins.
        "--allow=dead_code".to_string(),
    ]);
    // Creusot — whose attribute syntax this tool is compatible with — writes
    // `#[invariant(...)]` on the loop:
    //
    //     #[invariant(i >= 0)]
    //     while i < n { ... }
    //
    // That is an attribute in expression position, which rustc gates behind
    // `proc_macro_hygiene`. Without the gate the file does not compile, and
    // rustc's advice — "add `#![feature(proc_macro_hygiene)]` to the crate
    // attributes" — sends the reader to edit their source for a requirement
    // that is an artifact of how trust-wp compiles the file, exactly like the
    // dead-code lint above. trust-wp's own `#[invariant]` on the function
    // needs no gate, so a newcomer meets a hard error on the spelling the
    // ecosystem taught them and none on the other, with nothing saying why.
    //
    // Turning the feature on for single-file mode makes both placements work.
    // It is a syntax-position feature: it changes where an attribute may be
    // written, not what any contract means, so no obligation is affected. A
    // caller who sets their own `-Zcrate-attr` after `--` still lands later on
    // the command line and wins.
    if !passthrough_sets("-Zcrate-attr") {
        rustc_args.push("-Zcrate-attr=feature(proc_macro_hygiene)".to_string());
    }

    let source = fs::read_to_string(&path).unwrap_or_default();
    let mut dependency_dirs: Vec<PathBuf> = Vec::new();
    for (crate_name, rlib_name, package) in CONTRACT_CRATES {
        // A caller who put their own `--extern <crate>=...` after `--` has
        // answered the question themselves; injecting a second one would make
        // rustc reject the pair as a duplicate.
        let supplied = cli
            .passthrough
            .iter()
            .any(|a| a.contains(&format!("{crate_name}=")));
        if supplied {
            continue;
        }
        match find_contract_rlib(rlib_name) {
            Some((rlib, deps)) => {
                rustc_args.push("--extern".to_string());
                rustc_args.push(format!("{crate_name}={}", rlib.display()));
                if !dependency_dirs.contains(&deps) {
                    dependency_dirs.push(deps);
                }
            }
            // Only a hard error when the file actually imports it: a machine
            // that never built the Creusot shim can still verify native files.
            None if source.contains(crate_name) => {
                let root = repo_root().map_or_else(
                    || "/path/to/trust-wp".to_string(),
                    |root| root.display().to_string(),
                );
                eprintln!(
                    "error: {} uses the `{crate_name}` contract crate, but `{rlib_name}` is not built",
                    path.display()
                );
                eprintln!("help: build it:  cd {root} && cargo build --release -p {package}");
                eprintln!(
                    "help: or pass your own copy through:  trust-wp {} -- --extern {crate_name}=<path to {rlib_name}>",
                    path.display()
                );
                let _ = fs::remove_dir_all(&out_dir);
                return EXIT_ENCODING_ERROR;
            }
            None => {}
        }
    }
    for deps in dependency_dirs {
        rustc_args.push("-L".to_string());
        rustc_args.push(format!("dependency={}", deps.display()));
    }
    rustc_args.extend(cli.passthrough.iter().cloned());

    // `--force` makes the driver analyse a crate that does not declare a
    // trust-wp dependency; `cargo-trust-wp` prepends exactly the same flag.
    let mut engine_args = vec!["--force".to_string()];
    engine_args.extend(cli.engine_args.iter().cloned());
    let trust_wp_args = engine_args.join("\n");

    if cli.dry_run {
        // Under `--json` stdout carries the report, so the shell-style echo is
        // reported instead of printed.
        if cli.json {
            let command = dry_run_json(&engine, &rustc_args, Some(&trust_wp_args));
            let _ = fs::remove_dir_all(&out_dir);
            return dry_run_report(cli, "file", path.display().to_string(), command);
        }
        print_dry_run(&engine, &rustc_args, &trust_wp_args);
        let _ = fs::remove_dir_all(&out_dir);
        return EXIT_OK;
    }

    let caller_wants_wire = env::var_os(RESULT_PROTOCOL_ENV).is_some();
    let mut command = Command::new(&engine.program);
    command
        .args(&rustc_args)
        // Newline-delimited so path-valued options may contain spaces; the
        // driver's own parser detects newlines (#1691).
        .env("TRUST_WP_ARGS", &trust_wp_args)
        .env(RESULT_PROTOCOL_ENV, "1")
        .stdout(Stdio::inherit())
        .stderr(Stdio::piped());
    apply_sysroot_library_path(&mut command);
    apply_verbose_logging(cli, &mut command);

    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(err) => {
            eprintln!(
                "error: cannot run the trust-wp engine at {}: {err}",
                engine.program.display()
            );
            eprintln!("help: run `trust-wp doctor` to see what is missing");
            let _ = fs::remove_dir_all(&out_dir);
            emit_json_failure(
                cli,
                "file",
                path.display().to_string(),
                EXIT_ENCODING_ERROR,
                (
                    report::ErrorKind::EngineSpawn,
                    format!(
                        "cannot run the trust-wp engine at {}",
                        engine.program.display()
                    ),
                ),
            );
            return EXIT_ENCODING_ERROR;
        }
    };

    let started = Instant::now();
    let mut relay =
        StderrRelay::with_style(caller_wants_wire, style::Style::new(cli.color)).quiet(cli.quiet);
    relay.drain(child.stderr.take());

    let status = child.wait();
    let elapsed = started.elapsed();
    let _ = fs::remove_dir_all(&out_dir);

    let child_code = match status {
        Ok(status) => status.code().unwrap_or(101),
        Err(err) => {
            eprintln!("error: the trust-wp engine did not finish: {err}");
            return EXIT_ENCODING_ERROR;
        }
    };

    let code = engine_exit_code(
        child_code,
        relay.wire.as_ref(),
        cli.verify_mode(),
        cli.strict_obligations,
        relay.saw_compiler_error,
    );
    relay.print_hints(relay.wire.is_none() && child_code != 0);
    let nothing_proved = proved_nothing(child_code, relay.wire.as_ref(), cli.verify_mode());
    if nothing_proved {
        report_nothing_proved(cli);
    }
    report_elapsed(cli, elapsed);
    explain_exit_code(code);
    emit_json_report(
        cli,
        "file",
        path.display().to_string(),
        code,
        Some(child_code),
        relay,
        Some(engine),
        None,
        nothing_proved.then(|| {
            (
                report::ErrorKind::NoVerdict,
                "the engine examined no obligation — nothing was proved".to_string(),
            )
        }),
    );
    code
}

/// Print the `--json` report for an engine run, if one was asked for.
///
/// Human output has already gone to stderr by this point; stdout carries
/// exactly this document and nothing else.
#[allow(clippy::too_many_arguments)]
fn emit_json_report(
    cli: &Cli,
    mode: &'static str,
    target: String,
    exit_code: i32,
    child_exit_code: Option<i32>,
    relay: StderrRelay,
    driver: Option<Engine>,
    front: Option<Engine>,
    error: Option<(report::ErrorKind, String)>,
) {
    if !cli.json {
        return;
    }
    let run = report::RunReport {
        exit_code,
        mode,
        target,
        summary: relay.wire,
        diagnostics: relay.diagnostics,
        driver,
        front,
        child_exit_code,
        notes: Vec::new(),
        verify_mode: cli.verify_mode(),
        dry_run: false,
        dry_run_command: None,
        error,
    };
    report::print_json(&report::verify_report(&run, "verify"));
}

/// The report for a run that never reached the engine.
fn emit_json_failure(
    cli: &Cli,
    mode: &'static str,
    target: String,
    exit_code: i32,
    error: (report::ErrorKind, String),
) {
    if !cli.json {
        return;
    }
    let run = report::RunReport {
        exit_code,
        mode,
        target,
        verify_mode: cli.verify_mode(),
        error: Some(error),
        ..report::RunReport::default()
    };
    report::print_json(&report::verify_report(&run, "verify"));
}

/// Put the active sysroot's `lib/` on the dynamic loader path for the engine.
///
/// `scripts/run-trust-wp-rustc.sh` does exactly this, and this mode exists to
/// be that script without the script. The driver bakes loader-relative rpaths
/// to its `rustc_private` dylibs, so this is a fallback rather than the primary
/// mechanism — it rescues a driver built before the rpath work, or one whose
/// bundle layout has moved. A value the caller already set wins: they know
/// something about their environment that this does not.
fn apply_sysroot_library_path(command: &mut Command) {
    let var = if cfg!(target_os = "macos") {
        "DYLD_LIBRARY_PATH"
    } else {
        "LD_LIBRARY_PATH"
    };
    if env::var_os(var).is_some() {
        return;
    }
    let Ok(output) = Command::new("rustc").args(["--print", "sysroot"]).output() else {
        return;
    };
    if !output.status.success() {
        return;
    }
    let sysroot = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if sysroot.is_empty() {
        return;
    }
    command.env(var, Path::new(&sysroot).join("lib"));
}

/// True when a run that was supposed to produce a verdict produced none.
///
/// Two shapes reach here: no wire line at all (the engine never got as far as
/// reporting), and a wire line whose every counter is zero (it reported that it
/// looked at nothing). Both mean the same thing to the user — nothing was
/// proved — so both must be reported and neither may exit 0.
fn proved_nothing(
    child_code: i32,
    wire: Option<&StructuredVerificationResult>,
    verify_mode: bool,
) -> bool {
    verify_mode
        && child_code == 0
        && wire.map_or(true, StructuredVerificationResult::examined_nothing)
}

fn report_nothing_proved(cli: &Cli) {
    eprintln!("error: nothing was verified — the run proved nothing");
    if let Some(filter) = filter_value(cli) {
        eprintln!(
            "help: `--filter {filter}` matched no function; drop it to see everything the file \
             declares"
        );
    } else {
        eprintln!(
            "help: does the input carry `#[requires]` / `#[ensures]` contracts? \
             `trust-wp example > demo.rs` writes one that does"
        );
    }
}

/// The `--filter` value this run carried, if any.
fn filter_value(cli: &Cli) -> Option<&str> {
    let mut args = cli.engine_args.iter();
    while let Some(arg) = args.next() {
        if arg == "--filter" {
            return args.next().map(String::as_str);
        }
    }
    None
}

/// Ask the engine for per-function progress when the user asked for it.
///
/// `-v` advertises "show verification progress" and used to change nothing:
/// the engine's timing layer keys off its own log filter, and the `--verbose`
/// flag the CLI forwards does not reach it. Setting the filter here is what
/// makes the promise true — a verifier that thinks for seconds should be able
/// to say where the seconds went. An explicit `TRUST_WP_LOG` always wins, so a
/// user who has tuned the filter keeps their setting. Scoped to `trust_wp`
/// rather than a bare `info`: the latter also opens the solver's internal
/// spans, which bury the result under bound-axiom statistics.
fn apply_verbose_logging(cli: &Cli, command: &mut Command) {
    let verbose = cli.engine_args.iter().any(|a| a == "--verbose");
    if verbose && env::var_os("TRUST_WP_LOG").is_none() {
        command.env("TRUST_WP_LOG", "trust_wp=info");
    }
}

/// Say how long the run took.
///
/// Verification is not instant and the wait is silent, so the number is the
/// only evidence of what the tool actually did with the time. Suppressed under
/// `--json` (the report is the output) and on a dry run (nothing ran).
fn report_elapsed(cli: &Cli, elapsed: std::time::Duration) {
    if cli.json || cli.dry_run {
        return;
    }
    let style = style::Style::new(cli.color);
    let secs = elapsed.as_secs_f64();
    let rendered = if secs < 1.0 {
        format!("{}ms", elapsed.as_millis())
    } else {
        format!("{secs:.1}s")
    };
    eprintln!("{}", style.dim(&format!("finished in {rendered}")));
}

/// One actionable next step for the non-zero results a user can act on.
fn explain_exit_code(code: i32) {
    match code {
        EXIT_VERIFICATION_FAILURE => eprintln!(
            "help: a contract was not proved. Re-run just that function with \
             `--filter <NAME>`, or read the obligation with `--emit-smt`."
        ),
        // 3 is the engine's parse-error code and this tool's command-line
        // error code, and in crate mode it can arrive from either. Name both
        // rather than assert the one that happens to be more common.
        EXIT_USAGE => eprintln!(
            "help: exit 3 is either a contract that failed to parse — contract-syntax.md \
             in the trust-wp checkout has the full grammar — or a rejected command line."
        ),
        _ => {}
    }
}

/// Decide the process exit code the way `cargo-trust-wp` does: the engine's
/// structured counters win; the child's own status is the fallback.
///
/// Shared by both modes, because both ask the same question of the same wire
/// protocol — single-file mode reads it off `trust-wp-rustc` directly, crate
/// mode off the aggregate `cargo-trust-wp` re-emits.
pub(crate) fn engine_exit_code(
    child_code: i32,
    wire: Option<&StructuredVerificationResult>,
    verify_mode: bool,
    strict_obligations: bool,
    saw_compiler_error: bool,
) -> i32 {
    match wire {
        Some(wire) => {
            let effective = wire.effective_exit_code();
            if effective != 0 {
                return effective;
            }
            // Fail closed: an all-zero summary means the engine examined no
            // obligation — an empty file, a crate with no contracts, or a
            // `--filter` that matched nothing. Reporting that as success would
            // claim a proof that was never attempted.
            if verify_mode && wire.examined_nothing() {
                return EXIT_ENCODING_ERROR;
            }
            if strict_obligations && wire.warnings > 0 {
                return EXIT_ENCODING_ERROR;
            }
            if child_code != 0 {
                return child_code;
            }
            EXIT_OK
        }
        // Same rule for a run that never reported at all: a clean exit that
        // produced no verdict proved nothing — unless none was expected, as on
        // an emit-only or `--no-verify` run.
        None if child_code == 0 => {
            if verify_mode {
                EXIT_ENCODING_ERROR
            } else {
                EXIT_OK
            }
        }
        // The engine emits a wire line on every run that reaches verification,
        // so no wire line and a nonzero status means it stopped earlier — the
        // file did not compile, or the driver died. Passing rustc's exit 1
        // through would label that "a contract was not proved (a
        // counterexample exists)", a claim about a proof never attempted.
        // 3 (usage/parse) and 101 (panic) already say what they mean.
        // 101 normally means a panic, but `rustc_driver` also aborts with it
        // on a fatal diagnostic. A rejected program is an engine/compile
        // failure the user can act on, not an internal error to report.
        None if child_code == 101 && saw_compiler_error => EXIT_ENCODING_ERROR,
        None if child_code == EXIT_USAGE || child_code == 101 => child_code,
        None => EXIT_ENCODING_ERROR,
    }
}

/// Forwards the engine's human output and collects its machine wire lines.
pub(crate) struct StderrRelay {
    /// How to present the engine's human lines. `None` while collecting a
    /// saved transcript, where the text is not being shown.
    presentation: Option<(style::Style, Option<PathBuf>)>,
    show_wire: bool,
    /// Echo human lines to stderr. Off when decoding a saved transcript.
    echo_human: bool,
    pub(crate) wire: Option<StructuredVerificationResult>,
    /// Per-obligation records, kept for `--json`. Still hidden from the
    /// terminal unless the caller asked for the protocol.
    pub(crate) diagnostics: Vec<VerificationDiagnosticRecord>,
    saw_loader_error: bool,
    saw_missing_std: bool,
    saw_unresolved_contract_crate: bool,
    /// The compiler reported a diagnostic error before verification began.
    saw_compiler_error: bool,
    /// A verdict came back `unknown (proof-trusted)`.
    saw_proof_trusted: bool,
    /// `--quiet`: drop clean per-function verdicts and timings.
    quiet: bool,
    /// Whether any human line has been echoed yet, so quiet can drop the
    /// blank separator the engine prints before a summary it no longer
    /// follows anything.
    echoed_any: bool,
}

impl StderrRelay {
    /// A silent relay: collect, echo nothing. Used to decode a saved
    /// transcript, where the text has already been shown once.
    pub(crate) fn collecting() -> Self {
        Self {
            echo_human: false,
            presentation: None,
            ..Self::new(false)
        }
    }

    fn new(show_wire: bool) -> Self {
        Self::with_style(show_wire, style::Style::new(style::ColorChoice::Never))
    }

    fn with_style(show_wire: bool, style: style::Style) -> Self {
        Self {
            presentation: Some((style, env::current_dir().ok())),
            show_wire,
            echo_human: true,
            wire: None,
            diagnostics: Vec::new(),
            saw_loader_error: false,
            saw_missing_std: false,
            saw_unresolved_contract_crate: false,
            saw_compiler_error: false,
            saw_proof_trusted: false,
            quiet: false,
            echoed_any: false,
        }
    }

    /// Suppress routine progress. Symptom tracking and the wire summary are
    /// unaffected: quiet changes what is shown, never what is concluded.
    #[must_use]
    fn quiet(mut self, quiet: bool) -> Self {
        self.quiet = quiet;
        self
    }

    /// Forward the child's whole stderr, line by line.
    ///
    /// Deliberately byte-oriented. `BufRead::lines` yields `Err` on the first
    /// invalid UTF-8 sequence, and abandoning the pipe there would discard the
    /// wire line that decides the exit code — and leave the child blocked on a
    /// full pipe. rustc emits the user's own source spans, so a file in any
    /// other encoding is enough to trigger it. Lossy decoding keeps the stream
    /// moving and costs at most a replacement character in a diagnostic.
    fn drain(&mut self, stderr: Option<std::process::ChildStderr>) {
        let Some(stderr) = stderr else { return };
        let mut reader = BufReader::new(stderr);
        let mut buf = Vec::new();
        loop {
            buf.clear();
            match reader.read_until(b'\n', &mut buf) {
                Ok(0) | Err(_) => return,
                Ok(_) => {}
            }
            while matches!(buf.last(), Some(b'\n' | b'\r')) {
                buf.pop();
            }
            self.line(&String::from_utf8_lossy(&buf));
        }
    }

    pub(crate) fn line(&mut self, line: &str) {
        if line.starts_with(WIRE_PREFIX) {
            if let Some(mut parsed) = StructuredVerificationResult::from_wire_line(line) {
                parsed.normalize_exit_code();
                match self.wire.as_mut() {
                    Some(existing) => existing.merge(&parsed),
                    None => self.wire = Some(parsed),
                }
                if self.show_wire {
                    eprintln!("{line}");
                }
                return;
            }
        }
        // Per-obligation diagnostic lines exist for machine consumers; the
        // protocol is switched on for the exit code, not to spam the user.
        if line.starts_with(DIAGNOSTIC_WIRE_PREFIX) {
            if let Some(record) = VerificationDiagnosticRecord::from_wire_line(line) {
                self.diagnostics.push(record);
            }
            if !self.show_wire {
                return;
            }
        }
        self.note_symptom(line);
        if self.quiet {
            if style::is_routine_progress(line) {
                return;
            }
            // The engine separates the per-function lines from the summary
            // with a blank one. With the per-function lines gone, that
            // separator would open the output.
            if !self.echoed_any && line.trim().is_empty() {
                return;
            }
        }
        if self.echo_human {
            self.echoed_any = true;
            match &self.presentation {
                Some((style, cwd)) => {
                    eprintln!("{}", style::present(line, *style, cwd.as_deref()));
                }
                None => eprintln!("{line}"),
            }
        }
    }

    fn note_symptom(&mut self, line: &str) {
        // `rustc_driver` aborts on a fatal diagnostic, so the engine exits 101
        // — the code this tool documents as "internal error (panic)". A
        // rejected program is not an internal error, and telling the user it
        // is sends them to the issue tracker instead of to line 3 of their
        // file.
        if line.starts_with("error[E") || line.starts_with("error: aborting due to") {
            self.saw_compiler_error = true;
        }
        if line.contains("unknown (proof-trusted)") {
            self.saw_proof_trusted = true;
        }
        if line.contains("dyld")
            || line.contains("Library not loaded")
            || line.contains("cannot open shared object file")
            || line.contains("image not found")
        {
            self.saw_loader_error = true;
        }
        if line.contains("can't find crate for `std`")
            || line.contains("can't find crate for `core`")
        {
            self.saw_missing_std = true;
        }
        // E0463 "can't find crate", E0514 "compiled by a different version of
        // rustc", and the plain link failures all mean the same thing to the
        // user: the contract crate this run handed rustc is not usable.
        let names_contract_crate = line.contains("trust_wp") || line.contains("creusot_contracts");
        if names_contract_crate
            && (line.contains("unresolved")
                || line.contains("unlinked")
                || line.contains("can't find crate")
                || line.contains("E0463")
                || line.contains("E0514")
                || line.contains("compiled by"))
        {
            self.saw_unresolved_contract_crate = true;
        }
    }

    fn print_hints(&self, compile_failed: bool) {
        if self.saw_proof_trusted {
            // A bare `? f unknown (proof-trusted)` and a source span tell
            // someone nothing about what to do. The verdict has one dominant
            // so say what it means and what to try. An earlier version of this
            // hint named `&mut` plus a branch as "the usual cause"; that shape
            // proves now, and a hint that names a cause it no longer has sends
            // the reader to rewrite working code. What stays true is the
            // meaning and the two things worth doing next.
            eprintln!(
                "help: `proof-trusted` means the solver reached UNSAT but the proof carried a \
                 step no checker confirmed, so the verdict is withheld. It is a completeness \
                 gap, not a soundness one: nothing was proved wrong, and the contract may well \
                 be true."
            );
            eprintln!(
                "help: isolate it with `--filter <NAME>` and read the obligation with \
                 `--emit-smt`. Stating the same property in a form the solver can present — \
                 an explicit bound rather than an implied one, or returning a value rather \
                 than mutating through a reference — often gets it proved."
            );
        }
        if self.saw_loader_error {
            eprintln!(
                "help: that is a dynamic-loader failure, not a proof failure: `{DRIVER_BIN}` is \
                 linked with absolute rpaths into a Trust private sysroot. Rebuild it against the \
                 current stage2:  cargo build --release -p trust-wp-driver --bin trust-wp-rustc"
            );
        }
        if self.saw_missing_std {
            eprintln!(
                "help: the engine could not resolve a sysroot. Check that `rustc --print sysroot` \
                 names the Trust stage2 sysroot, then re-run."
            );
        }
        if self.saw_unresolved_contract_crate {
            eprintln!(
                "help: the contract crate was not usable — most often it is stale, built \
                 against an older compiler or an older trust-wp-core than the engine. \
                 Rebuild it:  cargo build -p trust-wp -p creusot-contracts"
            );
            eprintln!(
                "help: or pass your own:  trust-wp <FILE.rs> -- --extern \
                 trust_wp=<path to libtrust_wp.rlib>"
            );
        }
        if compile_failed
            && !self.saw_loader_error
            && !self.saw_missing_std
            && !self.saw_unresolved_contract_crate
        {
            eprintln!(
                "help: the code did not compile, so no contract was proved — the errors above \
                 come from the compiler, not from a failed proof."
            );
        }
    }
}

fn canonical_source(file: &Path) -> Option<PathBuf> {
    if file.extension() != Some(OsStr::new("rs")) {
        eprintln!("error: expected a `.rs` file, got `{}`", file.display());
        eprintln!("help: to verify a whole crate, run `trust-wp` inside the crate directory");
        eprintln!(
            "help: for something to try right now:  trust-wp example > demo.rs && trust-wp demo.rs"
        );
        return None;
    }
    match fs::canonicalize(file) {
        Ok(path) => Some(path),
        Err(err) => {
            eprintln!("error: cannot read `{}`: {err}", file.display());
            eprintln!(
                "help: for something to try right now:  trust-wp example > demo.rs && trust-wp demo.rs"
            );
            None
        }
    }
}

/// A stable per-input tag for the scratch output directory.
fn scratch_tag(path: &Path) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    path.hash(&mut hasher);
    hasher.finish()
}

/// Turn a file name into a legal crate name (`my-demo.rs` becomes `my_demo`).
fn crate_name_for(path: &Path) -> String {
    let stem = path
        .file_stem()
        .map_or_else(|| "demo".to_string(), |s| s.to_string_lossy().into_owned());
    let mut name: String = stem
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    if name.is_empty() || name.starts_with(|c: char| c.is_ascii_digit()) {
        name.insert(0, '_');
    }
    name
}

/// Render a value so a shell reproduces it byte for byte.
///
/// Single quotes, because the engine-argument block is newline-delimited on
/// purpose and a shell keeps newlines inside `'...'` verbatim. Collapsing them
/// to spaces would print a command the driver parses *differently* from the one
/// this tool actually runs: its parser splits on lines when a newline is
/// present and on whitespace when none is, so a value containing a space
/// (`--emit-smt-dir 'my smt'`) would silently become two arguments.
fn shell_quote(value: &str) -> String {
    format!("'{}'", value.replace('\'', r"'\''"))
}

/// The program plus its arguments as one shell-runnable line.
fn command_line(program: &Path, args: &[String]) -> String {
    let mut line = shell_quote(&program.display().to_string());
    for arg in args {
        line.push(' ');
        line.push_str(&shell_quote(arg));
    }
    line
}

/// The engine invocation, structured for the `--json` report.
fn dry_run_json(
    engine: &Engine,
    args: &[String],
    trust_wp_args: Option<&str>,
) -> serde_json::Value {
    let mut env = serde_json::json!({ RESULT_PROTOCOL_ENV: "1" });
    if let (Some(map), Some(trust_wp_args)) = (env.as_object_mut(), trust_wp_args) {
        map.insert(
            "TRUST_WP_ARGS".to_string(),
            serde_json::Value::from(trust_wp_args),
        );
    }
    serde_json::json!({
        "program": engine.program.display().to_string(),
        "engine_origin": engine.origin,
        "args": args,
        "env": env,
    })
}

/// Emit the `--dry-run` report and return the exit code.
fn dry_run_report(
    cli: &Cli,
    mode: &'static str,
    target: String,
    command: serde_json::Value,
) -> i32 {
    if cli.json {
        let run = report::RunReport {
            exit_code: EXIT_OK,
            mode,
            target,
            verify_mode: cli.verify_mode(),
            dry_run: true,
            dry_run_command: Some(command),
            ..report::RunReport::default()
        };
        report::print_json(&report::verify_report(&run, "verify"));
    }
    EXIT_OK
}

fn print_dry_run(engine: &Engine, args: &[String], trust_wp_args: &str) {
    out!("# engine found via {}", engine.origin);
    out!("TRUST_WP_ARGS={} \\", shell_quote(trust_wp_args));
    out!("{RESULT_PROTOCOL_ENV}=1 \\");
    out!("{}", command_line(&engine.program, args));
}

// ---------------------------------------------------------------------------
// Crate mode
// ---------------------------------------------------------------------------

fn run_crate(cli: &Cli) -> i32 {
    warn_about_trust_wp_home();
    let manifest_given = cli
        .passthrough
        .iter()
        .any(|a| a == "--manifest-path" || a.starts_with("--manifest-path="));
    if !manifest_given && find_manifest().is_none() {
        let cwd = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        eprintln!(
            "error: no Cargo.toml in {} or any parent directory",
            cwd.display()
        );
        eprintln!("help: verify a single file instead:  trust-wp <FILE.rs>");
        eprintln!(
            "help: get something to verify right now:  trust-wp example > demo.rs && trust-wp demo.rs"
        );
        emit_json_failure(
            cli,
            "crate",
            cwd.display().to_string(),
            EXIT_USAGE,
            (
                report::ErrorKind::Io,
                format!("no Cargo.toml in {} or any parent directory", cwd.display()),
            ),
        );
        return EXIT_USAGE;
    }

    let front = match find_cargo_front() {
        Ok(engine) => engine,
        Err(missing) => {
            missing.report();
            emit_json_failure(
                cli,
                "crate",
                env::current_dir()
                    .map(|d| d.display().to_string())
                    .unwrap_or_default(),
                EXIT_ENCODING_ERROR,
                (report::ErrorKind::EngineMissing, missing.summary()),
            );
            return EXIT_ENCODING_ERROR;
        }
    };
    // `cargo-trust-wp` looks for the driver next to itself or on $PATH; make
    // sure the one this front door resolved is reachable either way.
    let driver = match find_engine(&DRIVER_BINS, "TRUST_WP_RUSTC") {
        Ok(engine) => engine,
        Err(missing) => {
            missing.report();
            emit_json_failure(
                cli,
                "crate",
                env::current_dir()
                    .map(|d| d.display().to_string())
                    .unwrap_or_default(),
                EXIT_ENCODING_ERROR,
                (report::ErrorKind::EngineMissing, missing.summary()),
            );
            return EXIT_ENCODING_ERROR;
        }
    };

    let mut args: Vec<String> = cli.engine_args.clone();
    if cli.strict_obligations {
        args.push("--strict-obligations".to_string());
    }
    args.extend(cli.passthrough.iter().cloned());

    // `cargo-trust-wp` looks for the driver next to itself or on $PATH, so the
    // real run puts the driver this front door resolved at the front of PATH.
    // The dry-run line has to show that too, or the command it prints resolves
    // a different engine than the command it stands for.
    let driver_dir = driver.program.parent().map(Path::to_path_buf);

    if cli.dry_run {
        if cli.json {
            let command = dry_run_json(&front, &args, None);
            let target = env::current_dir()
                .map(|dir| dir.display().to_string())
                .unwrap_or_default();
            return dry_run_report(cli, "crate", target, command);
        }
        out!("# engine found via {}", front.origin);
        if let Some(ref dir) = driver_dir {
            out!("PATH={} \\", shell_quote(&prepend_path(dir)));
        }
        out!("{}", command_line(&front.program, &args));
        return EXIT_OK;
    }

    let caller_wants_wire = env::var_os(RESULT_PROTOCOL_ENV).is_some();
    let mut command = Command::new(&front.program);
    apply_verbose_logging(cli, &mut command);
    command
        .args(&args)
        .stdout(Stdio::inherit())
        // Piped, not inherited: `cargo-trust-wp` re-emits the aggregated wire
        // line and forwards the driver's per-obligation `TRUST_WP_DIAGNOSTIC:`
        // lines unconditionally, because harnesses consume them. Those are
        // machine output; the help promises a user sees them only on request.
        // Relaying through the same filter single-file mode uses keeps the two
        // modes telling the user the same story.
        .stderr(Stdio::piped());
    if let Some(ref dir) = driver_dir {
        command.env("PATH", prepend_path(dir));
    }

    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(err) => {
            eprintln!(
                "error: cannot run the trust-wp cargo front end at {}: {err}",
                front.program.display()
            );
            eprintln!("help: run `trust-wp doctor` to see what is missing");
            return EXIT_ENCODING_ERROR;
        }
    };

    let started = Instant::now();
    let mut relay =
        StderrRelay::with_style(caller_wants_wire, style::Style::new(cli.color)).quiet(cli.quiet);
    relay.drain(child.stderr.take());

    let elapsed = started.elapsed();
    let child_code = match child.wait() {
        Ok(status) => status.code().unwrap_or(101),
        Err(err) => {
            eprintln!("error: the trust-wp cargo front end did not finish: {err}");
            return EXIT_ENCODING_ERROR;
        }
    };

    // `cargo-trust-wp` has already applied `--strict-obligations`; passing it
    // again here would be redundant, not wrong, but the wire record is the
    // single source of truth either way.
    let code = engine_exit_code(
        child_code,
        relay.wire.as_ref(),
        cli.verify_mode(),
        cli.strict_obligations,
        relay.saw_compiler_error,
    );
    relay.print_hints(relay.wire.is_none() && child_code != 0);
    let nothing_proved = proved_nothing(child_code, relay.wire.as_ref(), cli.verify_mode());
    if nothing_proved {
        report_nothing_proved(cli);
    }
    report_elapsed(cli, elapsed);
    explain_exit_code(code);
    let target = env::current_dir()
        .map(|dir| dir.display().to_string())
        .unwrap_or_default();
    let error = nothing_proved.then(|| {
        (
            report::ErrorKind::NoVerdict,
            "the engine examined no obligation — nothing was proved".to_string(),
        )
    });
    emit_json_report(
        cli,
        "crate",
        target,
        code,
        Some(child_code),
        relay,
        None,
        None,
        error,
    );
    code
}

fn find_manifest() -> Option<PathBuf> {
    let cwd = env::current_dir().ok()?;
    cwd.ancestors()
        .map(|dir| dir.join("Cargo.toml"))
        .find(|manifest| manifest.is_file())
}

fn prepend_path(dir: &Path) -> String {
    let current = env::var_os("PATH").unwrap_or_default();
    let mut dirs = vec![dir.to_path_buf()];
    dirs.extend(env::split_paths(&current));
    env::join_paths(dirs).map_or_else(
        |_| dir.to_string_lossy().into_owned(),
        |joined| joined.to_string_lossy().into_owned(),
    )
}

// ---------------------------------------------------------------------------
// `example` and `doctor`
// ---------------------------------------------------------------------------

/// A tiny contracted crate that this tool can actually verify.
///
/// Both contracts are lifted from the workspace's own passing fixture,
/// `tests/fixtures/simple_project/src/lib.rs`.
const EXAMPLE_SOURCE: &str = r#"// demo.rs — written by `trust-wp example`
//
//   verify it:            trust-wp demo.rs
//   verify one function:  trust-wp --filter increment demo.rs
//   see the proof query:  trust-wp --emit-smt demo.rs
//   watch it fail:        change `x + 1` to `x - 1` below and re-run
//
// In a Cargo project, depend on the contract crate instead:
//   [dependencies]
//   trust-wp = { path = "/path/to/trust-wp/crates/trust-wp" }
// then run `trust-wp` in the crate directory.

use trust_wp::{ensures, requires};

/// `requires` is the precondition the caller must establish; `ensures` is the
/// postcondition trust-wp proves for every input that satisfies it.
#[requires(x > 0)]
#[ensures(result > x)]
pub fn increment(x: i32) -> i32 {
    x + 1
}

/// The simplest possible contract: `result` names the return value.
#[ensures(result == x)]
pub fn identity(x: i32) -> i32 {
    x
}
"#;

/// Write generated text to a file, or to stdout when no path is given.
///
/// `next` names the command to run against the file just written, so every
/// generator ends by telling the user what to do with the result.
pub(crate) fn write_text(
    out: Option<&Path>,
    text: &str,
    what: &str,
    next: impl FnOnce(&Path) -> String,
) -> i32 {
    match out {
        Some(path) => match fs::write(path, text) {
            Ok(()) => {
                eprintln!("wrote {}", path.display());
                eprintln!("next:  {}", next(path));
                EXIT_OK
            }
            Err(err) => {
                eprintln!("error: cannot write {}: {err}", path.display());
                EXIT_USAGE
            }
        },
        None => match std::io::stdout().write_all(text.as_bytes()) {
            Ok(()) => EXIT_OK,
            Err(err) => {
                eprintln!("error: cannot write {what}: {err}");
                EXIT_USAGE
            }
        },
    }
}

fn write_example(out: Option<&Path>) -> i32 {
    match out {
        Some(path) => match fs::write(path, EXAMPLE_SOURCE) {
            Ok(()) => {
                eprintln!("wrote {}", path.display());
                eprintln!("next:  trust-wp {}", path.display());
                EXIT_OK
            }
            Err(err) => {
                // The command line was fine; the filesystem was not. Exit 3
                // means "you typed something wrong", which would send the user
                // looking in the wrong place.
                eprintln!("error: cannot write {}: {err}", path.display());
                EXIT_ENCODING_ERROR
            }
        },
        None => match std::io::stdout().write_all(EXAMPLE_SOURCE.as_bytes()) {
            Ok(()) => EXIT_OK,
            Err(err) => {
                eprintln!("error: cannot write the example: {err}");
                EXIT_ENCODING_ERROR
            }
        },
    }
}

fn run_doctor(json: bool) -> i32 {
    if json {
        return report::doctor_report();
    }
    out!("{}", render_version());
    out!();

    let mut ready = true;

    // Report a rejected $TRUST_WP_HOME before anything it would have
    // affected, so the rest of the report is read in that light.
    if let Some(complaint) = trust_wp_home_complaint() {
        // No "run doctor" pointer here: the checkout line below already
        // answers the question, and this is doctor.
        ready = false;
        out!("  TRUST_WP_HOME     IGNORED — {complaint}");
    }

    match repo_root() {
        Some(root) => out!("  checkout          {}", root.display()),
        None => {
            ready = false;
            // Saying "set $TRUST_WP_HOME" to someone who already set it is
            // how a five-minute problem becomes an hour.
            match env::var_os("TRUST_WP_HOME") {
                Some(_) => out!("  checkout          NOT FOUND ($TRUST_WP_HOME did not resolve)"),
                None => out!("  checkout          NOT FOUND (set $TRUST_WP_HOME)"),
            }
        }
    }

    match find_engine(&DRIVER_BINS, "TRUST_WP_RUSTC") {
        Ok(engine) => {
            out!(
                "  {DRIVER_BIN:<17} {} (via {})",
                engine.program.display(),
                engine.origin
            );
            // Ask the driver to print its own option help: the cheapest probe
            // that still loads every rustc_private dylib it needs at runtime.
            match Command::new(&engine.program)
                .env("TRUST_WP_ARGS", "--help")
                .output()
            {
                Ok(output) if output.status.success() => {
                    out!("  engine runtime    ok (driver loads and responds)");
                }
                Ok(output) => {
                    ready = false;
                    let detail = String::from_utf8_lossy(&output.stderr);
                    let first = detail.lines().next().unwrap_or("no output").trim();
                    out!("  engine runtime    BROKEN: {first}");
                    out!(
                        "                    it needs a Trust sysroot at runtime; rebuild it against \
                         the current stage2:"
                    );
                    out!(
                        "                    cargo build --release -p trust-wp-driver --bin trust-wp-rustc"
                    );
                }
                Err(err) => {
                    ready = false;
                    out!("  engine runtime    BROKEN: {err}");
                }
            }
        }
        Err(missing) => {
            ready = false;
            out!("  {DRIVER_BIN:<17} MISSING (single-file and crate mode unavailable)");
            for fix in missing.actionable_fixes() {
                out!("                    {fix}");
            }
        }
    }

    match find_cargo_front() {
        Ok(engine) => out!(
            "  {CARGO_FRONT_BIN:<17} {} (via {})",
            engine.program.display(),
            engine.origin
        ),
        Err(missing) => {
            ready = false;
            out!("  {CARGO_FRONT_BIN:<17} MISSING (crate mode unavailable)");
            for fix in missing.actionable_fixes() {
                out!("                    {fix}");
            }
        }
    }

    for (crate_name, rlib_name, package) in CONTRACT_CRATES {
        let label = format!("  {crate_name:<17}");
        match find_contract_rlib(rlib_name) {
            Some((rlib, _)) => out!("{label} {}", rlib.display()),
            None => {
                // Only the native contract crate is required: a machine that
                // never built the Creusot compat shim is still ready.
                let required = crate_name == "trust_wp";
                ready &= !required;
                let note = if required {
                    "NOT BUILT (single-file mode needs it)"
                } else {
                    "not built (only needed for `use creusot_contracts::…` files)"
                };
                out!("{label} {rlib_name} {note}");
                out!("                    cargo build --release -p {package}");
            }
        }
    }

    // Crate mode shells out to `cargo`; a report that says "ready" without it
    // is wrong for half the tool.
    match Command::new("cargo").arg("--version").output() {
        Ok(output) if output.status.success() => {
            let version = String::from_utf8_lossy(&output.stdout).trim().to_string();
            out!("  cargo             {version}");
        }
        _ => {
            ready = false;
            out!("  cargo             NOT RUNNABLE (crate mode unavailable)");
            out!("                    single-file mode still works: trust-wp <FILE.rs>");
        }
    }

    // Asked from inside the checkout on purpose: `rust-toolchain.toml` pins
    // `channel = "trust"`, and rustup resolves that per directory. Probing in
    // the user's cwd would report whatever toolchain *they* are pinned to,
    // which is not the one the engine was built against.
    let mut sysroot_probe = Command::new("rustc");
    sysroot_probe.args(["--print", "sysroot"]);
    if let Some(root) = repo_root() {
        sysroot_probe.current_dir(root);
    }
    match sysroot_probe.output() {
        Ok(output) if output.status.success() => {
            let sysroot = String::from_utf8_lossy(&output.stdout).trim().to_string();
            out!("  active sysroot    {sysroot}");
        }
        Ok(output) => {
            ready = false;
            let detail = String::from_utf8_lossy(&output.stderr);
            out!(
                "  active sysroot    UNAVAILABLE: {}",
                detail.lines().next().unwrap_or("unknown error").trim()
            );
            out!("                    the Trust toolchain must be installed and built");
        }
        Err(err) => {
            ready = false;
            out!("  active sysroot    UNAVAILABLE: {err}");
        }
    }

    out!();
    if ready {
        out!("ready. try:  trust-wp example > demo.rs && trust-wp demo.rs");
        EXIT_OK
    } else {
        out!("not ready — fix the lines above, then re-run `trust-wp doctor`.");
        EXIT_ENCODING_ERROR
    }
}

// ---------------------------------------------------------------------------
// Help and version
// ---------------------------------------------------------------------------

/// The version this binary reports, with build metadata when it was built
/// from a git checkout: `0.3.0+gc1645cf`, or `0.3.0` from a tarball.
///
/// The `+g…` form is the repository's documented dev-build spelling and, being
/// SemVer build metadata, is ignored for version comparison — `0.3.0+gc1645cf`
/// still satisfies `version = "0.3"` and `"=0.3.0"`.
pub(crate) fn build_version() -> String {
    match option_env!("TRUST_WP_BUILD") {
        Some(build) => format!("{}+{build}", env!("CARGO_PKG_VERSION")),
        None => env!("CARGO_PKG_VERSION").to_string(),
    }
}

fn render_version() -> String {
    format!(
        "trust-wp {} ({})",
        build_version(),
        env!("CARGO_PKG_REPOSITORY")
    )
}

fn render_help(topic: Option<&str>, brief: bool) -> String {
    match topic {
        None | Some("help" | "version") if brief => render_brief(),
        None | Some("help" | "version") => render_overview(),
        Some("verify") => render_verify_help(),
        Some("contract") => contract::help(),
        Some("bundle") => bundle::help(),
        Some("result") => render_result_help(),
        Some("doctor") => render_doctor_help(),
        Some("example") => render_example_help(),
        Some("completions") => render_completions_help(),
        Some("man") => render_man_help(),
        Some(_) => render_overview(),
    }
}

fn render_overview() -> String {
    format!(
        r"trust-wp {version} — deductive verification for Rust (weakest precondition)

Write contracts — #[requires], #[ensures], #[invariant], #[variant],
proof_assert! — and trust-wp proves them: it intercepts post-borrowck MIR,
generates verification conditions with a Dijkstra-style weakest-precondition
transformation, and discharges them on the `ay` SMT solver.

The verbs, flag spellings and exit codes are meant to feel familiar to users of
Creusot. trust-wp is an independent ALab tool: not affiliated with, derived
from, or endorsed by that project.

USAGE:
    trust-wp <FILE.rs> [OPTIONS]    verify one file — no Cargo project needed
    trust-wp [OPTIONS]              verify the crate in the current directory
    trust-wp <COMMAND> [ARGS]

COMMANDS:
    verify [FILE.rs] [OPTIONS]   run the verifier (the two forms above, spelled out)
    contract parse <EXPR>        parse a contract expression; print its normalized form
    contract vc ...              emit a weakest-precondition VC as SMT-LIB2
    bundle verify <REQ.json>     verify a verify-bundle request in-process (no solver)
    bundle validate <REQ.json>   check a request's structure only
    bundle replay <REQ> <RES>    re-check a result's proof evidence, independently
    bundle example [-o FILE]     write a minimal request to start from
    result [FILE | -]            decode a saved result-protocol transcript
    completions <SHELL>          print a completion script for bash, zsh or fish
    man                          print the roff manual page
    doctor                       report what is installed, and how to fix what is not
    example [-o FILE]            write a tiny contracted sample and exit
    help [COMMAND]               this text, or one command's help

    `contract`, `bundle` and `result` run in this process: no engine, no
    sysroot and no solver. `trust-wp help <COMMAND>` has the details.

FIRST RUN (nothing to configure):
    trust-wp example > demo.rs && trust-wp demo.rs

OPTIONS:
    --filter <NAME>        only verify functions whose path matches NAME
    --timeout <SECS>       per-function solver timeout (engine default: 60)
    --emit-smt             print the SMT-LIB2 queries to stdout
    --emit-smt-dir <DIR>   write one annotated .smt2 file per function
                           These render the obligation as a weakest
                           precondition; they are not the query that decided
                           the verdict, and for a `&mut` parameter they cannot
                           be. Any query that is too weak to decide says so in
                           a comment naming the symbols it leaves free.
    --strict-trust         require independently replayed proof authority. This
                           is the engine's default and cannot be turned off;
                           the flag exists so scripts can state it.
    --no-strict-trust      deprecated compatibility spelling; accepted, and
                           does NOT relax the requirement
    --strict-axioms        treat unverified axioms as errors
    --strict-obligations   treat dropped-obligation warnings as errors (exit 2)
    --stop-after-analysis  stop the compiler after MIR analysis (contracts are
                           still verified; nothing is code-generated)
    --no-verify            skip verification entirely
    --verify               verify even when only emitting SMT (--emit-smt alone
                           emits without proving)
    --track <LEVEL>        memory tracking: auto, reg, ptr, mem
    --edition <YEAR>       edition for single-file mode (default: 2021)
    --dry-run              print the exact engine command instead of running it
    -q, --quiet            print only failures, and the summary. Suppresses the
                           per-function `verified ✓` lines and timings; nothing
                           that went wrong is ever suppressed.
    -v, -vv, --verbose     show verification progress
    --color <WHEN>         auto (default), always, never. `auto` colours when
                           stderr is a terminal and NO_COLOR is unset.
    --json                 print one JSON report on stdout (trust-wp.cli-report.v1) —
                           exactly one document, on every exit, for every command that
                           takes it; human output stays on stderr and exit codes are
                           unchanged. Not accepted by `help`, `example` or
                           `bundle example`, nor alongside `--emit-smt`.
    -h, --help             -h for a summary, --help for this page (both work
                           with nothing installed)
    -V, --version          print the version (works with nothing installed)

    Unknown options are refused, never ignored. To hand an option to the
    underlying tool unchanged, put it after `--`:
        trust-wp -- -p mycrate --all-features     (crate mode: goes to cargo)
        trust-wp demo.rs -- --cfg foo             (single file: goes to rustc)

EXIT CODES:
    0    everything verified
    1    at least one contract failed (a counterexample exists)
    2    encoding/solver error, soundness gap, nothing was proved, or the
         engine could not run
    3    contract parse error, or bad command line
    101  internal error (panic)

ENVIRONMENT:
    TRUST_WP_RUSTC          path to the `{driver}` driver binary
    TRUST_WP_CARGO          path to the `{cargo_front}` binary
    TRUST_WP_HOME           trust-wp checkout to resolve helpers and libraries from
    TRUST_WP_RESULT_PROTOCOL=1
                            also print the machine-readable result line on stderr
    NO_COLOR                set to any value and `--color auto` stays plain

{log_help}

WHAT THIS BINARY IS:
    A front door. It runs `{cargo_front}` for a crate and `{driver}` for a single
    file, and reads their structured result protocol to choose an exit code. The
    proving happens there, not here.

See contract-syntax.md in the trust-wp checkout for the full contract grammar.",
        version = build_version(),
        log_help = trust_wp_log_help(),
        cargo_front = CARGO_FRONT_BIN,
        driver = DRIVER_BIN,
    )
}

/// The `-h` page: what to type, and where the full text is.
///
/// Every line here is also in `--help`; this is a selection, never a second
/// source of truth.
fn render_brief() -> String {
    format!(
        r"trust-wp {version}
Prove Rust code correct for every input, without running it.

USAGE:
    trust-wp <FILE.rs>       verify one file — no Cargo project needed
    trust-wp                 verify the crate in the current directory
    trust-wp <COMMAND>       verify, contract, bundle, result, doctor, example, help

COMMON OPTIONS:
    --filter <NAME>          only verify functions whose path matches NAME
    --timeout <SECS>         per-function solver timeout (engine default: 60)
    -q, --quiet              print only failures, and the summary
    -v, --verbose            show verification progress
    --json                   print one JSON report on stdout
    --dry-run                print the engine command instead of running it
    -V, --version            print the version

FIRST RUN (nothing to configure):
    trust-wp example > demo.rs && trust-wp demo.rs

`trust-wp --help` for every option, `trust-wp help <COMMAND>` for one command,
`trust-wp doctor` if something is not installed.",
        version = build_version(),
    )
}

fn render_man_help() -> String {
    r"trust-wp man — print the roff manual page

USAGE:
    trust-wp man

    The page goes to stdout. To read it without installing:

        trust-wp man | man -l -

    To install it where `man trust-wp` will find it:

        trust-wp man > ~/.local/share/man/man1/trust-wp.1

    It is generated from the same option table as `completions` and `--help`,
    and carries no build date, so the same binary always prints the same page."
        .to_string()
}

fn render_completions_help() -> String {
    r#"trust-wp completions — print a shell completion script

USAGE:
    trust-wp completions <bash|zsh|fish>

    The script goes to stdout. Install it where your shell looks:

        bash   trust-wp completions bash > \
                 ~/.local/share/bash-completion/completions/trust-wp
        zsh    trust-wp completions zsh > "${fpath[1]}/_trust-wp"
        fish   trust-wp completions fish > \
                 ~/.config/fish/completions/trust-wp.fish

    Then start a new shell. The script is generated from the same option table
    the parser and `--help` are checked against, so it cannot fall behind them
    without a test failing.

    Completes: the verbs, `.rs` files in first position, every option, and the
    values of the options that take a fixed set (--color, --track, --edition).
    Options whose value is a function name or a number complete nothing, which
    is better than offering filenames that would be wrong."#
        .to_string()
}

fn render_result_help() -> String {
    r"trust-wp result — decode a result-protocol transcript

USAGE:
    trust-wp result [FILE | -]

    Reads a transcript that contains the engine's machine lines
    (`TRUST_WP_RESULT:v1 ...` and `TRUST_WP_DIAGNOSTIC:v1 ...` — the stderr of a
    run with TRUST_WP_RESULT_PROTOCOL=1, or of `cargo-trust-wp`), merges them the
    way `verify` does, and prints the verdict (or the `--json` report).

    The exit code is the decoded verdict's (0/1/2/3); a transcript with no result
    line exits 2 — nothing was proved — exactly like a run. With no FILE (or `-`)
    the transcript is read from stdin.

    `--json` reports the same document `verify` does, with mode `transcript`.

EXAMPLE:
    TRUST_WP_RESULT_PROTOCOL=1 cargo-trust-wp 2> run.log; trust-wp --json result run.log"
        .to_string()
}

fn render_doctor_help() -> String {
    r"trust-wp doctor — report what is installed, and how to fix what is not

USAGE:
    trust-wp doctor [--json]

    Checks the trust-wp checkout, the `trust-wp-rustc` driver (and that it loads
    at runtime), the `cargo-trust-wp` front end, the built `trust_wp` contract
    crate, and the active rustc sysroot. Exit 0 when everything `verify` needs is
    in place, 2 otherwise. The in-process verbs (`contract`, `bundle`, `result`)
    work either way.

    `--json` reports {ready, status, checks[{name, ok, detail, fixes[]}]}."
        .to_string()
}

fn render_example_help() -> String {
    r"trust-wp example — write a tiny contracted sample

USAGE:
    trust-wp example [-o FILE]

    Writes a small Rust file with two contracted functions to stdout (or FILE).
    `trust-wp example > demo.rs && trust-wp demo.rs` is the whole first run.
    `trust-wp bundle example` is the equivalent for verify-bundle requests."
        .to_string()
}

fn render_verify_help() -> String {
    format!(
        r"trust-wp verify — run the verifier on one file or on a crate

USAGE:
    trust-wp [verify] <FILE.rs> [OPTIONS] [-- RUSTC_ARGS]
    trust-wp [verify] [OPTIONS] [-- CARGO_ARGS]

    With a file, `{driver}` compiles and verifies that one file (no Cargo
    project needed; `use trust_wp::{{ensures, requires}};` resolves against the
    built contract crate). Without one, `{cargo_front}` verifies the crate whose
    Cargo.toml is found from the current directory.

OPTIONS:
    --filter <NAME>        only verify functions whose path matches NAME
    --timeout <SECS>       per-function solver timeout (engine default: 60)
    --emit-smt             print the SMT-LIB2 queries to stdout (not with --json)
    --emit-smt-dir <DIR>   write one annotated .smt2 file per function
    --strict-trust         require independently replayed proof authority (always on)
    --no-strict-trust      deprecated compatibility spelling; ignored
    --strict-axioms        treat unverified axioms as errors
    --strict-obligations   treat dropped-obligation warnings as errors (exit 2)
    --stop-after-analysis  stop after MIR analysis; prove nothing
    --no-verify            skip verification entirely
    --track <LEVEL>        memory tracking: auto, reg, ptr, mem
    --wide-pointers        enable wide-pointer support [UNIMPLEMENTED in the engine]
    --edition <YEAR>       edition for single-file mode (default: 2021)
    --dry-run              print the exact engine command instead of running it
    --json                 one JSON report on stdout: `status`, the engine's aggregate
                           counters (`summary`), and `diagnostics` — per-obligation
                           records the engine emits for NON-CLEAN obligations only
                           (`diagnostics_scope`), so a cleanly verified function has no
                           entry and an entry with `status: verified` is an uncredited
                           evidence gap (read `classification`). Records carry no source
                           location, violated clause or counterexample today; those keys
                           are reserved and null. With `--dry-run` the engine command is
                           reported under `dry_run` instead of being printed.
    -v, --verbose          show verification progress

    Unknown options are refused, never ignored. To hand an option to the
    underlying tool unchanged, put it after `--`. Options and the file may
    appear in either order; a value that itself starts with `-` must be
    attached (`--filter=-foo`).

    `status` in the JSON report is derived from the exit code AND the counters,
    so it separates what the exit code alone conflates:
        verified        contracts were proved
        no_obligations  exit 0, but nothing was checked — a `--filter` that
                        matched nothing, or a target with no contracts
        not_requested   the run never asked for a verdict (--no-verify,
                        --stop-after-analysis, or emit-only without --verify)
        failed          a contract was disproved
        soundness_gap   exit 2 whose only cause is unproved-but-accepted work
                        (trusted, skipped, assumed, axiom-dependent, vacuous)
        error           an encoding/solver error, panic, or structural failure
        compile_failed  the target did not compile, so nothing was proved
        no_verdict      the engine ran and reported no summary (fail-closed)
        parse_error     a contract failed to parse
        dry_run         nothing ran; `dry_run` holds the command

{exit_codes}

    A clean compile that produces no verification summary exits 2: nothing was
    proved, so nothing is reported as proved.",
        driver = DRIVER_BIN,
        cargo_front = CARGO_FRONT_BIN,
        exit_codes = EXIT_CODES,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn a_proof_trusted_verdict_is_explained_and_nothing_else_triggers_it() {
        let mut relay = StderrRelay::collecting();
        relay.line("trust-wp: f verified \u{2713}");
        relay.line("trust-wp: g FAILED \u{2717} (postcondition)");
        assert!(
            !relay.saw_proof_trusted,
            "a clean run and an ordinary failure must not look like a demotion"
        );

        // The engine's own spelling, which is what the relay actually sees.
        relay.line("? abs_mut unknown (proof-trusted)");
        assert!(relay.saw_proof_trusted);
    }

    #[test]
    fn a_set_but_unusable_trust_wp_home_is_complained_about() {
        // Unset, or set to nothing: no instruction was given, so none is
        // being ignored.
        assert_eq!(complaint_for_home(None), None);
        assert_eq!(complaint_for_home(Some(OsStr::new(""))), None);

        // A real checkout is accepted in silence.
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("the crate is two levels below the workspace root");
        assert_eq!(complaint_for_home(Some(root.as_os_str())), None);

        // Set to something that is not a checkout: the value is discarded, so
        // it has to be reported. Silently resolving the engine from a
        // different checkout than the caller named is the failure this
        // prevents.
        let missing = complaint_for_home(Some(OsStr::new("/nonexistent-trust-wp-checkout")))
            .expect("a nonexistent path must be complained about");
        assert!(missing.contains("no such directory"), "{missing}");
        assert!(
            missing.contains("/nonexistent-trust-wp-checkout"),
            "{missing}"
        );

        let wrong_dir = complaint_for_home(Some(OsStr::new("/")))
            .expect("a directory that is not a checkout must be complained about");
        assert!(
            wrong_dir.contains("no crates/trust-wp-driver"),
            "{wrong_dir}"
        );
    }

    #[test]
    fn help_and_version_need_no_engine() {
        assert_eq!(
            parse_cli(&args(&["--help"])).unwrap().mode,
            Mode::Help {
                topic: None,
                brief: false,
            }
        );
        assert_eq!(
            parse_cli(&args(&["-h"])).unwrap().mode,
            Mode::Help {
                topic: None,
                brief: true,
            }
        );
        assert_eq!(
            parse_cli(&args(&["--version"])).unwrap().mode,
            Mode::Version
        );
        assert_eq!(parse_cli(&args(&["-V"])).unwrap().mode, Mode::Version);
        // Even with a file and options present, help wins and stays pure.
        assert_eq!(
            parse_cli(&args(&["demo.rs", "--filter", "f", "--help"]))
                .unwrap()
                .mode,
            Mode::Help {
                topic: None,
                brief: false,
            }
        );
        // Both pages tell a first-time reader the same first command, and the
        // short one stays inside an 80x24 terminal.
        for page in [render_help(None, false), render_help(None, true)] {
            assert!(page.contains("trust-wp example > demo.rs && trust-wp demo.rs"));
            assert!(page.lines().all(|l| l.chars().count() <= 88), "{page}");
        }
        let brief = render_help(None, true);
        assert!(
            brief.lines().count() <= 24,
            "-h is {} lines",
            brief.lines().count()
        );
        assert!(brief.contains("--help"), "-h must point at the full page");
        assert!(render_version().starts_with("trust-wp "));
    }

    #[test]
    fn bare_file_is_single_file_mode() {
        let cli = parse_cli(&args(&["demo.rs"])).unwrap();
        assert_eq!(cli.mode, Mode::File(PathBuf::from("demo.rs")));
        assert_eq!(cli.edition, "2021");
    }

    #[test]
    fn no_file_is_crate_mode() {
        let cli = parse_cli(&args(&["--filter", "increment"])).unwrap();
        assert_eq!(cli.mode, Mode::Crate);
        assert_eq!(cli.engine_args, args(&["--filter", "increment"]));
    }

    #[test]
    fn engine_flags_are_normalized_to_engine_spelling() {
        let cli = parse_cli(&args(&[
            "-v",
            "--emit-smt",
            "--emit-smt-dir=./smt",
            "--timeout=30",
            "--track",
            "reg",
            "--no-strict-trust",
            "demo.rs",
        ]))
        .unwrap();
        assert_eq!(
            cli.engine_args,
            args(&[
                "--verbose",
                "--emit-smt",
                "--emit-smt-dir",
                "./smt",
                "--timeout",
                "30",
                "--track=reg",
                "--no-strict-trust",
            ])
        );
    }

    #[test]
    fn strict_obligations_is_wrapper_local() {
        let cli = parse_cli(&args(&["--strict-obligations"])).unwrap();
        assert!(cli.strict_obligations);
        assert!(cli.engine_args.is_empty());
    }

    #[test]
    fn passthrough_is_split_at_double_dash() {
        let cli = parse_cli(&args(&["demo.rs", "--", "--cfg", "foo"])).unwrap();
        assert_eq!(cli.mode, Mode::File(PathBuf::from("demo.rs")));
        assert_eq!(cli.passthrough, args(&["--cfg", "foo"]));
    }

    #[test]
    fn unknown_flags_fail_loudly() {
        let err = parse_cli(&args(&["--frobnicate"])).unwrap_err();
        assert!(err.message.contains("--frobnicate"));
        assert!(err.help.iter().any(|h| h.contains("--")));
    }

    #[test]
    fn flags_from_other_verifiers_name_the_alternative() {
        let err = parse_cli(&args(&["--verify-fn", "increment"])).unwrap_err();
        assert!(err.message.contains("--verify-fn"));
        assert!(err.help.iter().any(|h| h.contains("--filter")));

        let err = parse_cli(&args(&["--unwind=5"])).unwrap_err();
        assert!(err.message.contains("--unwind"));
        assert!(err.help.iter().any(|h| h.contains("#[invariant")));
    }

    #[test]
    fn missing_flag_values_are_reported() {
        let err = parse_cli(&args(&["--timeout"])).unwrap_err();
        assert!(err.message.contains("--timeout"));
        let err = parse_cli(&args(&["--track", "sideways"])).unwrap_err();
        assert!(err.message.contains("sideways"));
    }

    #[test]
    fn two_files_is_an_error() {
        let err = parse_cli(&args(&["a.rs", "b.rs"])).unwrap_err();
        assert!(err.message.contains("one file per run"));
    }

    #[test]
    fn example_verb_writes_to_stdout_by_default() {
        assert_eq!(
            parse_cli(&args(&["example"])).unwrap().mode,
            Mode::Example { out: None }
        );
        assert_eq!(
            parse_cli(&args(&["example", "-o", "demo.rs"]))
                .unwrap()
                .mode,
            Mode::Example {
                out: Some(PathBuf::from("demo.rs"))
            }
        );
        assert!(parse_cli(&args(&["example", "--nope"])).is_err());
    }

    #[test]
    fn example_source_is_something_the_engine_can_verify() {
        assert!(EXAMPLE_SOURCE.contains("use trust_wp::{ensures, requires};"));
        assert!(EXAMPLE_SOURCE.contains("#[requires(x > 0)]"));
        assert!(EXAMPLE_SOURCE.contains("#[ensures(result > x)]"));
        // crate-type=lib: a `fn main` would be dead weight.
        assert!(!EXAMPLE_SOURCE.contains("fn main"));
    }

    #[test]
    fn verify_mode_is_off_for_no_verify_and_emit_only_runs() {
        assert!(parse_cli(&args(&["demo.rs"])).unwrap().verify_mode());
        assert!(!parse_cli(&args(&["--no-verify", "demo.rs"]))
            .unwrap()
            .verify_mode());
        // `--stop-after-analysis` stops rustc before codegen; trust-wp has
        // already verified by then, so a verdict IS expected.
        assert!(parse_cli(&args(&["--stop-after-analysis"]))
            .unwrap()
            .verify_mode());
        assert!(!parse_cli(&args(&["--emit-smt"])).unwrap().verify_mode());
        assert!(parse_cli(&args(&["--emit-smt", "--verify"]))
            .unwrap()
            .verify_mode());
    }

    #[test]
    fn crate_names_are_legal_identifiers() {
        assert_eq!(crate_name_for(Path::new("/tmp/my-demo.rs")), "my_demo");
        assert_eq!(crate_name_for(Path::new("/tmp/9lives.rs")), "_9lives");
        assert_eq!(crate_name_for(Path::new("demo.rs")), "demo");
    }

    /// A wire record that reports real work: one verified function.
    fn verified_wire() -> StructuredVerificationResult {
        let mut wire = StructuredVerificationResult::default();
        wire.verified = 1;
        wire.normalize_exit_code();
        wire
    }

    #[test]
    fn exit_code_follows_the_engine_wire_line() {
        let mut failed = StructuredVerificationResult::default();
        failed.failed = 1;
        failed.normalize_exit_code();
        assert_eq!(
            engine_exit_code(0, Some(&failed), true, false, false),
            EXIT_VERIFICATION_FAILURE
        );

        let mut warned = verified_wire();
        warned.warnings = 2;
        warned.normalize_exit_code();
        assert_eq!(
            engine_exit_code(0, Some(&warned), true, false, false),
            EXIT_OK
        );
        assert_eq!(
            engine_exit_code(0, Some(&warned), true, true, false),
            EXIT_ENCODING_ERROR
        );

        let clean = verified_wire();
        assert_eq!(
            engine_exit_code(0, Some(&clean), true, false, false),
            EXIT_OK
        );
        // A compile failure under a clean wire line is still a failure.
        assert_eq!(engine_exit_code(1, Some(&clean), true, false, false), 1);
    }

    #[test]
    fn a_verdictless_run_fails_closed() {
        assert_eq!(
            engine_exit_code(0, None, true, false, false),
            EXIT_ENCODING_ERROR
        );
        // ...but only when a verdict was expected.
        assert_eq!(engine_exit_code(0, None, false, false, false), EXIT_OK);

        // The engine reports on every run that reaches verification, so no
        // wire line means it stopped earlier — the file did not compile.
        // rustc's exit 1 must NOT be relayed as "a counterexample exists".
        assert_eq!(
            engine_exit_code(1, None, true, false, false),
            EXIT_ENCODING_ERROR
        );
        // ...while the codes that already say what they mean pass through.
        assert_eq!(
            engine_exit_code(EXIT_USAGE, None, true, false, false),
            EXIT_USAGE
        );
        assert_eq!(engine_exit_code(101, None, true, false, false), 101);
    }

    /// An all-zero summary is the engine saying "I looked at nothing". A file
    /// with no contracts, or a `--filter` that matched nothing, both land here
    /// — and neither may be reported as a successful verification.
    #[test]
    fn a_run_that_examined_nothing_fails_closed() {
        let empty = StructuredVerificationResult::default();
        assert!(empty.examined_nothing());
        assert_eq!(
            engine_exit_code(0, Some(&empty), true, false, false),
            EXIT_ENCODING_ERROR
        );
        // Emit-only and --no-verify runs are not expected to prove anything.
        assert_eq!(
            engine_exit_code(0, Some(&empty), false, false, false),
            EXIT_OK
        );
        assert!(!verified_wire().examined_nothing());

        assert!(proved_nothing(0, None, true));
        assert!(proved_nothing(0, Some(&empty), true));
        assert!(!proved_nothing(0, Some(&verified_wire()), true));
        assert!(!proved_nothing(0, Some(&empty), false));
        // A compile failure is reported by the compiler, not by this hint.
        assert!(!proved_nothing(1, Some(&empty), true));
    }

    #[test]
    fn the_nothing_proved_hint_names_the_filter_that_matched_nothing() {
        let cli = parse_cli(&args(&["--filter", "typo", "demo.rs"])).unwrap();
        assert_eq!(filter_value(&cli), Some("typo"));
        let cli = parse_cli(&args(&["demo.rs"])).unwrap();
        assert_eq!(filter_value(&cli), None);
    }

    #[test]
    fn wire_lines_are_collected_even_when_hidden() {
        let mut relay = StderrRelay::new(false);
        let mut result = StructuredVerificationResult::default();
        result.verified = 3;
        relay.line(&result.to_wire_line());
        assert_eq!(relay.wire.as_ref().map(|w| w.verified), Some(3));
    }

    #[test]
    fn loader_failures_are_named_as_such() {
        let mut relay = StderrRelay::new(false);
        relay.note_symptom("dyld[123]: Library not loaded: @rpath/librustc_driver.dylib");
        assert!(relay.saw_loader_error);
    }
}
