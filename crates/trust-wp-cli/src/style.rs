// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Presentation for the engine's output.
//!
//! The engine writes plain, greppable lines — `trust-wp: <path> verified ✓`,
//! counterexample blocks, a counts summary — and every machine consumer reads
//! the wire protocol, not this text. That split is deliberate: the compat
//! harness and `cargo-trust-wp` drive the engine directly, so nothing here can
//! reach them. Presentation is the front door's job, and it happens on the way
//! through the relay.
//!
//! Three things happen to a line: the `trust-wp: ` prefix comes off (the user
//! knows which tool they ran), absolute paths inside the working directory are
//! shortened, and a verdict gets colour. Colour follows the usual contract —
//! `--color`, then `NO_COLOR`, then whether stderr is a terminal — so a piped
//! or redirected run is byte-identical to the plain text the engine emitted,
//! minus the prefix.

use std::{
    io::IsTerminal,
    path::{Path, MAIN_SEPARATOR},
};

/// When to colourise.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ColorChoice {
    /// Colour when stderr is a terminal and `NO_COLOR` is unset.
    #[default]
    Auto,
    Always,
    Never,
}

impl ColorChoice {
    /// Parse a `--color` value.
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "auto" => Some(Self::Auto),
            "always" | "yes" | "on" => Some(Self::Always),
            "never" | "no" | "off" => Some(Self::Never),
            _ => None,
        }
    }

    /// The accepted spellings, for the usage error.
    pub const VALUES: [&'static str; 3] = ["auto", "always", "never"];

    /// Resolve to a yes/no for this process.
    ///
    /// `NO_COLOR` is honoured for `auto` only: a user who wrote `--color=always`
    /// on the command line has overridden the environment on purpose.
    fn enabled(self) -> bool {
        match self {
            Self::Always => true,
            Self::Never => false,
            Self::Auto => std::env::var_os("NO_COLOR").is_none() && std::io::stderr().is_terminal(),
        }
    }
}

/// A resolved palette. `None` everywhere when colour is off, so the same code
/// path produces plain text without branching at every call site.
#[derive(Debug, Clone, Copy)]
pub struct Style {
    on: bool,
}

const RESET: &str = "\u{1b}[0m";
const BOLD: &str = "\u{1b}[1m";
const DIM: &str = "\u{1b}[2m";
const RED: &str = "\u{1b}[31m";
const GREEN: &str = "\u{1b}[32m";
const YELLOW: &str = "\u{1b}[33m";
const BLUE: &str = "\u{1b}[34m";

impl Style {
    pub fn new(choice: ColorChoice) -> Self {
        Self {
            on: choice.enabled(),
        }
    }

    fn wrap(self, code: &str, text: &str) -> String {
        if self.on && !text.is_empty() {
            format!("{code}{text}{RESET}")
        } else {
            text.to_string()
        }
    }

    pub fn bold(self, text: &str) -> String {
        self.wrap(BOLD, text)
    }
    pub fn dim(self, text: &str) -> String {
        self.wrap(DIM, text)
    }
    pub fn red(self, text: &str) -> String {
        self.wrap(RED, text)
    }
    pub fn green(self, text: &str) -> String {
        self.wrap(GREEN, text)
    }
    pub fn yellow(self, text: &str) -> String {
        self.wrap(YELLOW, text)
    }
    pub fn blue(self, text: &str) -> String {
        self.wrap(BLUE, text)
    }
    pub fn bold_red(self, text: &str) -> String {
        if self.on {
            format!("{BOLD}{RED}{text}{RESET}")
        } else {
            text.to_string()
        }
    }
    pub fn bold_green(self, text: &str) -> String {
        if self.on {
            format!("{BOLD}{GREEN}{text}{RESET}")
        } else {
            text.to_string()
        }
    }
}

/// The engine's own prefix on every human line.
const ENGINE_PREFIX: &str = "trust-wp: ";

/// Present one relayed engine line.
///
/// Returns the line to show. Anything unrecognised passes through with only
/// the prefix and path shortening applied, so a message this function has
/// never seen still reads correctly — it just does not gain colour.
/// True when `--quiet` should swallow this line.
///
/// Quiet means "tell me what went wrong": a clean verdict and its timing are
/// noise on a 200-function crate, and a CI log does not want 200 of them. The
/// summary, every non-clean verdict and every diagnostic still print, so a
/// quiet run that says nothing but its counts is a run that found nothing.
#[must_use]
pub fn is_routine_progress(line: &str) -> bool {
    let line = line.strip_prefix("trust-wp ").unwrap_or(line);
    let body = line.strip_prefix(ENGINE_PREFIX).unwrap_or(line);
    body.ends_with(" verified \u{2713}") || body.starts_with("timing: ")
}

pub fn present(line: &str, style: Style, cwd: Option<&Path>) -> String {
    // `-v` timing lines carry their own prefix, without the colon.
    let line = line.strip_prefix("trust-wp ").map_or(line, |rest| rest);
    let body = line.strip_prefix(ENGINE_PREFIX).unwrap_or(line);
    let body = shorten_paths(body, cwd);

    // The summary: "3 verified, 1 failed, 0 errors[, ...]".
    if let Some(rendered) = present_summary(&body, style) {
        return rendered;
    }

    // Per-obligation verdicts. The mark moves to the front so a wall of
    // results can be scanned down the left edge, but the WORD stays: `✗` alone
    // is invisible to `grep FAILED`, to a terminal without the glyph, and to a
    // screen reader. Redundant on purpose, the way `cargo test` prints
    // `... FAILED`.
    if let Some(name) = body.strip_suffix(" verified \u{2713}") {
        return format!(
            "{} {} {}",
            style.bold_green("✓"),
            style.bold(name),
            style.dim("verified")
        );
    }
    if let Some((name, rest)) = body.split_once(" FAILED \u{2717}") {
        return format!(
            "{} {} {}{}",
            style.bold_red("✗"),
            style.bold(name),
            style.bold_red("FAILED"),
            style.red(rest)
        );
    }
    for (marker, colour) in [
        (" unknown (", YELLOW),
        (" assumed (", YELLOW),
        (" vacuous", YELLOW),
        (" evidence gap (", YELLOW),
    ] {
        if let Some(index) = body.find(marker) {
            let (name, rest) = body.split_at(index);
            let mark = if colour == YELLOW { "?" } else { "!" };
            return format!(
                "{} {}{}",
                style.yellow(mark),
                style.bold(name),
                style.yellow(rest)
            );
        }
    }

    // Timing lines are secondary to the verdicts they sit between: dim the
    // whole line so `-v` adds detail without burying the result.
    if let Some(rest) = body.strip_prefix("timing: ") {
        return style.dim(&format!("  {rest}"));
    }

    // Diagnostic labels, wherever they appear.
    for (label, render) in [
        ("error: ", Style::bold_red as fn(Style, &str) -> String),
        ("warning: ", Style::yellow),
        ("help: ", Style::blue),
        ("note: ", Style::dim),
    ] {
        if let Some(rest) = body.strip_prefix(label) {
            let name = label.trim_end_matches(' ').trim_end_matches(':');
            return format!("{}: {rest}", render(style, name));
        }
    }

    // Counterexample bindings are indented `name = value`; dim the `=` so the
    // values stand out in the block that is the whole point of a failure.
    if let Some(rest) = body.strip_prefix("    ") {
        if let Some((name, value)) = rest.split_once(" = ") {
            if !name.contains(' ') {
                return format!(
                    "    {} {} {}",
                    style.bold(name),
                    style.dim("="),
                    style.green(value)
                );
            }
        }
    }

    body
}

/// Render the counts summary, colouring each count by what it means.
fn present_summary(body: &str, style: Style) -> Option<String> {
    // "N verified, N failed, N errors" is the engine's fixed opening; the
    // optional tail (", 2 trusted", ...) varies.
    if !body.contains(" verified, ") || !body.contains(" failed, ") {
        return None;
    }
    let parts: Vec<String> = body
        .split(", ")
        .map(|part| {
            let zero = part.starts_with("0 ");
            match part.split_once(' ') {
                // A zero count is not news; dim it so the eye lands on what happened.
                _ if zero => style.dim(part),
                Some((_, "verified")) => style.bold_green(part),
                Some((_, "failed")) => style.bold_red(part),
                Some((_, "errors" | "panicked")) => style.bold_red(part),
                _ => style.yellow(part),
            }
        })
        .collect();
    Some(parts.join(", "))
}

/// Rewrite absolute paths inside the working directory to relative ones.
///
/// The engine reports spans with absolute paths because it has no idea where
/// the user is standing. `/long/absolute/prefix/src/lib.rs:20:5` is noise when
/// the user is sitting in that directory.
fn shorten_paths(line: &str, cwd: Option<&Path>) -> String {
    let Some(cwd) = cwd else {
        return line.to_string();
    };
    let mut prefix = cwd.display().to_string();
    if !prefix.ends_with(MAIN_SEPARATOR) {
        prefix.push(MAIN_SEPARATOR);
    }
    if prefix.len() <= 1 || !line.contains(&prefix) {
        return line.to_string();
    }
    line.replace(&prefix, "")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plain() -> Style {
        Style::new(ColorChoice::Never)
    }
    fn coloured() -> Style {
        Style::new(ColorChoice::Always)
    }

    #[test]
    fn color_choice_parses_the_usual_spellings() {
        assert_eq!(ColorChoice::parse("auto"), Some(ColorChoice::Auto));
        assert_eq!(ColorChoice::parse("always"), Some(ColorChoice::Always));
        assert_eq!(ColorChoice::parse("never"), Some(ColorChoice::Never));
        assert_eq!(ColorChoice::parse("technicolor"), None);
        assert!(!ColorChoice::Never.enabled());
        assert!(ColorChoice::Always.enabled());
    }

    #[test]
    fn plain_output_keeps_the_shape_a_script_greps_for() {
        // The verdict moves to the front — `✓ name` reads better than
        // `name verified ✓` and matches how other tools report — but the shape
        // does NOT depend on whether colour is on, so a piped run and a
        // terminal run differ only in escape codes.
        assert_eq!(
            present("trust-wp: demo::increment verified ✓", plain(), None),
            "✓ demo::increment verified"
        );
        // The counts summary is the line scripts actually parse, and it is
        // passed through verbatim.
        assert_eq!(
            present("trust-wp: 2 verified, 0 failed, 0 errors", plain(), None),
            "2 verified, 0 failed, 0 errors"
        );
        assert_eq!(
            present("  counterexample:", plain(), None),
            "  counterexample:"
        );
    }

    #[test]
    fn a_verdict_gets_a_mark_and_colour() {
        let out = present("trust-wp: demo::increment verified ✓", coloured(), None);
        assert!(out.contains('✓'), "{out}");
        assert!(
            out.contains("\u{1b}[32m") || out.contains("\u{1b}[1m\u{1b}[32m"),
            "{out}"
        );
        assert!(out.contains("demo::increment"), "{out}");

        let out = present(
            "trust-wp: demo::increment FAILED ✗ (postcondition)",
            coloured(),
            None,
        );
        assert!(out.contains('✗'), "{out}");
        assert!(out.contains("\u{1b}[31m"), "{out}");
        assert!(out.contains("(postcondition)"), "{out}");
    }

    #[test]
    fn an_unknown_verdict_is_not_dressed_as_a_failure() {
        let out = present("trust-wp: demo::f unknown (timeout)", coloured(), None);
        assert!(
            out.contains("\u{1b}[33m"),
            "unknown is yellow, not red: {out}"
        );
        assert!(!out.contains("\u{1b}[31m"), "{out}");
    }

    #[test]
    fn zero_counts_recede_and_real_ones_stand_out() {
        let out = present("trust-wp: 1 verified, 1 failed, 0 errors", coloured(), None);
        assert!(
            out.contains("\u{1b}[2m0 errors"),
            "a zero count is dimmed: {out}"
        );
        assert!(out.contains("1 failed"), "{out}");
        // The plain rendering keeps the exact text the demo asserts on.
        assert_eq!(
            present("trust-wp: 1 verified, 1 failed, 0 errors", plain(), None),
            "1 verified, 1 failed, 0 errors"
        );
    }

    #[test]
    fn paths_under_the_working_directory_lose_the_prefix() {
        let cwd = Path::new("/work/project");
        assert_eq!(
            shorten_paths("  at /work/project/src/lib.rs:20:5", Some(cwd)),
            "  at src/lib.rs:20:5"
        );
        // A path outside the working directory is left alone: shortening it
        // would be a lie about where the file is.
        assert_eq!(
            shorten_paths("  at /elsewhere/src/lib.rs:20:5", Some(cwd)),
            "  at /elsewhere/src/lib.rs:20:5"
        );
    }

    #[test]
    fn unrecognised_lines_pass_through() {
        // The engine says plenty this function has never been taught; it must
        // still reach the user intact.
        assert_eq!(
            present("something entirely new from the solver", plain(), None),
            "something entirely new from the solver"
        );
        assert_eq!(
            present("trust-wp: brand new message", plain(), None),
            "brand new message"
        );
    }

    #[test]
    fn quiet_drops_routine_progress_only() {
        assert!(is_routine_progress("trust-wp: demo::f verified ✓"));
        assert!(is_routine_progress("trust-wp timing: demo::f: 28ms"));
        // Everything that is not a clean pass survives --quiet.
        assert!(!is_routine_progress(
            "trust-wp: demo::f FAILED ✗ (postcondition)"
        ));
        assert!(!is_routine_progress("trust-wp: demo::f unknown (timeout)"));
        assert!(!is_routine_progress(
            "trust-wp: 2 verified, 0 failed, 0 errors"
        ));
        assert!(!is_routine_progress("error: something broke"));
        assert!(!is_routine_progress("    x = 1"));
    }

    #[test]
    fn timing_lines_are_secondary() {
        // `trust-wp timing: …` loses the tool prefix like every other line and
        // is indented under the verdict it belongs to.
        assert_eq!(
            present(
                "trust-wp timing: increment: 28ms (solve: 28ms)",
                plain(),
                None
            ),
            "  increment: 28ms (solve: 28ms)"
        );
        let out = present("trust-wp timing: total 43ms", coloured(), None);
        assert!(out.contains("\u{1b}[2m"), "timing is dimmed: {out}");
    }

    #[test]
    fn counterexample_bindings_are_highlighted() {
        let out = present("    x = 1", coloured(), None);
        assert!(out.contains('x') && out.contains('1'), "{out}");
        assert_eq!(present("    x = 1", plain(), None), "    x = 1");
    }
}
