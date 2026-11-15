//! `trust-wp man` — the roff manual page.
//!
//! Generated from [`completions::FLAGS`] and [`completions::COMMANDS`], the
//! same table the parser and `--help` are tested against, so the three cannot
//! disagree. A man page written by hand is the artifact most likely to rot:
//! nothing executes it, so nothing notices when it goes stale.

use std::fmt::Write as _;

use crate::completions::{Value, COMMANDS, FLAGS};

/// Escape text for roff.
///
/// A leading `.` or `'` is a control character and would turn the line into a
/// (bogus) request, and `\` introduces an escape. Hyphens become `\-` so they
/// render as ASCII hyphen-minus rather than a Unicode dash — a copied
/// `--quiet` has to be paste-able back into a shell.
fn roff(text: &str) -> String {
    let escaped = text.replace('\\', "\\\\").replace('-', "\\-");
    match escaped.chars().next() {
        Some('.' | '\'') => format!("\\&{escaped}"),
        _ => escaped,
    }
}

/// Render the manual page.
#[must_use]
pub fn render() -> String {
    let mut page = String::new();

    // A manual page is dated by when its content last changed, which is the
    // commit date — never the build date, which would make one commit render
    // a different page every time it is built. Absent git there is no commit
    // to date it by, and an empty field is better than a wrong one.
    let _ = writeln!(
        page,
        ".TH TRUST\\-WP 1 \"{}\" \"trust\\-wp {}\" \"User Commands\"",
        option_env!("TWP_COMMIT_DATE").unwrap_or(""),
        crate::build_version()
    );

    page.push_str(
        ".SH NAME\n\
         trust\\-wp \\- prove Rust code correct for every input, without running it\n\
         .SH SYNOPSIS\n\
         .B trust\\-wp\n\
         .I FILE.rs\n\
         .RI [ OPTIONS ]\n\
         .br\n\
         .B trust\\-wp\n\
         .RI [ OPTIONS ]\n\
         .br\n\
         .B trust\\-wp\n\
         .I COMMAND\n\
         .RI [ ARGS ]\n\
         .SH DESCRIPTION\n\
         Contracts are ordinary Rust attributes \\(em\n\
         .BR #[requires] ,\n\
         .BR #[ensures] ,\n\
         .B #[invariant]\n\
         and\n\
         .B proof_assert!\n\
         \\(em and trust\\-wp proves them: it intercepts post\\-borrowck MIR,\n\
         generates verification conditions with a Dijkstra\\-style\n\
         weakest\\-precondition transformation, and discharges them on the\n\
         .B ay\n\
         SMT solver. A proof covers every input, not the ones a test happened\n\
         to try.\n\
         .PP\n\
         With no FILE, trust\\-wp verifies the crate in the current directory.\n\
         Its exit status is the answer; see EXIT STATUS.\n\
         .PP\n\
         Arithmetic overflow is currently assumed rather than proved: MIR's\n\
         overflow assertions enter the verification condition as hypotheses,\n\
         so a proof means \"correct assuming no overflow\".\n",
    );

    page.push_str(".SH COMMANDS\n");
    for (name, help) in COMMANDS {
        let _ = writeln!(page, ".TP\n.B {}\n{}", roff(name), roff(help));
    }
    page.push_str(
        ".PP\n\
         .BR contract , \" bundle\" \" and\" \" result\"\n\
         run in this process: no engine, no sysroot and no solver.\n",
    );

    page.push_str(".SH OPTIONS\n");
    for flag in FLAGS {
        let arg = match flag.value {
            Value::None => String::new(),
            Value::Choices(values) => format!(" \" \" \\fI{}\\fR", roff(&values.join("|"))),
            Value::Dir => " \" \" \\fIDIR\\fR".to_string(),
            Value::Free => " \" \" \\fIVALUE\\fR".to_string(),
        };
        let head = match flag.short {
            Some(short) => format!(
                ".BR {} \", \" {}{arg}",
                roff(short),
                roff(flag.long).replace(' ', "\\ ")
            ),
            None => format!(".BR {}{arg}", roff(flag.long)),
        };
        let _ = writeln!(page, ".TP\n{head}\n{}", roff(flag.help));
    }
    page.push_str(
        ".PP\n\
         Unknown options are refused, never ignored. To hand an option to the\n\
         underlying tool unchanged, put it after\n\
         .BR \\-\\- :\n\
         .B trust\\-wp \\-\\- \\-p mycrate\n\
         goes to cargo in crate mode, and\n\
         .B trust\\-wp demo.rs \\-\\- \\-\\-cfg foo\n\
         goes to rustc for a single file.\n",
    );

    page.push_str(
        ".SH EXIT STATUS\n\
         .TP\n\
         .B 0\n\
         everything verified\n\
         .TP\n\
         .B 1\n\
         at least one contract failed \\(em a counterexample exists\n\
         .TP\n\
         .B 2\n\
         encoding or solver error, soundness gap, nothing was proved, or the\n\
         engine could not run\n\
         .TP\n\
         .B 3\n\
         contract parse error, or bad command line\n\
         .TP\n\
         .B 101\n\
         internal error (panic)\n\
         .SH ENVIRONMENT\n\
         .TP\n\
         .B TRUST_WP_RUSTC\n\
         path to the trust\\-wp\\-rustc driver binary\n\
         .TP\n\
         .B TRUST_WP_CARGO\n\
         path to the cargo\\-trust\\-wp binary\n\
         .TP\n\
         .B TRUST_WP_HOME\n\
         trust\\-wp checkout to resolve helpers and libraries from. A value\n\
         that is not a checkout is reported rather than silently ignored.\n\
         .TP\n\
         .B TRUST_WP_RESULT_PROTOCOL\n\
         set to 1 to also print the machine\\-readable result line on stderr\n\
         .TP\n\
         .B TRUST_WP_LOG\n\
         log filter, e.g.\n\
         .B TRUST_WP_LOG=trust_wp=info\n\
         .TP\n\
         .B NO_COLOR\n\
         set to any value and\n\
         .B \\-\\-color auto\n\
         stays plain\n\
         .SH EXAMPLES\n\
         .TP\n\
         Verify a single file, with nothing configured:\n\
         .B trust\\-wp example > demo.rs && trust\\-wp demo.rs\n\
         .TP\n\
         Check what is installed, and how to fix what is not:\n\
         .B trust\\-wp doctor\n\
         .TP\n\
         Verify one function and read its obligation:\n\
         .B trust\\-wp demo.rs \\-\\-filter clamp \\-\\-emit\\-smt\n\
         .TP\n\
         Install shell completions:\n\
         .B trust\\-wp completions zsh > \"${fpath[1]}/_trust\\-wp\"\n\
         .SH SEE ALSO\n\
         .BR cargo (1),\n\
         .BR rustc (1).\n\
         .PP\n\
         Full contract grammar: contract\\-syntax.md in the trust\\-wp checkout.\n\
         Project home: https://github.com/alabsystems/trust\\-wp\n\
         .SH AUTHOR\n\
         Andrew Yates.\n",
    );

    page
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every option and verb the tool has reaches the manual.
    ///
    /// The page is generated from the same table as the completions, so this
    /// is really a check that the generator does not drop entries — the
    /// failure a hand-written page has silently.
    #[test]
    fn the_manual_documents_every_flag_and_command() {
        let page = render();
        for flag in FLAGS {
            // Hyphens are escaped in roff, so compare on the escaped form.
            let needle = roff(flag.long);
            assert!(page.contains(&needle), "man page omits `{}`", flag.long);
        }
        for (name, _) in COMMANDS {
            assert!(page.contains(&roff(name)), "man page omits `{name}`");
        }
    }

    /// It has to be a manual page, not merely text.
    #[test]
    fn the_manual_is_well_formed_roff() {
        let page = render();
        assert!(page.starts_with(".TH "), "no title header:\n{page}");
        for section in [
            ".SH NAME",
            ".SH SYNOPSIS",
            ".SH DESCRIPTION",
            ".SH COMMANDS",
            ".SH OPTIONS",
            ".SH EXIT STATUS",
            ".SH ENVIRONMENT",
            ".SH EXAMPLES",
            ".SH SEE ALSO",
        ] {
            assert!(page.contains(section), "missing {section}");
        }
        assert!(page.ends_with('\n'), "a man page ends with a newline");
        // Every control line must be a request roff knows, not a stray `.`
        // from an escaped description.
        for line in page.lines().filter(|l| l.starts_with('.')) {
            let request = line[1..].split_whitespace().next().unwrap_or("");
            assert!(
                matches!(
                    request,
                    "TH" | "SH" | "TP" | "PP" | "B" | "I" | "BR" | "RI" | "IR" | "br" | "\\&"
                ),
                "unknown roff request: {line}"
            );
        }
    }

    /// The page is the same every time it is generated from one commit.
    ///
    /// The date it carries is the commit date, not the build date, precisely
    /// so that this holds: rebuilding the same source must not produce a page
    /// that differs from the one already installed.
    #[test]
    fn the_manual_is_reproducible() {
        assert_eq!(render(), render());
        let date = option_env!("TWP_COMMIT_DATE").unwrap_or("");
        if !date.is_empty() {
            assert!(
                date.len() == 10 && date.starts_with("20"),
                "expected a YYYY-MM-DD commit date, got `{date}`"
            );
            assert!(render().contains(date), "the date never reached the page");
        }
    }
}
