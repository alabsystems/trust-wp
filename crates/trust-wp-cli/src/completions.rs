//! `trust-wp completions <shell>` — tab completion for bash, zsh and fish.
//!
//! The scripts are generated from [`FLAGS`] and [`COMMANDS`] rather than
//! written out by hand, because hand-written completions rot: a flag is added
//! to the parser, the completion file is not touched, and the shell quietly
//! stops offering it. Generating them does not by itself prevent that — the
//! table could still fall behind the parser — so `tests/completions.rs` walks
//! every entry here and checks it against both the parser and `--help`.
//!
//! No dependency on a completion-generating framework: this CLI parses its own
//! arguments, so it describes its own arguments too.

use std::fmt::Write as _;

use crate::style::ColorChoice;

/// What a flag expects after it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value {
    /// A bare switch.
    None,
    /// One of a fixed set, which the shell can offer directly.
    Choices(&'static [&'static str]),
    /// A file path.
    Path,
    /// A directory.
    Dir,
    /// Free text the shell cannot guess (a function name, a number).
    Free,
}

/// One option, as the parser accepts it and as `--help` describes it.
#[derive(Debug, Clone, Copy)]
pub struct Flag {
    /// Long spelling, e.g. `--filter`.
    pub long: &'static str,
    /// Short spelling, if any.
    pub short: Option<&'static str>,
    pub value: Value,
    /// One line, shown by zsh and fish beside the flag.
    pub help: &'static str,
}

const EDITIONS: &[&str] = &["2015", "2018", "2021", "2024"];
const TRACK_LEVELS: &[&str] = &["auto", "reg", "ptr", "mem"];
const COLORS: &[&str] = &ColorChoice::VALUES;

/// Every option `verify` accepts. Kept in the order `--help` lists them.
pub const FLAGS: &[Flag] = &[
    Flag {
        long: "--filter",
        short: None,
        value: Value::Free,
        help: "only verify functions whose path matches NAME",
    },
    Flag {
        long: "--timeout",
        short: None,
        value: Value::Free,
        help: "per-function solver timeout in seconds",
    },
    Flag {
        long: "--emit-smt",
        short: None,
        value: Value::None,
        help: "print the SMT-LIB2 queries to stdout",
    },
    Flag {
        long: "--emit-smt-dir",
        short: None,
        value: Value::Dir,
        help: "write one annotated .smt2 file per function",
    },
    Flag {
        long: "--strict-trust",
        short: None,
        value: Value::None,
        help: "require independently replayed proof authority (already the default)",
    },
    Flag {
        long: "--no-strict-trust",
        short: None,
        value: Value::None,
        help: "deprecated spelling; does NOT relax the requirement",
    },
    Flag {
        long: "--strict-axioms",
        short: None,
        value: Value::None,
        help: "treat unverified axioms as errors",
    },
    Flag {
        long: "--strict-obligations",
        short: None,
        value: Value::None,
        help: "treat dropped-obligation warnings as errors",
    },
    Flag {
        long: "--stop-after-analysis",
        short: None,
        value: Value::None,
        help: "stop the compiler after MIR analysis",
    },
    Flag {
        long: "--no-verify",
        short: None,
        value: Value::None,
        help: "skip verification entirely",
    },
    Flag {
        long: "--verify",
        short: None,
        value: Value::None,
        help: "verify even when only emitting SMT",
    },
    Flag {
        long: "--track",
        short: None,
        value: Value::Choices(TRACK_LEVELS),
        help: "memory tracking level",
    },
    Flag {
        long: "--edition",
        short: None,
        value: Value::Choices(EDITIONS),
        help: "edition for single-file mode",
    },
    Flag {
        long: "--dry-run",
        short: None,
        value: Value::None,
        help: "print the engine command instead of running it",
    },
    Flag {
        long: "--quiet",
        short: Some("-q"),
        value: Value::None,
        help: "print only failures, and the summary",
    },
    Flag {
        long: "--verbose",
        short: Some("-v"),
        value: Value::None,
        help: "show verification progress",
    },
    Flag {
        long: "--color",
        short: None,
        value: Value::Choices(COLORS),
        help: "when to colourise output",
    },
    Flag {
        long: "--json",
        short: None,
        value: Value::None,
        help: "print one JSON report on stdout",
    },
    Flag {
        long: "--help",
        short: Some("-h"),
        value: Value::None,
        help: "-h for a summary, --help for the full page",
    },
    Flag {
        long: "--version",
        short: Some("-V"),
        value: Value::None,
        help: "print the version",
    },
];

/// The verbs, with the one-line summary the shell shows beside each.
pub const COMMANDS: &[(&str, &str)] = &[
    ("verify", "run the verifier"),
    (
        "contract",
        "parse a contract, or emit its verification condition",
    ),
    (
        "bundle",
        "verify, validate or replay a verify-bundle request",
    ),
    ("result", "decode a saved result-protocol transcript"),
    (
        "doctor",
        "report what is installed, and how to fix what is not",
    ),
    ("example", "write a tiny contracted sample"),
    ("completions", "print a shell completion script"),
    ("man", "print the roff manual page"),
    ("help", "help, or one command's page"),
    ("version", "print the version"),
];

/// Shells with a generator here.
pub const SHELLS: [&str; 3] = ["bash", "zsh", "fish"];

/// Render the completion script for `shell`, or `None` if unsupported.
#[must_use]
pub fn render(shell: &str) -> Option<String> {
    match shell {
        "bash" => Some(bash()),
        "zsh" => Some(zsh()),
        "fish" => Some(fish()),
        _ => None,
    }
}

/// Every accepted spelling, short and long.
fn spellings() -> Vec<&'static str> {
    let mut all = Vec::new();
    for flag in FLAGS {
        all.push(flag.long);
        if let Some(short) = flag.short {
            all.push(short);
        }
    }
    all
}

fn bash() -> String {
    let flags = spellings().join(" ");
    let commands: Vec<&str> = COMMANDS.iter().map(|(name, _)| *name).collect();
    let choice_arms = FLAGS
        .iter()
        .filter_map(|flag| match flag.value {
            Value::Choices(values) => {
                Some(format!("        {})\n            COMPREPLY=($(compgen -W \"{}\" -- \"$cur\"))\n            return;;", flag.long, values.join(" ")))
            }
            Value::Dir => Some(format!(
                "        {})\n            COMPREPLY=($(compgen -d -- \"$cur\"))\n            return;;",
                flag.long
            )),
            Value::Path => Some(format!(
                "        {})\n            COMPREPLY=($(compgen -f -- \"$cur\"))\n            return;;",
                flag.long
            )),
            // A function name or a number: the shell has nothing to offer, and
            // guessing filenames here would be worse than offering nothing.
            Value::Free | Value::None => None,
        })
        .collect::<Vec<_>>()
        .join("\n");

    format!(
        r#"# trust-wp completions for bash.
#   trust-wp completions bash > /usr/local/etc/bash_completion.d/trust-wp
# or, without root:
#   trust-wp completions bash > ~/.local/share/bash-completion/completions/trust-wp
_trust_wp() {{
    local cur prev
    cur="${{COMP_WORDS[COMP_CWORD]}}"
    prev="${{COMP_WORDS[COMP_CWORD-1]}}"

    # A value position: complete the value, never a flag.
    case "$prev" in
{choice_arms}
    esac

    if [[ "$cur" == -* ]]; then
        COMPREPLY=($(compgen -W "{flags}" -- "$cur"))
        return
    fi

    # First word: a verb, or the .rs file to verify.
    if [[ $COMP_CWORD -eq 1 ]]; then
        COMPREPLY=($(compgen -W "{commands}" -- "$cur"))
        COMPREPLY+=($(compgen -f -X '!*.rs' -- "$cur"))
        COMPREPLY+=($(compgen -d -- "$cur"))
        return
    fi
    COMPREPLY=($(compgen -f -- "$cur"))
}}
complete -F _trust_wp trust-wp
"#,
        commands = commands.join(" "),
    )
}

/// Make `text` safe inside a zsh single-quoted string.
///
/// The specs below are single-quoted, so an apostrophe in a description ends
/// the string and leaves the rest as syntax — which is exactly what "one
/// command's page" did to the generated script.
fn zsh_quote(text: &str) -> String {
    text.replace('\'', "'\\''")
}

fn zsh() -> String {
    let mut arguments = String::new();
    for flag in FLAGS {
        // zsh takes the description after a `[...]`; a literal `]` inside one
        // would close it early.
        let help = zsh_quote(&flag.help.replace(']', ")"));
        let spec = match flag.value {
            Value::None => String::new(),
            Value::Choices(values) => format!(":value:({})", values.join(" ")),
            Value::Path => ":file:_files".to_string(),
            Value::Dir => ":directory:_files -/".to_string(),
            Value::Free => ":value:".to_string(),
        };
        match flag.short {
            Some(short) => {
                let _ = writeln!(
                    arguments,
                    "        '({short} {long})'{{{short},{long}}}'[{help}]{spec}' \\",
                    long = flag.long
                );
            }
            None => {
                let _ = writeln!(arguments, "        '{}[{help}]{spec}' \\", flag.long);
            }
        }
    }
    let commands = COMMANDS
        .iter()
        // A literal `:` would split the description from the value.
        .map(|(name, help)| {
            format!(
                "                '{name}:{}'",
                zsh_quote(&help.replace(':', " -"))
            )
        })
        .collect::<Vec<_>>()
        .join("\n");

    format!(
        r#"#compdef trust-wp
# trust-wp completions for zsh.
#   trust-wp completions zsh > "${{fpath[1]}}/_trust-wp"
# then restart the shell, or: compinit
_trust-wp() {{
    local -a commands
    _arguments -C \
{arguments}        '1: :->first' \
        '*: :_files' && return 0

    case $state in
        first)
            commands=(
{commands}
            )
            _describe -t commands 'trust-wp command' commands
            # A path is as likely as a verb here: `trust-wp demo.rs`.
            _files -g '*.rs'
            ;;
    esac
}}
_trust-wp "$@"
"#
    )
}

fn fish() -> String {
    let mut lines = String::new();
    let verbs = COMMANDS
        .iter()
        .map(|(name, _)| *name)
        .collect::<Vec<_>>()
        .join(" ");
    // Verbs are offered only in first position.
    let _ = writeln!(
        lines,
        "# Only offer a verb where one can go: `trust-wp <verb>`."
    );
    let _ = writeln!(
        lines,
        "function __trust_wp_no_verb\n    set -l tokens (commandline -opc)\n    test (count $tokens) -eq 1\nend"
    );
    for (name, help) in COMMANDS {
        let _ = writeln!(
            lines,
            "complete -c trust-wp -n __trust_wp_no_verb -f -a '{name}' -d '{}'",
            help.replace('\'', "")
        );
    }
    for flag in FLAGS {
        let long = flag.long.trim_start_matches('-');
        let short = flag
            .short
            .map(|s| format!(" -s {}", s.trim_start_matches('-')))
            .unwrap_or_default();
        let help = flag.help.replace('\'', "");
        let tail = match flag.value {
            Value::None => " -f".to_string(),
            Value::Choices(values) => format!(" -x -a '{}'", values.join(" ")),
            Value::Path => " -r -F".to_string(),
            Value::Dir => " -x -a '(__fish_complete_directories)'".to_string(),
            Value::Free => " -x".to_string(),
        };
        let _ = writeln!(
            lines,
            "complete -c trust-wp -l {long}{short}{tail} -d '{help}'"
        );
    }
    format!(
        "# trust-wp completions for fish.\n\
         #   trust-wp completions fish > ~/.config/fish/completions/trust-wp.fish\n\
         # Verbs: {verbs}\n\
         {lines}"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|s| (*s).to_string()).collect()
    }

    /// A representative value for a flag that needs one, so the parser sees a
    /// well-formed invocation rather than a missing-value error.
    fn sample(flag: &Flag) -> Option<&'static str> {
        match flag.value {
            Value::None => None,
            Value::Choices(values) => Some(values[0]),
            Value::Path => Some("out.txt"),
            Value::Dir => Some("out"),
            Value::Free if flag.long == "--timeout" => Some("30"),
            Value::Free => Some("some_function"),
        }
    }

    /// Every flag offered by the shell must be one the parser accepts.
    ///
    /// This is the failure mode hand-written completions have: the table and
    /// the parser drift, and the shell offers a flag that errors, or stops
    /// offering one that works.
    #[test]
    fn every_completed_flag_is_accepted_by_the_parser() {
        for flag in FLAGS {
            for spelling in [Some(flag.long), flag.short].into_iter().flatten() {
                let mut line = vec![spelling];
                line.extend(sample(flag));
                // Single-file mode, where every option in the table applies:
                // `--edition` is rejected in crate mode, since a crate takes
                // its edition from Cargo.toml.
                line.push("demo.rs");
                // `--help` and `--version` short-circuit; the rest reach the
                // verify parser. Either way, none may be rejected.
                let parsed = crate::parse_cli(&args(&line));
                assert!(
                    parsed.is_ok(),
                    "completions offer `{spelling}`, which the parser rejects: {:?}",
                    parsed.err().map(|e| format!("{e:?}"))
                );
            }
        }
    }

    /// And every flag the parser documents must be offered by the shell.
    #[test]
    fn every_documented_flag_is_offered_by_the_shell() {
        let help = crate::render_help(None, false);
        let offered: Vec<&str> = spellings();
        let mut missing = Vec::new();
        for line in help.lines() {
            let trimmed = line.trim_start();
            // Option lines start at a flag; prose and examples do not.
            if !trimmed.starts_with('-') || line.starts_with("        ") {
                continue;
            }
            let Some(word) = trimmed.split([' ', ',', '=']).next() else {
                continue;
            };
            // `-vv` is a spelling of `--verbose` that the shell has no reason
            // to offer separately.
            if word == "-vv" || word.is_empty() {
                continue;
            }
            if !offered.contains(&word) {
                missing.push(word.to_string());
            }
        }
        assert!(
            missing.is_empty(),
            "--help documents options the completions do not offer: {missing:?}"
        );
    }

    /// Every verb the completions name has to have a help page, and vice
    /// versa: a verb the shell offers but the tool does not have is worse than
    /// no completion at all.
    #[test]
    fn completed_commands_match_the_command_words() {
        for (name, _) in COMMANDS {
            assert!(
                crate::COMMAND_WORDS.contains(name),
                "completions offer `{name}`, which is not a command"
            );
        }
        for word in crate::COMMAND_WORDS {
            assert!(
                COMMANDS.iter().any(|(name, _)| *name == word),
                "`{word}` is a command the completions never offer"
            );
        }
    }

    /// The generators must produce something for every advertised shell, and
    /// nothing for anything else.
    #[test]
    fn every_advertised_shell_has_a_script() {
        for shell in SHELLS {
            let script = render(shell).unwrap_or_else(|| panic!("no script for `{shell}`"));
            assert!(script.contains("trust-wp"), "{shell}: {script}");
            // Each script must carry every flag and every verb. fish names a
            // long option without its dashes (`-l filter`), so compare on the
            // bare name, which all three spellings contain.
            for flag in FLAGS {
                let bare = flag.long.trim_start_matches('-');
                assert!(script.contains(bare), "{shell} omits `{}`", flag.long);
            }
            for (name, _) in COMMANDS {
                assert!(script.contains(name), "{shell} omits the `{name}` verb");
            }
        }
        assert!(render("tcsh").is_none());
        assert!(render("").is_none());
    }

    /// zsh specs and fish descriptions are single-quoted; an unescaped
    /// apostrophe in a help string ends the quote and corrupts the script.
    #[test]
    fn descriptions_survive_shell_quoting() {
        assert_eq!(zsh_quote("one command's page"), r"one command'\''s page");
        for (_, help) in COMMANDS {
            assert!(
                !help.contains('\n'),
                "a description must stay on one line: {help}"
            );
        }
        for flag in FLAGS {
            assert!(!flag.help.contains('\n'), "{}: {}", flag.long, flag.help);
            assert!(
                flag.long.starts_with("--"),
                "{} is not a long flag",
                flag.long
            );
        }
    }
}
