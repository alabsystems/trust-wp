// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `trust-wp contract` — the contract grammar and the WP generator, without
//! rustc or a solver.
//!
//! `contract parse` runs one expression through trust-wp's contract parser and
//! prints its normalized form; `contract vc` parses a whole contract
//! (`--requires`/`--ensures`/`--result`) and emits the weakest-precondition
//! verification condition as SMT-LIB2 with the same simple generator
//! `--emit-smt` uses. The engine's full encoder adds loop, ADT, ghost and
//! borrow context on top of this; these verbs are the grammar and the
//! calculus, not the prover.

use std::{
    fs,
    io::{self, Read},
    path::PathBuf,
};

use serde_json::{json, Value};
use trust_wp_core::{
    contract_parser::{parse_contract, ParseError},
    formula::PureExpr,
    smt::SmtGenerator,
};

use crate::{
    report::{self, ErrorKind},
    split_inline_value, take_value, UsageError, EXIT_ENCODING_ERROR, EXIT_OK, EXIT_USAGE,
};

/// Where a contract expression comes from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContractSource {
    Inline(String),
    File(PathBuf),
    Stdin,
}

/// `contract parse` / `contract vc`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContractCommand {
    Parse {
        source: ContractSource,
    },
    Vc {
        name: String,
        requires: Vec<String>,
        ensures: Vec<String>,
        result: Option<String>,
    },
}

pub fn parse(args: &[String]) -> Result<ContractCommand, UsageError> {
    const USAGE: &str = "usage: trust-wp contract parse <EXPR> | --file <F> | --stdin | -\n       \
                         trust-wp contract vc [--name F] [--requires E]... [--ensures E]... [--result E]";
    match args.first().map(String::as_str) {
        Some("parse") => {
            let rest = &args[1..];
            let mut source: Option<ContractSource> = None;
            let mut set = |candidate: ContractSource| -> Result<(), UsageError> {
                if source.is_some() {
                    return Err(UsageError::new(
                        "`trust-wp contract parse` takes exactly one expression source",
                    )
                    .with_help(USAGE));
                }
                source = Some(candidate);
                Ok(())
            };
            let mut i = 0;
            while i < rest.len() {
                let arg = rest[i].clone();
                let (name, inline) = split_inline_value(&arg);
                match name {
                    "--file" => {
                        let value = take_value(name, inline, rest, &mut i)?;
                        set(ContractSource::File(PathBuf::from(value)))?;
                    }
                    "--stdin" => set(ContractSource::Stdin)?,
                    // `-` means stdin, the way it does for `trust-wp result`
                    // and for every other Unix tool. It previously fell through
                    // to the inline arm and was parsed as an expression, so
                    // `... | trust-wp contract parse -` answered with
                    // "parse error at position 1: expected expression | -",
                    // which describes the dash rather than the input and sends
                    // the reader looking for a bug in their contract.
                    "-" => set(ContractSource::Stdin)?,
                    _ if arg.starts_with('-') => {
                        return Err(UsageError::new(format!(
                            "`trust-wp contract parse` does not accept `{arg}`"
                        ))
                        .with_help(USAGE)
                        .with_help(
                            "an expression that starts with `-` can be given as `--file`/`--stdin`",
                        ));
                    }
                    _ => set(ContractSource::Inline(arg.clone()))?,
                }
                i += 1;
            }
            let Some(source) = source else {
                return Err(UsageError::new(
                    "`trust-wp contract parse` needs an expression, `--file <F>` or `--stdin`",
                )
                .with_help(USAGE)
                .with_help("for example: trust-wp contract parse \"x > 0 && result == x + 1\""));
            };
            Ok(ContractCommand::Parse { source })
        }
        Some("vc") => {
            let rest = &args[1..];
            let mut name = "f".to_string();
            let mut requires = Vec::new();
            let mut ensures = Vec::new();
            let mut result: Option<String> = None;
            let mut i = 0;
            while i < rest.len() {
                let arg = rest[i].clone();
                let (flag, inline) = split_inline_value(&arg);
                match flag {
                    "--name" => name = take_value(flag, inline, rest, &mut i)?,
                    "--requires" => requires.push(take_value(flag, inline, rest, &mut i)?),
                    "--ensures" => ensures.push(take_value(flag, inline, rest, &mut i)?),
                    "--result" => {
                        if result.is_some() {
                            return Err(UsageError::new("`--result` may be given once"));
                        }
                        result = Some(take_value(flag, inline, rest, &mut i)?);
                    }
                    _ => {
                        return Err(UsageError::new(format!(
                            "`trust-wp contract vc` does not accept `{arg}`"
                        ))
                        .with_help(USAGE));
                    }
                }
                i += 1;
            }
            if requires.is_empty() && ensures.is_empty() {
                return Err(UsageError::new(
                    "`trust-wp contract vc` needs at least one `--requires` or `--ensures` clause",
                )
                .with_help(
                    "for example: trust-wp contract vc --requires \"x > 0\" --ensures \"result > x\" --result \"x + 1\"",
                ));
            }
            Ok(ContractCommand::Vc {
                name,
                requires,
                ensures,
                result,
            })
        }
        Some(other) => Err(UsageError::new(format!(
            "unknown `trust-wp contract` subcommand `{other}`"
        ))
        .with_help(USAGE)),
        None => Err(UsageError::new("`trust-wp contract` needs a subcommand").with_help(USAGE)),
    }
}

pub fn run(command: &ContractCommand, json: bool) -> i32 {
    match command {
        ContractCommand::Parse { source } => run_parse(source, json),
        ContractCommand::Vc {
            name,
            requires,
            ensures,
            result,
        } => vc(name, requires, ensures, result.as_deref(), json),
    }
}

fn read_source(source: &ContractSource) -> Result<(String, String), String> {
    match source {
        ContractSource::Inline(text) => Ok((text.clone(), "<arg>".to_string())),
        ContractSource::File(path) => fs::read_to_string(path)
            .map(|text| (text, path.display().to_string()))
            .map_err(|err| format!("cannot read `{}`: {err}", path.display())),
        ContractSource::Stdin => {
            let mut text = String::new();
            io::stdin()
                .read_to_string(&mut text)
                .map(|_| (text, "<stdin>".to_string()))
                .map_err(|err| format!("cannot read stdin: {err}"))
        }
    }
}

/// A parse error as the report's uniform `error` object, with the position.
fn parse_error_json(err: &ParseError) -> Value {
    let mut error = report::error_json(ErrorKind::ContractParse, err.message.clone());
    if let Some(map) = error.as_object_mut() {
        map.insert("position".to_string(), json!(err.position));
    }
    error
}

fn run_parse(source: &ContractSource, json: bool) -> i32 {
    const COMMAND: &str = "contract parse";
    let (text, origin) = match read_source(source) {
        Ok(read) => read,
        Err(message) => {
            eprintln!("error: {message}");
            if json {
                let mut map = report::envelope(COMMAND, EXIT_USAGE);
                map.insert("ok".into(), Value::from(false));
                map.insert("error".into(), report::error_json(ErrorKind::Io, message));
                report::print_json(&Value::Object(map));
            }
            return EXIT_USAGE;
        }
    };
    let text = text.trim();

    match parse_contract(text) {
        Ok(expr) => {
            let normalized = expr.to_string();
            if json {
                let mut map = report::envelope(COMMAND, EXIT_OK);
                map.insert("ok".into(), Value::from(true));
                map.insert("source".into(), Value::from(origin));
                map.insert("input".into(), Value::from(text));
                map.insert("normalized".into(), Value::from(normalized));
                map.insert("error".into(), Value::Null);
                report::print_json(&Value::Object(map));
            } else {
                println!("{normalized}");
            }
            EXIT_OK
        }
        Err(err) => {
            eprintln!("error: {err}");
            point_at(text, err.position);
            eprintln!("help: contract-syntax.md in the trust-wp checkout has the full grammar");
            if json {
                let mut map = report::envelope(COMMAND, EXIT_USAGE);
                map.insert("ok".into(), Value::from(false));
                map.insert("source".into(), Value::from(origin));
                map.insert("input".into(), Value::from(text));
                map.insert("error".into(), parse_error_json(&err));
                report::print_json(&Value::Object(map));
            }
            EXIT_USAGE
        }
    }
}

/// Show the offending position under a single-line input.
fn point_at(text: &str, position: usize) {
    if text.contains('\n') {
        return;
    }
    let column = text
        .char_indices()
        .take_while(|(index, _)| *index < position)
        .count();
    eprintln!("  {text}");
    eprintln!("  {}^", " ".repeat(column));
}

/// Parse every clause of a contract, naming the clause that failed.
fn parse_clauses(label: &str, clauses: &[String]) -> Result<Vec<PureExpr>, (String, ParseError)> {
    clauses
        .iter()
        .map(|clause| parse_contract(clause).map_err(|err| (format!("{label} `{clause}`"), err)))
        .collect()
}

fn vc(
    name: &str,
    requires: &[String],
    ensures: &[String],
    result: Option<&str>,
    json: bool,
) -> i32 {
    const COMMAND: &str = "contract vc";
    let parsed = (|| {
        let requires = parse_clauses("--requires", requires)?;
        let ensures = parse_clauses("--ensures", ensures)?;
        let result = result
            .map(|clause| {
                parse_contract(clause).map_err(|err| (format!("--result `{clause}`"), err))
            })
            .transpose()?;
        Ok::<_, (String, ParseError)>((requires, ensures, result))
    })();
    let (requires, ensures, result) = match parsed {
        Ok(parsed) => parsed,
        Err((clause, err)) => {
            eprintln!("error: in {clause}: {err}");
            eprintln!("help: contract-syntax.md in the trust-wp checkout has the full grammar");
            if json {
                let mut map = report::envelope(COMMAND, EXIT_USAGE);
                map.insert("ok".into(), Value::from(false));
                map.insert("clause".into(), Value::from(clause));
                map.insert("error".into(), parse_error_json(&err));
                report::print_json(&Value::Object(map));
            }
            return EXIT_USAGE;
        }
    };

    let mut generator = SmtGenerator::new();
    generator.generate_vc(name, &requires, &ensures, result.as_ref());
    let smt = generator.into_output();
    if smt.trim().is_empty() {
        eprintln!("error: the generator produced no verification condition");
        return EXIT_ENCODING_ERROR;
    }

    if json {
        let mut map = report::envelope(COMMAND, EXIT_OK);
        map.insert("ok".into(), Value::from(true));
        map.insert("function".into(), Value::from(name));
        map.insert(
            "requires".into(),
            Value::Array(
                requires
                    .iter()
                    .map(|e| Value::from(e.to_string()))
                    .collect(),
            ),
        );
        map.insert(
            "ensures".into(),
            Value::Array(ensures.iter().map(|e| Value::from(e.to_string())).collect()),
        );
        map.insert(
            "result".into(),
            result
                .as_ref()
                .map_or(Value::Null, |e| Value::from(e.to_string())),
        );
        map.insert("smt".into(), Value::from(smt));
        map.insert("error".into(), Value::Null);
        report::print_json(&Value::Object(map));
    } else {
        print!("{smt}");
        if !smt.ends_with('\n') {
            println!();
        }
    }
    EXIT_OK
}

pub fn help() -> String {
    r"trust-wp contract — the contract grammar and the WP generator, in-process

USAGE:
    trust-wp contract parse <EXPR>
    trust-wp contract parse --file <F> | --stdin | -
    trust-wp contract vc [--name F] [--requires E]... [--ensures E]... [--result E]

    parse   parse one contract expression with trust-wp's grammar and print its
            normalized form (exit 0), or the parse error and position (exit 3).
    vc      emit the weakest-precondition verification condition for a contract as
            SMT-LIB2 on stdout: preconditions asserted, `result` bound to --result,
            the postcondition negated, `(check-sat)` — unsat means the contract
            holds. This is the same simple generator `verify --emit-smt` uses; the
            engine's encoder adds loop, ADT, ghost and borrow context on top.

    A bare `-` reads the expression from stdin, as it does for `trust-wp
    result`. A clause that starts with `-` must be attached:
    `--requires=-1 < x`.

EXAMPLES:
    trust-wp contract parse 'x > 0 && result == x + 1'
    trust-wp contract vc --name increment --requires 'x > 0' --ensures 'result > x' --result 'x + 1'

Neither needs rustc, a sysroot or the solver. `--json` wraps the output in a report."
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contract_expressions_parse_and_normalize() {
        let expr = parse_contract("x > 0 && result == x + 1").unwrap();
        let normalized = expr.to_string();
        assert!(normalized.contains('x'));
        assert!(parse_contract("x > ").is_err());
    }

    #[test]
    fn the_vc_generator_emits_smt_lib() {
        let requires = parse_clauses("--requires", &["x > 0".to_string()]).unwrap();
        let ensures = parse_clauses("--ensures", &["result > x".to_string()]).unwrap();
        let result = parse_contract("x + 1").unwrap();
        let mut generator = SmtGenerator::new();
        generator.generate_vc("increment", &requires, &ensures, Some(&result));
        let smt = generator.into_output();
        assert!(smt.contains("increment"));
        assert!(smt.contains("(check-sat)"));
        assert!(smt.contains("(declare-const x Int)"));
    }

    #[test]
    fn clause_errors_name_the_clause() {
        let err =
            parse_clauses("--ensures", &["ok == 1".to_string(), "x >".to_string()]).unwrap_err();
        assert!(err.0.starts_with("--ensures `x >`"));
    }
}
