// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Standalone replay and reducer tooling for trust-wp-produced AY native replay
//! JSON artifacts.

use std::{
    collections::{HashMap, HashSet},
    env, fs,
    path::PathBuf,
};

use ay_core::{term::TermData, TermId};
use ay_dpll::api::{
    NativeReplayArtifact, NativeReplayEvent, NativeReplayEventKind, NativeReplaySymbolKind,
    NativeReplayTermNode, Solver,
};

const USAGE: &str = "\
Usage:
  trust-wp-ay-native-replay replay [--expect stored|replay|sat|unsat|unknown] <artifact.json>
  trust-wp-ay-native-replay shrink [--expect stored|replay|sat|unsat|unknown] [--min-assertions N] [-o <out.json>] <artifact.json>

Commands:
  replay   Load and replay a AY native replay JSON artifact.
  shrink   Deterministically remove active assertions while preserving the target status.

Defaults:
  --expect stored      Preserve the artifact's stored solve.result when present.
  --min-assertions 1   Keep at least one active assertion when the input has assertions.
";

type CliResult<T> = Result<T, String>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CommandKind {
    Replay,
    Shrink,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
enum Expected {
    #[default]
    Stored,
    Replay,
    Status(String),
}

#[derive(Debug, Clone)]
struct Command {
    kind: CommandKind,
    input: PathBuf,
    output: Option<PathBuf>,
    expect: Expected,
    min_assertions: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReplayStatus {
    status: String,
}

#[derive(Debug, Clone, Default)]
struct ShrinkStats {
    attempts: usize,
    removed_assertions: usize,
    input_assertions: usize,
    output_assertions: usize,
    input_terms: usize,
    output_terms: usize,
    terms_pruned: bool,
}

fn main() {
    match run(env::args().skip(1).collect()) {
        Ok(()) => {}
        Err(err) => {
            eprintln!("error: {err}");
            eprintln!();
            eprintln!("{USAGE}");
            std::process::exit(2);
        }
    }
}

fn run(args: Vec<String>) -> CliResult<()> {
    let command = parse_args(args)?;
    let input_text = fs::read_to_string(&command.input)
        .map_err(|err| format!("failed to read {}: {err}", command.input.display()))?;
    let artifact = NativeReplayArtifact::from_json_str(&input_text)
        .map_err(|err| format!("failed to parse {}: {err}", command.input.display()))?;

    match command.kind {
        CommandKind::Replay => replay_command(&command, &artifact),
        CommandKind::Shrink => shrink_command(&command, artifact),
    }
}

fn replay_command(command: &Command, artifact: &NativeReplayArtifact) -> CliResult<()> {
    let target = target_status(artifact, &command.expect)?;
    let replay = replay_status(artifact)?;
    let stored = stored_status(artifact).unwrap_or_else(|| "none".to_string());
    if replay != target {
        return Err(format!(
            "replay status {} did not match target {} (stored={stored})",
            replay.status, target.status
        ));
    }

    println!(
        "status=ok command=replay input={} stored={} target={} replay={} assertions={} terms={}",
        command.input.display(),
        stored,
        target.status,
        replay.status,
        artifact.assertions.len(),
        artifact.terms.len(),
    );
    Ok(())
}

fn shrink_command(command: &Command, mut artifact: NativeReplayArtifact) -> CliResult<()> {
    let target = target_status(&artifact, &command.expect)?;
    let baseline = replay_status(&artifact)?;
    let stored = stored_status(&artifact).unwrap_or_else(|| "none".to_string());
    if baseline != target {
        return Err(format!(
            "input replay status {} did not match target {} (stored={stored}); use --expect replay or an explicit status to reduce current behavior",
            baseline.status, target.status
        ));
    }

    let mut stats = shrink_assertions(&mut artifact, &target, command.min_assertions)?;
    stats.terms_pruned = prune_terms_if_replay_preserved(&mut artifact, &target)?;
    stats.output_assertions = artifact.assertions.len();
    stats.output_terms = artifact.terms.len();
    append_reducer_note(&mut artifact, &stats);

    let final_status = replay_status(&artifact)?;
    if final_status != target {
        return Err(format!(
            "internal error: shrunk artifact replay status {} did not match target {}",
            final_status.status, target.status
        ));
    }

    let output_json = artifact.to_pretty_json();
    if let Some(output) = &command.output {
        fs::write(output, output_json)
            .map_err(|err| format!("failed to write {}: {err}", output.display()))?;
        println!(
            "status=ok command=shrink input={} output={} stored={} target={} baseline={} final={} assertions={}->{} terms={}->{} attempts={} removed_assertions={} terms_pruned={}",
            command.input.display(),
            output.display(),
            stored,
            target.status,
            baseline.status,
            final_status.status,
            stats.input_assertions,
            stats.output_assertions,
            stats.input_terms,
            stats.output_terms,
            stats.attempts,
            stats.removed_assertions,
            stats.terms_pruned,
        );
    } else {
        eprintln!(
            "status=ok command=shrink input={} stored={} target={} baseline={} final={} assertions={}->{} terms={}->{} attempts={} removed_assertions={} terms_pruned={}",
            command.input.display(),
            stored,
            target.status,
            baseline.status,
            final_status.status,
            stats.input_assertions,
            stats.output_assertions,
            stats.input_terms,
            stats.output_terms,
            stats.attempts,
            stats.removed_assertions,
            stats.terms_pruned,
        );
        println!("{output_json}");
    }
    Ok(())
}

fn parse_args(args: Vec<String>) -> CliResult<Command> {
    let Some((command, rest)) = args.split_first() else {
        return Err("missing command".to_string());
    };
    if command == "--help" || command == "-h" {
        println!("{USAGE}");
        std::process::exit(0);
    }

    let kind = match command.as_str() {
        "replay" => CommandKind::Replay,
        "shrink" | "minimize" | "reduce" => CommandKind::Shrink,
        other => return Err(format!("unknown command `{other}`")),
    };

    let mut expect = Expected::default();
    let mut output = None;
    let mut min_assertions = 1usize;
    let mut input = None;
    let mut i = 0usize;
    while i < rest.len() {
        match rest[i].as_str() {
            "--help" | "-h" => {
                println!("{USAGE}");
                std::process::exit(0);
            }
            "--expect" => {
                i += 1;
                let value = rest
                    .get(i)
                    .ok_or_else(|| "--expect requires a value".to_string())?;
                expect = parse_expected(value)?;
            }
            "--min-assertions" => {
                i += 1;
                let value = rest
                    .get(i)
                    .ok_or_else(|| "--min-assertions requires a value".to_string())?;
                min_assertions = value
                    .parse::<usize>()
                    .map_err(|err| format!("invalid --min-assertions `{value}`: {err}"))?;
            }
            "-o" | "--output" => {
                if kind != CommandKind::Shrink {
                    return Err("--output is only valid for shrink".to_string());
                }
                i += 1;
                let value = rest
                    .get(i)
                    .ok_or_else(|| "--output requires a path".to_string())?;
                output = Some(PathBuf::from(value));
            }
            value if value.starts_with('-') => return Err(format!("unknown option `{value}`")),
            value => {
                if input.is_some() {
                    return Err(format!("unexpected extra input `{value}`"));
                }
                input = Some(PathBuf::from(value));
            }
        }
        i += 1;
    }

    let input = input.ok_or_else(|| "missing artifact path".to_string())?;
    Ok(Command {
        kind,
        input,
        output,
        expect,
        min_assertions,
    })
}

fn parse_expected(value: &str) -> CliResult<Expected> {
    match value {
        "stored" => Ok(Expected::Stored),
        "replay" => Ok(Expected::Replay),
        "sat" | "unsat" | "unknown" => Ok(Expected::Status(value.to_string())),
        other => Err(format!(
            "invalid --expect `{other}`; expected stored, replay, sat, unsat, or unknown"
        )),
    }
}

fn target_status(artifact: &NativeReplayArtifact, expect: &Expected) -> CliResult<ReplayStatus> {
    match expect {
        Expected::Stored => stored_status(artifact)
            .map(|status| ReplayStatus { status })
            .map_or_else(|| replay_status(artifact), Ok),
        Expected::Replay => replay_status(artifact),
        Expected::Status(status) => Ok(ReplayStatus {
            status: status.clone(),
        }),
    }
}

fn stored_status(artifact: &NativeReplayArtifact) -> Option<String> {
    artifact.solve.as_ref().map(|solve| solve.result.clone())
}

fn replay_status(artifact: &NativeReplayArtifact) -> CliResult<ReplayStatus> {
    let details = Solver::replay_native_replay_artifact(artifact)
        .map_err(|err| format!("native replay failed: {err}"))?;
    if env::var_os("TRUST_WP_AY_NATIVE_REPLAY_VERBOSE").is_some() {
        eprintln!(
            "details result={} unknown_reason={:?} diagnostic={:?} validated={} independent={} delegated={} incomplete={} extra={:?}",
            details.result.result(),
            details.unknown_reason,
            details.unknown_diagnostic,
            details.verification.sat_model_validated,
            details.verification.sat_independent_checks,
            details.verification.sat_delegated_checks,
            details.verification.sat_incomplete_checks,
            details.statistics.extra,
        );
    }
    Ok(ReplayStatus {
        status: details.result.result().to_string(),
    })
}

fn shrink_assertions(
    artifact: &mut NativeReplayArtifact,
    target: &ReplayStatus,
    requested_min_assertions: usize,
) -> CliResult<ShrinkStats> {
    normalize_assertions(artifact);
    let input_assertions = artifact.assertions.len();
    let input_terms = artifact.terms.len();
    let min_assertions = requested_min_assertions.min(input_assertions);
    let mut stats = ShrinkStats {
        input_assertions,
        output_assertions: input_assertions,
        input_terms,
        output_terms: input_terms,
        ..ShrinkStats::default()
    };

    if artifact.assertions.len() <= min_assertions {
        return Ok(stats);
    }

    let mut chunk = (artifact.assertions.len() / 2).max(1);
    loop {
        let mut start = 0usize;
        while start < artifact.assertions.len() {
            let len = artifact.assertions.len();
            let end = (start + chunk).min(len);
            if end <= start || len - (end - start) < min_assertions {
                start += chunk;
                continue;
            }

            let mut candidate = artifact.clone();
            candidate.assertions.drain(start..end);
            normalize_assertions(&mut candidate);
            stats.attempts += 1;
            if replay_status(&candidate)? == *target {
                stats.removed_assertions += end - start;
                *artifact = candidate;
            } else {
                start += chunk;
            }
        }

        if chunk == 1 {
            break;
        }
        chunk = (chunk / 2).max(1);
    }

    Ok(stats)
}

fn normalize_assertions(artifact: &mut NativeReplayArtifact) {
    artifact.assertions.sort_by_key(|assertion| assertion.index);
    for (index, assertion) in artifact.assertions.iter_mut().enumerate() {
        assertion.index = index;
    }
}

fn prune_terms_if_replay_preserved(
    artifact: &mut NativeReplayArtifact,
    target: &ReplayStatus,
) -> CliResult<bool> {
    let before = artifact.terms.len();
    let mut candidate = artifact.clone();
    prune_unreachable_terms(&mut candidate);
    if candidate.terms.len() == before {
        return Ok(false);
    }
    if replay_status(&candidate)? == *target {
        *artifact = candidate;
        Ok(true)
    } else {
        artifact.replay_gaps.push(
            "native replay reducer skipped term pruning because replay status drifted".to_string(),
        );
        Ok(false)
    }
}

fn prune_unreachable_terms(artifact: &mut NativeReplayArtifact) {
    let active_assertion_roots: HashSet<TermId> = artifact
        .assertions
        .iter()
        .map(|assertion| assertion.term)
        .collect();
    let mut roots: Vec<TermId> = active_assertion_roots.iter().copied().collect();
    roots.extend(final_check_sat_assumptions(&artifact.events));

    let node_by_id: HashMap<TermId, NativeReplayTermNode> = artifact
        .terms
        .iter()
        .cloned()
        .map(|node| (node.id, node))
        .collect();
    let mut reachable = HashSet::new();
    let mut stack = roots;
    while let Some(id) = stack.pop() {
        if !reachable.insert(id) {
            continue;
        }
        if let Some(node) = node_by_id.get(&id) {
            push_term_children(&node.data, &mut stack);
        }
    }

    artifact.terms.retain(|node| reachable.contains(&node.id));
    artifact
        .declarations
        .retain(|declaration| reachable.contains(&declaration.term));
    artifact.events.retain(|event| {
        event_references_reachable_terms(event, &reachable, &active_assertion_roots)
    });
    prune_symbol_identities(artifact);
}

/// Drop the identity rows for symbols pruning just removed.
///
/// The identity table is not free-standing bookkeeping: ay validates that it
/// has exactly one row per declaration, per function declaration, and per
/// datatype member, and fails the whole artifact closed when it does not
/// (`native replay identity table has N rows, expected M`). Pruning
/// declarations and datatype-declaring events without pruning their rows left
/// every reduced artifact unloadable, so `shrink` could not reduce any input
/// that actually lost a declaration — which is every non-trivial one.
fn prune_symbol_identities(artifact: &mut NativeReplayArtifact) {
    let surviving_symbols: HashSet<&str> = artifact
        .declarations
        .iter()
        .map(|declaration| declaration.core_name.as_str())
        .chain(
            artifact
                .function_declarations
                .iter()
                .map(|declaration| declaration.core_name.as_str()),
        )
        .collect();
    let surviving_datatypes: HashSet<&str> = artifact
        .events
        .iter()
        .filter_map(|event| match &event.kind {
            NativeReplayEventKind::DeclareDatatype { datatype } => Some(datatype.name.as_str()),
            _ => None,
        })
        .collect();

    artifact
        .symbol_identities
        .retain(|identity| match identity.kind {
            NativeReplaySymbolKind::Uninterpreted | NativeReplaySymbolKind::Theory => {
                surviving_symbols.contains(identity.core_name.as_str())
            }
            // A datatype member belongs to its datatype, not to any one
            // declaration: it survives exactly as long as the `declare-datatype`
            // event that introduced it.
            NativeReplaySymbolKind::DatatypeConstructor
            | NativeReplaySymbolKind::DatatypeSelector
            | NativeReplaySymbolKind::DatatypeTester => identity
                .datatype_core
                .as_deref()
                .is_some_and(|name| surviving_datatypes.contains(name)),
            // `NativeReplaySymbolKind` is `#[non_exhaustive]`. Any kind added later
            // is still a symbol with a core identity, so tie it to its declaration
            // the same way — that keeps the table consistent with whatever the
            // reducer kept, which is the property ay validates.
            _ => surviving_symbols.contains(identity.core_name.as_str()),
        });
}

fn final_check_sat_assumptions(events: &[NativeReplayEvent]) -> Vec<TermId> {
    for event in events.iter().rev() {
        match &event.kind {
            NativeReplayEventKind::CheckSatAssuming { assumptions } => {
                return assumptions.clone();
            }
            NativeReplayEventKind::CheckSat => return Vec::new(),
            _ => {}
        }
    }
    Vec::new()
}

fn push_term_children(data: &TermData, stack: &mut Vec<TermId>) {
    match data {
        TermData::Const(_) | TermData::Var(_, _) => {}
        TermData::App(_, args) => stack.extend(args.iter().copied()),
        TermData::Let(bindings, body) => {
            stack.extend(bindings.iter().map(|(_, term)| *term));
            stack.push(*body);
        }
        TermData::Not(inner) => stack.push(*inner),
        TermData::Ite(cond, then_term, else_term) => {
            stack.push(*cond);
            stack.push(*then_term);
            stack.push(*else_term);
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            stack.push(*body);
            for trigger in triggers {
                stack.extend(trigger.iter().copied());
            }
        }
        _ => {}
    }
}

fn event_references_reachable_terms(
    event: &NativeReplayEvent,
    reachable: &HashSet<TermId>,
    active_assertion_roots: &HashSet<TermId>,
) -> bool {
    match &event.kind {
        NativeReplayEventKind::DeclareConst { term, .. } => reachable.contains(term),
        NativeReplayEventKind::Assert { term, .. } => active_assertion_roots.contains(term),
        NativeReplayEventKind::CheckSatAssuming { assumptions } => {
            assumptions.iter().all(|term| reachable.contains(term))
        }
        NativeReplayEventKind::SetLogic { .. }
        | NativeReplayEventKind::DeclareFun { .. }
        | NativeReplayEventKind::Push
        | NativeReplayEventKind::Pop
        | NativeReplayEventKind::Reset
        | NativeReplayEventKind::ResetAssertions
        | NativeReplayEventKind::CheckSat => true,
        _ => true,
    }
}

fn append_reducer_note(artifact: &mut NativeReplayArtifact, stats: &ShrinkStats) {
    artifact.replay_gaps.push(format!(
        "trust-wp-ay-native-replay shrink preserved status after {} attempts; assertions {}->{}, terms {}->{}, term_pruned={}",
        stats.attempts,
        stats.input_assertions,
        stats.output_assertions,
        stats.input_terms,
        stats.output_terms,
        stats.terms_pruned,
    ));
}
