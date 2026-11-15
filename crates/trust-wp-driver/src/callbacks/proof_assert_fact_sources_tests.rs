// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Every place the proof_assert lane adds a fact to an assertion's context,
//! and the rule that decides where that fact holds (D-190).
//!
//! A fact is established at some program point and speaks of the values the
//! names it mentions had there. It is a premise of an assertion only where it
//! still holds, and each source below names the rule that decides that. A
//! source whose fact is established at a program point other than the
//! assertion's own is [`Scope::FactScope`]: it is stated only through
//! [`crate::mir_analysis::fact_scope::FactScope`], which asks that the point
//! dominate the assertion and that nothing the fact names be written on a
//! path between. The lanes this registry was built from had sources that
//! asked neither (the relacq post-loop fact matched comment text and stated
//! the assertion itself; an `Rc` clone fact read its receiver at the
//! assertion; a ghost write in a branch was read as the value at the
//! assertion).
//!
//! The test scans the lane files: every statement that adds to a fact sink
//! (a push, extend or insert into one, a `let mut` that seeds one, a `&mut`
//! handed to a function) must carry a `// fact-source: <id>` marker naming an
//! entry here, every entry must be marked somewhere, and every
//! [`Scope::FactScope`] entry's producer must call the query. A new fact
//! source therefore fails this test until it is registered with its rule, and
//! one registered as point-scoped fails it until it actually asks.

use std::collections::{BTreeSet, HashSet};

/// The rule that decides where a source's facts hold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Scope {
    /// Established at a program point other than the assertion's; stated
    /// only through `FactScope` (dominance plus written-since, D-189).
    FactScope,
    /// Read by the program-point walk that stops at the assertion itself
    /// (the substitutions at the assertion and their equalities), or stated
    /// by the assertion's own text (a lemma call inside `proof_assert!`).
    AtAssertion,
    /// A fact about the function's entry (`#[requires]`, a parameter's type
    /// invariant), withdrawn where the body re-binds a parameter or writes
    /// its pointee (D-38, D-140), or stated of the entry symbol of a
    /// by-value parameter the walks name apart from its current value
    /// (D-241).
    Entry,
    /// A callee postcondition or a store recorded at the point the walk to
    /// the assertion passes, under its path guard, withdrawn when it reads
    /// memory written since (D-186).
    CallEffect,
    /// Prophecy resolution between a borrow and its reborrow: it relates
    /// final values, which no later write changes.
    Prophecy,
    /// A type invariant: it holds of every value of the type.
    TypeInvariant,
    /// A consequence of premises already in the context (or a rewrite of
    /// them); it holds wherever they do.
    Derived,
    /// Moves facts a source above already produced from one sink to another.
    Handoff,
    /// Removes or rewrites facts in place; adds none.
    Withdrawal,
    /// Renames a binding to the carrier symbol of the borrow it holds; adds
    /// no premise.
    CarrierRename,
    /// Function-level context only (no assertion cutoff): never reaches an
    /// assertion's context.
    NotAnAssertionFact,
}

/// `(id, rule, producer)`: the producer is the function whose body must call
/// the `FactScope` query when the rule is [`Scope::FactScope`].
const FACT_SOURCES: &[(&str, Scope, &str)] = &[
    // proof_assert_snapshot.rs
    (
        "reborrow_carrier_rename",
        Scope::CarrierRename,
        "derive_plain_reborrow_carrier_aliases",
    ),
    (
        "snapshot_deref_aliases",
        Scope::CarrierRename,
        "derive_projected_snapshot_deref_aliases",
    ),
    (
        "projected_write_overrides",
        Scope::FactScope,
        "prior_ghost_source_projected_write_repair_facts",
    ),
    (
        "ghost_closure_projected_writes",
        Scope::FactScope,
        "prior_ghost_projected_write_repair_facts",
    ),
    ("wrapper_alias_substitutions", Scope::Derived, ""),
    ("current_state_rewrite", Scope::Withdrawal, ""),
    (
        "ghost_deref_write_overrides",
        Scope::FactScope,
        "whole_value_ghost_deref_write_substitutions",
    ),
    ("substitution_facts", Scope::AtAssertion, ""),
    ("stale_alias_withdrawal", Scope::Withdrawal, ""),
    ("reborrow_parent_finals", Scope::Prophecy, ""),
    ("body_effect_facts", Scope::CallEffect, ""),
    ("call_postconditions", Scope::CallEffect, ""),
    (
        "rc_call_result_facts",
        Scope::FactScope,
        "synthesize_snapshot_call_facts",
    ),
    (
        "ghost_closure_loop_facts",
        Scope::FactScope,
        "extract_ghost_closure_loop_assumptions",
    ),
    (
        "post_loop_facts",
        Scope::FactScope,
        "extract_function_local_post_loop_assumptions",
    ),
    (
        "in_body_loop_facts",
        Scope::FactScope,
        "extract_function_local_in_body_assumptions",
    ),
    // verification/proof_assert_driver.rs
    (
        "loop_lane_exit_facts",
        Scope::FactScope,
        "extend_with_loop_assumptions",
    ),
    ("match_exit_goals", Scope::Derived, ""),
    ("ghost_context_handoff", Scope::Handoff, ""),
    ("delayed_writebacks", Scope::Prophecy, ""),
    ("entry_pinning_withdrawal", Scope::Withdrawal, ""),
    ("call_assumption_handoff", Scope::Handoff, ""),
    ("closure_call_assumptions", Scope::Derived, ""),
    // proof_assert_verify/mod.rs
    ("entry_requires", Scope::Entry, ""),
    ("entry_fact_withdrawal", Scope::Withdrawal, ""),
    ("lemma_calls_in_the_assertion", Scope::AtAssertion, ""),
    ("field_rewrites", Scope::Withdrawal, ""),
    ("loop_fact_handoff", Scope::Handoff, ""),
    ("parameter_type_invariants", Scope::Entry, ""),
    ("assumed_fact_handoff", Scope::Handoff, ""),
    ("mapping_closure_ground_instances", Scope::Derived, ""),
    ("constructor_facts", Scope::Derived, ""),
    ("ground_equality_facts", Scope::Derived, ""),
    ("transitive_disequalities", Scope::Derived, ""),
    ("irrelevant_fact_withdrawal", Scope::Withdrawal, ""),
    ("final_alias_substitutions", Scope::Derived, ""),
    ("closure_wiring", Scope::Handoff, ""),
    // proof_assert_wiring.rs
    ("closure_capture_invariants", Scope::TypeInvariant, ""),
    // ghost_context/mod.rs
    (
        "ghost_block_facts",
        Scope::FactScope,
        "build_ghost_context_for_function",
    ),
    ("ghost_block_capture_filter", Scope::Withdrawal, ""),
    ("ghost_final_deref_derivation", Scope::Derived, ""),
    (
        "function_level_return_tuple_facts",
        Scope::NotAnAssertionFact,
        "",
    ),
];

/// The lane files, as `(name, source)`.
const LANE_FILES: &[(&str, &str)] = &[
    (
        "proof_assert_snapshot.rs",
        include_str!("proof_assert_snapshot.rs"),
    ),
    (
        "verification/proof_assert_driver.rs",
        include_str!("verification/proof_assert_driver.rs"),
    ),
    (
        "proof_assert_verify/mod.rs",
        include_str!("proof_assert_verify/mod.rs"),
    ),
    (
        "proof_assert_wiring.rs",
        include_str!("proof_assert_wiring.rs"),
    ),
    ("ghost_context/mod.rs", include_str!("ghost_context/mod.rs")),
];

/// The local names that hold an assertion's facts on their way to the
/// solver.
const SINKS: &[&str] = &[
    "preconditions",
    "prepared.preconditions",
    "assumed_facts",
    "assumption_substitution_facts",
    "substitution_facts",
    "phase1_assumptions",
    "post_loop_assumptions",
    "ghost_context",
    "pa_ghost_context",
    "semantic_facts_raw",
    "block_assumptions",
    "proof_assert_call_assumptions",
    "substitutions",
];

/// The `FactScope` entry points a point-scoped producer must call.
const FACT_SCOPE_QUERIES: &[&str] = &[
    "stale_names(",
    "stale_names_after_region(",
    "written_since(",
    "exit_fact_stale_names",
    "placement.holds(",
    "LoopHeadNames::new(",
];

/// The lane code before its `#[cfg(test)] mod tests`.
fn production_part(source: &str) -> &str {
    source
        .find("#[cfg(test)]\nmod tests")
        .map_or(source, |end| &source[..end])
}

/// Whether `line` adds to (or hands on) a fact sink.
fn adds_to_a_sink(line: &str) -> bool {
    let line = line.trim();
    if line.starts_with("//") {
        return false;
    }
    SINKS.iter().any(|sink| {
        let seeded = line
            .strip_prefix(&format!("let mut {sink} = "))
            .is_some_and(|init| {
                !init.starts_with("Vec::new()") && !init.starts_with("HashSet::new()")
            });
        let added = [".push(", ".extend(", ".insert(", ".append("]
            .iter()
            .any(|op| contains_word_then(line, sink, op));
        let handed = contains_word_then(line, &format!("&mut {sink}"), "")
            && !line.contains(&format!("in &mut {sink}"));
        seeded || added || handed
    })
}

/// Whether `line` contains `word` (not as the tail of a longer identifier or
/// path) immediately followed by `then`.
fn contains_word_then(line: &str, word: &str, then: &str) -> bool {
    let needle = format!("{word}{then}");
    line.match_indices(&needle).any(|(at, _)| {
        let before = line[..at].chars().next_back();
        let after = line[at + needle.len()..].chars().next();
        let starts_word =
            !before.is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '.');
        let ends_word = !then.is_empty()
            || !after.is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '.');
        starts_word && ends_word
    })
}

/// The ids a `// fact-source:` marker on `line` names.
fn marker_ids(line: &str) -> Option<Vec<String>> {
    let (_, ids) = line.split_once("// fact-source:")?;
    Some(ids.split(',').map(|id| id.trim().to_string()).collect())
}

/// The body of `fn name` in the lane files, up to the end of that item.
fn function_body(name: &str) -> Option<&'static str> {
    LANE_FILES.iter().find_map(|(_, source)| {
        let source = production_part(source);
        let start = source
            .find(&format!("fn {name}("))
            .or_else(|| source.find(&format!("fn {name}<")))?;
        let rest = &source[start..];
        let end = rest.find("\n}\n").map_or(rest.len(), |end| end + 2);
        Some(&rest[..end])
    })
}

#[test]
fn every_fact_sink_write_names_a_registered_source() {
    let registered: HashSet<&str> = FACT_SOURCES.iter().map(|(id, _, _)| *id).collect();
    let mut unmarked = Vec::new();
    let mut unknown = BTreeSet::new();
    let mut used = HashSet::new();
    for (file, source) in LANE_FILES {
        let lines: Vec<&str> = production_part(source).lines().collect();
        for (index, line) in lines.iter().enumerate() {
            if !adds_to_a_sink(line) {
                continue;
            }
            // The marker sits on the statement's first line or one of the
            // three lines above it.
            let marker = (index.saturating_sub(3)..=index)
                .rev()
                .find_map(|at| marker_ids(lines[at]));
            let Some(ids) = marker else {
                unmarked.push(format!("{file}:{}: {}", index + 1, line.trim()));
                continue;
            };
            for id in ids {
                if registered.contains(id.as_str()) {
                    used.insert(id);
                } else {
                    unknown.insert(format!("{file}:{}: {id}", index + 1));
                }
            }
        }
    }
    assert!(
        unmarked.is_empty(),
        "a statement adds to an assertion's facts without naming its source; register it in \
         FACT_SOURCES with the rule that decides where it holds and mark it \
         `// fact-source: <id>`:\n{}",
        unmarked.join("\n")
    );
    assert!(
        unknown.is_empty(),
        "unregistered fact-source ids: {unknown:?}"
    );
    let never_marked: Vec<&str> = FACT_SOURCES
        .iter()
        .map(|(id, _, _)| *id)
        .filter(|id| !used.contains(*id))
        .collect();
    assert!(
        never_marked.is_empty(),
        "registered fact sources no statement is marked with: {never_marked:?}"
    );
}

#[test]
fn every_point_scoped_fact_source_asks_fact_scope() {
    let mut not_asking = Vec::new();
    for (id, scope, producer) in FACT_SOURCES {
        if *scope != Scope::FactScope {
            continue;
        }
        let Some(body) = function_body(producer) else {
            not_asking.push(format!("{id}: producer `{producer}` not found"));
            continue;
        };
        if !FACT_SCOPE_QUERIES.iter().any(|query| body.contains(query)) {
            not_asking.push(format!("{id}: `{producer}` never asks FactScope"));
        }
    }
    assert!(not_asking.is_empty(), "{not_asking:#?}");
}

/// The lane's own fact fields: a new one is a new sink, and its facts would
/// reach the solver without passing a marked statement.
#[test]
fn the_snapshot_carries_only_the_registered_fact_fields() {
    let source = production_part(include_str!("proof_assert_snapshot.rs"));
    let start = source
        .find("pub(super) struct AssertionSnapshot {")
        .expect("AssertionSnapshot is declared in proof_assert_snapshot.rs");
    let body = &source[start..start + source[start..].find("\n}\n").unwrap_or(0)];
    let fact_fields: BTreeSet<&str> = body
        .lines()
        .filter_map(|line| line.trim().strip_prefix("pub(super) "))
        .filter(|field| field.contains("Vec<PureExpr>") || field.contains("Option<PureExpr>"))
        .filter_map(|field| field.split(':').next())
        .collect();
    let expected: BTreeSet<&str> = [
        "call_effect_expr",
        "return_expr",
        "assumed_facts",
        "substitution_facts",
        "call_assumptions",
        "call_obligations",
        "post_loop_assumptions",
    ]
    .into_iter()
    .collect();
    assert_eq!(
        fact_fields, expected,
        "AssertionSnapshot's fact fields changed; register the new field's source in \
         FACT_SOURCES and mark where it is filled"
    );
}

#[test]
fn the_scanner_sees_each_kind_of_sink_write() {
    assert!(adds_to_a_sink("            assumed_facts.extend(x);"));
    assert!(adds_to_a_sink("    preconditions.push(fact);"));
    assert!(adds_to_a_sink(
        "            prepared.preconditions.push(fact);"
    ));
    assert!(adds_to_a_sink(
        "                substitutions.insert(name, rhs);"
    ));
    assert!(adds_to_a_sink(
        "    let mut preconditions = fn_precond_vec;"
    ));
    assert!(adds_to_a_sink("        &mut prepared.preconditions,"));
    assert!(adds_to_a_sink("    apply(&mut substitutions, &facts);"));
    assert!(!adds_to_a_sink("    let mut ghost_context = Vec::new();"));
    assert!(!adds_to_a_sink("        for fact in &mut assumed_facts {"));
    assert!(!adds_to_a_sink(
        "    let n = closure_substitutions.insert(a, b);"
    ));
    assert!(!adds_to_a_sink("    // preconditions.push(fact);"));
    assert!(!adds_to_a_sink(
        "    snapshot.post_loop_assumptions.is_empty()"
    ));
}
