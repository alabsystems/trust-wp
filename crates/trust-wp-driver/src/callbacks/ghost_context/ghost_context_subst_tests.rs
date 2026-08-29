// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

use crate::mir_analysis::NameSubstitutions;

#[test]
fn derive_final_deref_ghost_substitutions_adds_missing_final_deref_key() {
    let mut substitutions = HashMap::new();
    substitutions.insert(
        "*g2".to_string(),
        PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "g2".to_string(),
            None,
        ))))),
    );

    super::derive_final_deref_ghost_substitutions(&mut substitutions);

    assert_eq!(
        substitutions.get("^*g2"),
        Some(&PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(
            PureExpr::Var("g2".to_string(), None),
        ))))),
        "should derive ^*g2 when *g2 maps to ^^g2"
    );
}

#[test]
fn derive_final_deref_ghost_substitutions_does_not_add_mismatched_or_existing_keys() {
    let mut substitutions = HashMap::new();
    substitutions.insert(
        "*x".to_string(),
        PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "y".to_string(),
            None,
        ))))),
    );
    substitutions.insert("^*x".to_string(), PureExpr::Int(7));

    super::derive_final_deref_ghost_substitutions(&mut substitutions);

    assert_eq!(
        substitutions.get("^*x"),
        Some(&PureExpr::Int(7)),
        "existing ^*x substitution should be preserved"
    );
    assert_eq!(
        substitutions.len(),
        2,
        "mismatched *x -> ^^y pattern must not synthesize extra bindings"
    );
}

/// Verify `GhostContextFacts` separates alias and semantic channels (#2326).
#[test]
fn ghost_context_facts_dual_channel_structure() {
    let alias_fact = PureExpr::BinOp(
        Arc::new(PureExpr::Var("v".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("call_1".to_string(), None)),
    );
    let semantic_fact = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "v".to_string(),
                Some(ExprSort::Seq),
            )))),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );

    let facts = super::GhostContextFacts {
        alias_facts: vec![alias_fact.clone()],
        semantic_facts: vec![semantic_fact.clone()],
    };

    assert_eq!(
        facts.alias_facts.len(),
        1,
        "alias channel should carry one equality"
    );
    assert_eq!(
        facts.semantic_facts.len(),
        1,
        "semantic channel should carry one postcondition-derived fact"
    );
    assert_eq!(facts.alias_facts[0], alias_fact);
    assert_eq!(facts.semantic_facts[0], semantic_fact);
}

#[test]
fn ghost_context_filters_double_final_closure_capture_alias() {
    let facts = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(10)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("c".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "__trust_wp_tuple1".to_string(),
                args: vec![PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(
                    PureExpr::Var("x".to_string(), None),
                ))))],
            }),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        ),
    ];

    let filtered = super::filter_stale_mutation_alias_facts(facts);
    let rendered: Vec<String> = filtered.iter().map(ToString::to_string).collect();

    assert!(
        rendered.iter().any(|text| text.contains("x == 10")),
        "ghost context should preserve ordinary substitution facts: {rendered:?}"
    );
    assert!(
        rendered.iter().any(|text| text.contains("^x == (x + 1)")),
        "ghost context should preserve useful mutating-call facts: {rendered:?}"
    );
    assert!(
        rendered
            .iter()
            .all(|text| !text.contains("c == __trust_wp_tuple1(^^x)")),
        "ghost context should drop the double-final closure capture alias: {rendered:?}"
    );
}

/// Verify that `assumption_targets_focus_vars` correctly filters semantic facts
/// by focus variable relevance — the same filter used on ghost closure effects.
#[test]
fn semantic_fact_focus_var_filtering() {
    let focus_vars: HashSet<String> = ["v".to_string()].into_iter().collect();

    // A fact that mentions a focus variable should pass.
    let relevant_fact = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "v".to_string(),
                None,
            )))),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );
    assert!(
        super::assumption_targets_focus_vars(&relevant_fact, &focus_vars),
        "fact mentioning focus var 'v' should be selected"
    );

    // A fact that mentions no focus variable should be filtered out.
    let irrelevant_fact = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    );
    assert!(
        !super::assumption_targets_focus_vars(&irrelevant_fact, &focus_vars),
        "fact not mentioning any focus var should be rejected"
    );
}

#[test]
fn rewrite_ghost_closure_capture_vars_restores_outer_focus_name() {
    let focus_vars: HashSet<String> = ["v".to_string()].into_iter().collect();
    let fact = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "self.0".to_string(),
                Some(ExprSort::Seq),
            )))),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );

    assert!(
        !super::assumption_targets_focus_vars(&fact, &focus_vars),
        "closure-local capture name should not match outer focus vars before rewrite"
    );

    let rewritten = super::rewrite_ghost_closure_capture_vars(&fact, &["v".to_string()]);

    assert_eq!(
        rewritten,
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "v".to_string(),
                    Some(ExprSort::Seq),
                )))),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        ),
        "capture rewrite should project self.0 back to the outer source name"
    );
    assert!(
        super::assumption_targets_focus_vars(&rewritten, &focus_vars),
        "rewritten fact should now survive the outer proof_assert focus filter"
    );
}

#[test]
fn ghost_substitution_assumptions_preserve_mir_backed_name_sorts_recursively() {
    let option_sort = ExprSort::Datatype(intern_sort_name("core::option::Option"));
    let substitutions = NameSubstitutions::new(
        HashMap::from([
            (
                "get1".to_string(),
                PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                        "v".to_string(),
                        None,
                    )))),
                    method: "get_ghost".to_string(),
                    args: vec![PureExpr::Var("idx".to_string(), None)],
                },
            ),
            (
                "is_empty".to_string(),
                PureExpr::LogicFnCall {
                    name: "is_empty_ghost".to_string(),
                    args: vec![PureExpr::Var("v".to_string(), None)],
                },
            ),
            (
                "pop1".to_string(),
                PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
                    method: "pop_back_ghost".to_string(),
                    args: vec![],
                },
            ),
        ]),
        HashMap::from([
            ("get1".to_string(), Some(option_sort.clone())),
            ("idx".to_string(), Some(ExprSort::Int)),
            ("is_empty".to_string(), Some(ExprSort::Bool)),
            ("pop1".to_string(), Some(option_sort.clone())),
            ("v".to_string(), Some(ExprSort::Seq)),
        ]),
    );

    let assumptions = super::substitution_assumptions(&substitutions);

    assert_eq!(
        assumptions,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("get1".to_string(), Some(option_sort.clone()))),
                BinOp::Eq,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                        "v".to_string(),
                        Some(ExprSort::Seq),
                    )))),
                    method: "get_ghost".to_string(),
                    args: vec![PureExpr::Var("idx".to_string(), Some(ExprSort::Int))],
                }),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("is_empty".to_string(), Some(ExprSort::Bool))),
                BinOp::Eq,
                Arc::new(PureExpr::LogicFnCall {
                    name: "is_empty_ghost".to_string(),
                    args: vec![PureExpr::Var("v".to_string(), Some(ExprSort::Seq))],
                }),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("pop1".to_string(), Some(option_sort))),
                BinOp::Eq,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("v".to_string(), Some(ExprSort::Seq))),
                    method: "pop_back_ghost".to_string(),
                    args: vec![],
                }),
            ),
        ],
        "ghost substitution assumptions should reuse driver-provided name_sorts instead of defaulting helper locals to Int"
    );
}

#[test]
fn ghost_substitution_assumptions_follow_preserved_name_sorts_through_helper_alias_chain() {
    let option_sort = ExprSort::Datatype(intern_sort_name("core::option::Option"));
    let substitutions = NameSubstitutions::new(
        HashMap::from([
            (
                "helper_result".to_string(),
                PureExpr::Var("pop1".to_string(), None),
            ),
            (
                "pop1".to_string(),
                PureExpr::LogicFnCall {
                    name: "pop_back_ghost".to_string(),
                    args: vec![PureExpr::Var("v".to_string(), None)],
                },
            ),
        ]),
        HashMap::from([
            ("pop1".to_string(), Some(option_sort.clone())),
            ("v".to_string(), Some(ExprSort::Seq)),
        ]),
    );

    let assumptions = super::substitution_assumptions(&substitutions);

    assert_eq!(
        assumptions,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::Var(
                    "helper_result".to_string(),
                    Some(option_sort.clone()),
                )),
                BinOp::Eq,
                Arc::new(PureExpr::Var("pop1".to_string(), Some(option_sort.clone()))),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("pop1".to_string(), Some(option_sort))),
                BinOp::Eq,
                Arc::new(PureExpr::LogicFnCall {
                    name: "pop_back_ghost".to_string(),
                    args: vec![PureExpr::Var("v".to_string(), Some(ExprSort::Seq))],
                }),
            ),
        ],
        "ghost helper result aliases should inherit preserved sorts from the terminal helper name before falling back to RHS shape heuristics"
    );
}

/// Verify that `derive_final_deref_ghost_substitutions` derives `^*base → value`
/// when `*base` maps to a concrete value (e.g., `Int(1)` from `**g2 = 1` inside
/// a ghost block). (#2671)
#[test]
fn derive_final_deref_ghost_substitutions_concrete_write_derives_final_deref() {
    let mut substitutions = HashMap::new();
    // Simulates *g2 → Int(1) from a ghost block double-deref write.
    substitutions.insert("*g2".to_string(), PureExpr::Int(1));

    super::derive_final_deref_ghost_substitutions(&mut substitutions);

    assert_eq!(
        substitutions.get("^*g2"),
        Some(&PureExpr::Int(1)),
        "should derive ^*g2 → 1 when *g2 maps to a concrete value from ghost write"
    );
}

/// Verify that concrete write derivation does not fire for identity mappings
/// like `*g2 → g2` (which are just aliases, not ghost writes).
#[test]
fn derive_final_deref_ghost_substitutions_identity_var_not_concrete() {
    let mut substitutions = HashMap::new();
    // *g2 → g2 is an identity alias, not a concrete write
    substitutions.insert("*g2".to_string(), PureExpr::Var("g2".to_string(), None));

    super::derive_final_deref_ghost_substitutions(&mut substitutions);

    assert!(
        !substitutions.contains_key("^*g2"),
        "identity alias *g2 → g2 should NOT derive ^*g2"
    );
}

/// Verify that concrete write derivation does not fire for Final-wrapped values
/// (those are handled by the existing double-Final pattern).
#[test]
fn derive_final_deref_ghost_substitutions_final_not_concrete() {
    let mut substitutions = HashMap::new();
    // *g2 → Final(Var("other")) is a Final-wrapped value
    substitutions.insert(
        "*g2".to_string(),
        PureExpr::Final(Arc::new(PureExpr::Var("other".to_string(), None))),
    );

    super::derive_final_deref_ghost_substitutions(&mut substitutions);

    assert!(
        !substitutions.contains_key("^*g2"),
        "Final-wrapped values should not trigger concrete write derivation"
    );
}

#[test]
fn normalize_ghost_context_fact_normalizes_view_syntax_for_seq_helper_results() {
    let fact = PureExpr::LogicFnCall {
        name: "view".to_string(),
        args: vec![PureExpr::Var("v".to_string(), Some(ExprSort::Seq))],
    };

    let normalized = super::normalize_ghost_context_fact(fact);

    assert_eq!(
        normalized,
        PureExpr::View(Arc::new(PureExpr::Var("v".to_string(), Some(ExprSort::Seq)))),
        "ghost-context semantic facts should normalize raw view(...) helper syntax before solver handoff"
    );
}

#[test]
fn scalar_tuple_projection_return_facts_bridge_scalar_tuple_get_artifact() {
    let x_plus_one = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    let return_expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![x_plus_one.clone()],
    };

    let facts = super::collect_scalar_tuple_projection_identity_facts(&return_expr);

    assert_eq!(
        facts,
        vec![PureExpr::BinOp(
            Arc::new(return_expr),
            BinOp::Eq,
            Arc::new(x_plus_one),
        )],
        "scalar tuple_get_0 return artifacts should be bridged to their scalar argument"
    );
}

#[test]
fn scalar_tuple_projection_return_facts_ignore_tuple_arguments() {
    let tuple_arg = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple2".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(2)],
    };
    let return_expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![tuple_arg],
    };

    let facts = super::collect_scalar_tuple_projection_identity_facts(&return_expr);

    assert!(
        facts.is_empty(),
        "real tuple projections must stay uninterpreted unless tuple axioms discharge them"
    );
}

/// Verify that closure substitution key rewriting converts `self.N`-based
/// keys to source capture names, preserving `*` and `^*` prefixes. (#2671)
#[test]
fn rewrite_closure_substitution_capture_names_rewrites_deref_keys() {
    use crate::mir_analysis::NameSubstitutions;

    let capture_names = vec!["g2".to_string()];
    let mut subs = NameSubstitutions::new(
        {
            let mut map = HashMap::new();
            // Simulates `*self.0 -> Int(1)` from a double-deref write in the closure.
            map.insert("*self.0".to_string(), PureExpr::Int(1));
            // Also a direct name mapping.
            map.insert(
                "self.0".to_string(),
                PureExpr::Var("arg0".to_string(), None),
            );
            map
        },
        HashMap::new(),
    );

    super::closure_mir::rewrite_closure_substitution_capture_names(&mut subs, &capture_names);

    assert_eq!(
        subs.exprs.get("*g2"),
        Some(&PureExpr::Int(1)),
        "should rewrite *self.0 to *g2 for capture variable"
    );
    assert!(
        !subs.exprs.contains_key("*self.0"),
        "original *self.0 key should be removed after rewriting"
    );
    assert!(
        subs.exprs.contains_key("g2"),
        "should rewrite self.0 to g2 for capture variable"
    );
}

/// Verify that projected reborrow carrier names from closure capture field
/// access are rewritten to source capture names. (#2691)
///
/// In closure MIR, `&mut ((*_1).0)` creates a carrier `__trust_wp_reborrow_1_deref_field0`
/// instead of `self.0`. The deref write `*carrier = Int(1)` needs to be rewritten
/// to `*g2 = Int(1)` so the ghost context produces `^*g2 -> Int(1)`.
#[test]
fn rewrite_closure_substitution_capture_names_rewrites_carrier_keys() {
    use crate::mir_analysis::NameSubstitutions;

    let capture_names = vec!["g2".to_string()];
    let mut subs = NameSubstitutions::new(
        {
            let mut map = HashMap::new();
            // Simulates `*__trust_wp_reborrow_1_deref_field0 -> Int(1)` from a
            // single-deref write through a projected reborrow carrier.
            map.insert(
                "*__trust_wp_reborrow_1_deref_field0".to_string(),
                PureExpr::Int(1),
            );
            // Also a direct carrier name mapping.
            map.insert(
                "__trust_wp_reborrow_1_deref_field0".to_string(),
                PureExpr::Var("arg0".to_string(), None),
            );
            map
        },
        HashMap::new(),
    );

    super::closure_mir::rewrite_closure_substitution_capture_names(&mut subs, &capture_names);

    assert_eq!(
        subs.exprs.get("*g2"),
        Some(&PureExpr::Int(1)),
        "should rewrite *__trust_wp_reborrow_1_deref_field0 to *g2 for capture variable"
    );
    assert!(
        !subs
            .exprs
            .contains_key("*__trust_wp_reborrow_1_deref_field0"),
        "original carrier key should be removed after rewriting"
    );
    assert!(
        subs.exprs.contains_key("g2"),
        "should rewrite __trust_wp_reborrow_1_deref_field0 to g2 for capture variable"
    );
}

/// Verify that projected reborrow carrier names in Var expressions are
/// rewritten to capture names by `rewrite_ghost_closure_capture_vars`. (#2691)
#[test]
fn rewrite_ghost_closure_capture_vars_rewrites_carrier_var_names() {
    let capture_names = vec!["g2".to_string()];
    let expr = PureExpr::Deref(Arc::new(PureExpr::Var(
        "__trust_wp_reborrow_1_deref_field0".to_string(),
        None,
    )));

    let rewritten = super::rewrite_ghost_closure_capture_vars(&expr, &capture_names);

    assert_eq!(
        rewritten,
        PureExpr::Deref(Arc::new(PureExpr::Var("g2".to_string(), None))),
        "should rewrite carrier Var to capture name in expressions"
    );
}

/// Verify that closure substitution rewriting also transforms Var references
/// in substitution values from closure-internal to source names. (#2671)
#[test]
fn rewrite_closure_substitution_capture_names_rewrites_value_vars() {
    use crate::mir_analysis::NameSubstitutions;

    let capture_names = vec!["x".to_string(), "y".to_string()];
    let mut subs = NameSubstitutions::new(
        {
            let mut map = HashMap::new();
            // Value references a closure capture variable.
            map.insert(
                "self.0".to_string(),
                PureExpr::BinOp(
                    Arc::new(PureExpr::Var("self.1".to_string(), None)),
                    trust_wp_core::formula::BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                ),
            );
            map
        },
        HashMap::new(),
    );

    super::closure_mir::rewrite_closure_substitution_capture_names(&mut subs, &capture_names);

    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("y".to_string(), None)),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    assert_eq!(
        subs.exprs.get("x"),
        Some(&expected),
        "should rewrite Var(self.1) to Var(y) in substitution values"
    );
}

/// End-to-end test for the ghost_let double-deref write pattern (#2691).
///
/// Simulates the full pipeline: carrier-named deref substitution from closure
/// extraction -> capture name rewriting -> final-deref derivation.
/// This is the exact pattern needed for `ghost! { **g2 = 1; }` where
/// `g2: Ghost<&mut i32>`.
#[test]
fn ghost_let_double_deref_write_carrier_to_final_deref_end_to_end() {
    use crate::mir_analysis::NameSubstitutions;

    // Step 1: Simulates what closure MIR extraction produces.
    // The closure has `**g2 = 1` decomposed into deref_mut + single-deref write.
    // The deref write goes through a projected reborrow carrier.
    let capture_names = vec!["g2".to_string()];
    let mut subs = NameSubstitutions::new(
        {
            let mut map = HashMap::new();
            // From the deref write through the carrier: `*carrier -> Int(1)`
            map.insert(
                "*__trust_wp_reborrow_1_deref_field0".to_string(),
                PureExpr::Int(1),
            );
            // The carrier's own identity
            map.insert(
                "__trust_wp_reborrow_1_deref_field0".to_string(),
                PureExpr::Var("call_1".to_string(), None),
            );
            map
        },
        HashMap::new(),
    );

    // Step 2: Rewrite closure capture names.
    super::closure_mir::rewrite_closure_substitution_capture_names(&mut subs, &capture_names);

    assert_eq!(
        subs.exprs.get("*g2"),
        Some(&PureExpr::Int(1)),
        "after capture name rewrite: *carrier should become *g2"
    );

    // Step 3: Derive final-deref substitutions.
    super::derive_final_deref_ghost_substitutions(&mut subs);

    assert_eq!(
        subs.exprs.get("^*g2"),
        Some(&PureExpr::Int(1)),
        "after final-deref derivation: should have ^*g2 -> Int(1)"
    );
}
