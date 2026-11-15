// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{BinOp, PureExpr};

use crate::{
    callbacks::verification::contract_transform::transform_contract, mir_analysis::MutBorrowBody,
};

pub(super) fn make_parsed_contract() -> crate::callbacks::parsing::ParsedContract {
    use crate::callbacks::parsing::{LoopFields, MutBorrowFields, ParsedContract};

    ParsedContract {
        requires: vec![],
        ensures: vec![],
        result_expr: None,
        result_expr_spanned: None,
        arg_names: vec![],
        call_assumptions: vec![],
        pre_loop_call_assumptions: vec![],
        call_obligations: vec![],
        pre_loop_call_obligations: vec![],
        post_loop_call_obligations: vec![],
        returning_path_facts: Vec::new(),
        extraction_fail_closed_reason: None,
        panic_unreachability_obligations: 0,
        user_written_false_obligations: 0,
        proved_dead_edges: Default::default(),
        loop_fields: LoopFields {
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],
            all_loop_spans: vec![],
            variants: vec![],
            loop_analysis: None,
            loop_obligation_groups: vec![],
        },
        mut_borrow: MutBorrowFields {
            mut_borrow_body: None,
            mut_ref_param_names: HashSet::new(),
            state_params: HashSet::new(),
            projected_final_pins: Vec::new(),
            stale_call_final_params: HashSet::new(),
        },
        reborrow_prophecy: None,
    }
}

#[test]
fn transform_contract_empty_contract_produces_empty_output() {
    let parsed = make_parsed_contract();
    let tc = transform_contract(&parsed);

    assert!(
        tc.effective_requires.is_empty(),
        "empty contract should produce no requires"
    );
    assert!(
        tc.effective_ensures.is_empty(),
        "empty contract should produce no ensures"
    );
    assert_eq!(tc.base_requires_count, 0);
    assert_eq!(tc.base_ensures_count, 0);
    assert!(tc.mut_ref_params.is_empty());
    assert!(tc.closure_capture_fields.is_empty());
}

#[test]
fn transform_contract_passthrough_no_transforms() {
    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Var("x".to_string(), None)];
    parsed.ensures = vec![PureExpr::Var("result".to_string(), None)];

    let tc = transform_contract(&parsed);

    assert_eq!(
        tc.effective_requires.len(),
        1,
        "single require should pass through"
    );
    assert_eq!(
        tc.effective_ensures.len(),
        1,
        "single ensure should pass through"
    );
    assert_eq!(tc.base_requires_count, 1);
    assert_eq!(tc.base_ensures_count, 1);
}

#[test]
fn transform_contract_closure_captures_excluded_from_mut_ref_params() {
    let mut parsed = make_parsed_contract();
    parsed.ensures = vec![PureExpr::Var("result".to_string(), None)];
    parsed.mut_borrow.mut_borrow_body = Some(MutBorrowBody {
        final_values: HashMap::from([
            ("self.0".to_string(), PureExpr::Int(1)),
            ("self.1".to_string(), PureExpr::Int(2)),
            ("x".to_string(), PureExpr::Int(3)),
        ]),
        indexed_writes: vec![],
        resolve_results: None,
        finality: HashMap::new(),
        borrow_id_origins: HashMap::new(),
        delayed_writeback_assumptions: vec![],
        mutation_continued_params: HashSet::new(),
        nested_slot_resolutions: vec![],
        nested_transfer_params: HashSet::new(),
        lent_path_resolutions: vec![],
    });

    let tc = transform_contract(&parsed);

    // self.0 and self.1 should be detected as closure capture fields
    assert!(
        tc.closure_capture_fields.contains("self.0"),
        "self.0 should be a closure capture field"
    );
    assert!(
        tc.closure_capture_fields.contains("self.1"),
        "self.1 should be a closure capture field"
    );
    assert_eq!(tc.closure_capture_fields.len(), 2);

    // Closure capture fields should be excluded from mut_ref_params
    assert!(
        !tc.mut_ref_params.contains("self.0"),
        "self.0 should NOT be in mut_ref_params"
    );
    assert!(
        !tc.mut_ref_params.contains("self.1"),
        "self.1 should NOT be in mut_ref_params"
    );
    // But 'x' (not a closure capture) should remain
    assert!(
        tc.mut_ref_params.contains("x"),
        "'x' should remain in mut_ref_params"
    );
}

#[test]
fn transform_contract_call_obligations_merged_into_ensures() {
    let obligation = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let mut parsed = make_parsed_contract();
    parsed.ensures = vec![PureExpr::Bool(true)];
    parsed.call_obligations = vec![obligation.clone()];

    let tc = transform_contract(&parsed);

    assert_eq!(
        tc.base_ensures_count, 1,
        "base ensures count excludes obligations"
    );
    assert_eq!(
        tc.effective_ensures.len(),
        2,
        "effective ensures should include base + obligations"
    );
    assert_eq!(
        tc.effective_ensures[1], obligation,
        "obligation should be appended after base ensures"
    );
}

#[test]
fn transform_contract_call_assumptions_merged_into_requires() {
    let assumption = PureExpr::BinOp(
        Arc::new(PureExpr::Var("y".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Bool(true)];
    parsed.call_assumptions = vec![assumption.clone()];

    let tc = transform_contract(&parsed);

    assert_eq!(
        tc.base_requires_count, 1,
        "base requires count excludes assumptions"
    );
    assert!(
        tc.effective_requires.len() >= 2,
        "effective requires should include base + assumptions; got {}",
        tc.effective_requires.len()
    );
    assert!(
        tc.effective_requires.contains(&assumption),
        "assumption should appear in effective requires"
    );
}

#[test]
fn transform_contract_bridges_old_call_result_constructor_to_upgraded() {
    let ok_five = PureExpr::LogicFnCall {
        name: "Ok".to_string(),
        args: vec![PureExpr::Int(5)],
    };
    let old_call_result_ok = PureExpr::BinOp(
        Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
            "$call_3".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(ok_five.clone()),
    );

    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Bool(true)];
    parsed.result_expr = Some(PureExpr::Var("$call_3".to_string(), None));
    parsed.call_assumptions = vec![old_call_result_ok];

    let tc = transform_contract(&parsed);

    assert!(
        tc.effective_requires.iter().any(|expr| matches!(
            expr,
            PureExpr::BinOp(left, BinOp::Eq, right)
                if matches!(left.as_ref(), PureExpr::Var(name, _) if name == "$call_3__upgraded")
                && **right == ok_five
        )),
        "call-result assumptions should synthesize an upgraded constructor fact; got {:?}",
        tc.effective_requires
    );
}

#[test]
fn transform_contract_base_counts_track_user_clauses_not_merged() {
    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Bool(true), PureExpr::Bool(false)];
    parsed.ensures = vec![PureExpr::Bool(true)];
    parsed.call_assumptions = vec![PureExpr::Int(1)];
    parsed.call_obligations = vec![PureExpr::Int(2), PureExpr::Int(3)];

    let tc = transform_contract(&parsed);

    assert_eq!(
        tc.base_requires_count, 2,
        "base requires = user requires only"
    );
    assert_eq!(tc.base_ensures_count, 1, "base ensures = user ensures only");
    assert!(
        tc.effective_requires.len() > 2,
        "effective requires includes merged assumptions"
    );
    assert_eq!(
        tc.effective_ensures.len(),
        3,
        "effective ensures = 1 base + 2 obligations"
    );
}

/// Creusot semantics: `*x` in an `ensures` over a `&mut` param is the ENTRY
/// value and stays a current read (`Deref`); only `^x` is the final value.
/// Rewriting it to `Final` lets `#[ensures(result@ == (*r)@)] fn f(r: &mut
/// u32) -> u32 { *r = 5; 5 }` verify although it is false for any entry
/// `*r != 5` (`s48_mutref_ens_entry_value.rs`).
#[test]
fn transform_contract_mut_ref_ensures_deref_stays_entry_read() {
    let mut parsed = make_parsed_contract();
    parsed.ensures = vec![PureExpr::Deref(Arc::new(PureExpr::Var(
        "x".to_string(),
        None,
    )))];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["x".to_string()]);

    let tc = transform_contract(&parsed);

    let first = &tc.effective_ensures[0];
    assert!(
        matches!(first, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "x")),
        "`*x` in a Creusot ensures must stay the entry read `Deref(x)`; got: {first:?}"
    );
}

/// The legacy dialect `*x == old(*x) + 1` marks the entry value with `old`:
/// in a clause naming `x` inside `old(..)`, bare `*x` is the post-state and is
/// still rewritten to `^x`, while `old(*x)` stays the entry read.
#[test]
fn transform_contract_legacy_old_clause_rewrites_bare_deref_to_final() {
    let mut parsed = make_parsed_contract();
    let deref_x = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));
    parsed.ensures = vec![PureExpr::BinOp(
        Arc::new(deref_x.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(deref_x))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["x".to_string()]);
    parsed.mut_borrow.state_params = parsed.mut_borrow.mut_ref_param_names.clone();

    let tc = transform_contract(&parsed);

    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = &tc.effective_ensures[0] else {
        panic!("expected an equality; got {:?}", tc.effective_ensures[0]);
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::Final(_)),
        "bare `*x` beside `old(*x)` is the post-state; got: {lhs:?}"
    );
    assert!(
        format!("{rhs:?}").contains("Old(Deref(Var(\"x\""),
        "`old(*x)` must stay the entry read; got: {rhs:?}"
    );
}

/// The legacy dialect is a property of the CLAUSE: in `*a == old(*b)` the
/// clause names a `&mut` param inside `old(..)`, so bare `*a` is the
/// post-state (`^a`) although `a` itself is never named under `old`. Reading
/// it as the entry value turns swap's contract into `entry(a) == entry(b)`.
#[test]
fn transform_contract_legacy_old_clause_rewrites_every_mut_ref_deref_to_final() {
    let mut parsed = make_parsed_contract();
    let deref = |n: &str| PureExpr::Deref(Arc::new(PureExpr::Var(n.to_string(), None)));
    parsed.ensures = vec![PureExpr::BinOp(
        Arc::new(deref("a")),
        BinOp::Eq,
        Arc::new(PureExpr::Old(Arc::new(deref("b")))),
    )];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["a".to_string(), "b".to_string()]);
    parsed.mut_borrow.state_params = parsed.mut_borrow.mut_ref_param_names.clone();

    let tc = transform_contract(&parsed);

    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = &tc.effective_ensures[0] else {
        panic!("expected an equality; got {:?}", tc.effective_ensures[0]);
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "a")),
        "bare `*a` in a clause with `old(*b)` is the post-state `^a`; got: {lhs:?}"
    );
    assert!(
        format!("{rhs:?}").contains("Old(Deref(Var(\"b\""),
        "`old(*b)` must stay the entry read; got: {rhs:?}"
    );
}

/// The dialect is decided over the signature's `&mut` parameters
/// (`state_params`), the set every call of the function reads the clause
/// over, never over the set body extraction widens. With no mut-borrow body,
/// extraction once added every name read as `old(*x)` to the rewrite's
/// parameters, so `*p == old(*x)` of a shared `x` read `*p` as `^p` here and
/// as the entry value at every call: the body was proved of one value and
/// each caller credited with another.
#[test]
fn transform_contract_reads_states_over_the_signature_parameters() {
    let mut parsed = make_parsed_contract();
    let deref = |n: &str| PureExpr::Deref(Arc::new(PureExpr::Var(n.to_string(), None)));
    parsed.ensures = vec![PureExpr::BinOp(
        Arc::new(deref("p")),
        BinOp::Eq,
        Arc::new(PureExpr::Old(Arc::new(deref("x")))),
    )];
    parsed.arg_names = vec!["x".to_string(), "p".to_string()];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["p".to_string()]);
    parsed.mut_borrow.state_params = HashSet::from(["p".to_string()]);

    let tc = transform_contract(&parsed);

    let PureExpr::BinOp(lhs, BinOp::Eq, _) = &tc.effective_ensures[0] else {
        panic!("expected an equality; got {:?}", tc.effective_ensures[0]);
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "p")),
        "`old(*x)` of a shared `x` puts no clause in the pre-Creusot dialect: `*p` stays the \
         entry read every call reads; got: {lhs:?}"
    );
}

/// A clause without `old(..)` keeps Creusot's reading for EVERY `&mut` param,
/// even when a sibling clause of the same contract is in the legacy dialect.
#[test]
fn transform_contract_old_dialect_is_per_clause() {
    let mut parsed = make_parsed_contract();
    let deref = |n: &str| PureExpr::Deref(Arc::new(PureExpr::Var(n.to_string(), None)));
    parsed.ensures = vec![
        PureExpr::BinOp(
            Arc::new(deref("a")),
            BinOp::Eq,
            Arc::new(PureExpr::Old(Arc::new(deref("b")))),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Eq,
            Arc::new(deref("a")),
        ),
    ];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["a".to_string(), "b".to_string()]);
    parsed.mut_borrow.state_params = parsed.mut_borrow.mut_ref_param_names.clone();

    let tc = transform_contract(&parsed);

    let PureExpr::BinOp(_, BinOp::Eq, rhs) = &tc.effective_ensures[1] else {
        panic!("expected an equality; got {:?}", tc.effective_ensures[1]);
    };
    assert!(
        matches!(rhs.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "a")),
        "`*a` in a clause without `old(..)` stays the entry read; got: {rhs:?}"
    );
}

/// `old(p)` on a by-value parameter must collapse to `p`.
///
/// Left alone, the encoder mints a separate unconstrained `old_p`, and a TRUE
/// contract relating the two comes back FAILED with a "counterexample" whose
/// values have no relationship — `old_x = 1, x = 0` for
/// `#[ensures(result == old(x) + 1)] fn f(mut x: i32) -> i32 { x += 1; x }`.
/// A by-value parameter cannot change under the caller's feet, so the entry
/// value and the specification's `p` are the same thing.
#[test]
fn transform_contract_collapses_old_over_a_by_value_param() {
    let mut parsed = make_parsed_contract();
    parsed.arg_names = vec!["x".to_string()];
    // result == old(x) + 1
    parsed.ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )];

    let transformed = transform_contract(&parsed);
    let rendered = format!("{:?}", transformed.effective_ensures);
    assert!(
        !rendered.contains("Old("),
        "old(x) over a by-value parameter must collapse: {rendered}"
    );
    assert!(
        rendered.contains("\"x\""),
        "the parameter itself must survive: {rendered}"
    );
}

/// ...but `old()` over a `&mut` parameter's contents must NOT collapse: that
/// cell genuinely does change, and the mut-borrow lane owns the distinction.
#[test]
fn transform_contract_keeps_old_over_a_mut_ref_deref() {
    let mut parsed = make_parsed_contract();
    parsed.arg_names = vec!["v".to_string()];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["v".to_string()]);
    // old(*v)
    parsed.ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Var("v".to_string(), None),
        ))))),
    )];

    let transformed = transform_contract(&parsed);
    let rendered = format!("{:?}", transformed.effective_ensures);
    assert!(
        rendered.contains("\"v\""),
        "the mut-ref parameter must survive the transform: {rendered}"
    );
}
