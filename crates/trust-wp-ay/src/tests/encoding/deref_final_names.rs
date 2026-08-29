// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_encode_nested_deref_succeeds() {
    // Nested deref *(*v) should succeed and produce v_current_current (Part of #329)
    let mut encoder = AYEncoder::new();

    // *(*v) - nested deref
    let expr = deref(deref(var("v")));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Nested deref *(*v) should succeed: {:?}",
        result.as_ref().err()
    );
    // Variable name should be v_current_current
    assert!(
        encoder.vars_for_test().contains_key("v_current_current"),
        "Should create v_current_current variable"
    );
    let term = result.expect("nested deref should encode");
    let expected = *encoder
        .vars_for_test()
        .get("v_current_current")
        .expect("v_current_current should be registered");
    let not_eq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoded nested deref term should be exactly v_current_current"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_deref_succeeds() {
    // Final of deref ^(*v) should succeed and produce v_current_final (Part of #329)
    let mut encoder = AYEncoder::new();

    // ^(*v) - final of deref
    let expr = final_expr(deref(var("v")));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Final of deref ^(*v) should succeed: {:?}",
        result.as_ref().err()
    );
    // Variable name should be v_current_final
    assert!(
        encoder.vars_for_test().contains_key("v_current_final"),
        "Should create v_current_final variable"
    );
    let term = result.expect("final of deref should encode");
    let expected = *encoder
        .vars_for_test()
        .get("v_current_final")
        .expect("v_current_final should be registered");
    let not_eq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoded final-of-deref term should be exactly v_current_final"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_deref_of_final_succeeds() {
    // Deref of final *(^v) should succeed and produce v_final_current (Part of #329)
    let mut encoder = AYEncoder::new();

    // *(^v) - deref of final
    let expr = deref(final_expr(var("v")));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Deref of final *(^v) should succeed: {:?}",
        result.as_ref().err()
    );
    // Variable name should be v_final_current
    assert!(
        encoder.vars_for_test().contains_key("v_final_current"),
        "Should create v_final_current variable"
    );
    let term = result.expect("deref of final should encode");
    let expected = *encoder
        .vars_for_test()
        .get("v_final_current")
        .expect("v_final_current should be registered");
    let not_eq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoded deref-of-final term should be exactly v_final_current"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_deref_binop_distributes() {
    // Deref of arithmetic expression like *(x + y) distributes the wrapper
    // into operands: Deref(x) + Deref(y) → x_current + y_current (#2700).
    let mut encoder = AYEncoder::new();

    // *(x + y) - deref of arithmetic expression
    let expr = deref(add(var("x"), var("y")));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Deref(BinOp) should succeed via BinOp distribution (#2700): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_simple_deref_succeeds() {
    // Simple *v should succeed (regression test)
    let mut encoder = AYEncoder::new();

    let expr = deref(var("v"));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Simple deref should succeed: {:?}",
        result.as_ref().err()
    );

    // Semantic: *v creates v_current variable
    assert!(
        encoder.vars_for_test().contains_key("v_current"),
        "Deref should create v_current variable"
    );
    // Semantic check: encoded term must be the canonical deref variable.
    let term = result.unwrap();
    let expected = *encoder
        .vars_for_test()
        .get("v_current")
        .expect("v_current should be registered");
    let neq_term = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoded deref term should be exactly v_current"
    );
}

#[test]
#[timeout(30000)]
fn test_simple_final_succeeds() {
    // Simple ^v should succeed (regression test)
    let mut encoder = AYEncoder::new();

    let expr = final_expr(var("v"));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Simple final should succeed: {:?}",
        result.as_ref().err()
    );

    // Semantic: ^v creates v_final variable
    assert!(
        encoder.vars_for_test().contains_key("v_final"),
        "Final should create v_final variable"
    );
    // Semantic check: encoded term must be the canonical final variable.
    let term = result.unwrap();
    let expected = *encoder
        .vars_for_test()
        .get("v_final")
        .expect("v_final should be registered");
    let neq_term = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoded final term should be exactly v_final"
    );
}

// ── Phase 1b: Non-borrow variable collapse tests (#2675) ──────────

#[test]
#[timeout(5000)]
fn test_deref_non_borrow_datatype_collapses_to_var() {
    // Deref of a Datatype-annotated variable (e.g., Result from a call site)
    // should collapse to the variable itself, NOT create a _current variable.
    // This is critical for consuming method specs like `Ok(result) == *self`
    // where `self` is a Result value, not a mutable borrow. (#2675)
    let mut encoder = AYEncoder::new();

    let call_var = var_with_sort(
        "call_3",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("OwnResult")),
    );
    let deref_expr = deref(call_var.clone());

    let deref_term = encoder
        .encode_pure(&deref_expr)
        .expect("Deref of Datatype var should succeed");
    let var_term = encoder
        .encode_pure(&call_var)
        .expect("Var encoding should succeed");

    // Both terms should be identical — Deref is a no-op for non-borrow vars
    let not_eq = encoder.solver.neq(deref_term, var_term);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Deref(Var(call_3, Datatype)) should produce the same term as Var(call_3)"
    );
    // call_3_current should NOT be created
    assert!(
        !encoder.vars_for_test().contains_key("call_3_current"),
        "call_3_current should NOT be created for non-borrow Deref"
    );
}

#[test]
#[timeout(5000)]
fn test_deref_non_borrow_int_collapses_to_var() {
    // Deref of an Int-annotated variable should collapse to the variable itself.
    let mut encoder = AYEncoder::new();

    let x = var_with_sort("x", ExprSort::Int);
    let deref_expr = deref(x.clone());

    let deref_term = encoder
        .encode_pure(&deref_expr)
        .expect("Deref of Int var should succeed");
    let var_term = encoder
        .encode_pure(&x)
        .expect("Var encoding should succeed");

    let not_eq = encoder.solver.neq(deref_term, var_term);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Deref(Var(x, Int)) should produce the same term as Var(x)"
    );
}

#[test]
#[timeout(5000)]
fn test_deref_non_borrow_bool_collapses_to_var() {
    // Deref of a Bool-annotated variable should collapse to the variable itself.
    let mut encoder = AYEncoder::new();

    let b = var_with_sort("flag", ExprSort::Bool);
    let deref_expr = deref(b.clone());

    let deref_term = encoder
        .encode_pure(&deref_expr)
        .expect("Deref of Bool var should succeed");
    let var_term = encoder
        .encode_pure(&b)
        .expect("Var encoding should succeed");

    let not_eq = encoder.solver.neq(deref_term, var_term);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Deref(Var(flag, Bool)) should produce the same term as Var(flag)"
    );
}

#[test]
#[timeout(5000)]
fn test_deref_mutref_still_creates_current() {
    // Deref of a MutRef-annotated variable should still create _current
    // (existing behavior preserved).
    let mut encoder = AYEncoder::new();

    let v = var_with_sort("v", ExprSort::MutRef(Box::new(ExprSort::Int)));
    let deref_expr = deref(v);

    let result = encoder.encode_pure(&deref_expr);
    assert!(result.is_ok(), "Deref of MutRef var should succeed");

    assert!(
        encoder.vars_for_test().contains_key("v_current"),
        "Deref of MutRef should create v_current"
    );
}

#[test]
#[timeout(5000)]
fn test_deref_unannotated_still_creates_current() {
    // Deref of an unannotated variable (None sort) should still create _current
    // for backward compatibility. This is the conservative default.
    let mut encoder = AYEncoder::new();

    let v = var("v"); // None annotation
    let deref_expr = deref(v);

    let result = encoder.encode_pure(&deref_expr);
    assert!(result.is_ok(), "Deref of unannotated var should succeed");

    assert!(
        encoder.vars_for_test().contains_key("v_current"),
        "Deref of unannotated var should create v_current (backward compat)"
    );
}

#[test]
#[timeout(5000)]
fn test_final_non_borrow_datatype_collapses_to_var() {
    // Final of a Datatype-annotated variable should collapse to the variable
    // itself when the datatype PROVABLY embeds no mutable reference. Final
    // (^v) is only meaningful for mutable borrows. (#2675)
    //
    // Fix A (Final-collapse audit): the collapse is now guarded by the
    // sort-aware fail-closed predicate, so the pure-payload proof requires a
    // registered ADT decl — an UNDECLARED datatype refuses instead (see
    // test_final_mut_ref_embedding_datatype_refuses below).
    let mut encoder = AYEncoder::new();
    let mut decls = trust_wp_core::logic::AdtDecls::new();
    decls.insert(
        "OwnResult".to_string(),
        trust_wp_core::logic::AdtDecl::new(
            "OwnResult".to_string(),
            "OwnResult".to_string(),
            trust_wp_core::logic::AdtKind::Enum,
            vec![
                trust_wp_core::logic::AdtConstructorDecl::new(
                    "Ok".to_string(),
                    "Ok".to_string(),
                    vec![trust_wp_core::logic::AdtFieldDecl::new(
                        "value".to_string(),
                        ExprSort::Int,
                    )],
                ),
                trust_wp_core::logic::AdtConstructorDecl::new(
                    "Err".to_string(),
                    "Err".to_string(),
                    vec![trust_wp_core::logic::AdtFieldDecl::new(
                        "error".to_string(),
                        ExprSort::Bool,
                    )],
                ),
            ],
        ),
    );
    encoder.register_adt_decls(&decls);

    let call_var = var_with_sort(
        "call_3",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("OwnResult")),
    );
    let final_e = final_expr(call_var.clone());

    let final_term = encoder
        .encode_pure(&final_e)
        .expect("Final of Datatype var should succeed");
    let var_term = encoder
        .encode_pure(&call_var)
        .expect("Var encoding should succeed");

    let not_eq = encoder.solver.neq(final_term, var_term);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Final(Var(call_3, Datatype)) should produce the same term as Var(call_3)"
    );
    assert!(
        !encoder.vars_for_test().contains_key("call_3_final"),
        "call_3_final should NOT be created for non-borrow Final"
    );
}

#[test]
#[timeout(5000)]
fn test_final_int_annotation_preserves_post_state_var() {
    // Ghost state can be represented with an Int-backed carrier, so Final must
    // remain a distinct post-state variable even though the annotation is not a
    // mutable borrow. Collapsing this makes old/new FSet facts contradictory.
    let mut encoder = AYEncoder::new();

    let set_var = var_with_sort("set", ExprSort::Int);
    let final_e = final_expr(set_var);

    let final_term = encoder
        .encode_pure(&final_e)
        .expect("Final of Int-backed ghost carrier should succeed");
    let expected = *encoder
        .vars_for_test()
        .get("set_final")
        .expect("set_final should be registered");

    let not_eq = encoder.solver.neq(final_term, expected);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Final(Var(set, Int)) should produce the post-state set_final term"
    );
}

// ────────────────────────────────────────────────────────────────────
// Final-collapse audit Fix A pins: the sort-aware fail-closed guard
// ────────────────────────────────────────────────────────────────────

#[test]
#[timeout(5000)]
fn test_final_undeclared_datatype_refuses_fail_closed() {
    // An UNDECLARED datatype cannot be proven free of embedded `&mut` —
    // the Final collapse must refuse (fail-closed) instead of asserting
    // the potential inversion `^x == x`, and the demoting
    // FinalCollapseRefused counter must fire.
    crate::encoder::unsoundness::reset();
    let before = crate::encoder::unsoundness::snapshot();
    let mut encoder = AYEncoder::new();

    let call_var = var_with_sort(
        "call_9",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name(
            "TotallyUndeclaredAdt",
        )),
    );
    let result = encoder.encode_pure(&final_expr(call_var));
    assert!(
        result.is_err(),
        "Final(Var(_, Datatype(undeclared))) must refuse, got: {result:?}"
    );
    let after = crate::encoder::unsoundness::snapshot();
    let delta = crate::encoder::unsoundness::delta(&before, &after);
    assert_eq!(
        delta.get(&crate::encoder::unsoundness::UnsoundnessCategory::FinalCollapseRefused),
        Some(&1),
        "refusal must fire the FinalCollapseRefused demoting counter"
    );
    crate::encoder::unsoundness::reset();
}

#[test]
#[timeout(5000)]
fn test_final_mut_ref_embedding_datatype_refuses() {
    // A DECLARED datatype whose field sorts (transitively) embed `&mut` must
    // refuse the Final collapse: `Option<&mut T>`-shaped payloads have no
    // prophecy slot in the collapsed encoding (take_first_mut adjudication).
    crate::encoder::unsoundness::reset();
    let mut encoder = AYEncoder::new();
    let mut decls = trust_wp_core::logic::AdtDecls::new();
    decls.insert(
        "MutHolder".to_string(),
        trust_wp_core::logic::AdtDecl::new(
            "MutHolder".to_string(),
            "MutHolder".to_string(),
            trust_wp_core::logic::AdtKind::Struct,
            vec![trust_wp_core::logic::AdtConstructorDecl::new(
                "MutHolder".to_string(),
                "MutHolder".to_string(),
                vec![trust_wp_core::logic::AdtFieldDecl::new(
                    "r".to_string(),
                    ExprSort::MutRef(Box::new(ExprSort::Int)),
                )],
            )],
        ),
    );
    encoder.register_adt_decls(&decls);

    let call_var = var_with_sort(
        "call_7",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("MutHolder")),
    );
    let result = encoder.encode_pure(&final_expr(call_var));
    assert!(
        result.is_err(),
        "Final on a &mut-embedding datatype must refuse, got: {result:?}"
    );
    assert!(
        !encoder.vars_for_test().contains_key("call_7_final"),
        "no phantom call_7_final may be minted on the refusal path"
    );
    crate::encoder::unsoundness::reset();
}

/// `match x { Node(a) => <body(a)>, _ => 0 }` over a single-Int-payload
/// datatype, with a caller-supplied arm body.
fn single_payload_match(body: PureExpr) -> PureExpr {
    PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                pattern: trust_wp_core::formula::Pattern::Constructor {
                    name: "Node".to_string(),
                    inner: Some(Box::new(trust_wp_core::formula::Pattern::Binding(
                        "a".to_string(),
                    ))),
                },
                body,
            },
            trust_wp_core::formula::MatchArm {
                pattern: trust_wp_core::formula::Pattern::Wildcard,
                body: PureExpr::Int(0),
            },
        ],
    }
}

fn declare_single_payload_datatype(encoder: &mut AYEncoder) {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    let datatype = DatatypeSort {
        name: "Holder".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Node".to_string(),
                fields: vec![DatatypeField {
                    name: "holder_node_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Empty".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&datatype);
    let sort = Sort::Datatype(datatype);
    encoder
        .get_or_declare_var("x", sort)
        .expect("declare scrutinee x");
}

#[test]
#[timeout(30000)]
fn test_match_binder_final_on_pure_payload_still_collapses() {
    // Fix A must NOT break the exact case: `^a` on a match binder whose
    // annotation is a provably pure value sort (Int) still collapses to the
    // bound payload projection — a pure value has no temporal state.
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_single_payload_datatype(&mut encoder);

    let body = final_expr(var_with_sort("a", ExprSort::Int));
    let term = encoder
        .encode_pure(&single_payload_match(body))
        .expect("Final on a pure Int-annotated binder must still collapse");
    let rendered = encoder.solver.format_term(term);
    assert!(
        rendered.contains("holder_node_0"),
        "collapsed ^a should be the payload selector; got: {rendered}"
    );
    assert!(
        encoder.var_term("a_final").is_none(),
        "no disconnected a_final may be minted for the collapsed pure binder"
    );
}

#[test]
#[timeout(30000)]
fn test_match_binder_final_unannotated_refuses() {
    // The take_first_mut shape: `^r` on an UNANNOTATED match binder (the
    // driver emits `Final(Var("r", None))` for the `Some(r)` arm of
    // `Option<&mut T>` postconditions). Unknown sort — fail-closed refusal,
    // never a collapse onto the current-value payload.
    crate::encoder::unsoundness::reset();
    let before = crate::encoder::unsoundness::snapshot();
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_single_payload_datatype(&mut encoder);

    let body = final_expr(var("a"));
    let result = encoder.encode_pure(&single_payload_match(body));
    assert!(
        result.is_err(),
        "Final on an unannotated match binder must refuse (fail-closed), got: {result:?}"
    );
    let after = crate::encoder::unsoundness::snapshot();
    let delta = crate::encoder::unsoundness::delta(&before, &after);
    assert!(
        delta
            .get(&crate::encoder::unsoundness::UnsoundnessCategory::FinalCollapseRefused)
            .copied()
            .unwrap_or(0)
            >= 1,
        "refusal must fire the FinalCollapseRefused demoting counter"
    );
    crate::encoder::unsoundness::reset();
}

#[test]
#[timeout(30000)]
fn test_match_binder_final_mut_ref_annotation_refuses() {
    // `^r` on a binder ANNOTATED as `&mut T` whose bound payload is NOT a
    // real-prophecy MutRef carrier (the Option<&mut T> payload collapsed to
    // Int) — the exact adjudicated inversion; must refuse.
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_single_payload_datatype(&mut encoder);

    let body = final_expr(var_with_sort(
        "a",
        ExprSort::MutRef(Box::new(ExprSort::Int)),
    ));
    let result = encoder.encode_pure(&single_payload_match(body));
    assert!(
        result.is_err(),
        "Final on a MutRef-annotated binder without a prophecy slot must refuse, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_match_binder_deref_still_collapses() {
    // The Deref side of the binder collapse (#2124 AC3) is untouched by
    // Fix A: `*a` on a match binder still collapses to the payload term.
    let mut encoder = AYEncoder::new_with_quantifiers();
    declare_single_payload_datatype(&mut encoder);

    let body = deref(var("a"));
    let term = encoder
        .encode_pure(&single_payload_match(body))
        .expect("Deref on a match binder must still collapse");
    let rendered = encoder.solver.format_term(term);
    assert!(
        rendered.contains("holder_node_0"),
        "collapsed *a should be the payload selector; got: {rendered}"
    );
}

// ────────────────────────────────────────────────────────────────────
// Value-model container carriers keep a distinct final variable (vacfix)
//
// Anti-rot pins for the `cc/seq::f` fabricated-contradiction fix. The
// Phase-1b `Final` collapse arm above is correct for plain value datatypes
// (see `test_final_non_borrow_datatype_collapses_to_var`), but the SAME arm
// used to swallow ghost CONTAINERS whose annotation arrives as
// `ExprSort::Datatype(creusot_std::Seq)` rather than `ExprSort::Seq`. Those
// have real post-state (`s.push_front_ghost(&mut x)`), so collapsing `^s`
// onto `s` asserted `^s == s` and manufactured a contradictory base.
// ────────────────────────────────────────────────────────────────────

/// `Final` on a value-model CONTAINER datatype must NOT collapse: `^s` gets
/// its own carrier, exactly as the `ExprSort::Seq` spelling of the same
/// carrier already did.
#[test]
#[timeout(30000)]
fn test_final_value_model_container_datatype_keeps_distinct_carrier() {
    for name in [
        "creusot_std::Seq",
        "Seq",
        "Vec",
        "HashMap",
        "FMap",
        "Mapping",
    ] {
        let mut encoder = AYEncoder::new();
        let s = var_with_sort(
            "call_5",
            ExprSort::Datatype(trust_wp_core::formula::intern_sort_name(name)),
        );
        let final_s = final_expr(s.clone());

        let final_term = encoder
            .encode_pure(&final_s)
            .expect("Final of a container datatype var should encode");
        let var_term = encoder
            .encode_pure(&s)
            .expect("Var encoding should succeed");

        assert_ne!(
            final_term, var_term,
            "`^call_5` on the post-state container {name} must not collapse onto `call_5` \
             (collapsing asserts the false equality `^s == s`)"
        );
        assert!(
            encoder.vars_for_test().contains_key("call_5_final"),
            "{name}: the distinct post-state carrier call_5_final must be minted"
        );
    }
}

/// THE FAITHFUL-ENCODING PIN: the minimized `cc/seq::f` base must be
/// SATISFIABLE.
///
/// The reported vacuity core was exactly `len(s) = 0` together with
/// `len(^s) = len(s) + 1` (the `push_front_ghost` mutation premise). Those are
/// consistent in source semantics — `^s` and `s` are different values — and
/// only contradict each other once `^s` has been collapsed onto `s`'s carrier.
/// If this ever goes back to `Unsat`, the collapse has regressed and `cc/seq`
/// is demoted "vacuous (contradictory premises)" again.
#[test]
#[timeout(30000)]
fn test_seq_container_mutation_premises_are_satisfiable() {
    let mut encoder = AYEncoder::new();
    let s = var_with_sort(
        "call_5",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("creusot_std::Seq")),
    );

    // len(^s) == len(s) + 1
    let grew = eq(
        method_call(final_expr(s.clone()), "len", vec![]),
        add(method_call(s.clone(), "len", vec![]), int(1)),
    );
    // len(s) == 0
    let empty = eq(method_call(s, "len", vec![]), int(0));

    for premise in [&grew, &empty] {
        let term = encoder
            .encode_pure(premise)
            .expect("cc/seq premise should encode");
        encoder.solver.assert_term(term);
    }

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "`len(^s) == len(s) + 1` and `len(s) == 0` are consistent; an UNSAT base here is the \
         fabricated contradiction that demoted cc/seq::f as vacuous"
    );
}

/// The carve-out must NOT reach plain value datatypes or the Fix A refusal —
/// the take_first_mut lane stays exactly as it was.
#[test]
#[timeout(30000)]
fn test_container_carveout_does_not_widen_fix_a_guard() {
    use crate::encoder::final_collapse_guard::expr_sort_is_post_state_container;

    // Containers: declined collapse.
    assert!(expr_sort_is_post_state_container(&ExprSort::Seq));
    assert!(expr_sort_is_post_state_container(&ExprSort::FMap));
    assert!(expr_sort_is_post_state_container(&ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("creusot_std::Seq")
    )));
    assert!(expr_sort_is_post_state_container(&ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("Mapping")
    )));

    // NOT containers: plain values, pointer-transparent value-model wrappers
    // (the Box-reborrow lane), user ADTs, references and mut-refs. These keep
    // whatever behavior they had — collapse or Fix A refusal.
    for sort in [
        ExprSort::Int,
        ExprSort::Bool,
        ExprSort::Unit,
        ExprSort::Float,
        ExprSort::Tuple(2),
        ExprSort::Ref(Box::new(ExprSort::Int)),
        ExprSort::MutRef(Box::new(ExprSort::Int)),
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Box")),
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Rc")),
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Snapshot")),
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("SomeUserAdt")),
    ] {
        assert!(
            !expr_sort_is_post_state_container(&sort),
            "{sort} must not be treated as a post-state container"
        );
    }
}
