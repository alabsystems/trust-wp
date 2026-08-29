// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// ── sort_to_expr_sort coverage (#901 proof_coverage) ──────────────

/// `sort_to_expr_sort` maps `Sort::Bool` to `ExprSort::Bool`.
#[test]
#[timeout(30000)]
fn sort_to_expr_sort_bool_maps_to_bool() {
    let result = sort_to_expr_sort(&Sort::Bool);
    assert_eq!(
        result,
        Some(trust_wp_core::formula::ExprSort::Bool),
        "Sort::Bool should map to ExprSort::Bool"
    );
}

/// `sort_to_expr_sort` maps `Sort::Seq(Int)` to `ExprSort::Seq`. (#2080)
#[test]
#[timeout(30000)]
fn sort_to_expr_sort_seq_maps_to_seq() {
    let result = sort_to_expr_sort(&Sort::seq(Sort::Int));
    assert_eq!(
        result,
        Some(trust_wp_core::formula::ExprSort::Seq),
        "Sort::Uninterpreted(\"Seq\") should map to ExprSort::Seq"
    );
}

/// `sort_to_expr_sort` maps `Sort::Int` to `None` (backward compat default).
#[test]
#[timeout(30000)]
fn sort_to_expr_sort_int_maps_to_none() {
    let result = sort_to_expr_sort(&Sort::Int);
    assert_eq!(
        result, None,
        "Sort::Int should map to None (default, backward compat)"
    );
}

/// `sort_to_expr_sort` maps `Sort::Uninterpreted("FMap")` to `ExprSort::FMap`.
/// Previously returned `None` (sort info lost through loop encoding); now
/// preserves FMap sort annotation via shared `ay_sort_to_expr_sort`. (#994, #2040)
#[test]
#[timeout(30000)]
fn sort_to_expr_sort_fmap_maps_to_fmap() {
    let result = sort_to_expr_sort(&Sort::Uninterpreted("FMap".to_string()));
    assert_eq!(
        result,
        Some(trust_wp_core::formula::ExprSort::FMap),
        "Sort::Uninterpreted(\"FMap\") should map to ExprSort::FMap"
    );
}

/// `sort_to_expr_sort` maps `Sort::Uninterpreted("Unit")` to `ExprSort::Unit`.
#[test]
#[timeout(30000)]
fn sort_to_expr_sort_unit_maps_to_unit() {
    let result = sort_to_expr_sort(&Sort::Uninterpreted("Unit".to_string()));
    assert_eq!(
        result,
        Some(trust_wp_core::formula::ExprSort::Unit),
        "Sort::Uninterpreted(\"Unit\") should map to ExprSort::Unit"
    );
}

/// `sort_to_expr_sort` maps `Sort::Uninterpreted("Tuple3")` to `ExprSort::Tuple(3)`.
#[test]
#[timeout(30000)]
fn sort_to_expr_sort_tuple_maps_to_tuple() {
    let result = sort_to_expr_sort(&Sort::Uninterpreted("Tuple3".to_string()));
    assert_eq!(
        result,
        Some(trust_wp_core::formula::ExprSort::Tuple(3)),
        "Sort::Uninterpreted(\"Tuple3\") should map to ExprSort::Tuple(3)"
    );
}

/// `sort_to_expr_sort` maps `Sort::Uninterpreted("MyAdt")` to
/// `ExprSort::Datatype(intern("MyAdt"))`.
#[test]
#[timeout(30000)]
fn sort_to_expr_sort_datatype_maps_to_datatype() {
    let result = sort_to_expr_sort(&Sort::Uninterpreted("MyAdt".to_string()));
    let expected = trust_wp_core::formula::ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("MyAdt"),
    );
    assert_eq!(
        result,
        Some(expected),
        "Sort::Uninterpreted(\"MyAdt\") should map to ExprSort::Datatype"
    );
}

/// `sort_to_expr_sort` maps ay-native `Sort::Datatype(DatatypeSort{name: "OptionInt", ..})`
/// to `ExprSort::Datatype(intern("OptionInt"))`. This handles the case where match
/// encoding has already upgraded a variable from Uninterpreted to native Datatype sort.
#[test]
#[timeout(30000)]
fn sort_to_expr_sort_native_datatype_maps_to_datatype() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeSort};
    let dt = DatatypeSort::new(
        "OptionInt",
        vec![
            DatatypeConstructor::unit("None_OptionInt"),
            DatatypeConstructor::new(
                "Some_OptionInt",
                vec![ay_dpll::api::DatatypeField::new("val", Sort::Int)],
            ),
        ],
    );
    let result = sort_to_expr_sort(&Sort::Datatype(dt));
    let expected = trust_wp_core::formula::ExprSort::Datatype(
        trust_wp_core::formula::intern_sort_name("OptionInt"),
    );
    assert_eq!(
        result,
        Some(expected),
        "Sort::Datatype(OptionInt) should map to ExprSort::Datatype(intern(\"OptionInt\"))"
    );
}

/// After c201e2c3 (#2062), TypeParam sorts use bare names (e.g. `"T"`)
/// without the old `__trust_wp_typaram::` prefix. The reverse mapper
/// `ay_sort_to_expr_sort` cannot distinguish bare TypeParam from Datatype,
/// so `Sort::Uninterpreted("T")` maps to `ExprSort::Datatype(intern("T"))`.
/// This lossy roundtrip is acceptable: both produce the same ay
/// Uninterpreted sort, and the ExprSort distinction only matters for
/// expression-level inference annotations. (#2062)
#[test]
#[timeout(30000)]
fn sort_to_expr_sort_type_param_lossy_roundtrip() {
    // Bare TypeParam name — no prefix after c201e2c3.
    let result = sort_to_expr_sort(&Sort::Uninterpreted("T".to_string()));
    let expected =
        trust_wp_core::formula::ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("T"));
    assert_eq!(
        result,
        Some(expected),
        "Sort::Uninterpreted(\"T\") should map to ExprSort::Datatype(T) (lossy TypeParam roundtrip)"
    );
}

// ── Bool variable sort propagation through body effects ──────────────

/// Bool-annotated variable in the body effect preserves its sort through
/// `collect_loop_sort_plan`. When the body effect for a Bool variable is
/// `PureExpr::BinOp(... BinOp::Eq ...)` (a comparison), the sort plan should
/// still resolve the modified variable as `Sort::Bool`.
///
/// Validates: `collect_loop_sort_plan` Phase 2 infers Bool for comparison effects.
#[test]
#[timeout(30000)]
fn bool_sort_propagation_through_comparison_body_effect() {
    let invariants = vec![PureExpr::Var("flag".to_string(), Some(ExprSort::Bool))];
    let modified_vars: Vec<&str> = vec!["flag"];
    // Body effect: flag = (i == 0) — a comparison producing Bool
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "flag".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
    );

    let mut encoder = setup_loop_encoder(&invariants, None, &[], &LoopEncoderConfig::default())
        .expect("encoder setup should succeed for Bool invariant");

    // Mark flag as Bool so collect_loop_sort_plan can propagate
    encoder.mark_bool_var("flag");

    let plan = collect_loop_sort_plan(&mut encoder, &modified_vars, &body_effect);

    assert_eq!(
        plan.sort_for("flag"),
        Some(&Sort::Bool),
        "Bool variable with comparison body effect should resolve to Sort::Bool"
    );
}

// ── Seq variable havoc sort resolution ──────────────

/// When a Seq variable is modified but has no body effect (havoc), the sort
/// plan should resolve it via `resolve_var_sort_or_int`. With a Seq sort hint
/// from the invariant (e.g., `s.len() >= 0`), the variable should not
/// default to Int.
///
/// Validates: `collect_loop_sort_plan` Phase 2 havoc branch uses
/// `resolve_var_sort_or_int` which checks suffix-derived base sorts.
#[test]
#[timeout(30000)]
fn seq_variable_havoc_sort_resolution() {
    // Invariant: s.len() >= 0 — establishes `s` as a Seq-like variable
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            method: "len".to_string(),
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "s".to_string(),
                Some(ExprSort::Seq),
            )))),
            args: vec![],
        }),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let modified_vars: Vec<&str> = vec!["s"];
    // No body effect for s — it is havoced
    let body_effect = HashMap::new();

    let mut encoder = setup_loop_encoder(&invariants, None, &[], &LoopEncoderConfig::default())
        .expect("encoder setup should succeed for Seq invariant");

    let plan = collect_loop_sort_plan(&mut encoder, &modified_vars, &body_effect);

    let s_sort = plan.sort_for("s");

    // With a Seq-annotated variable, the sort plan should resolve to either
    // Seq(Int) or an Uninterpreted("Seq") — not Sort::Int.
    assert_ne!(
        s_sort,
        Some(&Sort::Int),
        "Seq variable under havoc should not default to Sort::Int; got {s_sort:?}"
    );
}

// ── Mixed sort declarations (Int + Bool + Seq in same loop) ──────────────

/// Loop with Int, Bool, and Seq-sorted modified variables. All three should
/// get correct sorts in the sort plan. This exercises the full sort
/// resolution pipeline when multiple sort categories coexist.
///
/// Models: `while cond { i += 1; flag = (i > 5); s.push(i); }`
/// Modified: i (Int), flag (Bool), s (Seq)
#[test]
#[timeout(30000)]
fn mixed_sort_declarations_int_bool_seq() {
    let invariants = vec![
        // i >= 0 (Int)
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        // flag (Bool — bare variable used as formula)
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("flag".to_string(), Some(ExprSort::Bool))),
            BinOp::Or,
            Arc::new(PureExpr::Bool(true)),
        ),
    ];
    let modified_vars: Vec<&str> = vec!["i", "flag"];
    let mut body_effect = HashMap::new();
    // i = i + 1 (Int effect)
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );
    // flag = (i > 5) (Bool effect via comparison)
    body_effect.insert(
        "flag".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(5)),
        ),
    );

    let mut encoder = setup_loop_encoder(&invariants, None, &[], &LoopEncoderConfig::default())
        .expect("encoder setup should succeed for mixed-sort invariants");

    // Pre-mark Bool vars as the production pipeline does
    encoder.mark_bool_var("flag");

    let plan = collect_loop_sort_plan(&mut encoder, &modified_vars, &body_effect);

    assert_eq!(
        plan.sort_for("i"),
        Some(&Sort::Int),
        "i (Int body effect) should resolve to Sort::Int"
    );
    assert_eq!(
        plan.sort_for("flag"),
        Some(&Sort::Bool),
        "flag (Bool body effect, pre-marked) should resolve to Sort::Bool"
    );
}

/// Preservation VC with a Bool deref body effect should not panic from sort
/// mismatch. This verifies end-to-end that Bool sort propagation works
/// through the preservation path when a `*b = !old_b` pattern is encoded.
#[test]
#[timeout(30000)]
fn preservation_with_bool_deref_body_effect() {
    let invariants = vec![PureExpr::Bool(true)];
    let modified_vars: Vec<&str> = vec!["b"];
    let body_effect = HashMap::new();
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("b".to_string(), PureExpr::Bool(true));

    let result = verify_preservation_with_config(
        &invariants,
        None,
        false,
        &modified_vars,
        effects(&body_effect, &deref_body_effect, &HashMap::new()),
        &LoopEncoderConfig::default(),
    );

    let vr = result.expect("preservation with Bool deref should not return encoding error");
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "trivial invariant with Bool deref should verify; got {vr:?}"
    );
}

/// Loop invariants with `Final(View(var)).index_logic(idx)` patterns
/// require Array theory for decidable Seq store/select. Without this
/// detection the encoder uses QF_LIA which lacks Array support. (#1596)
#[test]
#[timeout(30000)]
fn new_loop_encoder_escalates_array_theory_for_seq_index_on_final() {
    // Invariant: (^a)@.index_logic(i) == value
    // This is Final(View(a)).index_logic(i) == value
    let invariant = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            method: "index_logic".to_string(),
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                PureExpr::Var("a".to_string(), None),
            ))))),
            args: vec![PureExpr::Var("i".to_string(), None)],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Var("value".to_string(), None)),
    );

    // This should succeed — Array theory encoder supports Seq indexing.
    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("loop encoder should escalate to Array theory for Seq index on Final (#1596)");
    assert_eq!(
        encoder.logic(),
        ay_dpll::api::Logic::QfAuflia,
        "Seq index on Final requires Array theory (QF_AUFLIA), got {:?}",
        encoder.logic()
    );
}

/// Postcondition borrow resolution must use the correct sort for bool
/// deref body effects. The borrow resolution at postcondition exit asserts
/// `x_final == x_current` for each deref_body_effect variable; if both
/// sides are declared as Sort::Int (hardcoded) rather than Sort::Bool
/// (inferred from the effect), the postcondition VC can produce a sort
/// mismatch or an incorrect result.
///
/// Regression test for algorithm audit finding: postcondition borrow
/// resolution hardcodes Sort::Int at lines 1303-1304 while preservation
/// (build_prime_substitutions) correctly infers Sort::Bool via is_bool_var.
#[test]
#[timeout(30000)]
fn verify_postcondition_borrow_resolution_bool_deref_effect() {
    // Scenario: fn toggle(b: &mut bool) with loop-local borrow resolution.
    // Invariant: true (trivial)
    // Postcondition: ^b == *b
    // deref_body_effect: b -> Bool(true)
    let invariants = vec![PureExpr::Bool(true)];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "b".to_string(),
            Some(ExprSort::Bool),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "b".to_string(),
            None,
        )))),
    )];
    let modified_vars: Vec<&str> = vec!["b"];
    let body_effect = HashMap::new();
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("b".to_string(), PureExpr::Bool(true));
    let double_deref_body_effect = HashMap::new();

    let result = verify_postcondition(
        &invariants,
        None,
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &[], &[]),
        effects(&body_effect, &deref_body_effect, &double_deref_body_effect),
        &LoopEncoderConfig::default(),
    );

    let vr = result.expect("postcondition encoding should succeed for bool deref effect");
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "postcondition with bool deref should verify, got {vr:?}"
    );
}

/// Variant checks must use alias-substituted invariants, not the original
/// `ctx.invariants`. When `pre_loop_assignments` contains an alias
/// `old_n = n` and both are unmodified, the invariant `old_n - i >= 0` is
/// substituted to `n - i >= 0`. Without substitution, `old_n` is an
/// unrelated free variable and the variant nonneg check fails. (#1656)
#[test]
#[timeout(30000)]
fn verify_variant_uses_substituted_invariants_with_alias() {
    // Model: let old_n = n; let mut i = 0; loop { if i >= n { break }; i += 1 }
    // Requires: n >= 0
    // Invariant: i >= 0, old_n - i >= 0
    // Variant: n - i
    // loop_condition: None (body-break, condition not extractable)
    //
    // The alias `old_n = n` triggers substitution since neither old_n
    // nor n is modified. After substitution, `old_n - i >= 0` becomes
    // `n - i >= 0`, which directly proves variant nonneg.
    //
    // loop_condition is None so the solver cannot infer n - i >= 0 from
    // i < n. Without alias substitution, old_n is unrelated to n and
    // the variant nonneg check fails.
    let requires = vec![n_ge(0)];
    let invariants = vec![
        i_ge_zero(),
        // old_n - i >= 0  — only useful after alias substitution maps old_n → n
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("old_n".to_string(), None)),
                BinOp::Sub,
                Arc::new(i_var()),
            )),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
    ];
    let variant = PureExpr::BinOp(Arc::new(n_var()), BinOp::Sub, Arc::new(i_var()));
    let modified_vars = modified_i();
    let body_effect = i_effect(1);
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    // Alias: old_n = n (both unmodified, so eligible for substitution)
    pre_loop_assignments.insert("old_n".to_string(), NamedBindingValue::untyped(n_var()));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &[],
        invariants: &invariants,
        // No extractable loop condition — the guard only appears inside
        // the loop body (body-break pattern). This is critical for the test:
        // if i < n were asserted, it alone proves n - i >= 0.
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("loop verification with alias + variant should encode");

    // The key assertion: variant nonneg must use substituted invariants
    // (old_n - i >= 0 → n - i >= 0) so the solver can prove n - i >= 0.
    // Without substitution, this would be Unknown or Failed.
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "variant nonneg should verify with alias-substituted invariants, got {:?}",
        result.variant_nonneg
    );
}
