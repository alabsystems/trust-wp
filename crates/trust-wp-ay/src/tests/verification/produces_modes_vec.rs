// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use super::*;

// =============================================================================
// IteratorSpec: produces predicate encoding tests (#379)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_produces_reflexivity_axiom() {
    // produces(iter, visited@, iter) — after encoding, the reflexivity axiom
    // `forall i. produces(i, seq_empty, i)` is asserted automatically.
    // If the axiom assertion panics (sort mismatch), encode_pure would fail.
    // Semantic guard: negating produces(iter, seq_empty, iter) must be UNSAT.
    let mut encoder = AYEncoder::new_with_quantifiers();

    let iter_var = var("iter");
    // Use a View expression: sort hint system marks it as Seq
    let visited = view(var("visited"));
    let produces_call = method_call(
        iter_var.clone(),
        "produces",
        vec![visited, iter_var.clone()],
    );

    encoder.register_sort_hints(std::slice::from_ref(&produces_call));
    let result = encoder.encode_pure(&produces_call);
    assert!(
        result.is_ok(),
        "produces with Seq-sorted visited should encode and axioms should be asserted: {result:?}"
    );

    let reflexive = method_call(
        iter_var.clone(),
        "produces",
        vec![logic_fn_call("seq_empty", vec![]), iter_var],
    );
    let reflexive_term = encoder
        .encode_pure(&reflexive)
        .expect("produces(iter, seq_empty, iter) should encode");
    let not_reflexive = encoder.solver_mut().not(reflexive_term);
    encoder.assert_term(not_reflexive);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Reflexivity axiom must force produces(iter, seq_empty, iter) to hold"
    );
}

#[test]
#[timeout(30000)]
fn test_produces_with_seq_view_argument() {
    // self.produces(visited, o) where `visited` is View(Var("produced"))
    // The sort hint system should mark visited as Seq.
    // Semantic guard: reflexivity must still hold after View-based registration.
    let mut encoder = AYEncoder::new_with_quantifiers();

    let self_var = deref(var("self"));
    let visited = view(var("produced"));
    let o_var = final_expr(var("self"));
    let produces = method_call(self_var, "produces", vec![visited, o_var]);

    encoder.register_sort_hints(std::slice::from_ref(&produces));
    let result = encoder.encode_pure(&produces);
    assert!(
        result.is_ok(),
        "produces with View arg should encode without sort mismatch: {result:?}"
    );

    let reflexive = method_call(
        var("a"),
        "produces",
        vec![logic_fn_call("seq_empty", vec![]), var("a")],
    );
    let reflexive_term = encoder
        .encode_pure(&reflexive)
        .expect("produces(a, seq_empty, a) should encode");
    let not_reflexive = encoder.solver_mut().not(reflexive_term);
    encoder.assert_term(not_reflexive);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "produces reflexivity must hold when registered via View argument"
    );
}

fn singleton_produces_expr() -> PureExpr {
    method_call(
        deref(var("self")),
        "produces",
        vec![
            logic_fn_call("seq", vec![var("v")]),
            final_expr(var("self")),
        ],
    )
}

fn singleton_produces_sat(negate: bool) -> SolveResult {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(Duration::from_millis(500)));
    let produces = singleton_produces_expr();
    encoder.register_sort_hints(std::slice::from_ref(&produces));
    let term = encoder
        .encode_pure(&produces)
        .expect("produces with seq![v] should encode");
    if negate {
        let not_term = encoder.solver.not(term);
        encoder.assert_term(not_term);
    } else {
        encoder.assert_term(term);
    }
    encoder.check_sat()
}

#[test]
#[timeout(30000)]
fn test_produces_with_singleton_seq() {
    // (*self).produces(seq![v], ^self) — the Iterator::next postcondition pattern.
    // Non-vacuousness: check BOTH produces and NOT(produces) are satisfiable,
    // proving it encodes as a genuine Bool predicate. (#888)

    let produces_result = singleton_produces_sat(false);
    // ay's soundness guard (ay#2865) may return Unknown for formulas with seq
    // axiom quantifiers. Not-Unsat is the key property.
    assert!(
        !matches!(produces_result, SolveResult::Unsat(_)),
        "produces(self, seq![v], ^self) should not be Unsat, got {produces_result:?}"
    );

    // Negative: NOT(produces(...)) is also not Unsat — proves the predicate
    // is a genuine Bool constraint, not a tautology or sort artifact.
    let neg_produces_result = singleton_produces_sat(true);
    assert!(
        !matches!(neg_produces_result, SolveResult::Unsat(_)),
        "NOT(produces(self, seq![v], ^self)) should not be Unsat, got {neg_produces_result:?}"
    );

    // Consistency guard: asserting both produces and NOT(produces) must be UNSAT.
    {
        let mut encoder = AYEncoder::new_with_quantifiers();
        encoder.set_timeout(Some(Duration::from_millis(500)));
        let produces = singleton_produces_expr();

        encoder.register_sort_hints(std::slice::from_ref(&produces));
        let term = encoder
            .encode_pure(&produces)
            .expect("produces with seq![v] should encode");
        encoder.assert_term(term);

        let term_again = encoder
            .encode_pure(&produces)
            .expect("re-encoding produces with seq![v] should still succeed");
        let neg = encoder.solver.not(term_again);
        encoder.assert_term(neg);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "produces(self, seq![v], ^self) and its negation cannot both hold: got {result:?}"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_produces_wrong_arity_rejected() {
    // produces with wrong number of args should error
    let mut encoder = AYEncoder::new();

    // Too few args (1 instead of 2)
    let expr = method_call(var("iter"), "produces", vec![var("seq")]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "produces with 1 arg should be rejected, got Ok({:?})",
        result.as_ref().ok()
    );

    // Too many args (3 instead of 2)
    let expr2 = method_call(var("iter"), "produces", vec![var("a"), var("b"), var("c")]);

    let mut encoder2 = AYEncoder::new();
    let result2 = encoder2.encode_pure(&expr2);
    assert!(
        result2.is_err(),
        "produces with 3 args should be rejected, got Ok({:?})",
        result2.as_ref().ok()
    );
}

/// mode_overrides length mismatch is silently dropped (#2316, #2700).
/// The overrides are computed from the full logic_fn_defs set, but logic_fns
/// may be a filtered subset. Rather than returning an encoding error, the
/// overrides are dropped so filter_logic_functions_for_goal falls back to
/// default mode scoping.
#[test]
#[timeout(30000)]
fn test_verify_function_with_modes_mode_override_length_mismatch_drops_overrides_silently() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let logic_fns = vec![
        LogicFnDef::new("f".to_string(), "test::f".to_string(), vec![], int(1))
            .with_mode(LogicMode::Open),
        LogicFnDef::new("g".to_string(), "test::g".to_string(), vec![], int(2))
            .with_mode(LogicMode::Open),
    ];
    let mode_overrides = [LogicMode::Open];

    let body = logic_fn_call("g", vec![]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[])
            .return_expr(Some(&body))
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides)),
    );
    // Should NOT error — overrides are dropped, verification proceeds
    assert!(
        result.is_ok(),
        "mode_overrides mismatch should be silently dropped, not error: {result:?}"
    );
}

/// mode_overrides length mismatch is silently dropped for mut_borrow path
/// (#2316, #2700).
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_with_modes_mode_override_length_mismatch_drops_overrides_silently() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let logic_fns = vec![
        LogicFnDef::new("f".to_string(), "test::f".to_string(), vec![], int(1))
            .with_mode(LogicMode::Open),
        LogicFnDef::new("g".to_string(), "test::g".to_string(), vec![], int(2))
            .with_mode(LogicMode::Open),
    ];
    let mode_overrides = [LogicMode::Open];
    let final_values = HashMap::new();

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[], &final_values)
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides)),
    );
    // Should NOT error — overrides are dropped, verification proceeds
    assert!(
        result.is_ok(),
        "mode_overrides mismatch should be silently dropped, not error: {result:?}"
    );
}

/// Raw ay test for Vec element invariant propagation (#869).
///
/// Isolates the SMT-level behavior: given a quantified element invariant and
/// an invariant defining axiom, can the solver derive element field properties?
#[test]
#[timeout(30000)]
fn test_ay_vec_element_invariant_raw() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::Auflia).unwrap();
    let seq_sort = Sort::seq(Sort::Int);

    // Declare UFs
    let seq_len = solver.declare_fun("seq_len", std::slice::from_ref(&seq_sort), Sort::Int);
    let seq_index =
        solver.declare_fun("seq_index_logic", &[seq_sort.clone(), Sort::Int], Sort::Int);
    let get_0 = solver.declare_fun("get_0", &[Sort::Int], Sort::Int);
    let get_1 = solver.declare_fun("get_1", &[Sort::Int], Sort::Int);

    // Concrete variable: x_view : Seq
    let x_view = solver.declare_const("x_view", seq_sort);

    // Precondition: len(x_view) > 0
    let len = solver.apply(&seq_len, &[x_view]);
    let zero = solver.int_const(0);
    let len_gt_0 = solver.gt(len, zero);
    solver.assert_term(len_gt_0);

    // Inlined element invariant bridge:
    // forall i. 0 <= i < len(x_view) =>
    //     get_0(index(x_view, i)) + get_1(index(x_view, i)) == 10
    // (body inlined directly — no intermediate inv_SumTo10 UF call)
    let i = solver.fresh_var("elem_i", Sort::Int);
    let i_ge_0 = solver.ge(i, zero);
    let i_lt_len = solver.lt(i, len);
    let in_bounds = solver.and(i_ge_0, i_lt_len);
    let elem = solver.apply(&seq_index, &[x_view, i]);
    let g0_i = solver.apply(&get_0, &[elem]);
    let g1_i = solver.apply(&get_1, &[elem]);
    let sum_i = solver.add(g0_i, g1_i);
    let ten = solver.int_const(10);
    let body_eq = solver.eq(sum_i, ten);
    let bridge_body = solver.implies(in_bounds, body_eq);
    // Trigger on seq_index(x_view, i) so ay instantiates when index(x_view, 0) appears
    let bridge = solver.forall_with_triggers(&[i], bridge_body, &[&[elem]]);
    solver.assert_term(bridge);

    // Negation of postcondition: NOT(get_0(index(x_view, 0)) + get_1(index(x_view, 0)) == 10)
    let elem_0 = solver.apply(&seq_index, &[x_view, zero]);
    let g0_elem = solver.apply(&get_0, &[elem_0]);
    let g1_elem = solver.apply(&get_1, &[elem_0]);
    let sum_elem = solver.add(g0_elem, g1_elem);
    let ten2 = solver.int_const(10);
    let post = solver.eq(sum_elem, ten2);
    let neg_post = solver.not(post);
    solver.assert_term(neg_post);

    let result = solver.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Vec element invariant should make NOT(x[0].a + x[0].b == 10) unsatisfiable: {result:?}"
    );
}

/// Vec element invariant propagation: `x[0].a + x[0].b == 10` from Vec<SumTo10> (#869).
///
/// Models the Creusot `vec_inv.rs` test: given `x: Vec<&mut SumTo10>` with
/// `SumTo10` invariant `a + b == 10`, prove that `x[0].a + x[0].b == 10`.
///
/// This tests the container element invariant bridge: `inv_Vec(x)` =>
/// `forall i. 0 <= i < len(x@) => inv_SumTo10(x@.index_logic(i))`.
#[test]
#[timeout(60000)]
fn test_verify_vec_element_invariant_propagation() {
    let sumto10_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");
    let vec_method = trust_wp_core::logic::type_invariant_method_name("Vec");

    // Element invariant: SumTo10(self) ⟺ get_0(self) + get_1(self) == 10
    let sumto10_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: eq(
            add(get_field(0, var("self")), get_field(1, var("self"))),
            int(10),
        ),
        is_newtype: false,
        element_invariant_method: None,
    };

    // Container invariant for Vec: trivially true body, element bridge to SumTo10.
    // The body is `true` because the semantic content is in the element bridge axiom
    // which asserts: forall i. 0 <= i < len(x_view) => inv_SumTo10(index(x_view, i))
    let vec_def = trust_wp_core::type_invariant_def! {
        type_name: "Vec".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: bool_expr(true),
        is_newtype: false,
        element_invariant_method: Some(sumto10_method.clone()),
    };

    // requires: x@.len() > 0 AND x.__trust_wp_invariant_Vec()
    let req_len = gt(method_call(view(var("x")), "len", vec![]), int(0));
    let req_inv = method_call(var("x"), &vec_method, vec![]);

    // ensures: x@.index_logic(0).get_0() + x@.index_logic(0).get_1() == 10
    // This is the proof_assert from vec_inv.rs
    let elem_0 = method_call(view(var("x")), "index_logic", vec![int(0)]);
    let ens = eq(
        add(get_field(0, elem_0.clone()), get_field(1, elem_0)),
        int(10),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_len, req_inv], &[ens])
            .timeout(Some(Duration::from_secs(1)))
            .type_invariants(Some(&[sumto10_def, vec_def])),
    )
    .unwrap();
    let VerificationResult::Verified(Some(summary)) = result else {
        panic!("Vec<SumTo10> element invariant propagation requires strict proof authority");
    };
    assert!(
        summary.is_fully_verified(),
        "Vec<SumTo10> element invariant proof must be independently checked: {summary:?}"
    );
}

/// Negative test: Vec element invariant does not hold for wrong field sum (#869).
///
/// Same setup as the positive test but checks `x[0].a + x[0].b == 20`.
/// Should fail because the element invariant says the sum is 10, not 20.
#[test]
#[timeout(60000)]
fn test_verify_vec_element_invariant_wrong_sum_fails() {
    let sumto10_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");
    let vec_method = trust_wp_core::logic::type_invariant_method_name("Vec");

    let sumto10_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: eq(
            add(get_field(0, var("self")), get_field(1, var("self"))),
            int(10),
        ),
        is_newtype: false,
        element_invariant_method: None,
    };

    let vec_def = trust_wp_core::type_invariant_def! {
        type_name: "Vec".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: bool_expr(true),
        is_newtype: false,
        element_invariant_method: Some(sumto10_method.clone()),
    };

    let req_len = gt(method_call(view(var("x")), "len", vec![]), int(0));
    let req_inv = method_call(var("x"), &vec_method, vec![]);

    // Wrong sum: 20 instead of 10
    let elem_0 = method_call(view(var("x")), "index_logic", vec![int(0)]);
    let ens = eq(
        add(get_field(0, elem_0.clone()), get_field(1, elem_0)),
        int(20),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_len, req_inv], &[ens])
            .timeout(Some(Duration::from_secs(1)))
            .type_invariants(Some(&[sumto10_def, vec_def])),
    )
    .unwrap();
    assert!(
        matches!(
            result,
            VerificationResult::Failed(_)
                | VerificationResult::Unknown(crate::verify::UnknownReason::Timeout)
        ),
        "Vec<SumTo10> wrong sum must remain a non-proof; the paired sum==10 test above verifies the positive invariant lane: got {result:?}"
    );
}

/// Vec element invariant with symbolic index — no concrete index ground term (#887).
///
/// Verifies that the triggered forall in `assert_container_element_invariant_body`
/// instantiates correctly when the postcondition uses a symbolic index `k` rather
/// than a literal `0`. The trigger `seq_index(x_view, i)` must match against
/// `seq_index(x_view, k)` for the invariant to fire.
///
/// Pre: len(x@) > 0 AND inv_Vec(x) AND 0 <= k < len(x@)
/// Post: x@.index_logic(k).get_0() + x@.index_logic(k).get_1() == 10
#[test]
#[timeout(60000)]
fn test_verify_vec_element_invariant_symbolic_index() {
    let sumto10_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");
    let vec_method = trust_wp_core::logic::type_invariant_method_name("Vec");

    let sumto10_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: eq(
            add(get_field(0, var("self")), get_field(1, var("self"))),
            int(10),
        ),
        is_newtype: false,
        element_invariant_method: None,
    };

    let vec_def = trust_wp_core::type_invariant_def! {
        type_name: "Vec".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: bool_expr(true),
        is_newtype: false,
        element_invariant_method: Some(sumto10_method.clone()),
    };

    // Preconditions: len > 0, invariant holds, and symbolic k is in bounds
    let req_len = gt(method_call(view(var("x")), "len", vec![]), int(0));
    let req_inv = method_call(var("x"), &vec_method, vec![]);
    let req_k_ge_0 = ge(var("k"), int(0));
    let req_k_lt_len = lt(var("k"), method_call(view(var("x")), "len", vec![]));

    // Postcondition uses symbolic index k — no concrete index(view, 0) ground term
    let elem_k = method_call(view(var("x")), "index_logic", vec![var("k")]);
    let ens = eq(
        add(get_field(0, elem_k.clone()), get_field(1, elem_k)),
        int(10),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_len, req_inv, req_k_ge_0, req_k_lt_len], &[ens])
            .type_invariants(Some(&[sumto10_def, vec_def])),
    )
    .unwrap();
    let VerificationResult::Verified(Some(summary)) = result else {
        panic!("symbolic Vec element invariant requires strict proof authority");
    };
    assert!(
        summary.is_fully_verified(),
        "symbolic Vec invariant proof must be independently checked: {summary:?}"
    );
}
