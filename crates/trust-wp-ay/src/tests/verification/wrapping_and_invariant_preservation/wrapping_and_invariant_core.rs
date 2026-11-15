// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// Wrapping arithmetic modular spec tests (#692)
//
// Validates that wrapping arithmetic specs using SMT `mod` produce correct
// verification results. The modular formula:
//   result == (op - MIN) % RANGE + MIN
// where RANGE = MAX - MIN + 1, correctly encodes wrapping for both signed
// and unsigned types.
//
// These tests exercise the encoding at the SMT level using verify_function_with_modes
// with concrete type_constants, bypassing the driver's spec string parsing.
// ============================================================================

/// Wrapping add (u8): no overflow case.
///
/// 100u8 + 50u8 = 150u8 (no wrapping needed).
/// Postcondition: result == (self + rhs - MIN) % RANGE + MIN
/// With MIN=0, MAX=255, RANGE=256: result == (100 + 50) % 256 = 150.
#[test]
#[timeout(30000)]
fn test_verify_wrapping_add_no_overflow_u8() {
    let mut tc = HashMap::new();
    tc.insert("Self::MIN".to_string(), PureExpr::Int(0));
    tc.insert("Self::MAX".to_string(), PureExpr::Int(255));

    // requires: self == 100 && rhs == 50
    let req_self = eq(var("self"), int(100));
    let req_rhs = eq(var("rhs"), int(50));

    // ensures: result == (self + rhs - Self::MIN) % (Self::MAX - Self::MIN + 1) + Self::MIN
    // With Self::MIN=0, Self::MAX=255, this becomes: result == (self + rhs) % 256
    let range = add(sub(var("Self::MAX"), var("Self::MIN")), int(1));
    let modular_expr = add(
        mod_expr(sub(add(var("self"), var("rhs")), var("Self::MIN")), range),
        var("Self::MIN"),
    );
    let ens = eq(var("result"), modular_expr);

    // body: result = 150 (the correct non-wrapping answer)
    let body = int(150);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs], &[ens])
            .return_expr(Some(&body))
            .type_constants(Some(&tc)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "u8 wrapping_add(100, 50) = 150 should verify: {result:?}"
    );
}

/// Wrapping add (u8): overflow case.
///
/// 200u8 + 100u8 wraps to 44 (300 % 256 = 44).
/// Tests that the modular formula correctly handles overflow.
#[test]
#[timeout(30000)]
fn test_verify_wrapping_add_overflow_u8() {
    let mut tc = HashMap::new();
    tc.insert("Self::MIN".to_string(), PureExpr::Int(0));
    tc.insert("Self::MAX".to_string(), PureExpr::Int(255));

    let req_self = eq(var("self"), int(200));
    let req_rhs = eq(var("rhs"), int(100));

    let range = add(sub(var("Self::MAX"), var("Self::MIN")), int(1));
    let modular_expr = add(
        mod_expr(sub(add(var("self"), var("rhs")), var("Self::MIN")), range),
        var("Self::MIN"),
    );
    let ens = eq(var("result"), modular_expr);

    // body: result = 44 (300 mod 256)
    let body = int(44);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs], &[ens])
            .return_expr(Some(&body))
            .type_constants(Some(&tc)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "u8 wrapping_add(200, 100) = 44 should verify: {result:?}"
    );
}

/// Wrapping add (u8): wrong result fails.
///
/// Verifying wrapping_add(200, 100) with body = 45 (wrong — should be 44)
/// should produce a counterexample, confirming the spec is not vacuously true.
#[test]
#[timeout(30000)]
fn test_verify_wrapping_add_wrong_result_fails_u8() {
    let mut tc = HashMap::new();
    tc.insert("Self::MIN".to_string(), PureExpr::Int(0));
    tc.insert("Self::MAX".to_string(), PureExpr::Int(255));

    let req_self = eq(var("self"), int(200));
    let req_rhs = eq(var("rhs"), int(100));

    let range = add(sub(var("Self::MAX"), var("Self::MIN")), int(1));
    let modular_expr = add(
        mod_expr(sub(add(var("self"), var("rhs")), var("Self::MIN")), range),
        var("Self::MIN"),
    );
    let ens = eq(var("result"), modular_expr);

    // body: result = 45 (WRONG — correct answer is 44)
    let body = int(45);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs], &[ens])
            .return_expr(Some(&body))
            .type_constants(Some(&tc)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "u8 wrapping_add(200, 100) = 45 (wrong) should fail: {result:?}"
    );
}

/// Wrapping add (i8): signed overflow case.
///
/// 100i8 + 100i8 wraps to -56 ((100 + 100 - (-128)) % 256 + (-128) = 328 % 256 - 128 = 72 - 128 = -56).
/// Validates that the modular formula handles signed type bounds correctly.
#[test]
#[timeout(30000)]
fn test_verify_wrapping_add_signed_overflow_i8() {
    let mut tc = HashMap::new();
    tc.insert("Self::MIN".to_string(), PureExpr::Int(-128));
    tc.insert("Self::MAX".to_string(), PureExpr::Int(127));

    let req_self = eq(var("self"), int(100));
    let req_rhs = eq(var("rhs"), int(100));

    let range = add(sub(var("Self::MAX"), var("Self::MIN")), int(1));
    let modular_expr = add(
        mod_expr(sub(add(var("self"), var("rhs")), var("Self::MIN")), range),
        var("Self::MIN"),
    );
    let ens = eq(var("result"), modular_expr);

    // body: result = -56 (correct wrapped i8 result)
    let body = neg(int(56));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs], &[ens])
            .return_expr(Some(&body))
            .type_constants(Some(&tc)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "i8 wrapping_add(100, 100) = -56 should verify: {result:?}"
    );
}

/// Wrapping sub (u8): underflow case.
///
/// 0u8 - 1u8 wraps to 255 ((-1 - 0) mod 256 + 0 = 255).
/// Validates wrapping subtraction for unsigned underflow.
#[test]
#[timeout(30000)]
fn test_verify_wrapping_sub_underflow_u8() {
    let mut tc = HashMap::new();
    tc.insert("Self::MIN".to_string(), PureExpr::Int(0));
    tc.insert("Self::MAX".to_string(), PureExpr::Int(255));

    let req_self = eq(var("self"), int(0));
    let req_rhs = eq(var("rhs"), int(1));

    let range = add(sub(var("Self::MAX"), var("Self::MIN")), int(1));
    // result == (self - rhs - Self::MIN) % RANGE + Self::MIN
    let modular_expr = add(
        mod_expr(sub(sub(var("self"), var("rhs")), var("Self::MIN")), range),
        var("Self::MIN"),
    );
    let ens = eq(var("result"), modular_expr);

    // body: result = 255 (correct wrapped u8 result)
    let body = int(255);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs], &[ens])
            .return_expr(Some(&body))
            .type_constants(Some(&tc)),
    );
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        result
            .as_ref()
            .is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "u8 wrapping_sub(0, 1) = 255 should verify: {result:?}"
    );
}

/// Logic function postcondition with type constants (#915).
///
/// Models the driver's logic function verification path: given a logic
/// function body and an `#[ensures]` that references `Self::MIN` / `Self::MAX`,
/// verify that the postcondition holds when type_constants are provided.
///
/// Without type_constants, `Self::MIN` and `Self::MAX` are uninterpreted
/// variables and the postcondition cannot be verified (spurious failure).
#[test]
#[timeout(30000)]
fn test_verify_logic_fn_postcondition_with_type_constants() {
    // Logic function: bounded_identity(x: i32) -> i32 { x }
    // ensures: result >= Self::MIN && result <= Self::MAX
    let mut tc = HashMap::new();
    tc.insert("Self::MIN".to_string(), PureExpr::Int(i64::from(i32::MIN)));
    tc.insert("Self::MAX".to_string(), PureExpr::Int(i64::from(i32::MAX)));

    let req = and(
        ge(var("x"), var("Self::MIN")),
        le(var("x"), var("Self::MAX")),
    );
    let ens = and(
        ge(var("result"), var("Self::MIN")),
        le(var("result"), var("Self::MAX")),
    );
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_constants(Some(&tc)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "logic fn postcondition with type_constants should verify: {result:?}"
    );
}

/// Without type_constants, wrapping arithmetic postconditions fail because
/// `Self::MIN`/`Self::MAX` are uninterpreted and the body's concrete result
/// cannot be matched to the abstract modular formula. (#915)
#[test]
#[timeout(30000)]
fn test_verify_logic_fn_wrapping_postcondition_without_type_constants_fails() {
    // Models: fn wrapping_add(a: u8, b: u8) -> u8 { body = 44 }
    // ensures: result == (a + b - Self::MIN) % (Self::MAX - Self::MIN + 1) + Self::MIN
    // requires: a == 200 && b == 100
    //
    // With type_constants (Self::MIN=0, Self::MAX=255): formula = (300) % 256 = 44 ✓
    // Without type_constants: Self::MIN/MAX are unconstrained — solver cannot
    // determine that the formula equals 44.
    let req = and(eq(var("a"), int(200)), eq(var("b"), int(100)));
    let range = add(sub(var("Self::MAX"), var("Self::MIN")), int(1));
    let modular_expr = add(
        mod_expr(sub(add(var("a"), var("b")), var("Self::MIN")), range),
        var("Self::MIN"),
    );
    let ens = eq(var("result"), modular_expr);
    let body = int(44);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    );
    // Without type constants the modular range is unconstrained, including the
    // divisor-safety obligation for `%`. The verifier must reject the VC rather
    // than treating incompleteness as success.
    match result {
        Ok(VerificationResult::Failed(counterexample)) => {
            assert!(
                counterexample
                    .values
                    .iter()
                    .any(|value| value.name == "Self::MIN"),
                "failure should expose unresolved Self::MIN in the witness: {counterexample:?}"
            );
            assert!(
                counterexample
                    .values
                    .iter()
                    .any(|value| value.name == "Self::MAX"),
                "failure should expose unresolved Self::MAX in the witness: {counterexample:?}"
            );
        }
        other => panic!(
            "wrapping postcondition without type_constants must fail with a counterexample: {other:?}"
        ),
    }
}

/// Type invariant preservation across binary operations (#359).
///
/// Models NonZeroU32::add(self, rhs) -> Self:
/// - Invariant preconditions: self > 0 ∧ rhs > 0
/// - Body: result = self + rhs
/// - Postcondition: result > 0
#[test]
#[timeout(30000)]
fn test_verify_invariant_preservation_add_pattern() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();

    let invariant_body = gt(var("self"), int(0));
    encoder
        .register_type_invariant("NonZero", "self", Sort::Int, &invariant_body)
        .expect("invariant registration should succeed");

    let self_var = encoder
        .get_or_declare_var("self_val", Sort::Int)
        .expect("declare self_val");
    let rhs_var = encoder
        .get_or_declare_var("rhs_val", Sort::Int)
        .expect("declare rhs_val");
    let result = encoder
        .get_or_declare_var("result", Sort::Int)
        .expect("declare result");

    let zero = encoder.solver.int_const(0);
    let self_gt_0 = encoder.solver.gt(self_var, zero);
    encoder.solver.assert_term(self_gt_0);
    let zero2 = encoder.solver.int_const(0);
    let rhs_gt_0 = encoder.solver.gt(rhs_var, zero2);
    encoder.solver.assert_term(rhs_gt_0);

    let sum = encoder.solver.add(self_var, rhs_var);
    let result_eq_sum = encoder.solver.eq(result, sum);
    encoder.solver.assert_term(result_eq_sum);

    let method_name = trust_wp_core::logic::type_invariant_method_name("NonZero");
    let inv_result = encoder
        .encode_pure(&method_call(var("result"), &method_name, vec![]))
        .expect("invariant encoding should succeed");
    let not_inv = encoder.solver.not(inv_result);
    encoder.solver.assert_term(not_inv);

    let solve_result = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(solve_result, ay_dpll::api::SolveResult::Unsat(_)),
        "invariant preservation for add should prove: {solve_result:?}"
    );
}

/// Type invariant preservation via verify_function pipeline (#359).
#[test]
#[timeout(30000)]
fn test_verify_invariant_preservation_add_via_pipeline() {
    let invariant = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        body: gt(var("self"), int(0)),
        param_sort: None,
        is_newtype: true,
        element_invariant_method: None,
    };

    let method_name = trust_wp_core::logic::type_invariant_method_name("NonZero");
    let self_inv = method_call(var("self_val"), &method_name, vec![]);
    let rhs_inv = method_call(var("rhs_val"), &method_name, vec![]);
    let result_inv = method_call(var("result"), &method_name, vec![]);
    let body = add(var("self_val"), var("rhs_val"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[self_inv, rhs_inv], &[result_inv])
            .return_expr(Some(&body))
            .type_invariants(Some(&[invariant])),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "invariant preservation add via pipeline should verify: {result:?}"
    );
}

/// Type invariant preservation with user precondition and view (#359).
///
/// Models NonZeroU32::add more faithfully:
/// - User pre: self@ + rhs@ <= MAX (with view expressions)
/// - Invariant pre: self.invariant() AND rhs.invariant()
/// - Body: result = self + rhs
/// - Post: result.invariant()
///
/// Tests whether adding view expressions causes solver incompleteness.
#[test]
#[timeout(30000)]
fn test_verify_invariant_preservation_add_with_user_precondition() {
    let invariant = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        body: gt(var("self"), int(0)),
        param_sort: None,
        is_newtype: true,
        element_invariant_method: None,
    };

    let method_name = trust_wp_core::logic::type_invariant_method_name("NonZero");

    // Invariant preconditions
    let self_inv = method_call(var("self_val"), &method_name, vec![]);
    let rhs_inv = method_call(var("rhs_val"), &method_name, vec![]);

    // User precondition: self@ + rhs@ <= MAX
    // After newtype simplification, self.0@ becomes self@ (view of self)
    let user_pre = le(
        add(view(var("self_val")), view(var("rhs_val"))),
        int(u32::MAX as i64),
    );

    let result_inv = method_call(var("result"), &method_name, vec![]);
    let body = add(var("self_val"), var("rhs_val"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[self_inv, rhs_inv, user_pre], &[result_inv])
            .return_expr(Some(&body))
            .type_invariants(Some(&[invariant])),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "invariant preservation add with user precondition should verify: {result:?}"
    );
}

/// Multi-field struct invariant preservation (Creusot parity: borrows.rs SumTo10) (#359).
///
/// Models SumTo10 { a: i32, b: i32 } with invariant a + b == 10.
/// The function `foo(&mut self)` does inc(&mut self.a); dec(&mut self.b).
/// Result: (self_a + 1) + (self_b - 1) == 10 iff self_a + self_b == 10.
#[test]
#[timeout(30000)]
fn test_verify_multi_field_invariant_preservation() {
    use ay_dpll::api::{Logic, Solver, Sort};

    // Invariant for SumTo10: self_a + self_b == 10
    // Proof obligation: given a+b=10, prove (a+1)+(b-1)==10.
    //
    // Inline the body into the postcondition to avoid intermediate result
    // variables; the inlined form is a valid encoding strategy independent of
    // whether ay solves the 4-variable equality chain directly (ay#2767).
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    let a = solver.declare_const("a", Sort::Int);
    let b = solver.declare_const("b", Sort::Int);

    // Pre: a + b == 10
    let sum = solver.add(a, b);
    let ten = solver.int_const(10);
    let pre = solver.eq(sum, ten);
    solver.assert_term(pre);

    // Post (inlined body): NOT((a+1) + (b-1) == 10) should be UNSAT
    let one = solver.int_const(1);
    let a1 = solver.add(a, one);
    let one2 = solver.int_const(1);
    let b1 = solver.sub(b, one2);
    let result_sum = solver.add(a1, b1);
    let ten2 = solver.int_const(10);
    let post = solver.eq(result_sum, ten2);
    let neg_post = solver.not(post);
    solver.assert_term(neg_post);

    let solve_result = solver.check_sat().into_inner();
    assert!(
        matches!(solve_result, ay_dpll::api::SolveResult::Unsat(_)),
        "SumTo10 foo() should preserve a+b==10: {solve_result:?}"
    );
}

/// Multi-field invariant violation: incrementing one field without compensating (#359).
///
/// Models a broken version of SumTo10::foo that only increments self.a
/// without decrementing self.b. The invariant should NOT be preserved.
#[test]
#[timeout(30000)]
fn test_verify_multi_field_invariant_violation() {
    use ay_dpll::api::{Logic, Solver, Sort};

    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    let self_a = solver.declare_const("self_a", Sort::Int);
    let self_b = solver.declare_const("self_b", Sort::Int);

    // Pre: self_a + self_b == 10
    let sum_ab = solver.add(self_a, self_b);
    let ten = solver.int_const(10);
    let inv_pre = solver.eq(sum_ab, ten);
    solver.assert_term(inv_pre);

    // Broken body: result_a = self_a + 1, result_b = self_b (no dec)
    let result_a = solver.declare_const("result_a", Sort::Int);
    let result_b = solver.declare_const("result_b", Sort::Int);
    let one = solver.int_const(1);
    let a_plus_1 = solver.add(self_a, one);
    let ra_eq = solver.eq(result_a, a_plus_1);
    solver.assert_term(ra_eq);
    let rb_eq = solver.eq(result_b, self_b);
    solver.assert_term(rb_eq);

    // Post: result_a + result_b == 10 — should be satisfiable to NEGATE
    // (i.e., NOT(invariant) is SAT because the broken body breaks it)
    let result_sum = solver.add(result_a, result_b);
    let ten2 = solver.int_const(10);
    let inv_post = solver.eq(result_sum, ten2);
    let not_inv = solver.not(inv_post);
    solver.assert_term(not_inv);

    let solve_result = solver.check_sat().into_inner();
    assert!(
        matches!(solve_result, ay_dpll::api::SolveResult::Sat),
        "broken SumTo10 foo() should fail to preserve a+b==10: {solve_result:?}"
    );
}

/// Raw ay congruence closure test: result = tuple2(a,b) → get_0(result) = a.
///
/// Isolates whether ay's E-matching + congruence closure can derive
/// `get_0(result) = a` from `result = tuple2(a, b)` with the tuple axiom
/// `forall x0 x1. get_0(tuple2(x0, x1)) = x0`.
///
/// If this test fails, the SumTo10 pipeline test cannot work with the
/// current tuple encoding — an alternative approach would be needed.
#[test]
#[timeout(5000)]
fn test_ay_tuple_congruence_closure_raw() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::Auflia).unwrap();

    // Declare UFs: tuple2: (Int, Int) -> Int, get_0: Int -> Int, get_1: Int -> Int
    let tuple2_decl = solver.declare_fun("tuple2", &[Sort::Int, Sort::Int], Sort::Int);
    let get_0_decl = solver.declare_fun("get_0", &[Sort::Int], Sort::Int);
    let get_1_decl = solver.declare_fun("get_1", &[Sort::Int], Sort::Int);

    // Bound variables for axiom
    let x0 = solver.fresh_var("x0", Sort::Int);
    let x1 = solver.fresh_var("x1", Sort::Int);

    // Build constructor application: tuple2(x0, x1)
    let ctor = solver.apply(&tuple2_decl, &[x0, x1]);

    // Axiom 0: forall x0 x1. get_0(tuple2(x0, x1)) = x0  [trigger: tuple2(x0,x1)]
    let get_0_ctor = solver.apply(&get_0_decl, &[ctor]);
    let axiom0_body = solver.eq(get_0_ctor, x0);
    let axiom0 = solver.forall_with_triggers(&[x0, x1], axiom0_body, &[&[ctor]]);
    solver.assert_term(axiom0);

    // Axiom 1: forall x0 x1. get_1(tuple2(x0, x1)) = x1  [trigger: tuple2(x0,x1)]
    let get_1_ctor = solver.apply(&get_1_decl, &[ctor]);
    let axiom1_body = solver.eq(get_1_ctor, x1);
    let axiom1 = solver.forall_with_triggers(&[x0, x1], axiom1_body, &[&[ctor]]);
    solver.assert_term(axiom1);

    // Ground constants
    let a = solver.declare_const("a", Sort::Int);
    let b = solver.declare_const("b", Sort::Int);
    let result = solver.declare_const("result", Sort::Int);

    // Assert: result = tuple2(a, b)
    let tuple_ab = solver.apply(&tuple2_decl, &[a, b]);
    let eq_result = solver.eq(result, tuple_ab);
    solver.assert_term(eq_result);

    // Negate: get_0(result) = a (we want UNSAT)
    let get_0_result = solver.apply(&get_0_decl, &[result]);
    let eq_get0 = solver.eq(get_0_result, a);
    let neg = solver.not(eq_get0);
    solver.assert_term(neg);

    // Expected UNSAT:
    // 1. tuple2(a, b) in E-graph → triggers axiom → get_0(tuple2(a,b)) = a
    // 2. result = tuple2(a, b) → congruence → get_0(result) = get_0(tuple2(a,b)) = a
    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Unsat(_)),
        "ay should derive get_0(result) = a via congruence from result = tuple2(a, b)"
    );
}

/// Diagnostic: ay derives individual field values but not their sum (#724).
///
/// ay CAN derive: get_0(result) = get_0(self_)+1 AND get_1(result) = get_1(self_)-1
/// (via tuple axiom E-matching + congruence closure).
///
/// ay CANNOT derive: get_0(result)+get_1(result) = get_0(self_)+get_1(self_)
/// (requires combining E-match equalities with LIA, which ay fails to do).
///
/// This documents the ay EUF↔LIA theory combination limitation (#724/#725).
#[test]
#[timeout(5000)]
fn test_ay_tuple_individual_field_congruence_passes() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::Auflia).unwrap();

    let tuple2_decl = solver.declare_fun("tuple2", &[Sort::Int, Sort::Int], Sort::Int);
    let get_0_decl = solver.declare_fun("get_0", &[Sort::Int], Sort::Int);
    let get_1_decl = solver.declare_fun("get_1", &[Sort::Int], Sort::Int);

    let x0 = solver.fresh_var("x0", Sort::Int);
    let x1 = solver.fresh_var("x1", Sort::Int);
    let ctor = solver.apply(&tuple2_decl, &[x0, x1]);

    let g0_ctor = solver.apply(&get_0_decl, &[ctor]);
    let ax0_body = solver.eq(g0_ctor, x0);
    let ax0 = solver.forall_with_triggers(&[x0, x1], ax0_body, &[&[ctor]]);
    solver.assert_term(ax0);

    let g1_ctor = solver.apply(&get_1_decl, &[ctor]);
    let ax1_body = solver.eq(g1_ctor, x1);
    let ax1 = solver.forall_with_triggers(&[x0, x1], ax1_body, &[&[ctor]]);
    solver.assert_term(ax1);

    let self_ = solver.declare_const("self_", Sort::Int);
    let result = solver.declare_const("result", Sort::Int);

    let g0_self = solver.apply(&get_0_decl, &[self_]);
    let g1_self = solver.apply(&get_1_decl, &[self_]);
    let one = solver.int_const(1);
    let g0_plus_1 = solver.add(g0_self, one);
    let one2 = solver.int_const(1);
    let g1_minus_1 = solver.sub(g1_self, one2);
    let tuple_val = solver.apply(&tuple2_decl, &[g0_plus_1, g1_minus_1]);
    let body_eq = solver.eq(result, tuple_val);
    solver.assert_term(body_eq);

    // Check: get_0(result) == get_0(self_)+1 AND get_1(result) == get_1(self_)-1
    let g0_result = solver.apply(&get_0_decl, &[result]);
    let g1_result = solver.apply(&get_1_decl, &[result]);
    let one3 = solver.int_const(1);
    let expected_0 = solver.add(g0_self, one3);
    let one4 = solver.int_const(1);
    let expected_1 = solver.sub(g1_self, one4);
    let eq0 = solver.eq(g0_result, expected_0);
    let eq1 = solver.eq(g1_result, expected_1);
    let conj = solver.and(eq0, eq1);
    let neg = solver.not(conj);
    solver.assert_term(neg);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Unsat(_)),
        "Individual field congruence should work"
    );
}

/// ay LIA equality chain: `a+b=10, c=a+1, d=b-1 → c+d=10` with four
/// variables must come back Unsat, not Unknown (ay#2767).
///
/// This is the shape `test_verify_multi_field_invariant_preservation` inlines
/// around; inlining stays a valid encoding strategy, but the pipeline does not
/// depend on it for LIA chains.
///
/// See ay#2767, trust-wp#724, trust-wp#725.
#[test]
#[timeout(30000)]
fn test_ay_lia_equality_chain_limitation_documented() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    // Set solver-level timeout so ay returns Unknown instead of looping forever
    solver.set_timeout(Some(std::time::Duration::from_secs(2)));

    let a = solver.declare_const("a", Sort::Int);
    let b = solver.declare_const("b", Sort::Int);
    let c = solver.declare_const("c", Sort::Int);
    let d = solver.declare_const("d", Sort::Int);

    // a + b == 10
    let sum_pre = solver.add(a, b);
    let ten = solver.int_const(10);
    let pre = solver.eq(sum_pre, ten);
    solver.assert_term(pre);

    // c = a + 1
    let one = solver.int_const(1);
    let a_plus_1 = solver.add(a, one);
    let eq0 = solver.eq(c, a_plus_1);
    solver.assert_term(eq0);

    // d = b - 1
    let one2 = solver.int_const(1);
    let b_minus_1 = solver.sub(b, one2);
    let eq1 = solver.eq(d, b_minus_1);
    solver.assert_term(eq1);

    // NOT(c + d == 10) — UNSAT
    let sum_post = solver.add(c, d);
    let ten2 = solver.int_const(10);
    let post = solver.eq(sum_post, ten2);
    let neg = solver.not(post);
    solver.assert_term(neg);

    let result = solver.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ay#2767 resolved: 4-variable equality chain should be Unsat, got {result:?}"
    );
}

/// SumTo10 preservation via body inlining.
///
/// Inlining the body into the postcondition avoids the intermediate result
/// variables that form a 4-variable LIA equality chain (ay#2767); the inlined
/// form is a valid encoding strategy in its own right, and this test covers it
/// through the verify_function pipeline. This matches the approach in
/// test_verify_multi_field_invariant_preservation.
///
/// Precondition invariant: get_0(self_) + get_1(self_) == 10
/// Inlined postcondition: (get_0(self_)+1) + (get_1(self_)-1) == 10
#[test]
#[timeout(30000)]
fn test_verify_sumto10_invariant_preservation_inlined_pipeline() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");

    // Invariant: get_0(self) + get_1(self) == 10
    let inv_def = trust_wp_core::type_invariant_def! {
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

    // requires: self_.invariant()
    let req = method_call(var("self_"), &inv_method, vec![]);

    // ensures: (get_0(self_)+1) + (get_1(self_)-1) == 10
    // This is the INLINED postcondition — body substituted directly
    // instead of going through result.invariant() + result = tuple2(...)
    let ens = eq(
        add(
            add(get_field(0, var("self_")), int(1)),
            sub(get_field(1, var("self_")), int(1)),
        ),
        int(10),
    );

    // No body — the postcondition is inlined
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "SumTo10 invariant preservation (inlined) should verify: got {result:?}"
    );
}

/// SumTo10 invariant violation via inlined body — broken increment.
///
/// Same as preservation test but body only increments field 0, no
/// decrement of field 1. Inlined postcondition: (get_0(self_)+1) + get_1(self_) == 10.
/// Should fail because the sum becomes 11.
#[test]
#[timeout(30000)]
fn test_verify_sumto10_invariant_violation_inlined_pipeline() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");

    let inv_def = trust_wp_core::type_invariant_def! {
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

    let req = method_call(var("self_"), &inv_method, vec![]);

    // BROKEN inlined postcondition: (get_0(self_)+1) + get_1(self_) == 10
    // Only increments field 0, no decrement of field 1 — sum becomes 11.
    let ens = eq(
        add(
            add(get_field(0, var("self_")), int(1)),
            get_field(1, var("self_")),
        ),
        int(10),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Broken SumTo10 invariant (inlined) should produce counterexample: got {result:?}"
    );
}

/// Ground tuple destructor instances compensate for E-matching + LIA gap (#724).
///
/// Tests that `assert_tuple_axioms()` eagerly asserts ground destructor
/// instances `get_I(tupleN(a0, ..., aN-1)) = aI` for constructor applications
/// in the ground pool. Without these, ay-dpll cannot combine E-matched
/// equalities from quantified tuple axioms with LIA arithmetic.
///
/// Encoding (all Int-sorted, no type invariant sort complexity):
/// - Pre: a + b == 10
/// - Body: t == tuple2(a + 1, b - 1)
/// - Post: get_0(t) + get_1(t) == 10
///
/// The quantified axioms `forall x0 x1. get_0(tuple2(x0,x1)) = x0` require
/// E-matching → congruence → LIA chain. The ground instances make it direct.
#[test]
#[timeout(30000)]
fn test_ground_tuple_destructor_instances_enable_lia_combination() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    // Pre: a + b == 10
    let pre = eq(add(var("a"), var("b")), int(10));

    // Body: t == tuple2(a + 1, b - 1)
    let tuple_ctor = logic_fn_call(
        &tuple_logic_fn_name(2),
        vec![add(var("a"), int(1)), sub(var("b"), int(1))],
    );
    let body_eq = eq(var("t"), tuple_ctor);

    // Post: get_0(t) + get_1(t) == 10
    let post = eq(add(get_field(0, var("t")), get_field(1, var("t"))), int(10));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[pre, body_eq], &[post])).unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Ground tuple destructor instances should verify: got {result:?}"
    );
}

/// Negative test: broken body makes post unprovable even with ground instances (#724).
///
/// Same as preservation test but body only increments field 0 (no decrement of
/// field 1), so `get_0(t) + get_1(t) != 10`.
#[test]
#[timeout(30000)]
fn test_ground_tuple_destructor_instances_detect_violation() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    let pre = eq(add(var("a"), var("b")), int(10));

    // BROKEN: only increments a, no decrement of b
    let tuple_ctor = logic_fn_call(
        &tuple_logic_fn_name(2),
        vec![add(var("a"), int(1)), var("b")],
    );
    let body_eq = eq(var("t"), tuple_ctor);

    let post = eq(add(get_field(0, var("t")), get_field(1, var("t"))), int(10));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[pre, body_eq], &[post])).unwrap();
    assert!(
        crate::tests::rejected(&result),
        "Broken body should produce counterexample: got {result:?}"
    );
}
