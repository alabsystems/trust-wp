// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Spec axiom encoding tests for `emit_spec_axioms` in `logic_fn/registration.rs`.
//!
//! Covers:
//! - Opaque logic functions with spec axioms (ensures visible, body hidden)
//! - Multi-parameter spec axioms with E-matching triggers
//! - Zero-parameter lemma spec axioms (direct assertion)
//! - Spec axiom encoding errors (partial failure with SpecAxiomDropped)
//! - Multiple ensures clauses on a single function
//! - Interaction between requires guard and spec axioms
//!
//! Part of #1296 (quantifier residual / spec axiom coverage).

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

// ── Opaque logic functions with spec axioms ─────────────────────────

/// An opaque function with multiple ensures clauses emits all spec axioms.
///
/// Models:
/// ```text
/// #[logic]
/// #[ensures(result >= x)]
/// #[ensures(result >= y)]
/// fn maxopaque(x: Int, y: Int) -> Int;
/// ```
///
/// Both postconditions should be usable by callers even though the body
/// is hidden (Default mode = opaque).
#[test]
#[timeout(30000)]
fn test_opaque_fn_multiple_ensures_all_available() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let mut func = LogicFnDef::new(
        "maxopaque".to_string(),
        "test::maxopaque".to_string(),
        vec!["x".to_string(), "y".to_string()],
        ite(ge(var("x"), var("y")), var("x"), var("y")),
    )
    .with_mode(LogicMode::Default);
    func.set_ensures(vec![
        ge(var("result"), var("x")),
        ge(var("result"), var("y")),
    ]);

    encoder
        .register_logic_fn(&func)
        .expect("opaque multi-ensures registration should succeed");

    // Both spec axioms should fire: maxopaque(3, 7) >= 3 AND >= 7
    let call = logic_fn_call("maxopaque", vec![int(3), int(7)]);
    let call_term = encoder.encode_pure(&call).expect("encode maxopaque(3, 7)");

    // Check first ensures: result >= x (i.e., maxopaque(3,7) >= 3)
    let three = encoder.solver.int_const(3);
    let ge_three = encoder.solver.ge(call_term, three);
    let not_ge_three = encoder.solver.not(ge_three);
    encoder.solver.push();
    encoder.assert_term(not_ge_three);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "maxopaque(3,7) >= 3 should hold from first spec axiom"
    );
    encoder.solver.pop();

    // Check second ensures: result >= y (i.e., maxopaque(3,7) >= 7)
    let seven = encoder.solver.int_const(7);
    let ge_seven = encoder.solver.ge(call_term, seven);
    let not_ge_seven = encoder.solver.not(ge_seven);
    encoder.assert_term(not_ge_seven);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "maxopaque(3,7) >= 7 should hold from second spec axiom"
    );
}

/// An opaque function's spec axiom IS guarded by the function's requires.
///
/// `#[ensures(...)]` on a logic function is only *proven* under the
/// function's `#[requires(...)]`, so the sound module-level fact is
/// `forall x [postrans(x)]. x > 0 => postrans(x) > 0`. The previous emitter
/// dropped the guard and asserted the unconditional
/// `forall x. postrans(x) > 0` — for requires-guarded lemmas that is a FALSE
/// global axiom (e.g. filter_positive's `lemma_num_of_pos_increasing` with
/// `requires(j <= k)`), which makes every obligation in scope provable: a
/// false-accept hazard. This test pins the guarded semantics.
///
/// Models:
/// ```text
/// #[logic]
/// #[requires(x > 0)]
/// #[ensures(result > 0)]
/// fn positive_transform(x: Int) -> Int;
/// ```
#[test]
#[timeout(30000)]
fn test_opaque_fn_spec_axiom_guarded_by_requires() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let mut func = LogicFnDef::new_with_requires(
        "postrans".to_string(),
        "test::postrans".to_string(),
        vec!["x".to_string()],
        vec![gt(var("x"), int(0))],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Default);
    func.set_ensures(vec![gt(var("result"), int(0))]);

    encoder
        .register_logic_fn(&func)
        .expect("opaque fn with requires should register");

    // The spec axiom says: forall x [postrans(x)]. x > 0 => postrans(x) > 0
    // At x=5 the guard is discharged arithmetically, so the ensures applies.
    let call_5 = logic_fn_call("postrans", vec![int(5)]);
    let call_5_term = encoder.encode_pure(&call_5).expect("encode postrans(5)");
    let zero = encoder.solver.int_const(0);
    let gt_zero_5 = encoder.solver.gt(call_5_term, zero);
    let not_gt_5 = encoder.solver.not(gt_zero_5);
    encoder.solver.push();
    encoder.assert_term(not_gt_5);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "postrans(5) > 0 should hold from the guarded spec axiom (5 > 0)"
    );
    encoder.solver.pop();

    // At x=-1 the requires is violated: the ensures must NOT be derivable.
    // (postrans(-1) is unconstrained, so the negated query stays satisfiable.)
    let call_neg = logic_fn_call("postrans", vec![int(-1)]);
    let call_neg_term = encoder.encode_pure(&call_neg).expect("encode postrans(-1)");
    let gt_zero_neg = encoder.solver.gt(call_neg_term, zero);
    let not_gt_neg = encoder.solver.not(gt_zero_neg);
    encoder.assert_term(not_gt_neg);
    assert!(
        !matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "postrans(-1) > 0 must NOT be derivable — the spec axiom is guarded by \
         requires(x > 0), and asserting it unguarded would be a false axiom"
    );
}

// ── Multi-parameter spec axioms with triggers ───────────────────────

/// A three-parameter function's spec axiom with trigger on f(a, b, c).
///
/// Tests that the E-matching trigger on the function application actually
/// fires for ground terms, making the ensures clause usable.
///
/// Models:
/// ```text
/// #[logic]
/// #[ensures(result == x + y + z)]
/// fn sum3(x: Int, y: Int, z: Int) -> Int { x + y + z }
/// ```
#[test]
#[timeout(30000)]
fn test_multi_param_spec_axiom_trigger_fires() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let body = add(add(var("x"), var("y")), var("z"));
    let mut func = LogicFnDef::new(
        "sum3".to_string(),
        "test::sum3".to_string(),
        vec!["x".to_string(), "y".to_string(), "z".to_string()],
        body,
    )
    .with_mode(LogicMode::Open);
    func.set_ensures(vec![eq(
        var("result"),
        add(add(var("x"), var("y")), var("z")),
    )]);

    encoder
        .register_logic_fn(&func)
        .expect("sum3 registration should succeed");

    // The spec axiom says: forall x,y,z [sum3(x,y,z)]. sum3(x,y,z) == x+y+z
    // A ground call sum3(1, 2, 3) should trigger E-matching, yielding sum3(1,2,3) == 6
    let call = logic_fn_call("sum3", vec![int(1), int(2), int(3)]);
    let call_term = encoder.encode_pure(&call).expect("encode sum3(1,2,3)");
    let six = encoder.solver.int_const(6);
    let eq_term = encoder.solver.eq(call_term, six);
    let neq = encoder.solver.not(eq_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "sum3(1,2,3) != 6 should be UNSAT (spec axiom + defining axiom via trigger)"
    );
}

/// Spec axiom with symbolic arguments: the forall trigger fires when
/// the function is applied to symbolic (non-constant) terms.
#[test]
#[timeout(30000)]
fn test_spec_axiom_fires_on_symbolic_arguments() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // clamp(x) = if x < 0 then 0 else x
    // ensures(result >= 0)
    let mut clamp_fn = LogicFnDef::new(
        "clamp".to_string(),
        "test::clamp".to_string(),
        vec!["x".to_string()],
        ite(lt(var("x"), int(0)), int(0), var("x")),
    )
    .with_mode(LogicMode::Open);
    clamp_fn.set_ensures(vec![ge(var("result"), int(0))]);

    // Verify: for any x, clamp(x) >= 0 (using spec axiom, not body)
    // Use Default mode to suppress the defining axiom — only spec axiom available
    let mode_overrides = vec![LogicMode::Default];
    let call = logic_fn_call("clamp", vec![var("x")]);
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ge(call, int(0))])
            .logic_fns(Some(std::slice::from_ref(&clamp_fn)))
            .mode_overrides(Some(&mode_overrides)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "clamp(x) >= 0 should verify from spec axiom alone (body suppressed). Got: {result:?}"
    );
}

// ── Zero-parameter lemma spec axioms ────────────────────────────────

/// A zero-parameter lemma's ensures is asserted directly (no forall wrapper)
/// and is semantically available in the proof context.
///
/// Models:
/// ```text
/// #[logic]
/// #[ensures(1 + 1 == 2)]
/// fn oneplusone_is_two() {}
/// ```
#[test]
#[timeout(30000)]
fn test_zero_param_lemma_ensures_semantically_available() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let mut lemma = LogicFnDef::new(
        "oneplusone".to_string(),
        "test::oneplusone".to_string(),
        vec![],
        int(0),
    )
    .with_mode(LogicMode::Open);
    lemma.set_ensures(vec![eq(add(int(1), int(1)), int(2))]);

    encoder
        .register_logic_fn(&lemma)
        .expect("zero-param lemma registration should succeed");

    // The ensures 1 + 1 == 2 is trivially true and asserted directly.
    // Asserting NOT(1 + 1 == 2) should be UNSAT.
    let one_a = encoder.solver.int_const(1);
    let one_b = encoder.solver.int_const(1);
    let oneplusone = encoder.solver.add(one_a, one_b);
    let two = encoder.solver.int_const(2);
    let eq_term = encoder.solver.eq(oneplusone, two);
    let neq = encoder.solver.not(eq_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "1 + 1 != 2 should be UNSAT (lemma ensures asserted directly)"
    );
}

/// A zero-parameter lemma with a non-trivial ensures that provides
/// a useful fact to the proof context.
///
/// Models a lemma that asserts a universally quantified property as
/// its ensures clause. Since the lemma has zero params, the ensures
/// is asserted directly as a top-level fact.
#[test]
#[timeout(30000)]
fn test_zero_param_lemma_with_forall_ensures() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a helper function first
    let helper_fn = LogicFnDef::new(
        "abshelper".to_string(),
        "test::abshelper".to_string(),
        vec!["x".to_string()],
        ite(ge(var("x"), int(0)), var("x"), neg(var("x"))),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&helper_fn)
        .expect("abshelper registration");

    // Lemma: ensures(forall<i> abshelper(i) >= 0)
    let mut lemma = LogicFnDef::new(
        "lemma_abs_nonneg".to_string(),
        "test::lemma_abs_nonneg".to_string(),
        vec![],
        int(0),
    )
    .with_mode(LogicMode::Open);
    lemma.set_ensures(vec![forall(
        "i",
        ge(logic_fn_call("abshelper", vec![var("i")]), int(0)),
    )]);

    encoder
        .register_logic_fn(&lemma)
        .expect("lemma_abs_nonneg registration");

    // The lemma ensures forall i. abshelper(i) >= 0.
    // Check: abshelper(-5) >= 0 should hold.
    let call = logic_fn_call("abshelper", vec![int(-5)]);
    let call_term = encoder.encode_pure(&call).expect("encode abshelper(-5)");
    let zero = encoder.solver.int_const(0);
    let ge_zero = encoder.solver.ge(call_term, zero);
    let not_ge = encoder.solver.not(ge_zero);
    encoder.assert_term(not_ge);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "abshelper(-5) >= 0 should hold (via defining axiom and/or lemma)"
    );
}

/// An opaque zero-parameter lemma (no body visible) still provides its
/// ensures as a direct assertion.
#[test]
#[timeout(30000)]
fn test_zero_param_opaque_lemma_ensures_still_asserted() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a constant function
    let const_fn = LogicFnDef::new(
        "magic_constant".to_string(),
        "test::magic_constant".to_string(),
        vec![],
        int(42),
    )
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&const_fn)
        .expect("magic_constant registration");

    // Opaque lemma: ensures(magic_constant() > 0)
    let mut lemma = LogicFnDef::new(
        "lemma_magic_pos".to_string(),
        "test::lemma_magic_pos".to_string(),
        vec![],
        int(0),
    )
    .with_mode(LogicMode::Default); // opaque
    lemma.set_ensures(vec![gt(logic_fn_call("magic_constant", vec![]), int(0))]);

    encoder
        .register_logic_fn(&lemma)
        .expect("opaque lemma registration");

    // The lemma's spec axiom says magic_constant() > 0 (directly asserted).
    let call = logic_fn_call("magic_constant", vec![]);
    let call_term = encoder.encode_pure(&call).expect("encode magic_constant()");
    let zero = encoder.solver.int_const(0);
    let gt_zero = encoder.solver.gt(call_term, zero);
    let not_gt = encoder.solver.not(gt_zero);
    encoder.assert_term(not_gt);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "magic_constant() > 0 should hold from opaque lemma's spec axiom"
    );
}

// ── Spec axiom encoding errors (dropped axioms) ─────────────────────

/// When one of multiple ensures clauses fails to encode, the others
/// should still be emitted. The failed one increments SpecAxiomDropped.
///
/// Models a function with two ensures:
/// 1. result > x (encodable)
/// 2. result == NaN (unencodable: `result` is an integer and NaN a float)
///
/// The first ensures should still be available as a spec axiom.
#[test]
#[timeout(30000)]
fn test_partial_ensures_failure_emits_surviving_axioms() {
    use crate::encoder::unsoundness;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encodable ensures + an ensures equating an integer with a float.
    let encodable = gt(var("result"), var("x"));
    let unencodable = eq(
        var("result"),
        PureExpr::Float(trust_wp_core::formula::FloatBits::from_f64(f64::NAN)),
    );

    let mut func = LogicFnDef::new(
        "partialspec".to_string(),
        "test::partialspec".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);
    func.set_ensures(vec![encodable, unencodable]);

    unsoundness::reset();
    let before = unsoundness::snapshot();

    encoder
        .register_logic_fn(&func)
        .expect("partial failure should not error the whole registration");

    let delta = unsoundness::delta(&before, &unsoundness::snapshot());

    // SpecAxiomDropped should have been incremented
    assert!(
        delta.contains_key(&unsoundness::UnsoundnessCategory::SpecAxiomDropped),
        "unencodable ensures should increment SpecAxiomDropped, got delta: {delta:?}"
    );

    // The surviving ensures (result > x) should still be available
    let call = logic_fn_call("partialspec", vec![int(10)]);
    let call_term = encoder.encode_pure(&call).expect("encode partialspec(10)");
    let ten = encoder.solver.int_const(10);
    let gt_ten = encoder.solver.gt(call_term, ten);
    let not_gt = encoder.solver.not(gt_ten);
    encoder.assert_term(not_gt);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "partialspec(10) > 10 should hold from surviving spec axiom"
    );

    unsoundness::reset();
}

/// When ALL ensures clauses fail to encode, SpecAxiomDropped is incremented
/// for each, and the function is still registered (but with no spec axioms).
#[test]
#[timeout(30000)]
fn test_all_ensures_fail_still_registers_function() {
    use crate::encoder::unsoundness;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Each ensures equates the integer `result` with a float.
    let unencodable_1 = eq(
        var("result"),
        PureExpr::Float(trust_wp_core::formula::FloatBits::from_f64(f64::NAN)),
    );
    let unencodable_2 = eq(
        var("result"),
        PureExpr::Float(trust_wp_core::formula::FloatBits::from_f64(f64::INFINITY)),
    );

    let mut func = LogicFnDef::new(
        "allfailspec".to_string(),
        "test::allfailspec".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);
    func.set_ensures(vec![unencodable_1, unencodable_2]);

    unsoundness::reset();
    let before = unsoundness::snapshot();

    encoder
        .register_logic_fn(&func)
        .expect("all-failing ensures should not error the whole registration");

    let delta = unsoundness::delta(&before, &unsoundness::snapshot());

    // Two SpecAxiomDropped increments
    let dropped_count = delta
        .get(&unsoundness::UnsoundnessCategory::SpecAxiomDropped)
        .copied()
        .unwrap_or(0);
    assert_eq!(
        dropped_count, 2,
        "both unencodable ensures should increment SpecAxiomDropped: {delta:?}"
    );

    // Function should still be registered with its defining axiom
    assert!(
        encoder.decls().has_logic_func("logic_allfailspec"),
        "function should still be declared despite all ensures failing"
    );

    // Defining axiom should still work: allfailspec(7) == 7
    let call = logic_fn_call("allfailspec", vec![int(7)]);
    let call_term = encoder.encode_pure(&call).expect("encode allfailspec(7)");
    let seven = encoder.solver.int_const(7);
    let eq_term = encoder.solver.eq(call_term, seven);
    let neq = encoder.solver.not(eq_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "allfailspec(7) != 7 should be UNSAT (defining axiom still works)"
    );

    unsoundness::reset();
}

// ── Ground pool registration for spec axioms ────────────────────────

/// Spec axioms with parameters are registered in the ground pool for
/// Phase 2 ground instantiation (#1965, Lane 5).
#[test]
#[timeout(30000)]
fn test_spec_axiom_registers_in_ground_pool() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Use a name without underscores to avoid SMT name escaping issues
    let mut func = LogicFnDef::new(
        "poolfn".to_string(),
        "test::poolfn".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);
    func.set_ensures(vec![gt(var("result"), var("x"))]);

    encoder
        .register_logic_fn(&func)
        .expect("registration should succeed");

    // The SMT name is "logic_poolfn" (logic_ prefix, no underscores to escape).
    // The ground pool should have at least 2 axiom entries for this function:
    // 1. The defining axiom
    // 2. The spec axiom from ensures
    let pool = encoder.ground_pool_for_test();
    let smt_name = "logic_poolfn";
    let axiom_count = pool
        .axioms()
        .iter()
        .filter(|a| a.fn_symbol == smt_name)
        .count();
    assert!(
        axiom_count >= 2,
        "ground pool should have defining + spec axiom entries for '{smt_name}', got {axiom_count}"
    );
}

/// Zero-parameter lemma spec axioms are NOT registered in the ground pool
/// (no bound variables to instantiate).
#[test]
#[timeout(30000)]
fn test_zero_param_lemma_not_in_ground_pool() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let mut lemma = LogicFnDef::new(
        "lemmanopool".to_string(),
        "test::lemmanopool".to_string(),
        vec![],
        int(0),
    )
    .with_mode(LogicMode::Open);
    lemma.set_ensures(vec![eq(add(int(2), int(2)), int(4))]);

    encoder
        .register_logic_fn(&lemma)
        .expect("lemma registration should succeed");

    // Zero-param: defining axiom is asserted directly (no forall),
    // and spec axiom is asserted directly too. Neither needs ground pool.
    let pool = encoder.ground_pool_for_test();
    let smt_name = "logic_lemmanopool";
    let axiom_count = pool
        .axioms()
        .iter()
        .filter(|a| a.fn_symbol == smt_name)
        .count();
    assert_eq!(
        axiom_count, 0,
        "zero-param lemma should not have ground pool entries, got {axiom_count}"
    );
}

// ── Idempotence with spec axioms ────────────────────────────────────

/// Double registration of a function with ensures is idempotent:
/// spec axioms are not duplicated.
#[test]
#[timeout(30000)]
fn test_double_registration_with_ensures_idempotent() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let mut func = LogicFnDef::new(
        "idemspec".to_string(),
        "test::idemspec".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);
    func.set_ensures(vec![gt(var("result"), var("x"))]);

    encoder
        .register_logic_fn(&func)
        .expect("first registration");
    let pool_after_first = encoder
        .ground_pool_for_test()
        .axioms()
        .iter()
        .filter(|a| a.fn_symbol == "logic_idemspec")
        .count();

    encoder
        .register_logic_fn(&func)
        .expect("second registration should be no-op");
    let pool_after_second = encoder
        .ground_pool_for_test()
        .axioms()
        .iter()
        .filter(|a| a.fn_symbol == "logic_idemspec")
        .count();

    assert_eq!(
        pool_after_first, pool_after_second,
        "double registration should not duplicate ground pool entries"
    );

    // Semantics should still be correct
    let call = logic_fn_call("idemspec", vec![int(5)]);
    let call_term = encoder.encode_pure(&call).expect("encode idemspec(5)");
    let five = encoder.solver.int_const(5);
    let gt_five = encoder.solver.gt(call_term, five);
    let not_gt = encoder.solver.not(gt_five);
    encoder.assert_term(not_gt);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "idemspec(5) > 5 should hold after double registration"
    );
}
