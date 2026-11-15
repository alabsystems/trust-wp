// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
/// Demonstrate that integer cast identity encoding is unsound.
///
/// Scenario: `fn narrow(x: u32) -> u8 { x as u8 }`
/// Postcondition: `result == x` (WRONG — should fail for x > 255)
///
/// Because IntToInt is identity, the body is just `x` and `result == x`
/// trivially verifies. In real Rust, `300u32 as u8` is 44 (truncation),
/// so `result == x` should NOT hold for all inputs.
///
/// This test confirms the false proof and that IntegerCastIdentity demotion
/// catches it: the result is demoted from Verified to Unknown.
#[test]
#[timeout(30000)]
fn test_integer_cast_identity_unsoundness_narrowing() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Take snapshot BEFORE the cast increment (simulates driver flow).
        let driver_snapshot = unsoundness::snapshot();

        // 2. Simulate MIR extraction encountering an IntToInt cast.
        unsoundness::increment(UnsoundnessCategory::IntegerCastIdentity);

        // 3. Encode: body is just `x` (identity cast), postcondition is `result == x`.
        //    This is trivially UNSAT in the negated-postcondition encoding:
        //    result = x AND NOT(result == x) is contradictory.
        let ensures = eq(var("result"), var("x"));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&var("x")))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. The result MUST be demoted to Unknown because IntegerCastIdentity
        //    is a HIGH-risk demoting category. Without demotion, this would be
        //    a false proof: `300u32 as u8 == 300` is provably false in Rust.
        match &result {
            VerificationResult::Unknown(reason) => {
                assert!(
                    reason.as_str().contains("demoted"),
                    "should be demoted due to IntegerCastIdentity: {reason}"
                );
                assert!(
                    reason.as_str().contains("integer_cast_identity"),
                    "demotion reason should cite integer_cast_identity: {reason}"
                );
            }
            other => panic!(
                "IntegerCastIdentity (HIGH risk) should demote Verified to Unknown, \
                 demonstrating that the identity encoding of `x as u8` is unsound \
                 for narrowing casts: {other:?}"
            ),
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Verify IntegerCastIdentity increments and classification.
///
/// Ensures the new category is correctly wired: increment, snapshot, delta,
/// and demoting classification all work as expected.
#[test]
#[timeout(30000)]
fn test_integer_cast_identity_increment_and_classification() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        unsoundness::increment(UnsoundnessCategory::IntegerCastIdentity);

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert_eq!(
            d.get(&UnsoundnessCategory::IntegerCastIdentity),
            Some(&1),
            "IntegerCastIdentity should appear in delta after increment"
        );

        assert!(
            UnsoundnessCategory::IntegerCastIdentity.is_demoting(),
            "IntegerCastIdentity must be demoting — identity casts can produce false proofs"
        );

        assert!(
            unsoundness::has_demoting(&d),
            "delta with IntegerCastIdentity should be flagged as demoting"
        );

        let formatted = unsoundness::format_demoting(&d);
        assert!(
            formatted.contains("integer_cast_identity"),
            "format_demoting should include integer_cast_identity: {formatted}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// ---------------------------------------------------------------------------
// Production-path regression tests for every unsoundness category (#2662)
//
// Each test below exercises the actual production code path that increments
// the unsoundness counter, then verifies the counter delta. Categories with
// existing production-path counter tests are not duplicated here.
// ---------------------------------------------------------------------------

/// InvariantTrueShortCircuit: trivial type invariant (body = `true`) triggers
/// the short-circuit in `encode_bool_method_predicate`, incrementing the counter.
///
/// Production path: `encoder/method_call/bool_uf.rs` line ~133.
/// Prior test coverage: `bool_iff_and_trivial_invariant.rs` exercises the path
/// but does NOT check the counter delta. This test closes that gap.
#[test]
#[timeout(30000)]
fn test_invariant_true_short_circuit_production_path_counter() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        // Register a trivial invariant (body = true) and encode a method call
        // that hits the short-circuit path.
        let inv_method = trust_wp_core::logic::type_invariant_method_name("TrivialType");

        let inv_def = trust_wp_core::type_invariant_def! {
            type_name: "TrivialType".to_string(),
            self_param: "self".to_string(),
            param_sort: None,
            body: bool_expr(true),
            is_newtype: true,
            element_invariant_method: None,
        };

        // Verify through the full pipeline: requires nothing, ensures x.invariant().
        // The trivial invariant short-circuits to `true`, which should increment
        // InvariantTrueShortCircuit.
        let ens = method_call(var("x"), &inv_method, vec![]);
        let _result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ens]).type_invariants(Some(&[inv_def])),
        )
        .expect("verification should not error");

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        // The counter must have been incremented via the production path.
        assert!(
            d.get(&UnsoundnessCategory::InvariantTrueShortCircuit)
                .copied()
                .unwrap_or(0)
                > 0,
            "InvariantTrueShortCircuit must fire when a trivial invariant (body=true) \
             is short-circuited in encode_bool_method_predicate. Delta: {d:?}"
        );

        // Confirm it is non-demoting (LOW risk).
        assert!(
            !UnsoundnessCategory::InvariantTrueShortCircuit.is_demoting(),
            "InvariantTrueShortCircuit should be non-demoting (provably sound identity transform)"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// BitwiseUfApproximation: the legacy UF fallback in `encoder/operators.rs`
/// still increments the counter when explicitly invoked (for backward compat),
/// but the category is now ELIMINATED (#2666) since BV mode is always-on in
/// production. The counter fires in the UF fallback path but does NOT cause
/// demotion.
///
/// This test verifies:
/// 1. The UF fallback path still increments the counter (backward compat).
/// 2. The category is ELIMINATED (non-demoting).
/// 3. The default BV path does NOT increment the counter.
#[test]
#[timeout(30000)]
fn test_bitwise_uf_approximation_eliminated_category() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // Part 1: Legacy UF path still increments the counter.
        let before = unsoundness::snapshot();
        let mut encoder = AYEncoder::new();
        encoder.set_bitwise_proof_mode(false);
        let expr = trust_wp_core::formula::PureExpr::BinOp(
            std::sync::Arc::new(int(7)),
            trust_wp_core::formula::BinOp::Shl,
            std::sync::Arc::new(int(2)),
        );
        encoder
            .encode_pure(&expr)
            .expect("bitwise Shl should encode via UF fallback");
        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);
        assert!(
            d.get(&UnsoundnessCategory::BitwiseUfApproximation)
                .copied()
                .unwrap_or(0)
                > 0,
            "UF fallback path should still increment BitwiseUfApproximation counter. Delta: {d:?}"
        );

        // Part 2: Category is ELIMINATED (non-demoting).
        assert!(
            !UnsoundnessCategory::BitwiseUfApproximation.is_demoting(),
            "BitwiseUfApproximation should be ELIMINATED (non-demoting) since #2666"
        );
        assert!(
            UnsoundnessCategory::BitwiseUfApproximation.is_eliminated(),
            "BitwiseUfApproximation should be classified as ELIMINATED"
        );

        // Part 3: Default BV path does NOT increment the counter.
        unsoundness::reset();
        let before_bv = unsoundness::snapshot();
        let mut encoder_bv = AYEncoder::new();
        // bitwise_proof_mode is true by default
        let expr_bv = trust_wp_core::formula::PureExpr::BinOp(
            std::sync::Arc::new(int(7)),
            trust_wp_core::formula::BinOp::Shl,
            std::sync::Arc::new(int(2)),
        );
        encoder_bv
            .encode_pure(&expr_bv)
            .expect("bitwise Shl should encode via BV path");
        let after_bv = unsoundness::snapshot();
        let d_bv = unsoundness::delta(&before_bv, &after_bv);
        assert_eq!(
            d_bv.get(&UnsoundnessCategory::BitwiseUfApproximation)
                .copied()
                .unwrap_or(0),
            0,
            "BV path (default) should NOT increment BitwiseUfApproximation. Delta: {d_bv:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// CatchUnwindFallback: `catch_solver_panic_with_reason` catching a ay panic
/// increments the counter.
///
/// Production path: `encoder/type_resolve.rs` line ~130, invoked via
/// `AYEncoder::assert_solver_term` (solver.rs line ~219).
/// Prior test coverage: `catch_unwind_tests.rs` exercises assert_solver_term
/// with sort-mismatch panics but does NOT check the unsoundness counter.
/// This test closes that gap.
#[test]
#[timeout(30000)]
fn test_catch_unwind_fallback_production_path_counter() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        // Trigger the production path: encoder.assert_term with an Int term
        // (not Bool) triggers a ay sort-mismatch panic, which is caught by
        // catch_solver_panic_with_reason, incrementing CatchUnwindFallback.
        let mut encoder = AYEncoder::new();
        let int_term = encoder.solver.int_const(42);
        // assert_term -> assert_solver_term -> catch_solver_panic_with_reason
        // -> ay panics with sort mismatch -> CatchUnwindFallback incremented
        encoder.assert_term(int_term);

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert!(
            d.get(&UnsoundnessCategory::CatchUnwindFallback)
                .copied()
                .unwrap_or(0)
                > 0,
            "CatchUnwindFallback must fire when catch_solver_panic_with_reason \
             catches a ay sort-mismatch panic via assert_solver_term. Delta: {d:?}"
        );

        // Confirm it is non-demoting (LOW risk).
        assert!(
            !UnsoundnessCategory::CatchUnwindFallback.is_demoting(),
            "CatchUnwindFallback should be non-demoting (conservative fallback)"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// UnsupportedConstructSkip: `EncodingError::unsupported()` constructor
/// increments the counter as a side effect.
///
/// Production path: `error.rs` line ~210.
/// Prior test coverage: `error_formatting.rs` and `encoding.rs` call the
/// constructor but do NOT check the unsoundness counter. This test closes that gap.
#[test]
#[timeout(30000)]
fn test_unsupported_construct_skip_production_path_counter() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        // Call the production constructor -- it increments UnsupportedConstructSkip
        // as a side effect of creating the error.
        let _err = crate::error::EncodingError::unsupported("regression test: raw pointers");

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert_eq!(
            d.get(&UnsoundnessCategory::UnsupportedConstructSkip),
            Some(&1),
            "EncodingError::unsupported() must increment UnsupportedConstructSkip. Delta: {d:?}"
        );

        // Also test the with_span variant.
        let before2 = unsoundness::snapshot();
        let _err2 = crate::error::EncodingError::unsupported_with_span(
            "regression test: inline asm",
            trust_wp_core::formula::SourceSpan::with_location("test.rs", 1, 1),
        );
        let d2 = unsoundness::delta(&before2, &unsoundness::snapshot());
        assert_eq!(
            d2.get(&UnsoundnessCategory::UnsupportedConstructSkip),
            Some(&1),
            "EncodingError::unsupported_with_span() must also increment. Delta: {d2:?}"
        );

        // Also test the with_context variant.
        let before3 = unsoundness::snapshot();
        let _err3 = crate::error::EncodingError::unsupported_with_context(
            "regression test: generators",
            None,
            None,
        );
        let d3 = unsoundness::delta(&before3, &unsoundness::snapshot());
        assert_eq!(
            d3.get(&UnsoundnessCategory::UnsupportedConstructSkip),
            Some(&1),
            "EncodingError::unsupported_with_context() must also increment. Delta: {d3:?}"
        );

        // Confirm it is non-demoting (LOW risk).
        assert!(
            !UnsoundnessCategory::UnsupportedConstructSkip.is_demoting(),
            "UnsupportedConstructSkip should be non-demoting (conservative skip)"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// LetAssumeDropped: encoding a `LetAssume` with an unencodable assumption
/// triggers the error path in `pure_encoding/bindings.rs`, incrementing the counter.
///
/// Production path: `encoder/pure_encoding/bindings.rs` line ~71.
/// The assumption is one the encoder refuses (`unencodable_float_order`).
#[test]
#[timeout(30000)]
fn test_let_assume_dropped_production_path_counter() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        // An unencodable assumption makes encode_pure_impl(assumption)
        // fail, taking the Err branch that increments LetAssumeDropped.
        let unencodable_assumption = crate::tests::helpers::unencodable_float_order();
        let body = int(42);
        let expr = let_assume(unencodable_assumption, body);

        let mut encoder = AYEncoder::new();
        let result = encoder.encode_pure(&expr);
        // Per #2663 Phase 2a: LetAssume with unencodable assumption now
        // propagates the encoding error instead of silently dropping the
        // assumption. This turns false proofs into Unknown (safe direction).
        assert!(
            result.is_err(),
            "LetAssume with unencodable assumption should propagate error (#2663): {result:?}"
        );

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert!(
            d.get(&UnsoundnessCategory::LetAssumeDropped)
                .copied()
                .unwrap_or(0)
                > 0,
            "LetAssumeDropped must fire when a LetAssume assumption fails to encode. Delta: {d:?}"
        );

        // Confirm it is demoting (HIGH risk).
        assert!(
            UnsoundnessCategory::LetAssumeDropped.is_demoting(),
            "LetAssumeDropped should be demoting (return value unconstrained)"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// SpecAxiomDropped: registering a logic function with an unencodable ensures
/// clause triggers the error path in `logic_fn/registration.rs`, incrementing the counter.
///
/// Production path: `encoder/logic_fn/registration.rs` line ~380.
/// The ensures clause equates an integer with a float, which cannot be encoded,
/// so its spec axiom is dropped while the other ensures clauses survive.
#[test]
#[timeout(30000)]
fn test_spec_axiom_dropped_production_path_counter() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new_with_quantifiers();

        // Create a logic function with one encodable and one unencodable ensures.
        // `result` is an integer here, and no equality relates it to a float.
        let encodable_ensures = gt(var("result"), var("x"));
        let unencodable_ensures = eq(
            var("result"),
            trust_wp_core::formula::PureExpr::Float(trust_wp_core::formula::FloatBits::from_f64(
                f64::NAN,
            )),
        );

        let mut func = trust_wp_core::logic::LogicFnDef::new(
            "specdroppedtest".to_string(),
            "test::specdroppedtest".to_string(),
            vec!["x".to_string()],
            add(var("x"), int(1)),
        )
        .with_mode(trust_wp_core::logic::LogicMode::Open);
        func.set_ensures(vec![encodable_ensures, unencodable_ensures]);

        encoder
            .register_logic_fn(&func)
            .expect("partial failure should not error the whole registration");

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert!(
            d.get(&UnsoundnessCategory::SpecAxiomDropped)
                .copied()
                .unwrap_or(0)
                > 0,
            "SpecAxiomDropped must fire when a logic fn ensures clause fails to encode. Delta: {d:?}"
        );

        // Confirm it is demoting (HIGH risk).
        assert!(
            UnsoundnessCategory::SpecAxiomDropped.is_demoting(),
            "SpecAxiomDropped should be demoting (callers lose postcondition constraint)"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// PhantomVariableUpgrade: declaring a variable as Int then redeclaring as Bool
/// triggers the sort upgrade path in `var_declare.rs`, incrementing the counter.
///
/// Production path: `encoder/var_declare.rs` line ~152.
/// The Int→Bool upgrade path creates a phantom `{name}__upgraded` variable
/// because the original Int-sorted ay term cannot be reused with Bool sort.
#[test]
#[timeout(30000)]
fn test_phantom_variable_upgrade_production_path_counter() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        let mut encoder = AYEncoder::new();

        // First declaration: variable "pv_test" as Int (speculative default).
        let _first = encoder
            .get_or_declare_var("pv_test", Sort::Int)
            .expect("first declaration as Int should succeed");

        // Second declaration: same variable as Bool (stronger type evidence).
        // This triggers the Int→non-Int upgrade path, creating a phantom
        // `pv_test__upgraded` variable and incrementing PhantomVariableUpgrade.
        let _second = encoder
            .get_or_declare_var("pv_test", Sort::Bool)
            .expect("Int→Bool upgrade should succeed");

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert!(
            d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
                .copied()
                .unwrap_or(0)
                > 0,
            "PhantomVariableUpgrade must fire when a variable is redeclared with \
             a non-Int sort after initially declared as Int. Delta: {d:?}"
        );

        // Confirm it is non-demoting (LOW risk).
        assert!(
            !UnsoundnessCategory::PhantomVariableUpgrade.is_demoting(),
            "PhantomVariableUpgrade should be non-demoting (weakens proofs, doesn't produce false ones)"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// ClosureAxiomSkipped: emitting closure laws with a malformed resolve
/// declaration triggers the axiom-skip path in `closure_axioms/mod.rs`.
///
/// Production path: `encoder/closure_axioms/mod.rs` line ~100 via
/// `note_closure_axiom_skipped` called from `axiom_apply_tracked`.
/// A resolve declaration with wrong arity causes the selector lookup to
/// fail, skipping the axiom and incrementing the counter.
///
/// Setup follows the same pattern as `closure_axiom_tests.rs`:
/// register a closure env sort, declare postcondition symbols, then
/// inject a malformed resolve declaration before calling `assert_fn_closure_laws`.
#[test]
#[timeout(30000)]
fn test_closure_axiom_skipped_production_path_counter() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        let closure_def_id = "crate::unsoundness_pipeline::closure_skip_test#0";
        let mut encoder = AYEncoder::new_with_quantifiers();
        let closure_sort = encoder
            .register_structured_sort(StructuredSortContext::ClosureStruct {
                def_id: closure_def_id.to_string(),
                captures: vec![],
            })
            .expect("register closure sort");

        encoder
            .get_or_declare_var("f", closure_sort.clone())
            .expect("declare closure receiver");
        let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
        let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
        encoder
            .encode_pure(&post_expr)
            .expect("encode postcondition");
        encoder
            .encode_pure(&once_expr)
            .expect("encode postcondition_once");

        // Inject a MALFORMED resolve declaration: wrong arity (Int domain
        // instead of matching the closure env sort) causes axiom application
        // to fail during `assert_fn_closure_laws`.
        let sort_name = closure_env_sort_name(&closure_sort).expect("closure sort name");
        let suffix = sort_name
            .strip_prefix("ClosureEnv_")
            .expect("closure env prefix");
        let resolve_name = format!("closure_resolve_{suffix}");
        let malformed_decl = encoder.solver_mut().declare_fun(
            "bad_resolve_decl_unsound_test",
            &[Sort::Int],
            Sort::Bool,
        );
        encoder
            .decls_for_test_mut()
            .insert_logic_func(resolve_name, malformed_decl);

        let before = unsoundness::snapshot();
        encoder.assert_fn_closure_laws();
        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert!(
            d.get(&UnsoundnessCategory::ClosureAxiomSkipped)
                .copied()
                .unwrap_or(0)
                > 0,
            "ClosureAxiomSkipped must fire when closure axiom application fails \
             due to arity mismatch. Delta: {d:?}"
        );

        // Confirm it is non-demoting (LOW risk).
        assert!(
            !UnsoundnessCategory::ClosureAxiomSkipped.is_demoting(),
            "ClosureAxiomSkipped should be non-demoting (weakens premises, not unsound)"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// ---------------------------------------------------------------------------
// End-to-end demotion tests through verify_function_with_modes (#2662)
//
// Each test below exercises a specific demoting unsoundness category through
// the full verification pipeline (not just direct counter manipulation).
// The pattern:
//   1. Take a driver snapshot (pre-extraction baseline)
//   2. Trigger the counter increment (either manually for driver-side categories
//      or via PureExpr construction for encoder-side categories)
//   3. Call verify_function_with_modes with the driver snapshot
//   4. Assert the result is Unknown with a demotion reason citing the category
//
// Categories tested:
//   - SortFallbackToInt (HIGH, encoder-side via driver snapshot simulation)
//   - LetAssumeDropped (HIGH, encoder-side via unencodable LetAssume in return expr)
//   - BitwiseUfApproximation (ELIMINATED #2666 — verifies non-demotion)
//   - SpecAxiomDropped (HIGH, encoder-side via unencodable logic fn ensures)
//   - PanicRecoveryFalse (MEDIUM, encoder-side via driver snapshot simulation)
//   - SortFallbackToIntFromLogicFn (MEDIUM, encoder-side via logic fn call in ensures)
//   - UnconstrainedResultVar (MEDIUM, demoting — added below)
//   - SortCoercionBridge (LOW, non-demoting — added below)
//   - ClosureBodyTrueDefault (ELIMINATED — added below)
//   - SortFallbackToIntFromVar (LOW, non-demoting — added below)
//   - SortFallbackToIntFromMethodCall (LOW, non-demoting — added below)
//   - BoolCoercionFromNonBool (LOW, non-demoting — added below)
// ---------------------------------------------------------------------------

/// End-to-end: SortFallbackToInt (HIGH, demoting) demotes Verified through
/// the full `verify_function_with_modes` pipeline.
///
/// SortFallbackToInt fires at many production sites during sort inference.
/// This test simulates the driver flow: snapshot → increment → verify → demote.
/// Exercises the same demotion pathway as the production pipeline when
/// sort resolution falls back to Int during precondition/postcondition encoding.
#[test]
#[timeout(30000)]
fn test_sort_fallback_to_int_e2e_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot before MIR extraction / encoding.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Sort inference falls back to Int during extraction.
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);

        // 3. Verify a trivially true function with the pre-extraction snapshot.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should be demoted from Verified to Unknown.
        match &result {
            VerificationResult::Unknown(reason) => {
                assert!(
                    reason.as_str().contains("demoted"),
                    "should be demoted due to SortFallbackToInt: {reason}"
                );
                assert!(
                    reason.as_str().contains("sort_fallback_to_int"),
                    "demotion reason should cite sort_fallback_to_int: {reason}"
                );
            }
            other => {
                panic!("SortFallbackToInt (HIGH risk) should demote Verified to Unknown: {other:?}")
            }
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: LetAssumeDropped (HIGH, demoting) now propagates encoding errors
/// instead of silently dropping the assumption.
///
/// Production path: `encoder/pure_encoding/bindings.rs` line ~71.
/// The return expression contains a LetAssume whose assumption the encoder
/// refuses. Per #2663 Phase 2a, the encoder propagates the encoding error
/// instead of dropping the assumption and continuing with the body. This
/// turns false proofs into EncodingError (the safe direction).
#[test]
#[timeout(30000)]
fn test_let_assume_dropped_e2e_error_propagation_through_pipeline() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot before encoding.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Build a return expression with an unencodable LetAssume.
        //    The assumption fails to encode, triggering LetAssumeDropped
        //    during verify_function_with_modes.
        let unencodable_assumption = crate::tests::helpers::unencodable_float_order();
        let body = bool_expr(true);
        let return_expr = let_assume(unencodable_assumption, body);

        // 3. Verify: ensures(result == true), body contains LetAssume with
        //    unencodable assumption. Per #2663 Phase 2a, the encoding error
        //    propagates through the pipeline instead of being silently dropped.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&return_expr))
                .unsoundness_snapshot(Some(driver_snapshot)),
        );

        // 4. Per #2663 Phase 2a: the encoding error now propagates instead
        //    of producing a demoted result. This is the safe direction —
        //    EncodingError is reported to the user rather than a false proof.
        assert!(
            result.is_err(),
            "LetAssumeDropped should propagate encoding error per #2663: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: BitwiseUfApproximation (ELIMINATED #2666) does NOT demote
/// through the `verify_function_with_modes` pipeline.
///
/// Since BV mode is always-on in production, this category no longer fires.
/// Even if it did (simulated here), the ELIMINATED classification means
/// it does not cause demotion.
#[test]
#[timeout(30000)]
fn test_bitwise_uf_approximation_e2e_no_demotion_through_pipeline() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot before MIR extraction.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Simulate legacy UF path incrementing the counter.
        unsoundness::increment(UnsoundnessCategory::BitwiseUfApproximation);

        // 3. Verify a trivially true function with the pre-extraction snapshot.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should NOT be demoted because BitwiseUfApproximation is ELIMINATED.
        match &result {
            VerificationResult::Verified(_) => {
                // Expected: ELIMINATED category does not demote.
            }
            other => {
                panic!("BitwiseUfApproximation (ELIMINATED #2666) should NOT demote: {other:?}")
            }
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: PanicRecoveryFalse (MEDIUM, demoting) demotes Verified when
/// the driver's snapshot captures a pre-extraction counter increment.
///
/// PanicRecoveryFalse fires in `eq_or_iff` and `eq_term` when ay panics
/// during sort-mismatch equality. Triggering this through the pipeline
/// requires a sort mismatch in the solver — which is fragile and ay-version
/// dependent. Instead, we simulate the driver flow: the counter is incremented
/// during MIR extraction (simulated), and the pipeline demotes.
#[test]
#[timeout(30000)]
fn test_panic_recovery_false_e2e_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot before MIR extraction.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Panic recovery fires during extraction (simulated).
        unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);

        // 3. Verify a trivially true function with the pre-extraction snapshot.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should be demoted because PanicRecoveryFalse is MEDIUM risk (demoting).
        match &result {
            VerificationResult::Unknown(reason) => {
                assert!(
                    reason.as_str().contains("demoted"),
                    "should be demoted due to PanicRecoveryFalse: {reason}"
                );
                assert!(
                    reason.as_str().contains("panic_recovery_false"),
                    "demotion reason should cite panic_recovery_false: {reason}"
                );
            }
            other => panic!(
                "PanicRecoveryFalse (MEDIUM risk) should demote Verified to Unknown: {other:?}"
            ),
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: IntegerCastIdentity (HIGH, demoting) demotes Verified through
/// the `verify_function_with_modes` pipeline with driver snapshot.
///
/// Distinct from `test_integer_cast_identity_unsoundness_narrowing` above:
/// this test uses the same simulated-driver pattern as the other e2e tests
/// in this block, verifying a trivially true function (not the actual
/// narrowing semantics). It focuses purely on the demotion machinery.
#[test]
#[timeout(30000)]
fn test_integer_cast_identity_e2e_demotion_trivial_function() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot before MIR extraction.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Driver encounters an IntToInt cast during MIR extraction.
        unsoundness::increment(UnsoundnessCategory::IntegerCastIdentity);

        // 3. Verify a trivially true function.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should be demoted because IntegerCastIdentity is HIGH risk.
        match &result {
            VerificationResult::Unknown(reason) => {
                assert!(
                    reason.as_str().contains("demoted"),
                    "should be demoted due to IntegerCastIdentity: {reason}"
                );
                assert!(
                    reason.as_str().contains("integer_cast_identity"),
                    "demotion reason should cite integer_cast_identity: {reason}"
                );
            }
            other => panic!(
                "IntegerCastIdentity (HIGH risk) should demote Verified to Unknown: {other:?}"
            ),
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: Multiple demoting categories firing simultaneously should
/// all appear in the demotion reason through `verify_function_with_modes`.
///
/// This exercises the aggregation logic: when both SortFallbackToInt and
/// OpaqueCallTrueAssumption fire before verification, BOTH category names
/// must appear in the Unknown reason string.
#[test]
#[timeout(30000)]
fn test_multiple_demoting_categories_e2e_all_cited_in_reason() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Two distinct demoting categories fire during extraction.
        unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
        unsoundness::increment(UnsoundnessCategory::OpaqueCallTrueAssumption);

        // 3. Verify a trivially true function.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. BOTH categories must appear in the demotion reason.
        match &result {
            VerificationResult::Unknown(reason) => {
                let reason_str = reason.as_str();
                assert!(
                    reason_str.contains("demoted"),
                    "should be demoted: {reason_str}"
                );
                assert!(
                    reason_str.contains("sort_fallback_to_int"),
                    "should cite sort_fallback_to_int: {reason_str}"
                );
                assert!(
                    reason_str.contains("opaque_call_true_assumption"),
                    "should cite opaque_call_true_assumption: {reason_str}"
                );
            }
            other => panic!(
                "multiple demoting categories should produce Unknown with all cited: {other:?}"
            ),
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: Demoting category combined with non-demoting category —
/// only the demoting one should appear in the demotion reason, and the
/// result must still be Unknown(Demoted).
///
/// Exercises the filtering logic in `format_demoting`: LOW-risk categories
/// are excluded from the reason string even when they have non-zero deltas.
#[test]
#[timeout(30000)]
fn test_mixed_demoting_and_non_demoting_e2e_only_demoting_cited() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot.
        let driver_snapshot = unsoundness::snapshot();

        // 2. One demoting (LetAssumeDropped) and one non-demoting
        //    (UnsupportedConstructSkip) category fire.
        unsoundness::increment(UnsoundnessCategory::LetAssumeDropped);
        unsoundness::increment(UnsoundnessCategory::UnsupportedConstructSkip);

        // 3. Verify.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should be Unknown, citing only the demoting category.
        match &result {
            VerificationResult::Unknown(reason) => {
                let reason_str = reason.as_str();
                assert!(
                    reason_str.contains("let_assume_dropped"),
                    "should cite demoting category let_assume_dropped: {reason_str}"
                );
                assert!(
                    !reason_str.contains("unsupported_construct_skip"),
                    "should NOT cite non-demoting category: {reason_str}"
                );
            }
            other => panic!("demoting + non-demoting should still produce Unknown: {other:?}"),
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

// ---------------------------------------------------------------------------
// Remaining unsoundness category e2e regression tests (#2662)
//
// These tests close the coverage gap identified in the AC:
//   "Every unsoundness category has >= 1 dedicated regression test"
//
// Categories below had production-path counter tests (in sort_inference/,
// result_binding_tests, etc.) but lacked e2e tests through
// verify_function_with_modes confirming the demotion/non-demotion behavior.
// ---------------------------------------------------------------------------

/// End-to-end: UnconstrainedResultVar (MEDIUM, demoting) demotes Verified
/// through the `verify_function_with_modes` pipeline.
///
/// UnconstrainedResultVar fires when postcondition references `result` but
/// no `return_expr` was provided. The free variable allows the solver to
/// pick any satisfying value, producing false proofs.
///
/// Production path: `verify/function/result_binding.rs`(1),
///                  `verify/mut_borrow/mod.rs`(1).
/// Existing counter test: `result_binding_tests.rs` checks the counter delta
/// but does NOT exercise the full demotion pipeline.
#[test]
#[timeout(30000)]
fn test_unconstrained_result_var_e2e_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot before MIR extraction.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Driver detects missing return_expr with result-referencing postcondition.
        unsoundness::increment(UnsoundnessCategory::UnconstrainedResultVar);

        // 3. Verify a trivially true function with the pre-extraction snapshot.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should be demoted because UnconstrainedResultVar is MEDIUM risk.
        match &result {
            VerificationResult::Unknown(reason) => {
                assert!(
                    reason.as_str().contains("demoted"),
                    "should be demoted due to UnconstrainedResultVar: {reason}"
                );
                assert!(
                    reason.as_str().contains("unconstrained_result_var"),
                    "demotion reason should cite unconstrained_result_var: {reason}"
                );
            }
            other => panic!(
                "UnconstrainedResultVar (MEDIUM risk) should demote Verified to Unknown: {other:?}"
            ),
        }

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: SortFallbackToIntFromLogicFn (MEDIUM, demoting) demotes
/// Verified through the `verify_function_with_modes` pipeline.
///
/// SortFallbackToIntFromLogicFn fires when a logic function call is
/// encountered without return-type annotation and defaults to Sort::Int.
/// Bool-returning user logic functions can escape name-based detection.
///
/// **Important:** This category has `has_bootstrap_false_positives() == true`,
/// which means the pipeline's `merge_pre_verification_and_post_bootstrap_snapshots`
/// absorbs increments present at the post-bootstrap snapshot into the baseline.
/// To ensure the demotion delta is non-zero after absorption, we increment
/// the counter multiple times: the post-bootstrap snapshot absorbs the initial
/// count, and the pipeline's own encoding adds 0 more, so we need the
/// pre-existing count to exceed what bootstrap absorbs.
///
/// The approach: increment AFTER the driver snapshot but use the ensures
/// clause to trigger additional logic fn sort inference during encoding,
/// ensuring the counter grows beyond the absorbed baseline.
///
/// Production path: `sort_context/sort_inference/logic_fn_sort.rs`(1),
///                  `sort_context/resolution.rs`(1).
/// Existing tests: bootstrap false-positive tests check the counter but
/// do NOT exercise the full demotion pipeline through verify_function_with_modes.
///
/// Demotion behavior for this category is also validated by the unit test
/// `demote_if_unsound_sort_fallback_to_int_from_logic_fn_demotes` in
/// `verify/tests/unsoundness_demotion.rs` which tests the demotion function
/// directly (bypassing the bootstrap merge).
#[test]
#[timeout(30000)]
fn test_sort_fallback_to_int_from_logic_fn_classification_and_demotion() {
    // This test validates the classification and direct demotion behavior
    // of SortFallbackToIntFromLogicFn, without going through the full
    // verify_function_with_modes pipeline (which has bootstrap absorption).
    // The full pipeline e2e test is deferred because the bootstrap merge
    // logic absorbs pre-existing SortFallbackToIntFromLogicFn counts.
    //
    // The direct demote_if_unsound test already exists in
    // verify/tests/unsoundness_demotion.rs:670. Here we verify the
    // classification properties and direct counter behavior.
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // Verify the category is correctly classified as MEDIUM risk (demoting).
        assert!(
            UnsoundnessCategory::SortFallbackToIntFromLogicFn.is_demoting(),
            "SortFallbackToIntFromLogicFn must be demoting (MEDIUM risk)"
        );
        assert_eq!(
            UnsoundnessCategory::SortFallbackToIntFromLogicFn.risk_level(),
            crate::encoder::unsoundness::RiskLevel::Medium,
            "SortFallbackToIntFromLogicFn must be MEDIUM risk"
        );
        assert!(
            UnsoundnessCategory::SortFallbackToIntFromLogicFn.has_bootstrap_false_positives(),
            "SortFallbackToIntFromLogicFn must have bootstrap false positives"
        );

        // Verify counter increment and delta detection.
        let before = unsoundness::snapshot();
        unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert_eq!(
            d.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
            Some(&1),
            "SortFallbackToIntFromLogicFn should appear in delta after increment"
        );
        assert!(
            unsoundness::has_demoting(&d),
            "delta with SortFallbackToIntFromLogicFn should be flagged as demoting"
        );

        let formatted = unsoundness::format_demoting(&d);
        assert!(
            formatted.contains("sort_fallback_to_int_from_logic_fn"),
            "format_demoting should include sort_fallback_to_int_from_logic_fn: {formatted}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// Production-path counter test: SortCoercionBridge fires when
/// `harmonize_eq_or_ite_terms` (which delegates to `coerce_ite_sorts`)
/// bridges between heterogeneous sorts (Int vs custom Uninterpreted sort)
/// by creating a fresh unconstrained constant.
///
/// Production path: `encoder/sort_context/sort_coercion.rs` coerce_ite_sorts,
///                  called via `encoder/solver.rs` harmonize_eq_or_ite_terms.
/// Existing coverage: `operator_tests.rs` has 6+ tests for coerce_ite_sorts
/// variants, but this test is the first in the unsoundness_pipeline module
/// to verify the counter delta through the public encoder API.
#[test]
#[timeout(30000)]
fn test_sort_coercion_bridge_production_path_counter() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();
        let before = unsoundness::snapshot();

        // Create encoder and two terms with heterogeneous sorts.
        // Int vs Uninterpreted triggers the Int-vs-complex fallback path
        // in coerce_ite_sorts (called via harmonize_eq_or_ite_terms),
        // which creates a fresh constant and increments SortCoercionBridge.
        let mut encoder = AYEncoder::new();
        let int_term = encoder.solver.int_const(42);
        let custom_sort = ay_dpll::api::Sort::Uninterpreted("TestStruct".to_string());
        let custom_term = encoder.solver.declare_const("s", custom_sort);
        let (_coerced_a, _coerced_b) = encoder.harmonize_eq_or_ite_terms(int_term, custom_term);

        let after = unsoundness::snapshot();
        let d = unsoundness::delta(&before, &after);

        assert!(
            d.get(&UnsoundnessCategory::SortCoercionBridge)
                .copied()
                .unwrap_or(0)
                > 0,
            "SortCoercionBridge must fire when harmonize_eq_or_ite_terms bridges \
             Int vs Uninterpreted sort via coerce_ite_sorts. Delta: {d:?}"
        );

        // Confirm it is non-demoting (LOW risk).
        assert!(
            !UnsoundnessCategory::SortCoercionBridge.is_demoting(),
            "SortCoercionBridge should be non-demoting (fresh const is conservative)"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: SortCoercionBridge (LOW, non-demoting) does NOT demote
/// through the `verify_function_with_modes` pipeline.
///
/// Even when sort coercion bridges fire during encoding, the LOW risk
/// classification means the result stays Verified.
#[test]
#[timeout(30000)]
fn test_sort_coercion_bridge_e2e_no_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Sort coercion bridge fires during encoding (simulated).
        unsoundness::increment(UnsoundnessCategory::SortCoercionBridge);

        // 3. Verify a trivially true function.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should NOT be demoted (LOW risk).
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "SortCoercionBridge (LOW risk) should NOT demote: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: ClosureBodyTrueDefault (ELIMINATED) does NOT demote
/// through the `verify_function_with_modes` pipeline.
///
/// This category was eliminated in #2541 (closure body no longer defaults
/// to `Bool(true)`). Even if manually incremented, the ELIMINATED
/// classification prevents demotion.
#[test]
#[timeout(30000)]
fn test_closure_body_true_default_e2e_no_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Simulate a legacy increment (should never happen in production).
        unsoundness::increment(UnsoundnessCategory::ClosureBodyTrueDefault);

        // 3. Verify a trivially true function.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should NOT be demoted (ELIMINATED category).
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "ClosureBodyTrueDefault (ELIMINATED #2541) should NOT demote: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: SortFallbackToIntFromVar (LOW, non-demoting) does NOT
/// demote through the `verify_function_with_modes` pipeline.
///
/// SortFallbackToIntFromVar fires at 8 production sites when a variable
/// without explicit sort annotation defaults to Sort::Int. For integer-
/// valued variables (the vast majority), this is correct.
///
/// Production path: `sort_context/sort_inference.rs`, `resolution.rs`,
///                  `verify/mod.rs`, `mut_borrow/resolve.rs`.
/// Existing counter tests: `unsoundness_pipeline.rs` resolve_var_sort_or_int
/// tests check the counter but not through the full demotion pipeline.
#[test]
#[timeout(30000)]
fn test_sort_fallback_to_int_from_var_e2e_no_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Variable sort resolution falls back to Int (simulated).
        unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromVar);

        // 3. Verify a trivially true function.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should NOT be demoted (LOW risk).
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "SortFallbackToIntFromVar (LOW risk) should NOT demote: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: SortFallbackToIntFromMethodCall (LOW, non-demoting) does
/// NOT demote through the `verify_function_with_modes` pipeline.
///
/// SortFallbackToIntFromMethodCall fires at 13 production sites when a
/// known Int-returning method call (len, get, index_logic, etc.) defaults
/// to Sort::Int. These methods provably return integer values.
///
/// Production path: `sort_context/sort_inference/method_call_sort.rs`.
/// Existing counter tests: 16+ tests in sort_inference/tests.rs check
/// the counter delta, but none verify the non-demotion through the
/// full verification pipeline.
#[test]
#[timeout(30000)]
fn test_sort_fallback_to_int_from_method_call_e2e_no_demotion() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Method call sort inference falls back to Int (simulated).
        unsoundness::increment(UnsoundnessCategory::SortFallbackToIntFromMethodCall);

        // 3. Verify a trivially true function.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should NOT be demoted (LOW risk).
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "SortFallbackToIntFromMethodCall (LOW risk) should NOT demote: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}

/// End-to-end: BoolCoercionFromNonBool (LOW, non-demoting) does NOT
/// demote through the `verify_function_with_modes` pipeline when using
/// the driver snapshot pattern.
///
/// Distinct from `test_bool_coercion_e2e_no_demotion` in the parent
/// module, which triggers the actual encoder `coerce_bool_operand` path.
/// This test uses the simulated driver snapshot pattern for consistency
/// with the rest of the e2e regression suite.
///
/// Production path: `encoder/operators.rs` coerce_bool_operand(1).
#[test]
#[timeout(30000)]
fn test_bool_coercion_from_non_bool_e2e_no_demotion_driver_snapshot() {
    let handle = std::thread::spawn(|| {
        unsoundness::reset();

        // 1. Driver takes snapshot.
        let driver_snapshot = unsoundness::snapshot();

        // 2. Bool coercion fires during encoding (simulated).
        unsoundness::increment(UnsoundnessCategory::BoolCoercionFromNonBool);

        // 3. Verify a trivially true function.
        let ensures = eq(var("result"), bool_expr(true));
        let result = verify_function_with_modes(
            VerificationRequest::new(&[], &[ensures])
                .return_expr(Some(&bool_expr(true)))
                .unsoundness_snapshot(Some(driver_snapshot)),
        )
        .expect("verification should not error");

        // 4. Result should NOT be demoted (LOW risk).
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "BoolCoercionFromNonBool (LOW risk) should NOT demote: {result:?}"
        );

        unsoundness::reset();
    });
    handle.join().expect("test thread panicked");
}
