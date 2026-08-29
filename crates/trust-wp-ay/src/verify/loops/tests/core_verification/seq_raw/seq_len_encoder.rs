// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Minimal seq_len preservation: `len(produced) == counter` with push_back
/// and counter + 1 effects. Simpler sibling of `seq_len_plus_base_eq_counter`
/// that tests `seq_len` in arithmetic without the additional `base` offset. (#2323)
#[test]
#[timeout(30000)]
fn seq_len_counter_sync_minimal() {
    use trust_wp_core::formula::ExprSort;

    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);
    let counter = PureExpr::Var("counter".to_string(), None);

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "len".to_string(),
        args: vec![],
    };

    // Invariant: len(produced) == counter
    let inv = PureExpr::BinOp(Arc::new(produced_len), BinOp::Eq, Arc::new(counter.clone()));

    let invariants = vec![inv];
    let loop_condition = PureExpr::BinOp(
        Arc::new(counter.clone()),
        BinOp::Lt,
        Arc::new(PureExpr::Int(100)),
    );

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "produced".to_string(),
        PureExpr::MethodCall {
            receiver: Arc::new(produced.clone()),
            method: "push_back".to_string(),
            args: vec![elem],
        },
    );
    body_effect.insert(
        "counter".to_string(),
        PureExpr::BinOp(
            Arc::new(counter.clone()),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let modified_vars: Vec<&str> = vec!["produced", "counter"];
    let config = LoopEncoderConfig::default();

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        BodyEffects::new(&body_effect, &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "len(produced) == counter preservation should verify, got {result:?}"
    );
}

/// Core regression test for #2323: `len(produced) + base == counter`.
/// This invariant requires UF (`seq_len`) in arithmetic (`+ base`), which
/// triggers ay-dpll's theory combination limitation without the auxiliary
/// Int variable bridge.
#[test]
#[timeout(30000)]
fn seq_len_plus_base_eq_counter() {
    use trust_wp_core::formula::ExprSort;

    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);
    let counter = PureExpr::Var("counter".to_string(), None);
    let base = PureExpr::Var("base".to_string(), None);

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "len".to_string(),
        args: vec![],
    };

    // Invariant: len(produced) + base == counter
    let inv = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(produced_len),
            BinOp::Add,
            Arc::new(base.clone()),
        )),
        BinOp::Eq,
        Arc::new(counter.clone()),
    );

    let invariants = vec![inv];
    let loop_condition = PureExpr::BinOp(
        Arc::new(counter.clone()),
        BinOp::Lt,
        Arc::new(PureExpr::Int(100)),
    );

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "produced".to_string(),
        PureExpr::MethodCall {
            receiver: Arc::new(produced.clone()),
            method: "push_back".to_string(),
            args: vec![elem],
        },
    );
    body_effect.insert(
        "counter".to_string(),
        PureExpr::BinOp(
            Arc::new(counter.clone()),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );

    let modified_vars: Vec<&str> = vec!["produced", "counter"];
    let config = LoopEncoderConfig::default();

    let result = verify_preservation_with_config(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        BodyEffects::new(&body_effect, &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "len(produced) + base == counter preservation should verify, got {result:?}"
    );
}

/// Direct encoder test: manually construct the formula that the preservation
/// pipeline SHOULD produce for `len(s) + base == counter` and check UNSAT.
/// This bypasses obligation slicing, sort plans, and the two-phase axiom solve
/// to isolate whether the encoder/solver can handle the arithmetic.
#[test]
#[timeout(30000)]
fn direct_encoder_seq_len_counter_base_unsat() {
    use trust_wp_core::formula::ExprSort;

    // Set up a loop encoder with the invariant and effects as extra expressions.
    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);
    let counter = PureExpr::Var("counter".to_string(), None);
    let base = PureExpr::Var("base".to_string(), None);

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "len".to_string(),
        args: vec![],
    };

    let inv = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(produced_len.clone()),
            BinOp::Add,
            Arc::new(base.clone()),
        )),
        BinOp::Eq,
        Arc::new(counter.clone()),
    );

    let push_back_effect = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "push_back".to_string(),
        args: vec![elem],
    };
    let counter_effect = PureExpr::BinOp(
        Arc::new(counter.clone()),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    let effects_vec: Vec<PureExpr> = vec![push_back_effect.clone(), counter_effect.clone()];
    let config = LoopEncoderConfig::default();
    let mut encoder = setup_loop_encoder(&[inv.clone()], None, &[&effects_vec], &config)
        .expect("encoder setup should succeed");

    // 1. Assert current invariant: seq_len(produced) + base = counter
    let inv_term = encoder.encode_pure(&inv).expect("inv encode");
    encoder.assert_term(inv_term);

    // 2. Encode body effects
    let push_term = encoder.encode_pure(&push_back_effect).expect("push encode");
    let counter_plus_1 = encoder
        .encode_pure(&counter_effect)
        .expect("counter encode");

    // 3. Declare prime variables
    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let produced_prime = encoder
        .get_or_declare_var("produced_prime", seq_sort)
        .expect("produced_prime");
    let counter_prime = encoder
        .get_or_declare_var("counter_prime", ay_dpll::api::Sort::Int)
        .expect("counter_prime");

    // 4. Constrain primes
    encoder.assert_eq(produced_prime, push_term);
    encoder.assert_eq(counter_prime, counter_plus_1);

    // 5. Assert Seq ground instances
    encoder.assert_seq_ground_instances(
        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
    );

    // 6. Build primed invariant: seq_len(produced_prime) + base == counter_prime
    let produced_prime_var = PureExpr::Var("produced_prime".to_string(), Some(ExprSort::Seq));
    let counter_prime_var = PureExpr::Var("counter_prime".to_string(), None);
    let primed_inv = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(produced_prime_var),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Add,
            Arc::new(base),
        )),
        BinOp::Eq,
        Arc::new(counter_prime_var),
    );
    encoder.register_sort_hints(std::slice::from_ref(&primed_inv));

    // 7. Negate primed invariant
    let primed_term = encoder.encode_pure(&primed_inv).expect("primed inv encode");
    let negated = encoder.solver_mut().not(primed_term);
    encoder.assert_term(negated);

    // 8. Check UNSAT
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "direct encoder formula should be UNSAT, got {result:?}"
    );
}

/// Diagnostic variant: same as `direct_encoder_seq_len_counter_base_unsat` but
/// explicitly asserts the congruence result `seq_len(produced_prime) = seq_len(produced) + 1`.
/// If this passes and the parent test fails, the issue is ay-dpll congruence propagation
/// not reaching the LIA solver.
#[test]
#[timeout(30000)]
fn direct_encoder_with_explicit_congruence_hint() {
    use trust_wp_core::formula::ExprSort;

    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);
    let counter = PureExpr::Var("counter".to_string(), None);
    let base = PureExpr::Var("base".to_string(), None);

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "len".to_string(),
        args: vec![],
    };

    let inv = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(produced_len.clone()),
            BinOp::Add,
            Arc::new(base.clone()),
        )),
        BinOp::Eq,
        Arc::new(counter.clone()),
    );

    let push_back_effect = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "push_back".to_string(),
        args: vec![elem],
    };
    let counter_effect = PureExpr::BinOp(
        Arc::new(counter.clone()),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    let effects_vec: Vec<PureExpr> = vec![push_back_effect.clone(), counter_effect.clone()];
    let config = LoopEncoderConfig::default();
    let mut encoder = setup_loop_encoder(&[inv.clone()], None, &[&effects_vec], &config)
        .expect("encoder setup should succeed");

    // 1. Assert invariant
    let inv_term = encoder.encode_pure(&inv).expect("inv encode");
    encoder.assert_term(inv_term);

    // 2. Encode body effects
    let push_term = encoder.encode_pure(&push_back_effect).expect("push encode");
    let counter_plus_1 = encoder
        .encode_pure(&counter_effect)
        .expect("counter encode");

    // 3. Declare primes
    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let produced_prime = encoder
        .get_or_declare_var("produced_prime", seq_sort)
        .expect("produced_prime");
    let counter_prime = encoder
        .get_or_declare_var("counter_prime", ay_dpll::api::Sort::Int)
        .expect("counter_prime");

    // 4. Constrain primes
    encoder.assert_eq(produced_prime, push_term);
    encoder.assert_eq(counter_prime, counter_plus_1);

    // 5. Seq ground instances
    encoder.assert_seq_ground_instances(
        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
    );

    // 6. EXPLICIT CONGRUENCE HINT: seq_len(produced_prime) = seq_len(produced) + 1
    // This manually provides what ay-dpll congruence closure SHOULD derive from:
    //   produced_prime = push_back(produced, elem)
    //   seq_len(push_back(produced, elem)) = seq_len(produced) + 1  (shape constraint)
    let produced_prime_len_expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var(
            "produced_prime".to_string(),
            Some(ExprSort::Seq),
        )),
        method: "len".to_string(),
        args: vec![],
    };
    let produced_len_expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("produced".to_string(), Some(ExprSort::Seq))),
        method: "len".to_string(),
        args: vec![],
    };
    let congruence_hint = PureExpr::BinOp(
        Arc::new(produced_prime_len_expr),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(produced_len_expr),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    encoder.register_sort_hints(std::slice::from_ref(&congruence_hint));
    let hint_term = encoder
        .encode_pure(&congruence_hint)
        .expect("congruence hint encode");
    encoder.assert_term(hint_term);

    // 7. Negate primed invariant
    let produced_prime_var = PureExpr::Var("produced_prime".to_string(), Some(ExprSort::Seq));
    let counter_prime_var = PureExpr::Var("counter_prime".to_string(), None);
    let primed_inv = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(produced_prime_var),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Add,
            Arc::new(base),
        )),
        BinOp::Eq,
        Arc::new(counter_prime_var),
    );
    encoder.register_sort_hints(std::slice::from_ref(&primed_inv));
    let primed_term = encoder.encode_pure(&primed_inv).expect("primed inv encode");
    let negated = encoder.solver_mut().not(primed_term);
    encoder.assert_term(negated);

    // 8. Check UNSAT — should pass with explicit congruence hint
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "with explicit congruence hint should be UNSAT, got {result:?}"
    );
}
