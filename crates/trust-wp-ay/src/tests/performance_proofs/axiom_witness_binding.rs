// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// Axiom witness binding: O(S × M × arity) eager fn_mut_once scaling
// =============================================================================

/// Measures eager fn_mut_once witness instantiation scaling with many ground
/// `postcondition_once` calls.
///
/// `assert_eager_fn_mut_once_instantiations` iterates over ground once-calls
/// and, for each compatible postcondition_mut symbol, builds
/// `witness(self,args,...)` and `postcondition_mut(...)` terms. With fixed
/// arity and fixed matching symbol count, scaling in ground-call count should
/// be linear.
///
/// Re: performance_proofs phase — axiom witness binding O(S × M × arity)
#[test]
#[timeout(30000)]
fn test_axiom_witness_instantiation_ground_call_scaling() {
    use std::time::Instant;

    use trust_wp_core::formula::ExprSort;

    let small_calls = 8;
    let large_calls = 32;
    let rounds = 5;
    let iters = 80;

    fn run_instantiations(ground_calls: usize, iters: usize) -> std::time::Duration {
        let start = Instant::now();
        for iter in 0..iters {
            let mut encoder = AYEncoder::new_with_quantifiers();

            // Register one once signature and two mut signatures with different
            // res_state sorts so M=2 matching candidates per ground call.
            let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
            let mut_int_state = method_call(
                var("f"),
                "postcondition_mut",
                vec![var("x"), var("s_int"), var("r")],
            );
            let mut_bool_state = method_call(
                var("f"),
                "postcondition_mut",
                vec![var("x"), var_with_sort("s_bool", ExprSort::Bool), var("r")],
            );
            encoder
                .encode_pure(&once_expr)
                .expect("postcondition_once signature should encode");
            encoder
                .encode_pure(&mut_int_state)
                .expect("int-state postcondition_mut signature should encode");
            encoder
                .encode_pure(&mut_bool_state)
                .expect("bool-state postcondition_mut signature should encode");
            encoder.assert_fn_mut_once_law();

            if iter == 0 {
                assert!(
                    encoder
                        .decls()
                        .has_logic_func("fn_mut_once_witness_3_i_i_i"),
                    "int-state witness should be declared by fn_mut_once law"
                );
                assert!(
                    encoder
                        .decls()
                        .has_logic_func("fn_mut_once_witness_3_i_i_i_b"),
                    "bool-state witness should be declared by fn_mut_once law"
                );
            }

            let requires: Vec<PureExpr> = (0..ground_calls)
                .map(|i| {
                    method_call(
                        var(&format!("f_{iter}_{i}")),
                        "postcondition_once",
                        vec![var(&format!("x_{iter}_{i}")), var(&format!("r_{iter}_{i}"))],
                    )
                })
                .collect();
            encoder
                .assert_eager_fn_mut_once_instantiations(&requires)
                .expect("eager fn_mut_once instantiation should succeed");
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_instantiations(small_calls, iters);
    let _ = run_instantiations(large_calls, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_instantiations(small_calls, iters);
        let large_time = run_instantiations(large_calls, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(S): ratio(32/8) ~= 4x. For O(S²): ratio ~= 16x.
    assert!(
        min_ratio < 14.0,
        "axiom witness instantiation scaling ratio ({large_calls}/{small_calls} calls) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 14x, eager fn_mut_once witness binding is superlinear in call count."
    );

    eprintln!(
        "axiom_witness_instantiation_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(S) expect ~4x for S={small_calls}→{large_calls}, M=2, arity=3)"
    );
}

/// Measures eager fn_mut_once witness instantiation scaling in arity with
/// fixed ground-call count (S) and fixed matching symbol count (M=2).
///
/// `assert_eager_fn_mut_once_instantiations` builds witness args and mut args
/// per match, doing O(arity) work per ground-call/symbol pair. This test keeps
/// S and M fixed and scales arity from 3 to 6 to validate the linear factor.
///
/// Re: performance_proofs phase — axiom witness binding O(S × M × arity)
#[test]
#[timeout(30000)]
fn test_axiom_witness_instantiation_arity_scaling() {
    use std::time::Instant;

    use trust_wp_core::formula::ExprSort;

    let small_arity = 3;
    let large_arity = 6;
    let ground_calls = 16;
    let rounds = 5;
    let iters = 70;

    fn run_instantiations_with_arity(
        once_arity: usize,
        ground_calls: usize,
        iters: usize,
    ) -> std::time::Duration {
        assert!(
            once_arity >= 3,
            "once arity must include receiver + arg + result"
        );
        let start = Instant::now();
        for iter in 0..iters {
            let mut encoder = AYEncoder::new_with_quantifiers();
            let user_arg_count = once_arity - 2;

            let mut once_args: Vec<PureExpr> = (0..user_arg_count)
                .map(|idx| var(&format!("x{idx}")))
                .collect();
            once_args.push(var("r"));
            let once_expr = method_call(var("f"), "postcondition_once", once_args);

            let mut mut_int_args: Vec<PureExpr> = (0..user_arg_count)
                .map(|idx| var(&format!("x{idx}")))
                .collect();
            mut_int_args.push(var("s_int"));
            mut_int_args.push(var("r"));
            let mut_int_state = method_call(var("f"), "postcondition_mut", mut_int_args);

            let mut mut_bool_args: Vec<PureExpr> = (0..user_arg_count)
                .map(|idx| var(&format!("x{idx}")))
                .collect();
            mut_bool_args.push(var_with_sort("s_bool", ExprSort::Bool));
            mut_bool_args.push(var("r"));
            let mut_bool_state = method_call(var("f"), "postcondition_mut", mut_bool_args);

            encoder
                .encode_pure(&once_expr)
                .expect("postcondition_once signature should encode");
            encoder
                .encode_pure(&mut_int_state)
                .expect("int-state postcondition_mut signature should encode");
            encoder
                .encode_pure(&mut_bool_state)
                .expect("bool-state postcondition_mut signature should encode");
            encoder.assert_fn_mut_once_law();

            let requires: Vec<PureExpr> = (0..ground_calls)
                .map(|call_idx| {
                    let mut args: Vec<PureExpr> = (0..user_arg_count)
                        .map(|arg_idx| var(&format!("x_{iter}_{call_idx}_{arg_idx}")))
                        .collect();
                    args.push(var(&format!("r_{iter}_{call_idx}")));
                    method_call(
                        var(&format!("f_{iter}_{call_idx}")),
                        "postcondition_once",
                        args,
                    )
                })
                .collect();
            encoder
                .assert_eager_fn_mut_once_instantiations(&requires)
                .expect("eager fn_mut_once instantiation should succeed");
        }
        start.elapsed()
    }

    // Warm up
    let _ = run_instantiations_with_arity(small_arity, ground_calls, iters);
    let _ = run_instantiations_with_arity(large_arity, ground_calls, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_instantiations_with_arity(small_arity, ground_calls, iters);
        let large_time = run_instantiations_with_arity(large_arity, ground_calls, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(arity): ratio(6/3) ~= 2x. For O(arity²): ratio ~= 4x.
    // Threshold 3.5x catches O(arity²) regression (4x > 3.5x) while leaving
    // headroom for O(arity) with system variance (observed: ~1.5x).
    assert!(
        min_ratio < 3.5,
        "axiom witness instantiation arity scaling ({large_arity}/{small_arity}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 3.5x, eager fn_mut_once binding has regressed toward O(arity²)."
    );

    eprintln!(
        "axiom_witness_instantiation_arity_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(arity) expect ~2x for arity={small_arity}→{large_arity}, S={ground_calls}, M=2)"
    );
}

/// Measures eager fn_mut_once witness instantiation scaling in matching symbol
/// count (M) with fixed arity and fixed ground-call count.
///
/// The implementation loops over all matching postcondition_mut signatures for
/// each ground postcondition_once call. With fixed S and arity, runtime should
/// scale linearly in M.
///
/// Re: performance_proofs phase — axiom witness binding O(S × M × arity)
#[test]
#[timeout(30000)]
fn test_axiom_witness_instantiation_matching_symbol_scaling() {
    use std::time::Instant;

    use trust_wp_core::formula::ExprSort;

    let small_m = 1;
    let large_m = 2;
    let ground_calls = 24;
    let rounds = 5;
    let iters = 90;

    fn run_instantiations_with_matches(
        matching_symbols: usize,
        ground_calls: usize,
        iters: usize,
    ) -> std::time::Duration {
        assert!(
            matching_symbols == 1 || matching_symbols == 2,
            "this test supports M in {{1,2}}"
        );

        let start = Instant::now();
        for iter in 0..iters {
            let mut encoder = AYEncoder::new_with_quantifiers();

            let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
            let mut_int_state = method_call(
                var("f"),
                "postcondition_mut",
                vec![var("x"), var("s_int"), var("r")],
            );
            encoder
                .encode_pure(&once_expr)
                .expect("postcondition_once signature should encode");
            encoder
                .encode_pure(&mut_int_state)
                .expect("int-state postcondition_mut signature should encode");

            if matching_symbols == 2 {
                let mut_bool_state = method_call(
                    var("f"),
                    "postcondition_mut",
                    vec![var("x"), var_with_sort("s_bool", ExprSort::Bool), var("r")],
                );
                encoder
                    .encode_pure(&mut_bool_state)
                    .expect("bool-state postcondition_mut signature should encode");
            }

            encoder.assert_fn_mut_once_law();

            if iter == 0 {
                assert!(
                    encoder
                        .decls()
                        .has_logic_func("fn_mut_once_witness_3_i_i_i"),
                    "int-state witness should be present"
                );
                assert_eq!(
                    encoder
                        .decls()
                        .has_logic_func("fn_mut_once_witness_3_i_i_i_b"),
                    matching_symbols == 2,
                    "bool-state witness presence should match M"
                );
            }

            let requires: Vec<PureExpr> = (0..ground_calls)
                .map(|call_idx| {
                    method_call(
                        var(&format!("f_{iter}_{call_idx}")),
                        "postcondition_once",
                        vec![
                            var(&format!("x_{iter}_{call_idx}")),
                            var(&format!("r_{iter}_{call_idx}")),
                        ],
                    )
                })
                .collect();
            encoder
                .assert_eager_fn_mut_once_instantiations(&requires)
                .expect("eager fn_mut_once instantiation should succeed");
        }

        start.elapsed()
    }

    // Warm up
    let _ = run_instantiations_with_matches(small_m, ground_calls, iters);
    let _ = run_instantiations_with_matches(large_m, ground_calls, iters);

    let mut ratios = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let small_time = run_instantiations_with_matches(small_m, ground_calls, iters);
        let large_time = run_instantiations_with_matches(large_m, ground_calls, iters);
        let small_secs = small_time.as_secs_f64().max(1e-12);
        ratios.push(large_time.as_secs_f64() / small_secs);
    }

    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min_ratio = ratios[0];

    // For O(M): ratio(2/1) ~= 2x. For O(M²): ratio ~= 4x.
    // Threshold 6x catches superlinear scaling while tolerating runtime variance.
    assert!(
        min_ratio < 6.0,
        "axiom witness instantiation matching-symbol scaling ({large_m}/{small_m}) = \
         {min_ratio:.1}x (rounds: {ratios:.1?}). \
         If > 6x, eager fn_mut_once binding is superlinear in matching symbol count."
    );

    eprintln!(
        "axiom_witness_instantiation_matching_symbol_scaling: min ratio={min_ratio:.1}x, \
         all rounds={ratios:.1?} \
         (O(M) expect ~2x for M={small_m}→{large_m}, S={ground_calls}, arity=3)"
    );
}
