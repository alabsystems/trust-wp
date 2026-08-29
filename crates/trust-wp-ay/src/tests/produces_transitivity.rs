// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for `produces` transitivity soundness.

use ntest::timeout;

use super::{super::*, helpers::*};
use crate::ExprSort;

#[test]
#[timeout(30000)]
fn test_produces_transitivity_axiom_semantic() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let ab = view(var("ab"));
    let bc = view(var("bc"));
    let ab_concat_bc = method_call(ab.clone(), "concat", vec![bc.clone()]);

    let p_ab = method_call(var("a"), "produces", vec![ab, var("b")]);
    let p_bc = method_call(var("b"), "produces", vec![bc, var("c")]);
    let p_concat = method_call(var("a"), "produces", vec![ab_concat_bc, var("c")]);

    // Register all involved sort hints up-front. `encode_pure` pre-scan runs
    // only once, so multi-expression semantic checks must batch their hints.
    encoder.register_sort_hints(&[p_ab.clone(), p_bc.clone(), p_concat.clone()]);

    let p_ab_term = encoder
        .encode_pure(&p_ab)
        .expect("premise produces(a, ab, b) should encode");
    let p_bc_term = encoder
        .encode_pure(&p_bc)
        .expect("premise produces(b, bc, c) should encode");
    let p_concat_term = encoder
        .encode_pure(&p_concat)
        .expect("conclusion produces(a, concat(ab, bc), c) should encode");

    let produces_symbols: Vec<_> = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with("method_produces_"))
        .collect();
    assert_eq!(
        produces_symbols.len(),
        1,
        "expected exactly one produces symbol in logic_funcs, got {produces_symbols:?}"
    );
    assert!(
        encoder.decls().has_logic_func("method_produces_3_i_s_i"),
        "expected Seq-specialized produces symbol method_produces_3_i_s_i"
    );

    encoder.assert_term(p_ab_term);
    encoder.assert_term(p_bc_term);
    let neg_conclusion = encoder.solver_mut().not(p_concat_term);
    encoder.assert_term(neg_conclusion);

    let result = encoder.check_sat();
    match &result {
        SolveResult::Sat => {
            let p_ab_val = encoder.solver().value(p_ab_term);
            let p_bc_val = encoder.solver().value(p_bc_term);
            let p_concat_val = encoder.solver().value(p_concat_term);
            panic!(
                "produces transitivity violated with Sat model: p_ab={p_ab_val:?}, \
                 p_bc={p_bc_val:?}, p_concat={p_concat_val:?}"
            );
        }
        SolveResult::Unknown => {
            panic!("produces transitivity must be decided as Unsat, got Unknown")
        }
        SolveResult::Unsat(_) => {}
        other => panic!("produces transitivity must be Unsat, got {other:?}"),
    }
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "produces transitivity forbids premises + negated conclusion; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_produces_transitivity_three_hop_chain_semantic() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let ab = view(var("ab"));
    let bc = view(var("bc"));
    let cd = view(var("cd"));
    let ab_concat_bc = method_call(ab.clone(), "concat", vec![bc.clone()]);
    let ab_concat_bc_concat_cd = method_call(ab_concat_bc.clone(), "concat", vec![cd.clone()]);

    let p_ab = method_call(var("a"), "produces", vec![ab, var("b")]);
    let p_bc = method_call(var("b"), "produces", vec![bc, var("c")]);
    let p_cd = method_call(var("c"), "produces", vec![cd, var("d")]);
    let p_abcd = method_call(var("a"), "produces", vec![ab_concat_bc_concat_cd, var("d")]);

    encoder.register_sort_hints(&[p_ab.clone(), p_bc.clone(), p_cd.clone(), p_abcd.clone()]);

    let p_ab_term = encoder
        .encode_pure(&p_ab)
        .expect("premise produces(a, ab, b) should encode");
    let p_bc_term = encoder
        .encode_pure(&p_bc)
        .expect("premise produces(b, bc, c) should encode");
    let p_cd_term = encoder
        .encode_pure(&p_cd)
        .expect("premise produces(c, cd, d) should encode");
    let p_abcd_term = encoder
        .encode_pure(&p_abcd)
        .expect("conclusion produces(a, concat(concat(ab, bc), cd), d) should encode");

    encoder.assert_term(p_ab_term);
    encoder.assert_term(p_bc_term);
    encoder.assert_term(p_cd_term);
    let neg_conclusion = encoder.solver_mut().not(p_abcd_term);
    encoder.assert_term(neg_conclusion);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "three-hop produces transitivity should forbid premises + negated conclusion; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_produces_reflexivity_holds_for_each_sort_signature() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let int_produces = method_call(var("a"), "produces", vec![view(var("ab")), var("b")]);
    let bool_state = var_with_sort("flag", ExprSort::Bool);
    let bool_refl = method_call(
        bool_state.clone(),
        "produces",
        vec![logic_fn_call("seq_empty", vec![]), bool_state.clone()],
    );

    encoder.register_sort_hints(&[int_produces.clone(), bool_refl.clone()]);

    let int_term = encoder
        .encode_pure(&int_produces)
        .expect("int-sorted produces call should encode");
    let bool_refl_term = encoder
        .encode_pure(&bool_refl)
        .expect("bool-sorted produces reflexive call should encode");

    encoder.assert_term(int_term);
    let neg_bool_refl = encoder.solver_mut().not(bool_refl_term);
    encoder.assert_term(neg_bool_refl);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "produces reflexivity should hold for every declared produces signature; got {result:?}"
    );
}

/// Verify that 4-hop transitivity holds with 4 incrementally-registered calls.
///
/// With 4 ground calls, 3-hop instances cover up to the first 3 hops. The
/// final hop (3-hop-derived-fact + 4th call) requires the quantified
/// transitivity axiom to close the proof. This test verifies that ground
/// instances and quantified axioms cooperate correctly for chains longer
/// than the 3-hop ground ceiling.
#[test]
#[timeout(30000)]
fn test_produces_transitivity_four_hop_incremental() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let ab = view(var("ab"));
    let bc = view(var("bc"));
    let cd = view(var("cd"));
    let de = view(var("de"));

    // Chain: a --ab--> b --bc--> c --cd--> d --de--> e
    let p_ab = method_call(var("a"), "produces", vec![ab.clone(), var("b")]);
    let p_bc = method_call(var("b"), "produces", vec![bc.clone(), var("c")]);
    let p_cd = method_call(var("c"), "produces", vec![cd.clone(), var("d")]);
    let p_de = method_call(var("d"), "produces", vec![de.clone(), var("e")]);

    // Conclusion: a produces(concat(concat(concat(ab, bc), cd), de)) e
    let ab_bc = method_call(ab, "concat", vec![bc]);
    let ab_bc_cd = method_call(ab_bc, "concat", vec![cd]);
    let ab_bc_cd_de = method_call(ab_bc_cd, "concat", vec![de]);
    let p_full = method_call(var("a"), "produces", vec![ab_bc_cd_de, var("e")]);

    encoder.register_sort_hints(&[
        p_ab.clone(),
        p_bc.clone(),
        p_cd.clone(),
        p_de.clone(),
        p_full.clone(),
    ]);

    let p_ab_term = encoder
        .encode_pure(&p_ab)
        .expect("produces(a, ab, b) should encode");
    let p_bc_term = encoder
        .encode_pure(&p_bc)
        .expect("produces(b, bc, c) should encode");
    let p_cd_term = encoder
        .encode_pure(&p_cd)
        .expect("produces(c, cd, d) should encode");
    let p_de_term = encoder
        .encode_pure(&p_de)
        .expect("produces(d, de, e) should encode");
    let p_full_term = encoder
        .encode_pure(&p_full)
        .expect("conclusion produces(a, concat(ab,bc,cd,de), e) should encode");

    encoder.assert_term(p_ab_term);
    encoder.assert_term(p_bc_term);
    encoder.assert_term(p_cd_term);
    encoder.assert_term(p_de_term);
    let neg_conclusion = encoder.solver_mut().not(p_full_term);
    encoder.assert_term(neg_conclusion);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "four-hop produces transitivity should be provable from ground instances; got {result:?}"
    );
}
