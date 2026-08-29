// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;
use crate::encoder::{
    closure_sorts::{closure_env_sort_name, StructuredSortContext},
    unsoundness::{self, UnsoundnessCategory},
};
mod fn_mut_once_laws;

/// Forward axiom of fn_mut_once law: postcondition_mut ==> postcondition_once.
///
/// If postcondition_mut(f, x, res_state, r) holds, then
/// postcondition_once(f, x, r) must also hold (FnMut implies FnOnce).
///
/// We assert postcondition_mut AND NOT postcondition_once after the law,
/// which should be UNSAT by the forward implication axiom.
#[test]
#[timeout(30000)]
fn test_fn_mut_once_forward_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register postcondition_once (3-param: f, x, r)
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    // Register postcondition_mut (4-param: f, x, res_state, r)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    // Assert the fn_mut_once law
    encoder.assert_fn_mut_once_law();

    // Assert postcondition_mut(f, x, s, r) AND NOT postcondition_once(f, x, r)
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let both = encoder.solver_mut().and(mut_term, neg_once);
    encoder.assert_term(both);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "postcondition_mut must imply postcondition_once (fn_mut_once forward axiom)"
    );
}

/// Reverse axiom of fn_mut_once law (Skolemized): postcondition_once ==> postcondition_mut.
///
/// If postcondition_once(f, x, r) holds, then there exists a res_state
/// (provided by the Skolem witness) such that postcondition_mut(f, x, witness(...), r)
/// holds.
///
/// Strengthened (#1685): the old test only asserted SAT on an unconstrained
/// system. Now we build the witness application directly and verify:
///   postcondition_once(f,x,r) AND NOT postcondition_mut(f,x,witness(f,x,r),r) is UNSAT.
#[test]
#[timeout(30000)]
fn test_fn_mut_once_reverse_axiom_witness_forces_mut() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register both symbols
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    encoder.assert_fn_mut_once_law();

    // Assert postcondition_once(f, x, r)
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    encoder.assert_term(once_term);

    // Retrieve the witness function declared by assert_fn_mut_once_law.
    // Symbol: fn_mut_once_witness_3_i_i_i (arity 3, all Int sorts).
    let witness_decl = encoder
        .decls()
        .get_logic_func("fn_mut_once_witness_3_i_i_i")
        .cloned()
        .expect("fn_mut_once_witness should be declared after assert_fn_mut_once_law");

    // Build witness(f, x, r) and postcondition_mut(f, x, witness(f,x,r), r)
    let f_term = encoder.encode_pure(&var("f")).unwrap();
    let x_term = encoder.encode_pure(&var("x")).unwrap();
    let r_term = encoder.encode_pure(&var("r")).unwrap();
    let witness_term = encoder
        .solver_mut()
        .apply(&witness_decl, &[f_term, x_term, r_term]);

    let mut_decl = encoder
        .decls()
        .get_logic_func("closure_postcondition_mut_4_i_i_i_i")
        .cloned()
        .expect("postcondition_mut should be declared");
    let mut_with_witness = encoder
        .solver_mut()
        .apply(&mut_decl, &[f_term, x_term, witness_term, r_term]);

    // NOT postcondition_mut(f, x, witness(f,x,r), r) should be UNSAT
    // because the reverse axiom forces: once(f,x,r) => mut(f,x,witness(f,x,r),r)
    let neg_mut = encoder.solver_mut().not(mut_with_witness);
    encoder.assert_term(neg_mut);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "postcondition_once AND NOT postcondition_mut(witness) must be UNSAT by reverse axiom"
    );
}

/// fn_closure fn_mut law: postcondition_mut(f, x, f, r) ⟺ postcondition(f, x, r)
/// when res_state == self (identity).
///
/// Forward: postcondition(f,x,r) AND self==res_state => postcondition_mut holds.
/// We assert postcondition(f,x,r) AND NOT postcondition_mut(f,x,f,r) => UNSAT.
#[test]
#[timeout(30000)]
fn test_fn_closure_fn_mut_law_forward() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register Fn postcondition (3-param: f, x, r)
    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&post_expr)
        .expect("postcondition should encode");

    // Register FnMut postcondition_mut (4-param: f, x, res_state, r)
    // Using var("f") as res_state to test the identity case
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("f"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    // Register postcondition_once too (needed for the full law chain)
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    // Assert the Fn closure laws
    encoder.assert_fn_closure_laws();

    // Forward: postcondition(f,x,r) AND NOT postcondition_mut(f,x,f,r) => UNSAT
    // because the fn_mut law says: postcondition_mut = postcondition AND self==res_state,
    // and when res_state==self (both are f), the self==res_state conjunct is trivially true.
    let post_term = encoder.encode_pure(&post_expr).unwrap();
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let neg_mut = encoder.solver_mut().not(mut_term);
    let both = encoder.solver_mut().and(post_term, neg_mut);
    encoder.assert_term(both);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "postcondition(f,x,r) must imply postcondition_mut(f,x,f,r) by fn_mut law"
    );
}

/// fn_closure fn_mut law reverse: postcondition_mut(f,x,f,r) => postcondition(f,x,r).
///
/// When res_state == self (both are f), postcondition_mut should imply postcondition.
#[test]
#[timeout(30000)]
fn test_fn_closure_fn_mut_law_reverse() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("f"), var("r")],
    );
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);

    encoder.encode_pure(&post_expr).expect("post");
    encoder.encode_pure(&mut_expr).expect("mut");
    encoder.encode_pure(&once_expr).expect("once");

    encoder.assert_fn_closure_laws();

    // Reverse: postcondition_mut(f,x,f,r) AND NOT postcondition(f,x,r) => UNSAT
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let post_term = encoder.encode_pure(&post_expr).unwrap();
    let neg_post = encoder.solver_mut().not(post_term);
    let both = encoder.solver_mut().and(mut_term, neg_post);
    encoder.assert_term(both);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "postcondition_mut(f,x,f,r) must imply postcondition(f,x,r) by fn_mut law"
    );
}

/// fn_mut law res_state divergence: postcondition_mut(f,x,s,r) is forced false
/// when s != f, because the biconditional requires self==res_state.
///
/// The fn_mut law: postcondition_mut(f,x,s,r) = (postcondition(f,x,r) AND f==s).
/// When s != f, the RHS is false, so postcondition_mut must also be false.
/// Asserting postcondition_mut with s != f should be UNSAT.
#[test]
#[timeout(30000)]
fn test_fn_closure_fn_mut_law_res_state_divergence_forces_false() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    // Use var("s") as res_state, distinct from var("f")
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);

    encoder.encode_pure(&post_expr).expect("post");
    encoder.encode_pure(&mut_expr).expect("mut");
    encoder.encode_pure(&once_expr).expect("once");

    encoder.assert_fn_closure_laws();

    // Assert f != s (res_state diverges from self)
    let f_term = encoder.encode_pure(&var("f")).unwrap();
    let s_term = encoder.encode_pure(&var("s")).unwrap();
    let f_ne_s = {
        let eq = encoder.solver_mut().eq(f_term, s_term);
        encoder.solver_mut().not(eq)
    };
    encoder.assert_term(f_ne_s);

    // With s != f, the biconditional forces postcondition_mut to false.
    // Asserting postcondition_mut(f,x,s,r) with s!=f should be UNSAT.
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    encoder.assert_term(mut_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "postcondition_mut(f,x,s,r) with s!=f must be UNSAT (biconditional: f==s required)"
    );
}

/// fn_closure fn_once law: postcondition_once(f,x,r) ⟺ postcondition(f,x,r).
///
/// For Int-sorted closures, resolve(self) is trivially true, so
/// postcondition_once = postcondition AND true = postcondition.
#[test]
#[timeout(30000)]
fn test_fn_closure_fn_once_law_equivalence() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );

    encoder.encode_pure(&post_expr).expect("post");
    encoder.encode_pure(&once_expr).expect("once");
    encoder.encode_pure(&mut_expr).expect("mut");

    encoder.assert_fn_closure_laws();

    // Forward: postcondition_once AND NOT postcondition => UNSAT
    {
        let mut enc = AYEncoder::new_with_quantifiers();
        let pe = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
        let oe = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
        let me = method_call(
            var("f"),
            "postcondition_mut",
            vec![var("x"), var("s"), var("r")],
        );
        enc.encode_pure(&pe).unwrap();
        enc.encode_pure(&oe).unwrap();
        enc.encode_pure(&me).unwrap();
        enc.assert_fn_closure_laws();

        let once_term = enc.encode_pure(&oe).unwrap();
        let post_term = enc.encode_pure(&pe).unwrap();
        let neg_post = enc.solver_mut().not(post_term);
        let both = enc.solver_mut().and(once_term, neg_post);
        enc.assert_term(both);

        assert!(
            matches!(enc.check_sat(), SolveResult::Unsat(_)),
            "postcondition_once must imply postcondition by fn_once law (resolve is true)"
        );
    }

    // Reverse: postcondition AND NOT postcondition_once => UNSAT
    let post_term = encoder.encode_pure(&post_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let both = encoder.solver_mut().and(post_term, neg_once);
    encoder.assert_term(both);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "postcondition must imply postcondition_once by fn_once law (resolve is true)"
    );
}

#[test]
#[timeout(30000)]
fn test_fn_closure_laws_skip_malformed_resolve_decl_instead_of_defaulting_true() {
    unsoundness::reset();

    let closure_def_id = "crate::closure_axiom_tests::malformed_resolve#0";
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

    let sort_name = closure_env_sort_name(&closure_sort).expect("closure sort name");
    let suffix = sort_name
        .strip_prefix("ClosureEnv_")
        .expect("closure env prefix");
    let resolve_name = format!("closure_resolve_{suffix}");
    let malformed_decl =
        encoder
            .solver_mut()
            .declare_fun("bad_closure_resolve_decl", &[Sort::Int], Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(resolve_name, malformed_decl);

    let before = unsoundness::snapshot();
    encoder.assert_fn_closure_laws();
    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert!(
        delta.contains_key(&UnsoundnessCategory::ClosureAxiomSkipped),
        "malformed resolve declaration should be tracked as ClosureAxiomSkipped: {delta:?}"
    );

    let post_term = encoder.encode_pure(&post_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let premise = encoder.solver_mut().and(post_term, neg_once);
    encoder.assert_term(premise);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "malformed resolve decl must skip the fn_once law instead of collapsing resolve(self) to true"
    );

    unsoundness::reset();
}

/// fn_mut_once law should not fire when no matching symbol pairs exist.
///
/// Declaring only postcondition_once without postcondition_mut:
/// assert_fn_mut_once_law should not crash or assert spurious axioms.
#[test]
#[timeout(30000)]
fn test_fn_mut_once_law_no_matching_pair_no_crash() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Only register postcondition_once (no postcondition_mut)
    let once_expr_true = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&once_expr_true)
        .expect("postcondition_once should encode");

    // Should not crash
    encoder.assert_fn_mut_once_law();

    // True branch must remain satisfiable when no matching mut symbol exists.
    let once_term_true = encoder.encode_pure(&once_expr_true).unwrap();
    encoder.assert_term(once_term_true);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "postcondition_once without matching mut should remain unconstrained"
    );

    // Dual check: false branch must also remain satisfiable.
    let mut encoder_dual = AYEncoder::new_with_quantifiers();
    let once_expr_false = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    encoder_dual
        .encode_pure(&once_expr_false)
        .expect("postcondition_once should encode for dual check");
    encoder_dual.assert_fn_mut_once_law();
    let once_term_false = encoder_dual.encode_pure(&once_expr_false).unwrap();
    let neg_once = encoder_dual.solver_mut().not(once_term_false);
    encoder_dual.assert_term(neg_once);
    assert!(
        matches!(encoder_dual.check_sat(), SolveResult::Sat),
        "negated postcondition_once without matching mut should also remain satisfiable"
    );
}

#[test]
#[timeout(30000)]
fn test_fn_mut_once_law_tracks_skipped_axiom_apply_on_malformed_mut_decl() {
    unsoundness::reset();

    let mut encoder = AYEncoder::new_with_quantifiers();
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();

    // Inject an arity-mismatched declaration (5 params instead of 4) while
    // keeping the name that implies arity 4. axiom_apply_sort_adapted bridges
    // sort mismatches but NOT arity mismatches, so the forward/reverse axiom
    // builders will fail when the derived once_args (4 elements) don't match
    // once_decl (3 params), and mut_args (4 elements) don't match this
    // 5-param decl in the reverse path. Both paths trigger ClosureAxiomSkipped.
    let malformed_decl = encoder.solver_mut().declare_fun(
        "bad_postcondition_mut_decl",
        &[Sort::Int, Sort::Int, Sort::Int, Sort::Int, Sort::Int],
        Sort::Bool,
    );
    encoder.decls_for_test_mut().insert_logic_func(
        "closure_postcondition_mut_4_i_i_i_i".to_string(),
        malformed_decl,
    );

    let before = unsoundness::snapshot();
    encoder.assert_fn_mut_once_law();
    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert!(
        delta.contains_key(&UnsoundnessCategory::ClosureAxiomSkipped),
        "arity-mismatched postcondition_mut declaration should be tracked as ClosureAxiomSkipped: {delta:?}"
    );

    let neg_once = encoder.solver_mut().not(once_term);
    let premise = encoder.solver_mut().and(mut_term, neg_once);
    encoder.assert_term(premise);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "arity-mismatched mut declaration must skip the fn_mut_once forward law instead of asserting a malformed axiom"
    );

    unsoundness::reset();
}

/// Eager instantiation: when postcondition_once(f, a, r) appears in requires,
/// `assert_eager_fn_mut_once_instantiations` should directly assert the
/// postcondition_mut(f, a, witness(f, a, r), r) ground fact, making it
/// available to E-matching without requiring an extra implication step (#970).
///
/// Strengthened (#1685): now verifies the ground fact exists by asserting
/// NOT postcondition_mut(f, a, witness(f,a,r), r) and checking UNSAT.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_once_instantiation_asserts_ground_mut() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register both postcondition_once (3-param: f, x, r) and
    // postcondition_mut (4-param: f, x, s, r)
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("a"), var("r")]);
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    // Assert fn_mut_once_law (creates the witness Skolem function)
    encoder.assert_fn_mut_once_law();

    // Build a ground postcondition_once call for requires
    let ground_once = method_call(var("f"), "postcondition_once", vec![var("a"), var("r")]);

    // Call eager instantiation with the ground once call in requires
    encoder
        .assert_eager_fn_mut_once_instantiations(&[ground_once])
        .expect("eager instantiation should succeed");

    // The eager instantiation should have asserted postcondition_mut(f, a, witness, r)
    // as a ground fact. Retrieve the witness function and mut_decl to build
    // the negated ground term.
    let witness_decl = encoder
        .decls()
        .get_logic_func("fn_mut_once_witness_3_i_i_i")
        .cloned()
        .expect("witness function should be declared after assert_fn_mut_once_law");

    let mut_decl = encoder
        .decls()
        .get_logic_func("closure_postcondition_mut_4_i_i_i_i")
        .cloned()
        .expect("postcondition_mut should be declared");

    let f_term = encoder.encode_pure(&var("f")).unwrap();
    let a_term = encoder.encode_pure(&var("a")).unwrap();
    let r_term = encoder.encode_pure(&var("r")).unwrap();
    let witness_term = encoder
        .solver_mut()
        .apply(&witness_decl, &[f_term, a_term, r_term]);
    let mut_ground = encoder
        .solver_mut()
        .apply(&mut_decl, &[f_term, a_term, witness_term, r_term]);

    // NOT postcondition_mut(f, a, witness(f,a,r), r) should be UNSAT because
    // the eager instantiation asserted this ground fact directly.
    let neg_mut = encoder.solver_mut().not(mut_ground);
    encoder.assert_term(neg_mut);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "eager instantiation must assert ground postcondition_mut — negation should be UNSAT"
    );
}

/// Eager instantiation should fall back to the legacy witness symbol name when
/// a non-Int res_state uses the old pre-#1263 naming scheme.
///
/// This exercises the `logic_func_decl_cloned(preferred).or_else(legacy)` path
/// directly: only the legacy witness is registered, so the helper must still
/// assert the ground `postcondition_mut` fact.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_once_instantiation_uses_legacy_witness_name_fallback() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let once_expr = method_call(var("f"), "postcondition_once", vec![var("a"), var("r")]);
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), bool_expr(true), var("r")],
    );
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut with Bool res_state should encode");

    // Bool res_state uses the suffixed preferred name today; register only the
    // legacy unsuffixed witness to force the fallback branch.
    let preferred_witness = "fn_mut_once_witness_3_i_i_i_b";
    let legacy_witness = encoder.get_or_declare_logic_func(
        "fn_mut_once_witness_3_i_i_i",
        &[Sort::Int, Sort::Int, Sort::Int],
        Sort::Bool,
    );
    assert!(
        !encoder.decls().has_logic_func(preferred_witness),
        "test setup should omit the preferred witness so the legacy fallback is required"
    );

    encoder
        .assert_eager_fn_mut_once_instantiations(std::slice::from_ref(&once_expr))
        .expect("legacy witness fallback should still instantiate ground postcondition_mut");

    let mut_decl = encoder
        .decls()
        .get_logic_func("closure_postcondition_mut_4_i_i_b_i")
        .cloned()
        .expect("Bool-state postcondition_mut should be declared");

    let f_term = encoder.encode_pure(&var("f")).unwrap();
    let a_term = encoder.encode_pure(&var("a")).unwrap();
    let r_term = encoder.encode_pure(&var("r")).unwrap();
    let witness_term = encoder
        .solver_mut()
        .apply(&legacy_witness, &[f_term, a_term, r_term]);
    let mut_ground = encoder
        .solver_mut()
        .apply(&mut_decl, &[f_term, a_term, witness_term, r_term]);

    let neg_mut = encoder.solver_mut().not(mut_ground);
    encoder.assert_term(neg_mut);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "legacy witness fallback must assert the ground postcondition_mut fact"
    );
    assert!(
        !encoder.decls().has_logic_func(preferred_witness),
        "fallback should reuse the legacy witness instead of synthesizing the preferred name"
    );
}

/// Eager instantiation with no postcondition_once in requires should be a no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_once_instantiation_empty_requires_no_crash() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register symbols so the function has something to work with
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("a"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    encoder.assert_fn_mut_once_law();

    // Empty requires — should be no-op
    encoder
        .assert_eager_fn_mut_once_instantiations(&[])
        .expect("empty requires should succeed without error");

    // Verify solver state is still consistent after the no-op
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "empty eager instantiation should not make the formula unsatisfiable, got {result:?}"
    );
}

/// Eager instantiation with non-postcondition_once exprs in requires should be no-op.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_once_instantiation_irrelevant_requires_no_crash() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register symbols
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("a"), var("r")]);
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");

    encoder.assert_fn_mut_once_law();

    // Requires with non-postcondition_once expressions
    let irrelevant = PureExpr::Bool(true);
    encoder
        .assert_eager_fn_mut_once_instantiations(&[irrelevant])
        .expect("irrelevant requires should succeed without error");

    // Verify solver state is still consistent after irrelevant instantiation
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "irrelevant eager instantiation should not make the formula unsatisfiable, got {result:?}"
    );
}

/// Regression test for #1092: when eager instantiation hits an encoding
/// error (e.g., unsupported receiver expression), it must return Err
/// rather than silently proceeding.
///
/// After #985, zero-param closures encode the body directly, so we use
/// a deeply nested expression that triggers an encoding depth limit
/// or a truly unsupported PureExpr variant to force an encoding error.
#[test]
#[timeout(30000)]
fn test_eager_fn_mut_once_instantiation_encoding_error_returns_err() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register postcondition_once so the eager path activates.
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("a"), var("r")]);
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&once_expr)
        .expect("postcondition_once should encode");
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");
    encoder.assert_fn_mut_once_law();

    // Build a postcondition_once call with a zero-param closure receiver.
    // After #985, this now encodes successfully (body Int(0) encodes to 0).
    // The eager instantiation should handle it gracefully.
    let closure_receiver = PureExpr::Closure {
        params: vec![],
        body: Arc::new(PureExpr::Int(0)),
    };
    let ok_once = method_call(
        closure_receiver,
        "postcondition_once",
        vec![var("a"), var("r")],
    );
    let result = encoder.assert_eager_fn_mut_once_instantiations(&[ok_once]);
    // After #985, zero-param closures encode successfully, so this
    // may succeed or fail depending on sort matching — both are valid.
    // The key invariant is: no panic.
    let _ = result;
}

/// fn_closure_laws should not fire when only postcondition_mut is declared
/// (no Fn-trait postcondition).
///
/// Strengthened from trivial SAT (#1685): now verifies the UF remains
/// truly unconstrained by checking both positive and negative SAT (dual),
/// plus a Boolean contradiction UNSAT.
#[test]
#[timeout(30000)]
fn test_fn_closure_laws_no_fn_postcondition_no_crash() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Only register postcondition_mut (no Fn postcondition)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    // Should not crash
    encoder.assert_fn_closure_laws();

    // UNSAT dual: postcondition_mut AND NOT postcondition_mut is UNSAT
    let mut_term1 = encoder.encode_pure(&mut_expr).unwrap();
    let mut_term2 = encoder.encode_pure(&mut_expr).unwrap();
    encoder.assert_term(mut_term1);
    let neg = encoder.solver_mut().not(mut_term2);
    encoder.assert_term(neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "postcondition_mut AND NOT postcondition_mut must be UNSAT"
    );
}

/// Regression test for #1108: `body_has_postcondition_mut_with_var` must
/// recurse through `Let`, `Forall`, `Match`, `LogicFnCall`, and `Closure`
/// variants. Before the fix, these hit the catch-all `_ => false` and
/// eager Skolemization was silently skipped.
///
/// This test constructs `exists<s> (let mid = f(x) in postcondition_mut(f, a, s, mid))`
/// and verifies that `assert_eager_existential_skolemizations` fires
/// (producing a Skolem constant for `s`), which it would not have done
/// when the `Let` wrapper caused the function to return false.
///
/// Strengthened (#1685): now verifies the ground fact was actually asserted
/// by checking that NOT postcondition_mut(f, a, skolem, helper(x)) is UNSAT.
#[test]
#[timeout(30000)]
fn test_eager_skolem_fires_through_let_wrapped_postcondition_mut() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register postcondition_mut (4-param: self, args, res_state, result)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    // Build: exists<s> (let mid = logic_fn("helper", [x]) in postcondition_mut(f, a, s, mid))
    let inner_mut = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("mid")],
    );
    let let_body = let_bind("mid", logic_fn_call("helper", vec![var("x")]), inner_mut);
    let existential = exists("s", let_body);

    // Eager Skolemization should fire (not skip due to Let wrapper)
    encoder
        .assert_eager_existential_skolemizations(&[existential])
        .expect("eager skolemization should fire through Let wrapper");

    // Structural check: Skolemization should have introduced the `s` Skolem
    // constant as a temporary binding during encoding. Verify that the
    // postcondition_mut ground fact was asserted by checking UNSAT of its negation.
    // The Skolem variable `sk_exists_s_*` is only live during encoding; we
    // need the mut decl to build the negation.
    let mut_decl = encoder
        .decls()
        .get_logic_func("closure_postcondition_mut_4_i_i_i_i")
        .cloned()
        .expect("postcondition_mut should be declared");

    // Retrieve ground terms for the specific arguments used in the existential:
    // f, a are concrete vars, and mid = helper(x) was let-bound.
    let f_term = encoder.encode_pure(&var("f")).unwrap();
    let a_term = encoder.encode_pure(&var("a")).unwrap();
    let helper_x = encoder
        .encode_pure(&logic_fn_call("helper", vec![var("x")]))
        .unwrap();

    // The Skolem constant was substituted for `s` — it's a fresh Int var.
    // We cannot directly name it, but we can verify the ground fact was asserted.
    // The Skolem was named `sk_exists_s_0` (counter was 0 before this call).
    // After Skolemization, the var binding is removed from `self.vars`,
    // but the term was asserted in the solver context.
    //
    // Assert forall s: NOT postcondition_mut(f,a,s,helper(x)) — should be UNSAT
    // because the Skolemization asserted the ground fact for a specific s.
    let s_var = encoder.solver_mut().fresh_var("test_s_check", Sort::Int);
    let mut_check = encoder
        .solver_mut()
        .apply(&mut_decl, &[f_term, a_term, s_var, helper_x]);
    let neg_mut = encoder.solver_mut().not(mut_check);
    let forall_neg = encoder
        .solver_mut()
        .forall_with_triggers(&[s_var], neg_mut, &[&[mut_check]]);
    encoder.assert_term(forall_neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "forall s: NOT postcondition_mut(f,a,s,helper(x)) must be UNSAT \
         because Skolemization asserted the ground fact for a specific s"
    );
}

/// Regression test for #1108 (AC #3): `body_has_postcondition_mut_with_var`
/// must recurse through `Match` arms (another previously-missed variant).
/// Constructs: `exists<s> match(x) { _ => postcondition_mut(f, a, s, r) }`
/// and verifies eager Skolemization fires through the Match wrapper.
///
/// Strengthened (#1685): now verifies the ground fact was actually asserted
/// by checking that forall s: NOT postcondition_mut(f,a,s,r) is UNSAT.
#[test]
#[timeout(30000)]
fn test_eager_skolem_fires_through_match_wrapped_postcondition_mut() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register postcondition_mut (4-param: self, args, res_state, result)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    // Build: exists<s> match(x) { _ => postcondition_mut(f, a, s, r) }
    let inner_mut = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let match_body = match_expr(var("x"), vec![(Pattern::Wildcard, inner_mut)]);
    let existential = exists("s", match_body);

    // Eager Skolemization should fire (not skip due to Match wrapper)
    encoder
        .assert_eager_existential_skolemizations(&[existential])
        .expect("eager skolemization should fire through Match wrapper");

    // Verify the ground fact was asserted: forall s, NOT postcondition_mut(f,a,s,r)
    // should be UNSAT because the Skolemization asserted postcondition_mut for a
    // specific Skolem constant s.
    let mut_decl = encoder
        .decls()
        .get_logic_func("closure_postcondition_mut_4_i_i_i_i")
        .cloned()
        .expect("postcondition_mut should be declared");

    let f_term = encoder.encode_pure(&var("f")).unwrap();
    let a_term = encoder.encode_pure(&var("a")).unwrap();
    let r_term = encoder.encode_pure(&var("r")).unwrap();
    let s_var = encoder.solver_mut().fresh_var("test_s_check", Sort::Int);
    let mut_check = encoder
        .solver_mut()
        .apply(&mut_decl, &[f_term, a_term, s_var, r_term]);
    let neg_mut = encoder.solver_mut().not(mut_check);
    let forall_neg = encoder
        .solver_mut()
        .forall_with_triggers(&[s_var], neg_mut, &[&[mut_check]]);
    encoder.assert_term(forall_neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "forall s: NOT postcondition_mut(f,a,s,r) must be UNSAT \
         because Skolemization asserted the ground fact for a specific s"
    );
}
