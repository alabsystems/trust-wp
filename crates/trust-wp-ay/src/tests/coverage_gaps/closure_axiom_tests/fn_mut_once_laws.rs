// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

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
