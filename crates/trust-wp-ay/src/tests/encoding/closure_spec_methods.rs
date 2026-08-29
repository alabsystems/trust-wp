// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_closure_spec_precondition_supports_mixed_arities() {
    let mut encoder = AYEncoder::new();

    let zero_arg_precondition = method_call(var("f"), "precondition", vec![]);
    let one_arg_precondition = method_call(var("g"), "precondition", vec![var("x")]);

    assert!(
        encoder.encode_pure(&zero_arg_precondition).is_ok(),
        "Zero-arg precondition should encode"
    );
    assert!(
        encoder.encode_pure(&one_arg_precondition).is_ok(),
        "One-arg precondition should encode after zero-arg precondition"
    );

    let precondition_symbol_count = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with("closure_precondition_"))
        .count();
    assert_eq!(
        precondition_symbol_count, 2,
        "Expected separate symbols for each precondition arity"
    );
}

#[test]
#[timeout(30000)]
fn test_closure_spec_postcondition_supports_mixed_sorts() {
    let mut encoder = AYEncoder::new();

    let int_arg_postcondition = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let bool_arg_postcondition =
        method_call(var("g"), "postcondition", vec![bool_expr(true), var("r2")]);

    assert!(
        encoder.encode_pure(&int_arg_postcondition).is_ok(),
        "Int-argument postcondition should encode"
    );
    assert!(
        encoder.encode_pure(&bool_arg_postcondition).is_ok(),
        "Bool-argument postcondition should encode after Int-argument version"
    );

    let postcondition_symbol_count = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with("closure_postcondition_"))
        .count();
    assert_eq!(
        postcondition_symbol_count, 2,
        "Expected separate symbols for each postcondition sort signature"
    );
}

#[test]
#[timeout(30000)]
fn test_closure_spec_receiver_deref_is_normalized() {
    let mut encoder = AYEncoder::new();

    let direct_receiver = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let deref_receiver = method_call(deref(var("f")), "postcondition", vec![var("x"), var("r")]);

    let direct_term = encoder
        .encode_pure(&direct_receiver)
        .expect("Direct receiver should encode");
    let deref_term = encoder
        .encode_pure(&deref_receiver)
        .expect("Deref receiver should encode");

    let eq_term = {
        let solver = encoder.solver_mut();
        solver.eq(direct_term, deref_term)
    };
    let neq_term = {
        let solver = encoder.solver_mut();
        solver.not(eq_term)
    };
    encoder.assert_term(neq_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Direct and deref receivers should encode to equivalent Bool terms"
    );

    assert!(
        !encoder.vars_for_test().contains_key("f_current"),
        "closure receiver deref should normalize to `f`, not introduce `f_current`"
    );
}

/// Box-wrapped closure postcondition receiver normalization (#1373).
///
/// When a closure is passed through `Box::new(f)`, the MIR introduces
/// an extra `Deref` layer from Box's `Deref` impl. The Fn::call spec
/// adds `(*self)` on top, producing `Deref(Deref(Var("f")))`. The
/// encoder must normalize ALL deref layers — not just one — so that
/// the UF symbol matches the caller's direct `f.postcondition(...)`.
#[test]
#[timeout(30000)]
fn test_closure_spec_receiver_double_deref_normalized_for_box() {
    let mut encoder = AYEncoder::new();

    let direct_receiver = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let double_deref_receiver = method_call(
        deref(deref(var("f"))),
        "postcondition",
        vec![var("x"), var("r")],
    );

    let direct_term = encoder
        .encode_pure(&direct_receiver)
        .expect("Direct receiver should encode");
    let double_deref_term = encoder
        .encode_pure(&double_deref_receiver)
        .expect("Double-deref receiver should encode");

    let eq_term = {
        let solver = encoder.solver_mut();
        solver.eq(direct_term, double_deref_term)
    };
    let neq_term = {
        let solver = encoder.solver_mut();
        solver.not(eq_term)
    };
    encoder.assert_term(neq_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Direct and double-deref receivers should encode to equivalent Bool terms (#1373)"
    );

    assert!(
            !encoder.vars_for_test().contains_key("f_current"),
            "Box-wrapped closure receiver double-deref should normalize to `f`, not `f_current` (#1373)"
        );
}

/// Triple-deref normalization (nested Box-in-Box edge case) (#1373).
#[test]
#[timeout(30000)]
fn test_closure_spec_receiver_triple_deref_normalized() {
    let mut encoder = AYEncoder::new();

    let direct_receiver = method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]);
    let triple_deref_receiver = method_call(
        deref(deref(deref(var("f")))),
        "postcondition_once",
        vec![var("x"), var("r")],
    );

    let direct_term = encoder
        .encode_pure(&direct_receiver)
        .expect("Direct receiver should encode");
    let triple_deref_term = encoder
        .encode_pure(&triple_deref_receiver)
        .expect("Triple-deref receiver should encode");

    let eq_term = {
        let solver = encoder.solver_mut();
        solver.eq(direct_term, triple_deref_term)
    };
    let neq_term = {
        let solver = encoder.solver_mut();
        solver.not(eq_term)
    };
    encoder.assert_term(neq_term);
    assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "Direct and triple-deref receivers should produce equivalent postcondition_once terms (#1373)"
        );
}

/// Test `postcondition_mut` encoding with four-place signature (Phase 2).
///
/// `postcondition_mut(self, arg, ^self, result)` uses a four-place predicate
/// where `^self` represents the closure's post-state. The encoder must:
/// 1. Accept the four-argument `MethodCall`
/// 2. Handle `Final(Var("f"))` as one of the arguments
/// 3. Produce a unique UF symbol for the 5-param signature (receiver + 4 args)
#[test]
#[timeout(30000)]
fn test_closure_spec_postcondition_mut_four_place() {
    let mut encoder = AYEncoder::new();

    // (*f).postcondition_mut(arg, ^f, result)
    // In the substituted form at call sites, this becomes a MethodCall with:
    //   receiver = Deref(Var("f"))  (the pre-state)
    //   args = [Var("x"), Final(Var("f")), Var("r")]  (arg, post-state, result)
    let postcondition_mut = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("r")],
    );

    let term = encoder.encode_pure(&postcondition_mut);
    assert!(
        term.is_ok(),
        "postcondition_mut with Final arg should encode: {term:?}"
    );

    // Verify the UF symbol was created with the correct arity
    let mut_symbol_count = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with("closure_postcondition_mut_"))
        .count();
    assert_eq!(
        mut_symbol_count, 1,
        "Expected one postcondition_mut UF symbol"
    );

    // The symbol should encode 4 params: receiver + 3 args
    let symbol_name = encoder
        .decls()
        .logic_func_names()
        .find(|name| name.starts_with("closure_postcondition_mut_"))
        .unwrap()
        .clone();
    assert!(
        symbol_name.starts_with("closure_postcondition_mut_4_"),
        "Expected arity 4 in symbol name, got: {symbol_name}"
    );
}

/// Test that `postcondition_mut` and `postcondition` produce distinct UF symbols.
///
/// Even with the same arity and sorts, different method names must produce
/// different SMT symbols to avoid conflation.
#[test]
#[timeout(30000)]
fn test_closure_spec_postcondition_mut_distinct_from_postcondition() {
    let mut encoder = AYEncoder::new();

    // postcondition(f, x, r) — three-place (Fn)
    let postcondition = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);

    // postcondition_mut(f, x, r) — three-place (but different method)
    let postcondition_mut = method_call(var("g"), "postcondition_mut", vec![var("x"), var("r")]);

    encoder.encode_pure(&postcondition).unwrap();
    encoder.encode_pure(&postcondition_mut).unwrap();

    let all_symbols: Vec<&String> = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with("closure_postcondition"))
        .collect();
    assert_eq!(
        all_symbols.len(),
        2,
        "postcondition and postcondition_mut should produce distinct symbols: {all_symbols:?}"
    );
}
