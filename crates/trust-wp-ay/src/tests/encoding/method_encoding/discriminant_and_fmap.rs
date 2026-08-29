// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_encode_addr_logic_as_uninterpreted() {
    // p.addr_logic() should encode as an Int-returning UF (#737).
    // UF name: method_addr_logic_1_i (1 param = receiver, sort = Int).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("p"), "addr_logic", vec![]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("addr_logic should encode as uninterpreted function");
    assert!(
        encoder.decls().has_logic_func("method_addr_logic_1_i"),
        "addr_logic should declare method_addr_logic_1_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_discriminant_as_uninterpreted() {
    // x.discriminant() should encode as an Int-returning UF (#947).
    // UF name: method_discriminant_1_i (1 param = receiver, sort = Int).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("x"), "discriminant", vec![]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("discriminant should encode as uninterpreted function");
    assert!(
        encoder.decls().has_logic_func("method_discriminant_1_i"),
        "discriminant should declare method_discriminant_1_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

/// Discriminant encoding should produce an Int that the solver can reason
/// about. Verify: if `x.discriminant() == 0` is assumed, then a conditional
/// `ite(x.discriminant() == 0, a, b) == a` should be provable.
///
/// This is the semantic path exercised by SwitchInt in MIR extraction:
/// the discriminant value selects which branch to take. (#947)
#[test]
#[timeout(30000)]
fn test_discriminant_semantic_ite_branch_selection() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // requires: x.discriminant() == 0
    let discr = method_call(var("x"), "discriminant", vec![]);
    let req = eq(discr.clone(), int(0));

    // body: ite(x.discriminant() == 0, 42, 99)
    let body = ite(eq(discr, int(0)), int(42), int(99));

    // ensures: result == 42
    let ens = eq(var("result"), int(42));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "discriminant == 0 should select ITE true-branch; got {result:?}"
    );
}

/// Discriminant: two different objects can have different discriminants.
/// `x.discriminant() == 0 && y.discriminant() == 1` should be satisfiable
/// (not contradictory), and `x.discriminant() != y.discriminant()` should
/// be provable from these assumptions.
#[test]
#[timeout(30000)]
fn test_discriminant_different_objects_independent() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let x_discr = method_call(var("x"), "discriminant", vec![]);
    let y_discr = method_call(var("y"), "discriminant", vec![]);

    // requires: x.discriminant() == 0 && y.discriminant() == 1
    let req = and(eq(x_discr.clone(), int(0)), eq(y_discr.clone(), int(1)));

    // ensures: x.discriminant() != y.discriminant()
    let ens = ne(x_discr, y_discr);

    // body: true (trivial — we're checking the requires => ensures)
    let body = bool_expr(true);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "different discriminant assumptions should prove inequality; got {result:?}"
    );
}

// --- method_call/ dispatch gap tests (Part of #1078) ---

#[test]
#[timeout(30000)]
fn test_fmap_lookup_declares_uf() {
    // m.lookup(k) should route to encode_fmap_method and declare fmap_lookup UF.
    // `lookup` is an FMap-exclusive method — it does not exist on Seq.
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("m"), "lookup", vec![int(3)]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("FMap.lookup should encode");
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "FMap.lookup should declare fmap_lookup UF; found spec_functions: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );

    // Semantic: lookup(m, 3) returns Int, check it's usable in a constraint
    let eq_expr = eq(method_call(var("m"), "lookup", vec![int(3)]), int(42));
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("lookup == 42 should encode");
    encoder.assert_term(eq_term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "FMap.lookup(m, 3) == 42 should be SAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_fmap_index_logic_routes_to_fmap_lookup() {
    // m.index_logic(k) on a non-Seq receiver should route to encode_fmap_method,
    // NOT to the Seq index_logic path. The contract parser lowers `map[k]` to
    // `index_logic(k)` — for FMap receivers this must resolve to fmap_lookup.
    use trust_wp_core::formula::ExprSort;
    let mut encoder = AYEncoder::new();
    // index_logic is ambiguous. Register FMap hint so the guard routes to fmap_lookup. (#2059)
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    // Use a bare Var (not View) so is_seq_receiver returns false
    let expr = method_call(var("m"), "index_logic", vec![int(5)]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("FMap.index_logic should encode");
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "index_logic on non-Seq should declare fmap_lookup; found spec_functions: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
    // Should NOT declare seq functions
    assert!(
        !encoder
            .decls()
            .logic_func_names()
            .any(|k| k.starts_with("seq_")),
        "index_logic on non-Seq should not touch Seq functions"
    );
}

#[test]
#[timeout(30000)]
fn test_index_logic_bool_context_with_seq_key_uses_bool_predicate() {
    use trust_wp_core::formula::ExprSort;

    // Regression for Creusot cell predicates: map-style `index_logic` with
    // non-Int key (`*s` where `s: Seq`) appears in Bool equality context.
    // This must not route through Seq indexing (`off + idx`) or Int-valued
    // fmap_lookup.
    let mut encoder = AYEncoder::new();

    let predicate_index = method_call(
        view(var("cell")),
        "index_logic",
        vec![deref(var_with_sort("s", ExprSort::Seq))],
    );
    let expr = eq(predicate_index, bool_expr(true));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Bool-context index_logic with Seq key should encode without sort panic: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "Bool-context index_logic should not record solver panic: {:?}",
        encoder.solver_panic_reason()
    );
    assert!(
        encoder
            .decls()
            .logic_func_names()
            .any(|k| k.starts_with("method_index_logic_2")),
        "Bool-context index_logic should declare Bool method UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_index_logic_bool_context_with_unannotated_seq_key_uses_bool_predicate() {
    // Regression for #1805: the key expression can be structurally Seq
    // (`*s`) even when the parser doesn't attach ExprSort::Seq to `s`.
    // In Bool context this must still route to Bool predicate encoding.
    let mut encoder = AYEncoder::new();

    let predicate_index = method_call(view(var("cell")), "index_logic", vec![deref(var("s"))]);
    let expr = eq(predicate_index, bool_expr(true));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Bool-context index_logic with unannotated Seq key should encode: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "Bool-context index_logic should not panic: {:?}",
        encoder.solver_panic_reason()
    );
    assert!(
        encoder
            .decls()
            .logic_func_names()
            .any(|k| k.starts_with("method_index_logic_2")),
        "Bool-context index_logic should declare Bool method UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}
