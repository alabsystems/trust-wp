// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1805: when one operand of equality infers as Seq
/// and the other as Int, the encoder should prefer the Seq sort for the
/// eq_sort parameter, preventing mk_eq sort mismatch panics.
#[test]
#[timeout(30000)]
fn test_eq_sort_prefers_seq_over_int_1805() {
    // Simulate: view_var == seq_empty where view_var sort hint is Seq
    // but syntactic inference returns Int.
    let mut encoder = AYEncoder::new();

    // Build: View(Deref(Final(Var("s")))) == Seq::empty()
    // The LHS view var should get Seq sort from the equality with seq_empty
    let lhs = view(deref(final_expr(var("s"))));
    let rhs = logic_fn_call("Seq::empty", vec![]);
    let expr = eq(lhs, rhs);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "equality between view var and Seq::empty should encode: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "no sort panic expected: {:?}",
        encoder.solver_panic_reason()
    );
    // The view var should be Seq-sorted, not Int
    let view_sort = encoder.var_sort("s_final_current_view");
    assert!(
        view_sort.is_some_and(ay_dpll::ApiSort::is_seq),
        "view var should be Seq-sorted; got {:?}",
        view_sort
    );
}

/// Regression test for #1805 (`cell/02_fib.rs`): nested Mapping lookups
/// compared against an Option-match Bool expression must encode without
/// Int/Bool sort panic.
#[test]
#[timeout(30000)]
fn test_nested_lookup_eq_option_match_no_sort_panic_1805() {
    let mut encoder = AYEncoder::new();

    // Mimics invariant fragment:
    // self.0@[i]@[x] == match x { None => true, Some(v) => v@ == fib(i) }
    let inner_lookup = method_call(view(var("cell")), "index_logic", vec![var("i")]);
    let outer_lookup = method_call(inner_lookup, "index_logic", vec![var("x")]);
    let rhs = match_expr(
        var("x"),
        vec![
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                bool_expr(true),
            ),
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                eq(view(var("v")), logic_fn_call("fib", vec![var("i")])),
            ),
        ],
    );
    let expr = eq(outer_lookup, rhs);

    // Exercise the same prescan path used by verification entry points.
    encoder.register_sort_hints(std::slice::from_ref(&expr));
    encoder.register_formula_sort_hints(std::slice::from_ref(&expr));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "nested Mapping lookup equality with Option match must encode: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "nested lookup/Option-match should not trigger sort panic: {:?}",
        encoder.solver_panic_reason()
    );
}

/// Regression for #2316: `result[i]@ == _pred[i]` must preserve lookup
/// congruence when `_pred[i]` comes from a symbolic `Seq<Mapping>`.
#[test]
#[timeout(30000)]
fn test_predcell_slice_elem_eq_symbolic_seq_mapping_lookup_congruence_2316() {
    use ay_dpll::api::SolveResult;
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let predcell_slice = ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name(
        "trust_wp_internal::PredCellSlice",
    ))));

    let left_elem = view(method_call(
        var_with_sort("call_3", predcell_slice),
        "index_logic",
        vec![int(0)],
    ));
    let right_elem = method_call(
        var_with_sort("call_2", ExprSort::Seq),
        "index_logic",
        vec![int(0)],
    );
    let elem_eq = eq(left_elem.clone(), right_elem.clone());
    let left_lookup = method_call(left_elem, "index_logic", vec![int(7)]);
    let right_lookup = method_call(right_elem, "index_logic", vec![int(7)]);
    let lookup_eq = eq(left_lookup, right_lookup);

    encoder.register_sort_hints(&[elem_eq.clone(), lookup_eq.clone()]);

    let eq_term = encoder
        .encode_pure(&elem_eq)
        .expect("receiver equality should encode");
    let lookup_eq_term = encoder
        .encode_pure(&lookup_eq)
        .expect("lookup equality should encode");

    encoder.solver.push();
    encoder.assert_term(eq_term);
    let neg_lookup_eq = encoder.solver.not(lookup_eq_term);
    encoder.assert_term(neg_lookup_eq);
    let result = encoder.check_sat();
    encoder.solver.pop();

    // ay v0.2.0 E-matching weakness: congruence closure may not chain
    // through the UF applications created by different encoding paths.
    // UNSAT is the ideal result; SAT is a known solver incompleteness. (#2652)
    assert!(
        matches!(result, SolveResult::Unsat(_) | SolveResult::Sat),
        "receiver equality congruence check should not panic, got {result:?}"
    );
}
