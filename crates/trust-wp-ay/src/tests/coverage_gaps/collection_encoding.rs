// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::ExprSort;

use super::*;

/// FMap len dispatches to fmap_len UF for non-Seq receivers.
///
/// Strengthened from trivial SAT (#1685): now verifies functional
/// consistency via UNSAT dual — len(m)==5 AND len(m)!=5 is UNSAT.
#[test]
#[timeout(30000)]
fn test_fmap_len_declares_uf() {
    let mut encoder = AYEncoder::new();
    // len is ambiguous (Seq/FMap). Register FMap hint so the guard routes to fmap_len. (#2059)
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let expr = method_call(var("m"), "len", vec![]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("FMap.len() should encode via fmap_len UF");
    assert!(
        encoder.decls().has_spec_func("fmap_len"),
        "FMap.len() should declare fmap_len UF; found spec_functions: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );

    // UNSAT dual: len(m)==5 AND len(m)!=5 must be UNSAT (functional consistency)
    let eq_expr = eq(method_call(var("m"), "len", vec![]), int(5));
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("fmap_len == 5 should encode");
    encoder.assert_term(eq_term);

    let neq_expr = ne(method_call(var("m"), "len", vec![]), int(5));
    let neq_term = encoder
        .encode_pure(&neq_expr)
        .expect("fmap_len != 5 should encode");
    encoder.assert_term(neq_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "fmap_len(m)==5 AND fmap_len(m)!=5 must be UNSAT"
    );
}

/// FMap get dispatches to fmap_lookup UF for non-Seq receivers.
///
/// Strengthened from trivial SAT (#1685): now verifies functional
/// consistency via UNSAT dual — get(m,3)==42 AND get(m,3)!=42 is UNSAT.
#[test]
#[timeout(30000)]
fn test_fmap_get_routes_to_fmap_lookup() {
    let mut encoder = AYEncoder::new();
    // get is ambiguous (Seq/FMap). Register FMap hint so the guard routes to fmap_lookup. (#2059)
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let expr = method_call(var("m"), "get", vec![int(3)]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("FMap.get(3) should encode via fmap_lookup UF");
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "FMap.get should route to fmap_lookup; found spec_functions: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );

    // UNSAT dual: get(m,3)==42 AND get(m,3)!=42 must be UNSAT
    let eq_expr = eq(method_call(var("m"), "get", vec![int(3)]), int(42));
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("fmap_lookup == 42 should encode");
    encoder.assert_term(eq_term);

    let neq_expr = ne(method_call(var("m"), "get", vec![int(3)]), int(42));
    let neq_term = encoder
        .encode_pure(&neq_expr)
        .expect("fmap_lookup != 42 should encode");
    encoder.assert_term(neq_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "fmap_lookup(m,3)==42 AND fmap_lookup(m,3)!=42 must be UNSAT"
    );
}

/// `FMap::get(k) == Some(v)` should normalize to `contains(k) && lookup(k) == v`.
#[test]
#[timeout(30000)]
fn test_fmap_get_eq_some_requires_contains() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let eq_some = eq(
        method_call(var("m"), "get", vec![int(3)]),
        logic_fn_call("Some", vec![int(42)]),
    );
    let eq_some_term = encoder
        .encode_pure(&eq_some)
        .expect("FMap.get == Some(...) should encode via contains+lookup");
    encoder.assert_term(eq_some_term);

    let not_contains = encoder
        .encode_pure(&not(method_call(var("m"), "contains", vec![int(3)])))
        .expect("negated FMap.contains should encode");
    encoder.assert_term(not_contains);

    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "FMap.get == Some(...) should declare fmap_contains"
    );
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "FMap.get == Some(...) should still use fmap_lookup for the value witness"
    );
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "get(m,3) == Some(42) must imply contains(m,3)"
    );
}

/// `FMap::get(k) == None` should normalize to `!contains(k)` without lookup.
#[test]
#[timeout(30000)]
fn test_fmap_get_eq_none_excludes_contains_without_lookup() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let eq_none = eq(
        method_call(var("m"), "get", vec![int(3)]),
        logic_fn_call("None", vec![]),
    );
    let eq_none_term = encoder
        .encode_pure(&eq_none)
        .expect("FMap.get == None should encode via !contains");
    encoder.assert_term(eq_none_term);

    let contains = encoder
        .encode_pure(&method_call(var("m"), "contains", vec![int(3)]))
        .expect("FMap.contains should encode");
    encoder.assert_term(contains);

    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "FMap.get == None should declare fmap_contains"
    );
    assert!(
        !encoder.decls().has_spec_func("fmap_lookup"),
        "FMap.get == None should not need fmap_lookup"
    );
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "get(m,3) == None must exclude contains(m,3)"
    );
}

/// Reversed `Some(v) == FMap::get(k)` must normalize to the same contains+lookup formula.
#[test]
#[timeout(30000)]
fn test_some_eq_fmap_get_requires_contains() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let reversed = eq(
        logic_fn_call("Some", vec![int(42)]),
        method_call(var("m"), "get", vec![int(3)]),
    );
    let reversed_term = encoder
        .encode_pure(&reversed)
        .expect("Some(...) == FMap.get should encode via contains+lookup");
    encoder.assert_term(reversed_term);

    let not_contains = encoder
        .encode_pure(&not(method_call(var("m"), "contains", vec![int(3)])))
        .expect("negated FMap.contains should encode");
    encoder.assert_term(not_contains);

    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "reversed Some == FMap.get should declare fmap_contains"
    );
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "reversed Some == FMap.get should still use fmap_lookup"
    );
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Some(42) == get(m,3) must imply contains(m,3)"
    );
}

/// Reversed `None == FMap::get(k)` must normalize to `!contains(k)` without lookup.
#[test]
#[timeout(30000)]
fn test_none_eq_fmap_get_excludes_contains_without_lookup() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let reversed = eq(
        logic_fn_call("None", vec![]),
        method_call(var("m"), "get", vec![int(3)]),
    );
    let reversed_term = encoder
        .encode_pure(&reversed)
        .expect("None == FMap.get should encode via !contains");
    encoder.assert_term(reversed_term);

    let contains = encoder
        .encode_pure(&method_call(var("m"), "contains", vec![int(3)]))
        .expect("FMap.contains should encode");
    encoder.assert_term(contains);

    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "reversed None == FMap.get should declare fmap_contains"
    );
    assert!(
        !encoder.decls().has_spec_func("fmap_lookup"),
        "reversed None == FMap.get should not need fmap_lookup"
    );
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "None == get(m,3) must exclude contains(m,3)"
    );
}

/// Reversed `Some(v) != FMap::get(k)` must negate the same contains+lookup witness.
#[test]
#[timeout(30000)]
fn test_some_ne_fmap_get_negates_contains_lookup() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let reversed = ne(
        logic_fn_call("Some", vec![int(42)]),
        method_call(var("m"), "get", vec![int(3)]),
    );
    let reversed_term = encoder
        .encode_pure(&reversed)
        .expect("Some(...) != FMap.get should negate contains+lookup");
    encoder.assert_term(reversed_term);

    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "reversed Some != FMap.get should declare fmap_contains"
    );
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "reversed Some != FMap.get should still use fmap_lookup"
    );

    let contains = encoder
        .encode_pure(&method_call(var("m"), "contains", vec![int(3)]))
        .expect("FMap.contains should encode");
    encoder.assert_term(contains);

    let lookup_eq = encoder
        .encode_pure(&eq(method_call(var("m"), "lookup", vec![int(3)]), int(42)))
        .expect("FMap.lookup == 42 should encode");
    encoder.assert_term(lookup_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Some(42) != get(m,3) must exclude the matching contains+lookup witness"
    );
}

/// `FMap::get(k) != None` should normalize to `contains(k)` without lookup.
#[test]
#[timeout(30000)]
fn test_fmap_get_ne_none_implies_contains_without_lookup() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let ne_none = ne(
        method_call(var("m"), "get", vec![int(3)]),
        logic_fn_call("None", vec![]),
    );
    let ne_none_term = encoder
        .encode_pure(&ne_none)
        .expect("FMap.get != None should encode via contains");
    encoder.assert_term(ne_none_term);

    let not_contains = encoder
        .encode_pure(&not(method_call(var("m"), "contains", vec![int(3)])))
        .expect("negated FMap.contains should encode");
    encoder.assert_term(not_contains);

    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "FMap.get != None should declare fmap_contains"
    );
    assert!(
        !encoder.decls().has_spec_func("fmap_lookup"),
        "FMap.get != None should not need fmap_lookup"
    );
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "get(m,3) != None must imply contains(m,3)"
    );
}

/// Reversed `None != FMap::get(k)` must normalize to `contains(k)` without lookup.
#[test]
#[timeout(30000)]
fn test_none_ne_fmap_get_implies_contains_without_lookup() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let reversed = ne(
        logic_fn_call("None", vec![]),
        method_call(var("m"), "get", vec![int(3)]),
    );
    let reversed_term = encoder
        .encode_pure(&reversed)
        .expect("None != FMap.get should encode via contains");
    encoder.assert_term(reversed_term);

    let not_contains = encoder
        .encode_pure(&not(method_call(var("m"), "contains", vec![int(3)])))
        .expect("negated FMap.contains should encode");
    encoder.assert_term(not_contains);

    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "reversed None != FMap.get should declare fmap_contains"
    );
    assert!(
        !encoder.decls().has_spec_func("fmap_lookup"),
        "reversed None != FMap.get should not need fmap_lookup"
    );
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "None != get(m,3) must imply contains(m,3)"
    );
}

/// FMap index dispatches to fmap_lookup UF for non-Seq receivers.
#[test]
#[timeout(30000)]
fn test_fmap_index_routes_to_fmap_lookup() {
    let mut encoder = AYEncoder::new();
    // index is ambiguous (Seq/FMap). Register FMap hint so the guard routes to fmap_lookup. (#2059)
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let expr = method_call(var("m"), "index", vec![int(7)]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("FMap.index(7) should encode via fmap_lookup UF");
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "FMap.index should route to fmap_lookup; found spec_functions: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );

    // Semantic check: index(m,7)==9 AND index(m,7)!=9 must be UNSAT.
    let eq_expr = eq(method_call(var("m"), "index", vec![int(7)]), int(9));
    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("fmap_lookup(index)==9 should encode");
    encoder.assert_term(eq_term);

    let neq_expr = ne(method_call(var("m"), "index", vec![int(7)]), int(9));
    let neq_term = encoder
        .encode_pure(&neq_expr)
        .expect("fmap_lookup(index)!=9 should encode");
    encoder.assert_term(neq_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "fmap_lookup(m,7)==9 AND fmap_lookup(m,7)!=9 must be UNSAT"
    );
}

/// FMap len and lookup on the same receiver share the correct UFs.
///
/// Strengthened from trivial SAT (#1685): now verifies that len and lookup
/// are distinct UFs by checking len(m) != lookup(m,0) is SAT (they are
/// independent uninterpreted functions), plus an UNSAT dual on lookup
/// consistency.
#[test]
#[timeout(30000)]
fn test_fmap_len_and_lookup_coexist() {
    let mut encoder = AYEncoder::new();
    // len is ambiguous (Seq/FMap). Register FMap hint so both methods use FMap UFs. (#2059)
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let len_expr = method_call(var("m"), "len", vec![]);
    let lookup_expr = method_call(var("m"), "lookup", vec![int(0)]);

    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("fmap_len should encode");
    let lookup_term = encoder
        .encode_pure(&lookup_expr)
        .expect("fmap_lookup should encode");

    assert_eq!(encoder.solver().get_sort(len_term), Sort::Int);
    assert_eq!(encoder.solver().get_sort(lookup_term), Sort::Int);
    assert!(
        encoder.solver().format_term(len_term).contains("fmap_len"),
        "m.len() should encode as fmap_len, got {}",
        encoder.solver().format_term(len_term)
    );
    assert!(
        encoder
            .solver()
            .format_term(lookup_term)
            .contains("fmap_lookup"),
        "m.lookup(0) should encode as fmap_lookup, got {}",
        encoder.solver().format_term(lookup_term)
    );
    let fmap = Sort::Uninterpreted("FMap".to_string());
    let fmap_len = encoder
        .decls()
        .get_spec_func("fmap_len")
        .expect("fmap_len should be declared");
    assert_eq!(fmap_len.domain(), &[fmap.clone()]);
    assert_eq!(fmap_len.range(), &Sort::Int);
    let fmap_lookup = encoder
        .decls()
        .get_spec_func("fmap_lookup")
        .expect("fmap_lookup should be declared");
    assert_eq!(fmap_lookup.domain(), &[fmap, Sort::Int]);
    assert_eq!(fmap_lookup.range(), &Sort::Int);

    // len and lookup are distinct UFs — their results can differ (SAT for !=)
    let neq = encoder.solver_mut().neq(len_term, lookup_term);
    encoder.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "fmap_len(m) != fmap_lookup(m,0) should be SAT — they are distinct UFs; got {result:?}"
    );
    assert!(encoder.decls().has_spec_func("fmap_len"));
    assert!(encoder.decls().has_spec_func("fmap_lookup"));
}

/// View(Final(Var("x"))) creates `final_x_view` variable and asserts scalar
/// identity `x_final == final_x_view` for Int-sorted views.
#[test]
#[timeout(30000)]
fn test_view_final_creates_final_view_var_with_identity() {
    let mut encoder = AYEncoder::new();

    // Encode (^x)@ — View(Final(Var("x")))
    let expr = view(final_expr(var("x")));
    let view_term = encoder
        .encode_pure(&expr)
        .expect("View(Final(Var(x))) should encode");

    // The encoder should have declared `final_x_view`
    assert!(
        encoder.vars_for_test().contains_key("final_x_view"),
        "View(Final(Var(x))) should declare final_x_view; vars: {:?}",
        encoder.vars_for_test().keys().collect::<Vec<_>>()
    );

    // The encoder should also have declared `x_final` via identity assertion
    assert!(
        encoder.vars_for_test().contains_key("x_final"),
        "scalar identity assertion should declare x_final"
    );

    // Semantic: the identity assertion links final_x_view and x_final.
    // Verify: asserting final_x_view != x_final should be UNSAT.
    // Strengthened (#1685): replaces trivially-SAT check with identity proof.
    let x_final_term = *encoder
        .vars_for_test()
        .get("x_final")
        .expect("x_final should be declared");
    let neq = encoder.solver_mut().neq(view_term, x_final_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "final_x_view != x_final must be UNSAT — scalar identity assertion forces equality"
    );
}

/// View of a scalar BinOp (complex inner expr, Int sort) is identity.
///
/// Exercises the complex-inner-expression branch at view.rs:127 where
/// `infer_expr_sort` returns Int, so `@` is a no-op.
#[test]
#[timeout(30000)]
fn test_view_complex_int_expr_is_identity() {
    let mut encoder = AYEncoder::new();

    // Encode (1 + 2)@ — View of Int BinOp should return inner term directly
    let inner = binop(int(1), BinOp::Add, int(2));
    let view_expr = view(inner.clone());
    let view_term = encoder
        .encode_pure(&view_expr)
        .expect("View(1+2) should encode");

    // Encode the inner directly (ensures both paths exercise encode_pure_impl)
    let _inner_term = encoder.encode_pure(&inner).expect("1+2 should encode");

    // View result should equal 3 (identity for Int)
    let three = encoder.solver_mut().int_const(3);
    let neq = encoder.solver_mut().eq(view_term, three);
    let neq = encoder.solver_mut().not(neq);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "View(1+2) should be identity (== 3)"
    );
}

/// View of a Bool expression (complex inner expr, Bool sort) is identity.
///
/// Strengthened from trivial SAT (#1685): now verifies View(x>0) is
/// identity by checking that View(x>0) AND x==0 is UNSAT — the view
/// assertion constrains x, proving the view propagates the inner Bool.
#[test]
#[timeout(30000)]
fn test_view_complex_bool_expr_is_identity() {
    let mut encoder = AYEncoder::new();

    // Encode (x > 0)@ — View of Bool comparison should return inner term directly
    let inner = gt(var("x"), int(0));
    let view_expr = view(inner.clone());
    let view_term = encoder
        .encode_pure(&view_expr)
        .expect("View(x > 0) should encode");

    // Assert the view (which should be identity: x > 0)
    encoder.assert_term(view_term);

    // UNSAT dual: if View is identity, x > 0 is asserted, so x == 0 is UNSAT
    let zero = encoder.encode_pure(&int(0)).unwrap();
    let x_term = encoder.encode_pure(&var("x")).unwrap();
    let eq_zero = encoder.solver_mut().eq(x_term, zero);
    encoder.assert_term(eq_zero);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "View(x > 0) AND x == 0 must be UNSAT — view identity preserves x > 0"
    );
}

/// Seq is_empty encodes as `seq_len(receiver) == 0` for Seq receivers.
///
/// `is_empty` is an ambiguous method that requires sort-hint registration
/// to dispatch to Seq (vs FSet). We use `register_sort_hints` directly
/// to tag v_view as Seq without encoding side-effect-laden operations.
#[test]
#[timeout(30000)]
fn test_seq_is_empty_encodes_as_len_eq_zero() {
    let mut encoder = AYEncoder::new();

    // Register v_view as Seq via a push_back expression scan (without encoding).
    // This populates sort_hints so is_seq_receiver returns true for v@.
    let hint_expr = method_call(view(var("v")), "push_back", vec![int(1)]);
    encoder.register_sort_hints(std::slice::from_ref(&hint_expr));

    // Now: is_empty on the same receiver should route to Seq path
    let expr = method_call(view(var("v")), "is_empty", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Seq.is_empty() should encode after Seq hint established");

    // is_empty should NOT create fset_is_empty UF (routed to Seq len==0)
    assert!(
        !encoder.decls().has_spec_func("fset_is_empty"),
        "Seq.is_empty should NOT use FSet UF; found: {:?}",
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );

    // The Seq path uses seq_len built-in function (from ensure_seq_functions),
    // not a spec_function UF. Verify the term is Bool-sorted by using it in
    // a formula without asserting it (avoids Seq axiom interactions).
    let _negated = encoder.solver_mut().not(term);
    // If term were not Bool-sorted, the not() call above would panic.
}

/// `is_some` on the same variable produces equal Bool terms.
#[test]
#[timeout(30000)]
fn test_datatype_is_some_is_deterministic() {
    let mut encoder = AYEncoder::new();
    let t1 = encoder
        .encode_pure(&method_call(var("x"), "is_some", vec![]))
        .expect("is_some should encode");
    let t2 = encoder
        .encode_pure(&method_call(var("x"), "is_some", vec![]))
        .expect("is_some should encode again");
    // Same application must yield same Bool term
    let xor = encoder.solver.xor(t1, t2);
    encoder.assert_term(xor);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(x) XOR is_some(x) must be UNSAT — deterministic predicate"
    );
}

/// `is_none` is the negation of `is_some`: asserting both is UNSAT.
#[test]
#[timeout(30000)]
fn test_datatype_is_none_contradicts_is_some() {
    let mut encoder = AYEncoder::new();
    let is_some = method_call(var("x"), "is_some", vec![]);
    let is_none = method_call(var("x"), "is_none", vec![]);
    let is_some_term = encoder
        .encode_pure(&is_some)
        .expect("is_some should encode");
    let is_none_term = encoder
        .encode_pure(&is_none)
        .expect("is_none should encode");
    encoder.assert_term(is_some_term);
    encoder.assert_term(is_none_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(x) AND is_none(x) must be UNSAT (mutual exclusion)"
    );
}

/// `is_ok` on the same variable produces equal Bool terms.
#[test]
#[timeout(30000)]
fn test_datatype_is_ok_is_deterministic() {
    let mut encoder = AYEncoder::new();
    let t1 = encoder
        .encode_pure(&method_call(var("x"), "is_ok", vec![]))
        .expect("is_ok should encode");
    let t2 = encoder
        .encode_pure(&method_call(var("x"), "is_ok", vec![]))
        .expect("is_ok should encode again");
    let xor = encoder.solver.xor(t1, t2);
    encoder.assert_term(xor);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(x) XOR is_ok(x) must be UNSAT — deterministic predicate"
    );
}

/// `is_err` is the negation of `is_ok`: asserting both is UNSAT.
#[test]
#[timeout(30000)]
fn test_datatype_is_err_contradicts_is_ok() {
    let mut encoder = AYEncoder::new();
    let is_ok = method_call(var("x"), "is_ok", vec![]);
    let is_err = method_call(var("x"), "is_err", vec![]);
    let is_ok_term = encoder.encode_pure(&is_ok).expect("is_ok should encode");
    let is_err_term = encoder.encode_pure(&is_err).expect("is_err should encode");
    encoder.assert_term(is_ok_term);
    encoder.assert_term(is_err_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(x) AND is_err(x) must be UNSAT (mutual exclusion)"
    );
}

/// `unwrap` and `unwrap_err` are distinct accessors on the same value.
///
/// Strengthened from trivial functional-equality checks (which test ay
/// term congruence, not encoder correctness) to verifying that the two
/// accessors produce different UF symbols.
#[test]
#[timeout(30000)]
fn test_datatype_unwrap_and_unwrap_err_are_distinct() {
    let mut encoder = AYEncoder::new();
    let unwrap_term = encoder
        .encode_pure(&method_call(var("x"), "unwrap", vec![]))
        .expect("unwrap should encode");
    let unwrap_err_term = encoder
        .encode_pure(&method_call(var("x"), "unwrap_err", vec![]))
        .expect("unwrap_err should encode");

    // `unwrap_err` seeds the native Result datatype after `x` was already
    // encoded in the erased Int lane. Its native `result_err_error` selector
    // and the Int-lane fallback must coexist under distinct solver symbols.
    let legacy_err_accessor = encoder
        .decls()
        .get_spec_func("result_err_error")
        .expect("erased Result accessor should remain discoverable by standard axioms");
    assert_ne!(
        legacy_err_accessor.name(),
        "result_err_error",
        "native selector must reserve the bare solver symbol"
    );
    let neq = encoder.solver.neq(unwrap_term, unwrap_err_term);
    encoder.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "unwrap(x) != unwrap_err(x): got {result:?}"
    );
}

/// Seq is_empty is UNSAT when combined with seq_len > 0.
#[test]
#[timeout(30000)]
fn test_seq_is_empty_contradicts_positive_len() {
    let mut encoder = AYEncoder::new();

    // Register Seq hint without encoding push_back (avoids axiom side effects)
    let hint_expr = method_call(view(var("v")), "push_back", vec![int(1)]);
    encoder.register_sort_hints(std::slice::from_ref(&hint_expr));

    // Assert v@.is_empty() == true (seq_len(v) == 0)
    let is_empty = method_call(view(var("v")), "is_empty", vec![]);
    let is_empty_term = encoder
        .encode_pure(&is_empty)
        .expect("Seq.is_empty() should encode");
    encoder.assert_term(is_empty_term);

    // Also assert v@.len() > 0, which contradicts is_empty
    let len_expr = method_call(view(var("v")), "len", vec![]);
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("Seq.len() should encode");
    let zero = encoder.solver_mut().int_const(0);
    let gt_zero = encoder.solver_mut().gt(len_term, zero);
    encoder.assert_term(gt_zero);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_empty AND len > 0 on the same Seq should be UNSAT"
    );
}
