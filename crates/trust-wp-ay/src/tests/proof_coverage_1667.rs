// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Focused proof-coverage tests for #1667.
//!
//! Covers two previously under-tested paths:
//! - `encode_constructor_test` fallback for `Some`/`None` under conflicting scrutinee sort
//! - `encode_formula_bool_expansion` single-variable formula quantifiers

use ntest::timeout;
use trust_wp_core::formula::Pattern;

use super::{super::*, helpers::*};

fn option_some_none_match_with_binding(scrutinee: &str) -> PureExpr {
    match_expr(
        var(scrutinee),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                add(var("v"), int(1)),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    )
}

fn option_some_none_match_constant_arms(scrutinee: &str) -> PureExpr {
    match_expr(
        var(scrutinee),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: None,
                },
                int(1),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    )
}

/// Force the Some/None UF fallback path (conflicting `x: Int`) and prove the
/// Some branch condition is encoded via `is_some(x)`.
#[test]
#[timeout(30000)]
fn option_some_fallback_enforces_some_branch_semantics() {
    let expr = option_some_none_match_constant_arms("x");

    // UNSAT: is_some(x) ∧ result!=1
    let mut encoder = AYEncoder::new();
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("should predeclare x as Int to force UF fallback");
    let result = encoder
        .encode_pure(&expr)
        .expect("Some/None match should encode on UF fallback path");
    let x_int_use = encoder.encode_pure(&add(var("x"), int(1)));
    assert!(
        x_int_use.is_ok(),
        "UF fallback should preserve predeclared x:Int binding: {x_int_use:?}"
    );

    let is_some = encoder
        .decls()
        .get_spec_func("is_some")
        .cloned()
        .expect("is_some tester should be declared on UF fallback path");

    let is_some_x = encoder.solver.apply(&is_some, &[x]);
    encoder.solver.assert_term(is_some_x);

    let one = encoder.solver.int_const(1);
    let result_eq_one = encoder.solver.eq(result, one);
    let result_neq_one = encoder.solver.not(result_eq_one);
    encoder.solver.assert_term(result_neq_one);

    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "is_some(x) should force Some arm result=1; got {sat:?}"
    );

    // SAT dual: the expected branch result should be consistent.
    let mut encoder2 = AYEncoder::new();
    let x2 = encoder2
        .get_or_declare_var("x", Sort::Int)
        .expect("should predeclare x as Int to force UF fallback");
    let result2 = encoder2
        .encode_pure(&expr)
        .expect("Some/None match should encode on UF fallback path");

    let is_some2 = encoder2
        .decls()
        .get_spec_func("is_some")
        .cloned()
        .expect("is_some tester should be declared on UF fallback path");

    let is_some_x2 = encoder2.solver.apply(&is_some2, &[x2]);
    encoder2.solver.assert_term(is_some_x2);

    let one2 = encoder2.solver.int_const(1);
    let result_eq_one2 = encoder2.solver.eq(result2, one2);
    encoder2.solver.assert_term(result_eq_one2);

    let sat2 = encoder2.check_sat();
    assert!(
        matches!(sat2, SolveResult::Sat),
        "is_some(x) ∧ result=1 should be satisfiable: {sat2:?}"
    );
}

/// Force the Some/None UF fallback path (conflicting `x: Int`) and prove the
/// None branch is exactly `!is_some(x)`.
#[test]
#[timeout(30000)]
fn option_none_fallback_enforces_none_branch_semantics() {
    let expr = option_some_none_match_with_binding("x");

    // UNSAT: !is_some(x) ∧ result!=0
    let mut encoder = AYEncoder::new();
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("should predeclare x as Int to force UF fallback");
    let result = encoder
        .encode_pure(&expr)
        .expect("Some/None match should encode on UF fallback path");
    let x_int_use = encoder.encode_pure(&add(var("x"), int(1)));
    assert!(
        x_int_use.is_ok(),
        "UF fallback should preserve predeclared x:Int binding: {x_int_use:?}"
    );

    let is_some = encoder
        .decls()
        .get_spec_func("is_some")
        .cloned()
        .expect("is_some tester should be declared on UF fallback path");
    let is_some_x = encoder.solver.apply(&is_some, &[x]);
    let not_is_some_x = encoder.solver.not(is_some_x);
    encoder.solver.assert_term(not_is_some_x);

    let zero = encoder.solver.int_const(0);
    let result_eq_zero = encoder.solver.eq(result, zero);
    let result_neq_zero = encoder.solver.not(result_eq_zero);
    encoder.solver.assert_term(result_neq_zero);

    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "!is_some(x) should force None arm result=0; got {sat:?}"
    );

    // SAT dual: !is_some(x) ∧ result=0 should be satisfiable.
    let mut encoder2 = AYEncoder::new();
    let x2 = encoder2
        .get_or_declare_var("x", Sort::Int)
        .expect("should predeclare x as Int to force UF fallback");
    let result2 = encoder2
        .encode_pure(&expr)
        .expect("Some/None match should encode on UF fallback path");

    let is_some2 = encoder2
        .decls()
        .get_spec_func("is_some")
        .cloned()
        .expect("is_some tester should be declared on UF fallback path");
    let is_some_x2 = encoder2.solver.apply(&is_some2, &[x2]);
    let not_is_some_x2 = encoder2.solver.not(is_some_x2);
    encoder2.solver.assert_term(not_is_some_x2);

    let zero2 = encoder2.solver.int_const(0);
    let result_eq_zero2 = encoder2.solver.eq(result2, zero2);
    encoder2.solver.assert_term(result_eq_zero2);

    let sat2 = encoder2.check_sat();
    assert!(
        matches!(sat2, SolveResult::Sat),
        "!is_some(x) ∧ result=0 should be satisfiable: {sat2:?}"
    );
}

/// Dedicated single-variable `Formula::Forall` Bool expansion test:
/// `forall b. (b || c)` should reduce to `c` and preserve free-`c` semantics.
#[test]
#[timeout(30000)]
fn formula_forall_single_bool_expansion_unsat_dual_sat() {
    let formula = formula_forall("b", pure(or(var("b"), var("c"))));

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("c", Sort::Bool)
        .expect("seed free c:Bool for non-tautological forall expansion check");
    let term = encoder
        .encode(&formula)
        .expect("formula forall bool should encode via single-var bool expansion");
    encoder.assert_term(term);
    let not_c = encoder
        .encode_pure(&not(var("c")))
        .expect("free c:Bool should be available after forall encoding");
    encoder.assert_term(not_c);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "forall b. (b || c) with c=false should be Unsat, got {sat:?}"
    );

    // SAT dual: with c=true, `forall b. (b || c)` should be satisfiable.
    let mut encoder2 = AYEncoder::new_with_quantifiers();
    encoder2
        .get_or_declare_var("c", Sort::Bool)
        .expect("seed free c:Bool for non-tautological forall expansion check");
    let term2 = encoder2
        .encode(&formula)
        .expect("formula forall bool should encode via single-var bool expansion");
    encoder2.assert_term(term2);
    let c_true = encoder2
        .encode_pure(&var("c"))
        .expect("free c:Bool should be available after forall encoding");
    encoder2.assert_term(c_true);
    let sat2 = encoder2.check_sat();
    assert!(
        matches!(sat2, SolveResult::Sat),
        "forall b. (b || c) with c=true should be Sat, got {sat2:?}"
    );
}

/// Dedicated single-variable `Formula::Exists` Bool expansion test:
/// `exists b. (b && c)` should reduce to `c` and be non-tautological.
/// Also checks old-binding restore branch in `encode_formula_bool_expansion`
/// with a same-sort predeclared Bool symbol.
#[test]
#[timeout(30000)]
fn formula_exists_single_bool_expansion_sat_dual_unsat_and_restores_binding() {
    let formula = formula_exists("b", pure(and(var("b"), var("c"))));

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("b", Sort::Bool)
        .expect("seed free b:Bool to exercise old-binding restore path");
    encoder
        .get_or_declare_var("c", Sort::Bool)
        .expect("seed free c:Bool for non-tautological exists expansion check");

    let term = encoder
        .encode(&formula)
        .expect("formula exists bool should encode via single-var bool expansion");
    encoder.assert_term(term);
    let c_true = encoder
        .encode_pure(&var("c"))
        .expect("free c:Bool should be available after exists encoding");
    encoder.assert_term(c_true);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Sat),
        "exists b. (b && c) with c=true should be Sat after bool expansion, got {sat:?}"
    );

    // Restore-path check: free `b` should remain Bool after quantified-body encoding.
    let bool_use = not(var("b"));
    let bool_use_result = encoder.encode_pure(&bool_use);
    assert!(
        bool_use_result.is_ok(),
        "quantifier encoding should restore prior Bool binding for free `b`: {bool_use_result:?}"
    );

    // UNSAT dual: with c=false, `exists b. (b && c)` should be unsatisfiable.
    let mut encoder2 = AYEncoder::new_with_quantifiers();
    encoder2
        .get_or_declare_var("b", Sort::Bool)
        .expect("seed free b:Bool to exercise old-binding restore path");
    encoder2
        .get_or_declare_var("c", Sort::Bool)
        .expect("seed free c:Bool for non-tautological exists expansion check");
    let term2 = encoder2
        .encode(&formula)
        .expect("formula exists bool should encode via single-var bool expansion");
    encoder2.assert_term(term2);
    let not_c = encoder2
        .encode_pure(&not(var("c")))
        .expect("free c:Bool should be available after exists encoding");
    encoder2.assert_term(not_c);
    let sat2 = encoder2.check_sat();
    assert!(
        matches!(sat2, SolveResult::Unsat(_)),
        "exists b. (b && c) with c=false should be Unsat, got {sat2:?}"
    );

    let bool_use2 = not(var("b"));
    let bool_use_result2 = encoder2.encode_pure(&bool_use2);
    assert!(
        bool_use_result2.is_ok(),
        "quantifier encoding should restore prior Bool binding for free `b`: {bool_use_result2:?}"
    );
}
