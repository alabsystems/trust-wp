// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::formula::internal::tuple_lowering::{
    tuple_field_logic_fn_name, tuple_logic_fn_name,
};

use super::*;

/// Verify tuple1 getter axiom: get_0(tuple1(x)) == x.
/// Arity 1 is valid since d6f665e9 (newtype struct decomposition).
#[test]
#[timeout(30000)]
fn test_tuple1_get_0_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let tuple_expr = logic_fn_call(&tuple_logic_fn_name(1), vec![int(42)]);
    let get_0_expr = logic_fn_call(&tuple_field_logic_fn_name(0), vec![tuple_expr]);

    let get_0_term = encoder
        .encode_pure(&get_0_expr)
        .expect("tuple_get_0(tuple1(42)) should encode");
    let forty_two = encoder.encode_pure(&int(42)).unwrap();

    encoder.assert_tuple_axioms();

    // Assert get_0(tuple1(42)) != 42 — should be UNSAT
    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(get_0_term, forty_two);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "get_0(tuple1(42)) must equal 42 after tuple axioms"
    );
}

/// Registered datatype payload bridges should not depend on raw tuple
/// constructor declarations being present in the same query.
#[test]
#[timeout(30000)]
fn test_registered_enum_tuple_get_reconstruction_without_tuple_ctor_decl() {
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]));

    let own_result_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::OwnResult")));
    let getter_name = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    let getter = encoder.solver.declare_fun(
        &getter_name,
        std::slice::from_ref(&own_result_sort),
        Sort::Int,
    );
    encoder
        .decls_for_test_mut()
        .insert_logic_func(getter_name, getter.clone());

    encoder.assert_tuple_axioms();

    let self_term = encoder
        .solver
        .declare_const("self", own_result_sort.clone());
    let datatype = match own_result_sort {
        Sort::Datatype(dt) => dt,
        other => panic!("expected OwnResult datatype sort, got {other:?}"),
    };
    let is_ok = encoder
        .solver
        .try_datatype_tester("Ok", self_term)
        .expect("Ok tester should be available for OwnResult");
    let payload = encoder.solver.apply(&getter, &[self_term]);
    let reconstructed = encoder
        .solver
        .datatype_constructor(&datatype, "Ok", &[payload]);
    let neq = encoder.solver.neq(reconstructed, self_term);

    encoder.assert_term(is_ok);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "getter-only tuple axiom setup should still reconstruct OwnResult::Ok(tuple_get_0(self))"
    );
}

/// Dotted projection bridges must preserve nested datatype payload sorts.
///
/// Re: #1296 — if the bridge declares `tuple_get_0(self)` as `Int` (or as a
/// term-sort alias like `Uninterpreted("Inner")`) for a datatype payload like
/// `self.0: Inner`, the native datatype payload axioms will skip the getter.
#[test]
#[timeout(30000)]
fn test_projection_variable_bridge_preserves_datatype_payload_sort() {
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };
    const INNER_NAME: &str = "ProjectionBridgeInner";
    const INNER_PATH: &str = "crate::ProjectionBridgeInner";
    const RESULT_NAME: &str = "ProjectionBridgeOwnResult";
    const RESULT_PATH: &str = "crate::ProjectionBridgeOwnResult";
    const INNER_ZERO: &str = "ProjectionBridgeInner::Zero";
    const INNER_WRAP: &str = "ProjectionBridgeInner::Wrap";
    const RESULT_OK: &str = "ProjectionBridgeOwnResult::Ok";
    const RESULT_ERR: &str = "ProjectionBridgeOwnResult::Err";

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_adt_decls(&std::collections::HashMap::from([
        (
            INNER_NAME.to_string(),
            AdtDecl::new(
                INNER_PATH.to_string(),
                INNER_NAME.to_string(),
                AdtKind::Enum,
                vec![
                    AdtConstructorDecl::new(INNER_ZERO.to_string(), "Zero".to_string(), vec![]),
                    AdtConstructorDecl::new(
                        INNER_WRAP.to_string(),
                        "Wrap".to_string(),
                        vec![AdtFieldDecl::new("value".to_string(), ExprSort::Int)],
                    ),
                ],
            ),
        ),
        (
            RESULT_NAME.to_string(),
            AdtDecl::new(
                RESULT_PATH.to_string(),
                RESULT_NAME.to_string(),
                AdtKind::Enum,
                vec![
                    AdtConstructorDecl::new(
                        RESULT_OK.to_string(),
                        "Ok".to_string(),
                        vec![AdtFieldDecl::new(
                            "ok".to_string(),
                            ExprSort::Datatype(intern_sort_name(INNER_PATH)),
                        )],
                    ),
                    AdtConstructorDecl::new(
                        RESULT_ERR.to_string(),
                        "Err".to_string(),
                        vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                    ),
                ],
            ),
        ),
    ]));

    let own_result_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name(RESULT_PATH)));
    let inner_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name(INNER_PATH)));

    encoder
        .get_or_declare_var("self", own_result_sort.clone())
        .expect("self should declare with OwnResult sort");
    encoder
        .get_or_declare_var("self.0", inner_sort.clone())
        .expect("self.0 should declare with Inner sort");

    encoder.assert_tuple_axioms();

    let getter_name = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    let getter = encoder
        .decls()
        .get_logic_func(&getter_name)
        .expect("projection bridge should declare tuple_get_0");
    assert_eq!(
        getter.range(),
        &inner_sort,
        "projection bridge must reuse the datatype payload sort"
    );
}

/// Tuple axioms must preserve datatype-typed elements, not just Int/Bool.
#[test]
#[timeout(30000)]
fn test_tuple2_get_0_axiom_with_datatype_elements() {
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "crate::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "OwnResult::Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("ok".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "OwnResult::Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("err".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]));

    let own_result_expr_sort = ExprSort::Datatype(intern_sort_name("crate::OwnResult"));
    let left = var_with_sort("left", own_result_expr_sort.clone());
    let right = var_with_sort("right", own_result_expr_sort.clone());
    let tuple_expr = logic_fn_call(&tuple_logic_fn_name(2), vec![left.clone(), right]);
    let get_0_expr = logic_fn_call(&tuple_field_logic_fn_name(0), vec![tuple_expr]);

    let get_0_term = encoder
        .encode_pure(&get_0_expr)
        .expect("tuple_get_0(tuple2(left, right)) should encode with datatype elements");
    let left_term = encoder
        .encode_pure(&left)
        .expect("left datatype variable should encode");
    let err0 = encoder
        .encode_pure(&logic_fn_call("OwnResult::Err", vec![int(0)]))
        .expect("OwnResult::Err(0) should encode");

    encoder.assert_tuple_axioms();
    // Use encoder.eq_term for sort coercion (OwnResult vs Int). (#994)
    let left_eq_err0 = encoder.eq_term(left_term, err0);
    encoder.assert_term(left_eq_err0);

    let get_0_eq_left = encoder.eq_term(get_0_term, left_term);
    let neq = encoder.solver_mut().not(get_0_eq_left);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "get_0(tuple2(left, right)) must reconstruct the datatype-valued first element"
    );
}

/// Edge case: empty tuple constructor has arity 0, so no accessor axioms apply.
///
/// `get_0(tuple0())` should remain unconstrained after `assert_tuple_axioms()`
/// because index 0 is out-of-range for arity 0.
#[test]
#[timeout(30000)]
fn test_tuple0_get_0_unconstrained() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let tuple_expr = logic_fn_call(&tuple_logic_fn_name(0), vec![]);
    let get_0_expr = logic_fn_call(&tuple_field_logic_fn_name(0), vec![tuple_expr]);

    let get_0_term = encoder
        .encode_pure(&get_0_expr)
        .expect("tuple_get_0(tuple0()) should encode");
    let seven = encoder.encode_pure(&int(7)).unwrap();

    encoder.assert_tuple_axioms();

    // No tuple0 accessor axiom exists, so getter output is unconstrained.
    let eq = {
        let solver = encoder.solver_mut();
        solver.eq(get_0_term, seven)
    };
    encoder.assert_term(eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "get_0(tuple0()) should remain unconstrained (edge case: empty tuple)"
    );

    // Dual check in a fresh context: unconstrained also means get_0(tuple0()) != 7 is SAT.
    let mut encoder2 = AYEncoder::new_with_quantifiers();
    let tuple_expr2 = logic_fn_call(&tuple_logic_fn_name(0), vec![]);
    let get_0_expr2 = logic_fn_call(&tuple_field_logic_fn_name(0), vec![tuple_expr2]);
    let get_0_term2 = encoder2
        .encode_pure(&get_0_expr2)
        .expect("tuple_get_0(tuple0()) should encode in dual check");
    let seven2 = encoder2.encode_pure(&int(7)).unwrap();

    encoder2.assert_tuple_axioms();

    let neq = {
        let solver = encoder2.solver_mut();
        let eq2 = solver.eq(get_0_term2, seven2);
        solver.not(eq2)
    };
    encoder2.assert_term(neq);

    assert!(
        matches!(encoder2.check_sat(), SolveResult::Sat),
        "get_0(tuple0()) != 7 should also be SAT (getter remains unconstrained)"
    );
}

/// Unit singleton: tuple0() is a concrete constant, so two occurrences
/// must be equal. Asserting tuple0() != tuple0() should be UNSAT. (#1271)
#[test]
#[timeout(30000)]
fn test_tuple0_is_concrete_constant() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let t0a = logic_fn_call(&tuple_logic_fn_name(0), vec![]);
    let t0b = logic_fn_call(&tuple_logic_fn_name(0), vec![]);

    let term_a = encoder.encode_pure(&t0a).expect("tuple0() should encode");
    let term_b = encoder.encode_pure(&t0b).expect("tuple0() should encode");

    // Assert tuple0() != tuple0() — should be UNSAT
    let neq = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(term_a, term_b);
        solver.not(eq)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "tuple0() must be self-equal (concrete unit value)"
    );
}

/// Unit singleton axiom: a variable annotated with ExprSort::Unit is
/// constrained to equal __trust_wp_unit after assert_unit_singleton_axioms.
/// Asserting unit_var != tuple0() should be UNSAT. (#1271)
#[test]
#[timeout(30000)]
fn test_unit_sorted_var_equals_tuple0() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode a unit-sorted variable
    let unit_var_expr = var_with_sort("x_unit", ExprSort::Unit);
    let unit_var_term = encoder
        .encode_pure(&unit_var_expr)
        .expect("unit-sorted var should encode");

    // Encode tuple0()
    let tuple0_expr = logic_fn_call(&tuple_logic_fn_name(0), vec![]);
    let tuple0_term = encoder
        .encode_pure(&tuple0_expr)
        .expect("tuple0() should encode");

    // Assert the singleton axioms
    encoder.assert_unit_singleton_axioms();

    // Assert x_unit != tuple0() — should be UNSAT (singleton constraint)
    let neq = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(unit_var_term, tuple0_term);
        solver.not(eq)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unit-sorted variable must equal tuple0() after singleton axiom (#1271)"
    );
}

/// Unit field in tuple decomposition: get_0(tuple1(tuple0())) coerces to 0.
///
/// With #2059 Phase 2, tuple0() returns a Unit-sorted constant and the
/// tuple decomposition axiom skips Unit-sorted elements. The getter returns
/// Unit-sorted, which coerces to Int(0) via sort coercion (Unit is a singleton).
/// ay v0.2.0 enforces strict sort checking, so the Unit→Int coercion is
/// now explicit via eq_term rather than implicit. (#2652)
#[test]
#[timeout(30000)]
fn test_tuple1_with_unit_field_get_0_unconstrained() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Build tuple1(tuple0()) — a struct with a single unit field
    let tuple0 = logic_fn_call(&tuple_logic_fn_name(0), vec![]);
    let tuple1_unit = logic_fn_call(&tuple_logic_fn_name(1), vec![tuple0]);
    let get_0 = logic_fn_call(&tuple_field_logic_fn_name(0), vec![tuple1_unit]);

    let get_0_term = encoder
        .encode_pure(&get_0)
        .expect("get_0(tuple1(tuple0())) should encode");
    let zero = encoder.encode_pure(&int(0)).unwrap();

    encoder.assert_tuple_axioms();

    // get_0(tuple1(tuple0())) == 0 should be SAT: Unit-sorted getter coerces
    // to Int(0) via sort coercion. (#2059, #2652)
    let eq = encoder.eq_term(get_0_term, zero);
    encoder.assert_term(eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "get_0(tuple1(unit)) coerces to 0 after Unit→Int sort coercion (#2652)"
    );
}

/// Verify the core tuple getter axiom: get_0(tuple2(x, y)) == x.
/// Encodes tuple2(10, 20), accesses field 0, and checks equality with 10.
#[test]
#[timeout(30000)]
fn test_tuple2_get_0_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let tuple_expr = logic_fn_call(&tuple_logic_fn_name(2), vec![int(10), int(20)]);
    let get_0_expr = logic_fn_call(&tuple_field_logic_fn_name(0), vec![tuple_expr]);

    let get_0_term = encoder
        .encode_pure(&get_0_expr)
        .expect("tuple_get_0(tuple2(10, 20)) should encode");
    let ten = encoder.encode_pure(&int(10)).unwrap();

    encoder.assert_tuple_axioms();

    // Assert get_0(tuple2(10, 20)) != 10 — should be UNSAT
    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(get_0_term, ten);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "get_0(tuple2(10, 20)) must equal 10 after tuple axioms"
    );
}

/// Verify the second field: get_1(tuple2(x, y)) == y.
#[test]
#[timeout(30000)]
fn test_tuple2_get_1_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let tuple_expr = logic_fn_call(&tuple_logic_fn_name(2), vec![int(10), int(20)]);
    let get_1_expr = logic_fn_call(&tuple_field_logic_fn_name(1), vec![tuple_expr]);

    let get_1_term = encoder
        .encode_pure(&get_1_expr)
        .expect("tuple_get_1(tuple2(10, 20)) should encode");
    let twenty = encoder.encode_pure(&int(20)).unwrap();

    encoder.assert_tuple_axioms();

    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(get_1_term, twenty);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "get_1(tuple2(10, 20)) must equal 20 after tuple axioms"
    );
}

/// Verify 3-tuple: get_2(tuple3(a, b, c)) == c.
#[test]
#[timeout(30000)]
fn test_tuple3_get_2_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let tuple_expr = logic_fn_call(&tuple_logic_fn_name(3), vec![int(1), int(2), int(3)]);
    let get_2_expr = logic_fn_call(&tuple_field_logic_fn_name(2), vec![tuple_expr]);

    let get_2_term = encoder
        .encode_pure(&get_2_expr)
        .expect("tuple_get_2(tuple3(1, 2, 3)) should encode");
    let three = encoder.encode_pure(&int(3)).unwrap();

    encoder.assert_tuple_axioms();

    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(get_2_term, three);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "get_2(tuple3(1, 2, 3)) must equal 3 after tuple axioms"
    );
}

/// Early-exit path: no constructors declared, only accessors.
/// assert_tuple_axioms should return without asserting anything,
/// leaving the accessor uninterpreted (SAT with any value).
#[test]
#[timeout(30000)]
fn test_tuple_axioms_no_constructors_early_exit() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Only declare an accessor (no constructor)
    let get_0_expr = logic_fn_call(&tuple_field_logic_fn_name(0), vec![var("t")]);
    let get_0_term = encoder
        .encode_pure(&get_0_expr)
        .expect("tuple_get_0(t) should encode");
    let eleven = encoder.encode_pure(&int(11)).unwrap();

    // Call axioms — should early-exit because no constructors
    encoder.assert_tuple_axioms();

    // Without axioms, get_0(t) is unconstrained — equality to any literal is SAT.
    let eq = {
        let solver = encoder.solver_mut();
        solver.eq(get_0_term, eleven)
    };
    encoder.assert_term(eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "No tuple constructors declared; get_0(t) == 11 should be SAT"
    );

    // Dual check: inequality to the same literal is also SAT in a fresh context.
    let mut encoder2 = AYEncoder::new_with_quantifiers();
    let get_0_expr2 = logic_fn_call(&tuple_field_logic_fn_name(0), vec![var("t")]);
    let get_0_term2 = encoder2
        .encode_pure(&get_0_expr2)
        .expect("tuple_get_0(t) should encode in dual check");
    let eleven2 = encoder2.encode_pure(&int(11)).unwrap();

    encoder2.assert_tuple_axioms();

    let neq = {
        let solver = encoder2.solver_mut();
        let eq2 = solver.eq(get_0_term2, eleven2);
        solver.not(eq2)
    };
    encoder2.assert_term(neq);

    assert!(
        matches!(encoder2.check_sat(), SolveResult::Sat),
        "No tuple constructors declared; get_0(t) != 11 should also be SAT"
    );
}

/// Index >= arity skip: get_2 should not apply to a tuple2 constructor.
/// Assert get_2(tuple2(10, 20)) == 99 should be SAT (accessor is
/// unconstrained for this constructor since index >= arity).
#[test]
#[timeout(30000)]
fn test_tuple_axiom_index_exceeds_arity_unconstrained() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let tuple_expr = logic_fn_call(&tuple_logic_fn_name(2), vec![int(10), int(20)]);
    // get_2 on a 2-tuple: index 2 >= arity 2, so no axiom
    let get_2_expr = logic_fn_call(&tuple_field_logic_fn_name(2), vec![tuple_expr]);

    let get_2_term = encoder
        .encode_pure(&get_2_expr)
        .expect("tuple_get_2(tuple2(10, 20)) should encode");
    let ninety_nine = encoder.encode_pure(&int(99)).unwrap();

    encoder.assert_tuple_axioms();

    // Assert get_2(tuple2(10, 20)) == 99 — should be SAT because
    // no axiom constrains get_2 for a 2-tuple
    let eq_term = {
        let solver = encoder.solver_mut();
        solver.eq(get_2_term, ninety_nine)
    };
    encoder.assert_term(eq_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "get_2 applied to tuple2 should be unconstrained (index >= arity)"
    );

    // Dual check in a fresh context: get_2(tuple2(...)) != 99 is also SAT.
    let mut encoder2 = AYEncoder::new_with_quantifiers();
    let tuple_expr2 = logic_fn_call(&tuple_logic_fn_name(2), vec![int(10), int(20)]);
    let get_2_expr2 = logic_fn_call(&tuple_field_logic_fn_name(2), vec![tuple_expr2]);
    let get_2_term2 = encoder2
        .encode_pure(&get_2_expr2)
        .expect("tuple_get_2(tuple2(10, 20)) should encode in dual check");
    let ninety_nine2 = encoder2.encode_pure(&int(99)).unwrap();

    encoder2.assert_tuple_axioms();

    let neq = {
        let solver = encoder2.solver_mut();
        let eq2 = solver.eq(get_2_term2, ninety_nine2);
        solver.not(eq2)
    };
    encoder2.assert_term(neq);

    assert!(
        matches!(encoder2.check_sat(), SolveResult::Sat),
        "get_2 applied to tuple2 should remain unconstrained (not forced to 99)"
    );
}

/// Tuple with Bool element: get_0(tuple2(true, 5)) coerces to 1 (Int).
///
/// Before #837, axiom bound variables were hardcoded to Sort::Int,
/// so ay's E-matching wouldn't fire for Bool-sorted elements.
/// The axiom uses ite(x0, 1, 0) to bridge Bool elements to Int getters.
/// Part of #837
#[test]
#[timeout(30000)]
fn test_tuple2_bool_element_get_0_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let tuple_expr = logic_fn_call(&tuple_logic_fn_name(2), vec![bool_expr(true), int(5)]);
    let get_0_expr = logic_fn_call(&tuple_field_logic_fn_name(0), vec![tuple_expr]);

    let get_0_term = encoder
        .encode_pure(&get_0_expr)
        .expect("tuple_get_0(tuple2(true, 5)) should encode");
    // The getter returns Int; Bool `true` coerces to Int `1` via ite
    let one = encoder.encode_pure(&int(1)).unwrap();

    encoder.assert_tuple_axioms();

    // Assert get_0(tuple2(true, 5)) != 1 — should be UNSAT
    // Use eq_term for sort coercion: get_0 returns Bool-sorted (from `true`),
    // one is Int. ay v0.2.0 enforces strict sort checking. (#2652)
    let eq = encoder.eq_term(get_0_term, one);
    let neq = encoder.solver_mut().not(eq);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "get_0(tuple2(true, 5)) must equal 1 (ite(true,1,0)) after tuple axioms (#837)"
    );
}

/// A `Bool`-ranged getter over an `Int` tuple payload must NOT receive the
/// quantified defining axiom.
///
/// `select_structural_sort_target(Bool, Int)` answers `Some(Bool)`, and
/// `eq_term` bridges the pair as `ite(get_1(tuple2(x0, x1)), 1, 0) = x1`.
/// Quantified over `x1: Int` that axiom says every integer is 0 or 1, so it is
/// unsatisfiable ON ITS OWN and turns every obligation carrying it into a
/// vacuous, genuinely checkable UNSAT. Measured on the checked-add tuple of
/// tests/adversarial/cases/s34_field_nested_struct.rs, where the false
/// `(^o).i.x == o.i.x` was credited `verified` (z3: the lone axiom is unsat).
///
/// Structural, not solver-outcome, on purpose: whether E-matching happens to
/// refute the stack within a unit-test budget is not deterministic, while the
/// emitted quantifier is. The companion arm pins that the legitimate `Int`
/// getter over the same payload still gets its axiom, so the test fails if the
/// emitter stops emitting altogether.
#[test]
#[timeout(30000)]
fn test_tuple_axiom_bool_getter_over_int_payload_is_not_asserted() {
    fn quantified_assertions(encoder: &AYEncoder) -> usize {
        let solver = encoder.solver();
        solver
            .assertions()
            .iter()
            .filter(|&&term| {
                matches!(
                    solver.term_kind(term),
                    ay_dpll::api::TermKind::Forall | ay_dpll::api::TermKind::Exists
                )
            })
            .count()
    }

    let emitted_axioms = |getter_range: Sort| {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let tuple_sort = Sort::Uninterpreted("Tuple2".to_string());
        let ctor_name = trust_wp_core::logic::logic_fn_smt_name(&tuple_logic_fn_name(2));
        let get_1_name = trust_wp_core::logic::logic_fn_smt_name(&tuple_field_logic_fn_name(1));
        encoder.get_or_declare_logic_func(&ctor_name, &[Sort::Int, Sort::Int], tuple_sort.clone());
        encoder.get_or_declare_logic_func(&get_1_name, &[tuple_sort], getter_range);
        let before = quantified_assertions(&encoder);
        encoder.assert_tuple_axioms();
        quantified_assertions(&encoder) - before
    };

    assert_eq!(
        emitted_axioms(Sort::Bool),
        0,
        "a Bool get_1 over an Int payload must not assert \
         `forall x0 x1. ite(get_1(tuple2(x0, x1)), 1, 0) = x1` (every Int is 0 or 1)"
    );
    assert_eq!(
        emitted_axioms(Sort::Int),
        1,
        "the sort-faithful Int get_1 over the same payload keeps its defining axiom"
    );
}
