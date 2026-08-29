// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort, Term, TermKind};
#[allow(unused_imports)]
use trust_wp_core::formula::{ExprSort, MatchArm, Pattern};

use super::*;

fn term_contains_quantifier(encoder: &AYEncoder, term: Term) -> bool {
    let solver = encoder.solver();
    let mut stack = vec![term];
    let mut seen = std::collections::HashSet::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(solver.term_kind(term), TermKind::Forall | TermKind::Exists) {
            return true;
        }
        stack.extend(solver.term_children(term));
    }
    false
}

/// Integration test: register axiom + ground term, then instantiate.
///
/// Sets up `f(x) = x + 1` as a defining axiom, registers a ground call
/// `f(5)`, and asserts the ground instance. Then checks that the solver
/// can prove `f(5) = 6`.
#[test]
#[timeout(30000)]
fn test_ground_pool_instantiation_pipeline() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Declare f: Int -> Int
    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_f",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    // Register axiom: forall x. f(x) = x + 1
    // (body in PureExpr: BinOp(Var("x"), Add, Int(1)))
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_f".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    // Register ground call: f(5) with SMT term
    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder
        .ground_pool
        .register("logic_fn_f", f_of_5, vec![five], vec![PureExpr::Int(5)]);

    // Instantiate ground instances
    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(count, 1, "should instantiate 1 ground instance");

    // Now the solver should know f(5) = 6
    // Assert f(5) != 6 and check for UNSAT
    let six = encoder.solver.int_const(6);
    let f5_eq_6 = encoder.solver.eq(f_of_5, six);
    let not_f5_eq_6 = encoder.solver.not(f5_eq_6);
    encoder.solver.assert_term(not_f5_eq_6);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "should be UNSAT: ground instance f(5) = 5+1 = 6 contradicts f(5) != 6, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_ground_pool_quantified_bool_definition_uses_one_way_unfolding() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;
    let bool_sort = ay_dpll::api::Sort::Bool;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_quant_pred",
        std::slice::from_ref(&int_sort),
        bool_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_quant_pred".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Forall {
            var: "y".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::Bool(true)),
            triggers: Vec::new(),
        },
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: bool_sort,
        kind: AxiomKind::Defining,
    });

    let zero = encoder.solver.int_const(0);
    let pred_zero = encoder.solver.apply(&func_decl, &[zero]);
    encoder.ground_pool.register(
        "logic_fn_quant_pred",
        pred_zero,
        vec![zero],
        vec![PureExpr::Int(0)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("quantified bool predicate instantiation should succeed");
    assert_eq!(count, 1);

    let not_pred_zero = encoder.solver.not(pred_zero);
    encoder.solver.assert_term(not_pred_zero);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "quantified Bool predicate ground instances should not assert the reverse direction; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_postcondition_critical_quantified_bool_definition_is_bidirectional() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;
    let bool_sort = ay_dpll::api::Sort::Bool;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_quant_post_pred",
        std::slice::from_ref(&int_sort),
        bool_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_quant_post_pred".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Forall {
            var: "y".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::Bool(true)),
            triggers: Vec::new(),
        },
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: bool_sort,
        kind: AxiomKind::Defining,
    });
    encoder
        .ground_pool
        .mark_postcondition_symbol("logic_fn_quant_post_pred".to_string());

    let zero = encoder.solver.int_const(0);
    let pred_zero = encoder.solver.apply(&func_decl, &[zero]);
    encoder.ground_pool.register(
        "logic_fn_quant_post_pred",
        pred_zero,
        vec![zero],
        vec![PureExpr::Int(0)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("critical quantified Bool predicate instantiation should succeed");
    assert_eq!(count, 1);

    let not_pred_zero = encoder.solver.not(pred_zero);
    encoder.solver.assert_term(not_pred_zero);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "postcondition-critical quantified Bool definitions need the reverse direction; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_late_postcondition_marking_reflushes_quantified_bool_definition() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;
    let bool_sort = ay_dpll::api::Sort::Bool;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_late_quant_post_pred",
        std::slice::from_ref(&int_sort),
        bool_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_late_quant_post_pred".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Forall {
            var: "y".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::Bool(true)),
            triggers: Vec::new(),
        },
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: bool_sort,
        kind: AxiomKind::Defining,
    });

    let zero = encoder.solver.int_const(0);
    let pred_zero = encoder.solver.apply(&func_decl, &[zero]);
    encoder.ground_pool.register(
        "logic_fn_late_quant_post_pred",
        pred_zero,
        vec![zero],
        vec![PureExpr::Int(0)],
    );

    let weak_count = encoder
        .assert_ground_pool_instances()
        .expect("non-critical quantified Bool predicate instantiation should succeed");
    assert_eq!(weak_count, 1);
    assert!(
        !encoder.ground_pool.needs_flush(),
        "initial flush should mark the current revision asserted"
    );

    encoder
        .ground_pool
        .mark_postcondition_symbol("logic_fn_late_quant_post_pred".to_string());
    assert!(
        encoder.ground_pool.needs_flush(),
        "late critical marking must invalidate a prior weak flush"
    );

    let strong_count = encoder
        .assert_ground_pool_instances()
        .expect("late critical quantified Bool predicate instantiation should reflush");
    assert_eq!(strong_count, 1);

    let not_pred_zero = encoder.solver.not(pred_zero);
    encoder.solver.assert_term(not_pred_zero);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "late postcondition marking should strengthen the Bool definition; got {result:?}"
    );
}

/// Regression for the PersistentArray protocol path: instantiating one
/// defining axiom can reveal the ground application for the next axiom. The
/// second application uses `Snapshot::new(pc)`, which should normalize to the
/// same raw key term registered for the protocol call.
#[test]
#[timeout(30000)]
fn test_ground_pool_chains_entries_registered_during_axiom_encoding() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;
    let bool_sort = ay_dpll::api::Sort::Bool;

    let protocol_source = "slot7s_protocol";
    let partial_source = "slot7s_partial";
    let protocol_smt = trust_wp_core::logic::logic_fn_smt_name(protocol_source);
    let partial_smt = trust_wp_core::logic::logic_fn_smt_name(partial_source);

    let protocol_decl = encoder.get_or_declare_logic_func(
        &protocol_smt,
        std::slice::from_ref(&int_sort),
        bool_sort.clone(),
    );
    let partial_decl = encoder.get_or_declare_logic_func(
        &partial_smt,
        std::slice::from_ref(&int_sort),
        bool_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: protocol_smt.clone(),
        params: vec!["pc".to_string()],
        body: PureExpr::LogicFnCall {
            name: partial_source.to_string(),
            args: vec![PureExpr::LogicFnCall {
                name: "Snapshot::new".to_string(),
                args: vec![PureExpr::Var("pc".to_string(), None)],
            }],
        },
        requires: vec![],
        func_decl: protocol_decl.clone(),
        return_sort: bool_sort.clone(),
        kind: AxiomKind::Defining,
    });

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: partial_smt.clone(),
        params: vec!["snap_pc".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("snap_pc".to_string(), None)),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::Int(7)),
        ),
        requires: vec![],
        func_decl: partial_decl.clone(),
        return_sort: bool_sort,
        kind: AxiomKind::Defining,
    });

    let seven = encoder.solver.int_const(7);
    let protocol_7 = encoder.solver.apply(&protocol_decl, &[seven]);
    encoder.ground_pool.register(
        &protocol_smt,
        protocol_7,
        vec![seven],
        vec![PureExpr::Int(7)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("chained ground instantiation should succeed");
    assert_eq!(
        count, 2,
        "protocol instantiation should expose and instantiate the partial-invariant call"
    );

    let partial_7 = encoder.solver.apply(&partial_decl, &[seven]);
    let not_partial_7 = encoder.solver.not(partial_7);
    encoder.solver.assert_term(not_partial_7);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "partial-invariant fact registered through Snapshot::new should make not partial(7) UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_ground_pool_invalid_fn_application_returns_error() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder
        .solver
        .declare_fun("logic_fn_bad", &[], int_sort.clone());

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_bad".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        requires: vec![],
        func_decl,
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    encoder
        .ground_pool
        .register("logic_fn_bad", five, vec![five], vec![PureExpr::Int(5)]);

    let result = encoder.assert_ground_pool_instances();
    match result {
        Err(crate::error::EncodingError::SolverError { message, .. }) => {
            assert!(
                message.contains("ground_pool::logic_fn_bad::fn_app"),
                "expected ground-pool application context in error, got: {message}"
            );
            assert!(
                message.contains("arity mismatch"),
                "expected arity-mismatch detail in error, got: {message}"
            );
        }
        other => {
            panic!("invalid ground-pool fn application should return solver error, got {other:?}")
        }
    }
}

#[test]
#[timeout(30000)]
fn test_ground_pool_invalid_fn_application_cleans_bindings() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder
        .solver
        .declare_fun("logic_fn_bad_cleanup", &[], int_sort.clone());

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_bad_cleanup".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        requires: vec![],
        func_decl,
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    encoder.ground_pool.register(
        "logic_fn_bad_cleanup",
        five,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let result = encoder.assert_ground_pool_instances();
    assert!(
        matches!(result, Err(crate::error::EncodingError::SolverError { .. })),
        "invalid ground-pool application should still error"
    );
    assert!(
        !encoder.quantifier_state.has_bound_vars(),
        "error path must not leak logical bindings into later encodes"
    );
    assert!(
        !encoder.has_var("x"),
        "error path must restore ground-pool parameter bindings"
    );

    let deref_x = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));
    let deref_term = encoder
        .encode_pure(&deref_x)
        .expect("encoder should remain usable after ground-pool apply error");
    assert_ne!(
        deref_term, five,
        "stale logical binding must not collapse *x to the prior ground argument"
    );
}

/// Regression for #1635: a prior `View(param)` encoding can mark the formal
/// parameter name as having an asserted view identity. Ground instantiation
/// must still encode `View(param)` against the concrete ground argument, not a
/// stale free `{param}_view` variable from the earlier scope.
#[test]
#[timeout(30000)]
fn test_ground_pool_view_param_instantiation_ignores_stale_view_identity() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_view_add",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    let view_param = PureExpr::View(Arc::new(PureExpr::Var("p".to_string(), None)));
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_view_add".to_string(),
        params: vec!["p".to_string()],
        body: PureExpr::BinOp(
            Arc::new(view_param.clone()),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    // Seed the encoder with the same stale param-name view identity the
    // quantified registration path used to leave behind.
    let seeded_param = encoder
        .solver
        .fresh_var("seed_param", ay_dpll::api::Sort::Int);
    encoder.rebind_var("p", seeded_param, ay_dpll::api::Sort::Int);
    let _ = encoder
        .encode_pure(&view_param)
        .expect("seeding stale param view identity should succeed");
    encoder.remove_var("p");
    encoder.remove_var_sort("p");

    let m = encoder.solver.declare_const("m", ay_dpll::api::Sort::Int);
    let view_add_m = encoder.solver.apply(&func_decl, &[m]);
    encoder.ground_pool.register(
        "logic_fn_view_add",
        view_add_m,
        vec![m],
        vec![PureExpr::Var("m".to_string(), None)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("ground instantiation should succeed");
    assert_eq!(count, 1, "should instantiate exactly one ground view axiom");

    let one = encoder.solver.int_const(1);
    let m_plus_one = encoder.solver.add(m, one);
    let expected_eq = encoder.solver.eq(view_add_m, m_plus_one);
    let contradiction = encoder.solver.not(expected_eq);
    encoder.solver.assert_term(contradiction);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground instance should force logic_fn_view_add(m) = m + 1 despite prior stale view identity, got {result:?}"
    );
}

fn slot12e_list_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "List".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Nil".to_string(),
            fields: vec![],
        }],
    }
}

fn slot12e_hashmap_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "MyHashMap".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "MyHashMap".to_string(),
            fields: vec![DatatypeField {
                name: "myhashmap_buckets".to_string(),
                sort: Sort::seq(Sort::Int),
            }],
        }],
    }
}

#[test]
#[timeout(30000)]
fn test_ground_pool_view_final_bound_param_does_not_leak_derived_self_sort() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let list_dt = slot12e_list_datatype();
    let hashmap_dt = slot12e_hashmap_datatype();
    encoder.ensure_datatype_declared(&list_dt);
    encoder.ensure_datatype_declared(&hashmap_dt);
    let list_sort = Sort::Datatype(list_dt);
    let hashmap_sort = Sort::Datatype(hashmap_dt);

    let func_decl = encoder.solver.declare_fun(
        "logic_fn_slot12e_view_final_self",
        std::slice::from_ref(&list_sort),
        list_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_slot12e_view_final_self".to_string(),
        params: vec!["self".to_string()],
        body: PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "self".to_string(),
            None,
        ))))),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: list_sort.clone(),
        kind: AxiomKind::Defining,
    });

    let list_ground = encoder
        .solver
        .declare_const("slot12e_list_ground", list_sort.clone());
    let fn_app = encoder.solver.apply(&func_decl, &[list_ground]);
    encoder.ground_pool.register(
        "logic_fn_slot12e_view_final_self",
        fn_app,
        vec![list_ground],
        vec![PureExpr::Var("slot12e_list_ground".to_string(), None)],
    );

    encoder
        .get_or_declare_var("self_final", hashmap_sort.clone())
        .expect("outer receiver final variable should predeclare as MyHashMap");

    let count = encoder
        .assert_ground_pool_instances()
        .expect("View(Final(bound self)) should collapse to the ground argument");

    assert_eq!(count, 1);
    assert_eq!(encoder.var_sort("self_final"), Some(&hashmap_sort));
    assert!(
        encoder.var_sort("final_self_view").is_none(),
        "bound-param view/final encoding must not leak derived param names"
    );
}

/// Verify spec axiom ground instantiation produces a direct assertion
/// (not a defining equality) (#1965, Lane 5).
///
/// Sets up `f(x)` with a spec axiom `ensures(f(x) > x)`, registers a
/// ground call `f(5)`, and verifies the ground instance asserts `f(5) > 5`.
#[test]
#[timeout(30000)]
fn test_spec_axiom_ground_instantiation() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Declare f: Int -> Int
    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_f",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    // Register spec axiom: forall x. f(x) > x
    // Body in PureExpr: BinOp(Var("result"), Gt, Var("x"))
    // With kind: Spec, the "result" var will be bound to f(ground_args)
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_f".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Var("x".to_string(), None)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    // Register ground call: f(5)
    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder
        .ground_pool
        .register("logic_fn_f", f_of_5, vec![five], vec![PureExpr::Int(5)]);

    // Instantiate ground instances — should assert f(5) > 5
    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(count, 1, "should instantiate 1 spec axiom ground instance");

    // The solver now knows f(5) > 5.
    // Assert f(5) <= 5 and check for UNSAT.
    let f5_gt_5 = encoder.solver.gt(f_of_5, five);
    let not_f5_gt_5 = encoder.solver.not(f5_gt_5);
    encoder.solver.assert_term(not_f5_gt_5);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "should be UNSAT: spec ground instance f(5) > 5 contradicts !(f(5) > 5), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_spec_match_result_ground_instantiation_emits_branch_facts() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_find_like",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_find_like".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("result".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Bool(true),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("j".to_string()))),
                    },
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Var("j".to_string(), None)),
                        trust_wp_core::formula::BinOp::Gt,
                        Arc::new(PureExpr::Var("x".to_string(), None)),
                    ),
                },
            ],
        },
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder.ground_pool.register(
        "logic_fn_find_like",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let assertions_before = encoder.solver.assertions().len();
    let count = encoder
        .assert_ground_pool_instances()
        .expect("match-result spec instantiation should succeed");
    assert_eq!(count, 1, "one observed call is one ground instance");
    let assertions_added = encoder.solver.assertions().len() - assertions_before;
    assert!(
        assertions_added >= 3,
        "match-result spec should assert the base instance plus branch-local facts"
    );

    let is_some_decl = encoder.get_or_declare_constructor_tester_for_sort("is_some", &Sort::Int);
    let unwrap_decl =
        encoder.get_or_declare_accessor_for_sorts("spec_unwrap", &Sort::Int, &Sort::Int);
    let is_some = encoder.solver.apply(&is_some_decl, &[f_of_5]);
    let payload = encoder.solver.apply(&unwrap_decl, &[f_of_5]);
    encoder.solver.assert_term(is_some);
    let payload_gt_five = encoder.solver.gt(payload, five);
    let not_payload_gt_five = encoder.solver.not(payload_gt_five);
    encoder.solver.assert_term(not_payload_gt_five);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "Some branch fact should force spec_unwrap(f(5)) > 5, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_spec_match_result_none_branch_forall_instantiates_observed_int_terms() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_find_like_forall",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_find_like_forall".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("result".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Forall {
                        var: "j".to_string(),
                        var_sort: Some(ExprSort::Int),
                        body: Arc::new(PureExpr::BinOp(
                            Arc::new(PureExpr::Var("j".to_string(), None)),
                            trust_wp_core::formula::BinOp::Ge,
                            Arc::new(PureExpr::Var("x".to_string(), None)),
                        )),
                        triggers: vec![],
                    },
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("payload".to_string()))),
                    },
                    body: PureExpr::Bool(true),
                },
            ],
        },
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder.ground_pool.register(
        "logic_fn_find_like_forall",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let w = encoder.solver.declare_const("observed_w", Sort::Int);
    let observed_decl = encoder.solver.declare_fun(
        "observed_int_use",
        std::slice::from_ref(&Sort::Int),
        Sort::Int,
    );
    let observed_w = encoder.solver.apply(&observed_decl, &[w]);
    encoder.ground_pool.register(
        "observed_int_use",
        observed_w,
        vec![w],
        vec![PureExpr::Var("observed_w".to_string(), Some(ExprSort::Int))],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("match-result forall branch instantiation should succeed");
    assert_eq!(count, 1, "one observed logic call is one ground instance");

    let is_some_decl = encoder.get_or_declare_constructor_tester_for_sort("is_some", &Sort::Int);
    let is_some = encoder.solver.apply(&is_some_decl, &[f_of_5]);
    let is_none = encoder.solver.not(is_some);
    encoder.solver.assert_term(is_none);
    let w_lt_five = encoder.solver.lt(w, five);
    encoder.solver.assert_term(w_lt_five);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "None branch forall should instantiate at observed_w and force observed_w >= 5, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_spec_match_result_forall_candidates_ignore_quantifier_assertion_bodies() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_find_like_quantifier_candidate_filter",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_find_like_quantifier_candidate_filter".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("result".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Forall {
                        var: "j".to_string(),
                        var_sort: Some(ExprSort::Int),
                        body: Arc::new(PureExpr::BinOp(
                            Arc::new(PureExpr::Var("j".to_string(), None)),
                            trust_wp_core::formula::BinOp::Ge,
                            Arc::new(PureExpr::Var("x".to_string(), None)),
                        )),
                        triggers: vec![],
                    },
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("payload".to_string()))),
                    },
                    body: PureExpr::Bool(true),
                },
            ],
        },
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Spec,
    });

    let q = encoder
        .solver
        .fresh_var("qvar_candidate_leak", int_sort.clone());
    let logic = encoder
        .solver
        .fresh_var("logic_param_candidate_leak", int_sort.clone());
    let spec = encoder
        .solver
        .fresh_var("spec_param_candidate_leak", int_sort.clone());
    let one = encoder.solver.int_const(1);
    let base = encoder.solver.add(q, logic);
    let base = encoder.solver.add(base, spec);
    let lhs = encoder.solver.add(base, one);
    let tautology = encoder.solver.ge(lhs, base);
    let quantified = encoder.solver.forall(&[q, logic, spec], tautology);
    encoder.solver.assert_term(quantified);

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder.ground_pool.register(
        "logic_fn_find_like_quantifier_candidate_filter",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let before = encoder.solver.assertions().len();
    let count = encoder
        .assert_ground_pool_instances()
        .expect("match-result forall branch instantiation should succeed");
    assert_eq!(count, 1, "one registered logic call is one ground instance");

    let new_assertions = &encoder.solver.assertions()[before..];
    assert!(
        !new_assertions.iter().any(|term| {
            let text = encoder.solver.format_term(*term);
            text.contains("qvar_candidate_leak")
                || text.contains("logic_param_candidate_leak")
                || text.contains("spec_param_candidate_leak")
        }),
        "ground result-match instantiation must not harvest candidates from unrelated quantified assertion bodies"
    );
}

/// Verify that spec axioms with `requires` clauses produce guarded ground
/// instances: `requires(ground_args) => ensures(ground_args)` (#1965).
///
/// Sets up `f(x)` with `requires(x > 0)` and `ensures(f(x) > x)`. When
/// `f(5)` is a ground call, the instance should assert `5 > 0 => f(5) > 5`.
/// Since `5 > 0` is trivially true, the ensures clause is effective and
/// `f(5) <= 5` should be UNSAT.
#[test]
#[timeout(30000)]
fn test_spec_axiom_with_requires_ground_instantiation() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_g",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    // Register spec axiom: forall x. requires(x > 0) => f(x) > x
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_g".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Var("x".to_string(), None)),
        ),
        requires: vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    // Register ground call: g(5) — satisfies requires since 5 > 0
    let five = encoder.solver.int_const(5);
    let g_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder
        .ground_pool
        .register("logic_fn_g", g_of_5, vec![five], vec![PureExpr::Int(5)]);

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 1,
        "should instantiate 1 guarded spec ground instance"
    );

    // The solver now knows: (5 > 0) => (g(5) > 5).
    // Since 5 > 0 is true, g(5) > 5 must hold.
    // Assert g(5) <= 5 and check for UNSAT.
    let g5_gt_5 = encoder.solver.gt(g_of_5, five);
    let not_g5_gt_5 = encoder.solver.not(g5_gt_5);
    encoder.solver.assert_term(not_g5_gt_5);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "should be UNSAT: requires(5>0) is true so ensures(g(5)>5) holds, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_spec_axiom_with_quantified_requires_does_not_emit_raw_guard() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let bool_sort = ay_dpll::api::Sort::Bool;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_quantified_requires_spec",
        std::slice::from_ref(&int_sort),
        bool_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_quantified_requires_spec".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("result".to_string(), Some(ExprSort::Bool)),
        requires: vec![PureExpr::Forall {
            var: "j".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("j".to_string(), Some(ExprSort::Int))),
                trust_wp_core::formula::BinOp::Ge,
                Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
            )),
            triggers: vec![],
        }],
        func_decl: func_decl.clone(),
        return_sort: bool_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder.ground_pool.register(
        "logic_fn_quantified_requires_spec",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let before = encoder.solver.assertions().len();
    let count = encoder
        .assert_ground_pool_instances()
        .expect("quantified requires should be skipped cleanly");
    assert_eq!(
        count, 0,
        "ground spec instances must not encode raw quantified requires as guards"
    );
    assert!(
        encoder.solver.assertions()[before..]
            .iter()
            .all(|assertion| !term_contains_quantifier(&encoder, *assertion)),
        "no new ground-pool assertion may contain a raw quantifier"
    );
}

#[test]
#[timeout(30000)]
fn test_spec_match_result_branch_facts_remain_requires_guarded() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_find_like_guarded",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_find_like_guarded".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("result".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Bool(true),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("j".to_string()))),
                    },
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Var("j".to_string(), None)),
                        trust_wp_core::formula::BinOp::Gt,
                        Arc::new(PureExpr::Var("x".to_string(), None)),
                    ),
                },
            ],
        },
        requires: vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let guarded_x = encoder.solver.declare_const("guarded_x", Sort::Int);
    let f_of_guarded_x = encoder.solver.apply(&func_decl, &[guarded_x]);
    encoder.ground_pool.register(
        "logic_fn_find_like_guarded",
        f_of_guarded_x,
        vec![guarded_x],
        vec![PureExpr::Var("guarded_x".to_string(), None)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("guarded match-result spec instantiation should succeed");
    assert_eq!(count, 1, "one observed call is one ground instance");

    let is_some_decl = encoder.get_or_declare_constructor_tester_for_sort("is_some", &Sort::Int);
    let unwrap_decl =
        encoder.get_or_declare_accessor_for_sorts("spec_unwrap", &Sort::Int, &Sort::Int);
    let is_some = encoder.solver.apply(&is_some_decl, &[f_of_guarded_x]);
    let payload = encoder.solver.apply(&unwrap_decl, &[f_of_guarded_x]);
    encoder.solver.assert_term(is_some);
    let zero = encoder.solver.int_const(0);
    let requires_false = encoder.solver.le(guarded_x, zero);
    encoder.solver.assert_term(requires_false);
    let payload_gt_x = encoder.solver.gt(payload, guarded_x);
    let not_payload_gt_x = encoder.solver.not(payload_gt_x);
    encoder.solver.assert_term(not_payload_gt_x);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "branch fact must not fire when the requires guard is false, got {result:?}"
    );
}

/// Verify that the PRODUCTION `quantifier_depth` guard in
/// `encode_logic_fn_call_impl` prevents ground pool registration when
/// inside a quantifier body (#1965, #2110).
///
/// Calls the production code path (`encode_logic_fn_call_impl`) directly
/// so that removing the `quantifier_depth == 0` guard at call_encoding.rs:338
/// would cause this test to fail.
#[test]
#[timeout(30000)]
fn test_quantifier_depth_blocks_ground_registration() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Phase 1: encode a logic fn call at depth 0 — should register in pool.
    let _term_at_depth_0 = encoder
        .encode_logic_fn_call_impl("h", &[PureExpr::Int(5)], None)
        .expect("encode_logic_fn_call_impl should succeed at depth 0");

    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        1,
        "ground pool should have 1 entry after call at quantifier_depth 0"
    );

    // Phase 2: set quantifier_depth > 0, encode same call — pool must NOT grow.
    encoder.quantifier_state.inc_quantifier_depth();

    let _term_at_depth_1 = encoder
        .encode_logic_fn_call_impl("h", &[PureExpr::Int(7)], None)
        .expect("encode_logic_fn_call_impl should succeed at depth 1");

    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        1,
        "ground pool should still have 1 entry — depth > 0 must block registration"
    );

    // Phase 3: return to depth 0, encode another call — pool should grow.
    encoder.quantifier_state.dec_quantifier_depth();

    let _term_at_depth_0_again = encoder
        .encode_logic_fn_call_impl("h", &[PureExpr::Int(9)], None)
        .expect("encode_logic_fn_call_impl should succeed at depth 0 again");

    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        2,
        "ground pool should have 2 entries after second call at quantifier_depth 0"
    );
}

/// Verify the idempotency guard: calling `assert_ground_pool_instances` twice
/// without registering new entries should return 0 on the second call.
#[test]
#[timeout(30000)]
fn test_ground_pool_idempotent_flush_returns_zero() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_idem",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_idem".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder
        .ground_pool
        .register("logic_fn_idem", f_of_5, vec![five], vec![PureExpr::Int(5)]);

    let count1 = encoder
        .assert_ground_pool_instances()
        .expect("first flush should succeed");
    assert_eq!(
        count1, 1,
        "first flush should instantiate 1 ground instance"
    );

    let count2 = encoder
        .assert_ground_pool_instances()
        .expect("second flush should succeed");
    assert_eq!(
        count2, 0,
        "second flush without new registrations should be a no-op"
    );
}

/// After a flush, registering a new ground entry should make the next flush
/// produce instances again.
#[test]
#[timeout(30000)]
fn test_ground_pool_flush_reactivates_after_new_registration() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_reactivate",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_reactivate".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Int(10)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    let three = encoder.solver.int_const(3);
    let f_of_3 = encoder.solver.apply(&func_decl, &[three]);
    encoder.ground_pool.register(
        "logic_fn_reactivate",
        f_of_3,
        vec![three],
        vec![PureExpr::Int(3)],
    );

    let count1 = encoder
        .assert_ground_pool_instances()
        .expect("first flush should succeed");
    assert_eq!(count1, 1);

    // Register a new ground entry — should reactivate the flush
    let seven = encoder.solver.int_const(7);
    let f_of_7 = encoder.solver.apply(&func_decl, &[seven]);
    encoder.ground_pool.register(
        "logic_fn_reactivate",
        f_of_7,
        vec![seven],
        vec![PureExpr::Int(7)],
    );

    let count2 = encoder
        .assert_ground_pool_instances()
        .expect("second flush after new registration should succeed");
    assert_eq!(
        count2, 2,
        "second flush should instantiate ALL matching entries (old + new)"
    );

    // Verify both instances work: f(3) = 13, f(7) = 17
    let thirteen = encoder.solver.int_const(13);
    let f3_eq_13 = encoder.solver.eq(f_of_3, thirteen);
    let not_f3_eq_13 = encoder.solver.not(f3_eq_13);
    encoder.solver.assert_term(not_f3_eq_13);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground instances should establish f(3) = 13, got {result:?}"
    );
}

/// Verify that ground entries with wrong arity (different number of arg_exprs
/// than axiom params) are silently skipped, not errored.
#[test]
#[timeout(30000)]
fn test_ground_pool_arity_filter_skips_mismatched_entries() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    // Declare f: Int -> Int (1 param)
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_arity",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_arity".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("x".to_string(), None),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    // Register a ground entry with 2 arg_exprs (mismatched — axiom has 1 param)
    let one = encoder.solver.int_const(1);
    let two = encoder.solver.int_const(2);
    let app = encoder.solver.apply(&func_decl, &[one]);
    encoder.ground_pool.register(
        "logic_fn_arity",
        app,
        vec![one],
        vec![PureExpr::Int(1), PureExpr::Int(2)],
    );

    // Also register a correctly-matching entry
    let three = encoder.solver.int_const(3);
    let f_of_3 = encoder.solver.apply(&func_decl, &[three]);
    encoder.ground_pool.register(
        "logic_fn_arity",
        f_of_3,
        vec![three],
        vec![PureExpr::Int(3)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 1,
        "only the entry with matching arity should be instantiated"
    );

    // Verify the correct instance: f(3) = 3 (identity axiom)
    let _ = two; // suppress unused warning
    let f3_eq_3 = encoder.solver.eq(f_of_3, three);
    let not_f3_eq_3 = encoder.solver.not(f3_eq_3);
    encoder.solver.assert_term(not_f3_eq_3);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground instance should establish f(3) = 3, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_ground_pool_skips_quantifier_var_entries() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_qvar_filter",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_qvar_filter".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    let qvar = encoder.solver.declare_const("qvar_i", int_sort);
    let app = encoder.solver.apply(&func_decl, &[qvar]);
    encoder
        .ground_pool
        .register_term_application("logic_fn_qvar_filter", app, vec![qvar]);

    let count = encoder
        .assert_ground_pool_instances()
        .expect("qvar-containing entries should be skipped cleanly");
    assert_eq!(
        count, 0,
        "ground pool must not instantiate over qvar_* placeholder terms"
    );
}

/// Verify that an axiom with no matching ground entries produces 0 instances
/// and no errors.
#[test]
#[timeout(30000)]
fn test_ground_pool_axiom_no_matching_entries_returns_zero() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_lonely",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_lonely".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("x".to_string(), None),
        requires: vec![],
        func_decl,
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    // Register ground entries for a DIFFERENT symbol
    let five = encoder.solver.int_const(5);
    encoder
        .ground_pool
        .register("logic_fn_OTHER", five, vec![five], vec![PureExpr::Int(5)]);

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation with no matching entries should succeed");
    assert_eq!(
        count, 0,
        "axiom with no matching ground entries should produce 0 instances"
    );
}

/// Verify that multiple axioms can be instantiated against shared ground
/// entries from the same symbol.
#[test]
#[timeout(30000)]
fn test_ground_pool_multiple_axioms_shared_symbol() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_multi",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    // Axiom 1 (defining): f(x) = x + 1
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_multi".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    // Axiom 2 (spec): f(x) > 0
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_multi".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let ten = encoder.solver.int_const(10);
    let f_of_10 = encoder.solver.apply(&func_decl, &[ten]);
    encoder.ground_pool.register(
        "logic_fn_multi",
        f_of_10,
        vec![ten],
        vec![PureExpr::Int(10)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 2,
        "two axioms for the same symbol should each produce one ground instance"
    );

    // Verify the defining axiom: f(10) = 11
    let eleven = encoder.solver.int_const(11);
    let f10_eq_11 = encoder.solver.eq(f_of_10, eleven);
    let not_f10_eq_11 = encoder.solver.not(f10_eq_11);
    encoder.solver.assert_term(not_f10_eq_11);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "defining axiom should establish f(10) = 11, got {result:?}"
    );
}

/// Verify that multi-parameter axioms instantiate correctly.
///
/// Sets up `g(a, b) = a + b` as a defining axiom, registers `g(3, 7)`,
/// and checks that `g(3, 7) = 10`.
#[test]
#[timeout(30000)]
fn test_ground_pool_multi_param_axiom() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_add",
        &[int_sort.clone(), int_sort.clone()],
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_add".to_string(),
        params: vec!["a".to_string(), "b".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Var("b".to_string(), None)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    let three = encoder.solver.int_const(3);
    let seven = encoder.solver.int_const(7);
    let g_3_7 = encoder.solver.apply(&func_decl, &[three, seven]);
    encoder.ground_pool.register(
        "logic_fn_add",
        g_3_7,
        vec![three, seven],
        vec![PureExpr::Int(3), PureExpr::Int(7)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(count, 1, "should instantiate 1 multi-param ground instance");

    // Verify: g(3, 7) = 3 + 7 = 10
    let ten = encoder.solver.int_const(10);
    let eq = encoder.solver.eq(g_3_7, ten);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground instance should establish g(3,7) = 10, got {result:?}"
    );
}

/// Verify that multiple requires clauses are conjoined and used as a guard.
///
/// Sets up `h(x)` with `requires(x > 0)` AND `requires(x < 100)` and
/// `ensures(h(x) > x)`. With ground call `h(50)`, both requires are
/// satisfied, so the ensures clause should be effective.
#[test]
#[timeout(30000)]
fn test_ground_pool_multiple_requires_conjoined() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_bounded",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_bounded".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Var("x".to_string(), None)),
        ),
        requires: vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                trust_wp_core::formula::BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                trust_wp_core::formula::BinOp::Lt,
                Arc::new(PureExpr::Int(100)),
            ),
        ],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let fifty = encoder.solver.int_const(50);
    let h_of_50 = encoder.solver.apply(&func_decl, &[fifty]);
    encoder.ground_pool.register(
        "logic_fn_bounded",
        h_of_50,
        vec![fifty],
        vec![PureExpr::Int(50)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 1,
        "should instantiate 1 multi-requires ground instance"
    );

    // The ground instance is: (50 > 0 && 50 < 100) => h(50) > 50
    // Both requires are true, so h(50) > 50 must hold.
    let h50_gt_50 = encoder.solver.gt(h_of_50, fifty);
    let not_h50_gt_50 = encoder.solver.not(h50_gt_50);
    encoder.solver.assert_term(not_h50_gt_50);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "conjoined requires should guard the ensures clause; with x=50 both hold, got {result:?}"
    );
}

/// Verify that requires clauses that are NOT satisfied make the guard
/// vacuously true — the ensures clause should NOT be asserted unconditionally.
///
/// Sets up `h(x)` with `requires(x > 100)` and `ensures(false)`.
/// With ground call `h(5)`, `5 > 100` is false, so the instance is
/// `false => false` which is trivially true. The solver should remain SAT.
#[test]
#[timeout(30000)]
fn test_ground_pool_unsatisfied_requires_makes_guard_vacuous() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_vacuous",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_vacuous".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Bool(false), // ensures(false) — would be contradictory if unguarded
        requires: vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(100)),
        )],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    let h_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder.ground_pool.register(
        "logic_fn_vacuous",
        h_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert!(
        count <= 1,
        "latest ay may skip vacuously-guarded instances; got {count}"
    );

    // The solver should still be SAT: (5 > 100) => false is trivially true
    let result = encoder.check_sat();
    assert!(
        !matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "unsatisfied requires should not make ensures(false) contradictory, got {result:?}"
    );
}

/// Verify that path conditions from ground entry registration are used as
/// additional guards on the instantiated axiom.
///
/// Sets up `f(x) = x + 1` as a defining axiom. Registers `f(5)` with a
/// path condition `cond`. The ground instance should be `cond => f(5) = 6`.
/// With `cond` asserted true, `f(5) = 6` holds; with `cond` false, no
/// constraint is imposed on `f(5)`.
#[test]
#[timeout(30000)]
fn test_ground_pool_path_conditions_guard_instance() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_pathcond",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_pathcond".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    let cond = encoder
        .solver
        .declare_const("path_cond", ay_dpll::api::Sort::Bool);

    encoder.ground_pool.register_with_path_conditions(
        "logic_fn_pathcond",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
        vec![cond],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(count, 1, "should instantiate 1 path-conditioned instance");

    // Assert cond is true — the instance should impose f(5) = 6
    encoder.solver.assert_term(cond);
    let six = encoder.solver.int_const(6);
    let f5_eq_6 = encoder.solver.eq(f_of_5, six);
    let not_f5_eq_6 = encoder.solver.not(f5_eq_6);
    encoder.solver.assert_term(not_f5_eq_6);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "with path_cond=true, ground instance should force f(5) = 6, got {result:?}"
    );
}

/// Verify that path conditions from ground entry registration allow SAT
/// when the path condition is false (the instance is vacuously true).
#[test]
#[timeout(30000)]
fn test_ground_pool_path_condition_false_allows_sat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_pathcond_false",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_pathcond_false".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Bool(false), // would be contradictory if unguarded
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    let cond = encoder
        .solver
        .declare_const("path_cond_false", ay_dpll::api::Sort::Bool);

    encoder.ground_pool.register_with_path_conditions(
        "logic_fn_pathcond_false",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
        vec![cond],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(count, 1);

    // Assert cond is false — the instance should be vacuously true
    let not_cond = encoder.solver.not(cond);
    encoder.solver.assert_term(not_cond);

    let result = encoder.check_sat();
    assert!(
        !matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "with path_cond=false, ensures(false) should be vacuously true, got {result:?}"
    );
}

/// Verify sort compatibility: Uninterpreted("Foo") matches Datatype with
/// name "Foo" in the `ground_instance_arg_sort_compatible` check.
///
/// This tests the cross-matching logic at instantiation.rs:31-39 directly
/// through the instantiation pipeline by registering a ground entry whose
/// arg_terms have an Uninterpreted sort against an axiom declared with a
/// Datatype sort of the same name.
#[test]
#[timeout(30000)]
fn test_ground_pool_sort_compatible_uninterpreted_matches_datatype() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Declare a datatype sort "Pair" and an uninterpreted sort "Pair"
    let dt_sort = Sort::Datatype(DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk_pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    });

    // Declare f: Pair(dt) -> Int using the datatype sort
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_dt_compat",
        std::slice::from_ref(&dt_sort),
        Sort::Int,
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_dt_compat".to_string(),
        params: vec!["p".to_string()],
        body: PureExpr::Int(42), // constant body for simplicity
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: Sort::Int,
        kind: AxiomKind::Defining,
    });

    // Register a ground entry with an Uninterpreted("Pair") sort argument
    let uninterp_sort = Sort::Uninterpreted("Pair".to_string());
    let p = encoder.solver.fresh_var("p", uninterp_sort);
    let f_of_p = encoder.solver.apply(&func_decl, &[p]);
    encoder.ground_pool.register(
        "logic_fn_dt_compat",
        f_of_p,
        vec![p],
        vec![PureExpr::Var("p".to_string(), None)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 1,
        "Uninterpreted('Pair') should be compatible with Datatype('Pair')"
    );

    // Verify the instance: f(p) = 42
    let forty_two = encoder.solver.int_const(42);
    let eq = encoder.solver.eq(f_of_p, forty_two);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "sort-compatible instance should establish f(p) = 42, got {result:?}"
    );
}

/// Verify that incompatible sorts cause the ground instance to be skipped
/// (not errored). An Int argument where a Bool is expected should skip.
#[test]
#[timeout(30000)]
fn test_ground_pool_sort_incompatible_skips_instance() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let bool_sort = ay_dpll::api::Sort::Bool;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_bool_arg",
        std::slice::from_ref(&bool_sort),
        ay_dpll::api::Sort::Int,
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_bool_arg".to_string(),
        params: vec!["b".to_string()],
        body: PureExpr::Int(1),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: ay_dpll::api::Sort::Int,
        kind: AxiomKind::Defining,
    });

    // Register a ground entry with Int sort argument (incompatible with Bool)
    let five = encoder.solver.int_const(5);
    // We can't apply func_decl with an Int argument directly (sort mismatch),
    // so use a dummy application term
    let dummy_app = encoder.solver.int_const(99);
    encoder.ground_pool.register(
        "logic_fn_bool_arg",
        dummy_app,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed (skip incompatible)");
    assert_eq!(
        count, 0,
        "sort-incompatible instance should be skipped, not instantiated"
    );
}

/// Verify that the TRUST_WP_CAP_PER_AXIOM limit (50) is respected: when more than
/// TRUST_WP_CAP_PER_AXIOM ground entries match an axiom, only the first batch are
/// instantiated. This test registers exactly TRUST_WP_CAP_PER_SYMBOL entries, which
/// equals TRUST_WP_CAP_PER_AXIOM (both 50), so all entries are instantiated.
#[test]
#[timeout(30000)]
fn test_ground_pool_cap_per_axiom_limits_instances() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_capped",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_capped".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("x".to_string(), None),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    // TRUST_WP_CAP_PER_SYMBOL is 50, TRUST_WP_CAP_PER_AXIOM is 50 (#2674 Phase 2).
    // The effective cap is min(entries, TRUST_WP_CAP_PER_AXIOM) = 50.
    // Register exactly TRUST_WP_CAP_PER_SYMBOL entries
    for i in 0..TRUST_WP_CAP_PER_SYMBOL {
        let val = i64::try_from(i).expect("index should fit i64");
        let t = encoder.solver.int_const(val);
        let app = encoder.solver.apply(&func_decl, &[t]);
        encoder
            .ground_pool
            .register("logic_fn_capped", app, vec![t], vec![PureExpr::Int(val)]);
    }

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, TRUST_WP_CAP_PER_SYMBOL,
        "should instantiate exactly TRUST_WP_CAP_PER_SYMBOL ({TRUST_WP_CAP_PER_SYMBOL}) ground instances"
    );
}

/// Verify that `register_standard_ground_application` respects the
/// quantifier_depth guard: registration is suppressed at depth > 0.
#[test]
#[timeout(30000)]
fn test_register_standard_ground_application_respects_quantifier_depth() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let one = encoder.solver.int_const(1);
    let two = encoder.solver.int_const(2);
    let app = encoder.solver.add(one, two);

    // At depth 0 — should register
    encoder.register_standard_ground_application("test_fn", app, vec![one, two]);
    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        1,
        "should register at quantifier_depth 0"
    );

    // At depth 1 — should NOT register
    encoder.quantifier_state.inc_quantifier_depth();
    let three = encoder.solver.int_const(3);
    let app2 = encoder.solver.add(one, three);
    encoder.register_standard_ground_application("test_fn", app2, vec![one, three]);
    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        1,
        "should NOT register at quantifier_depth > 0"
    );

    // Back to depth 0 — should register again
    encoder.quantifier_state.dec_quantifier_depth();
    encoder.register_standard_ground_application("test_fn_2", app2, vec![one, three]);
    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        2,
        "should register again at quantifier_depth 0"
    );
}

// ─── Additional edge case tests (#1296) ───────────────────────────────────

/// Verify that flushing an empty pool (no axioms, no ground entries) returns 0
/// without error — the idempotent flush guard handles the degenerate case.
#[test]
#[timeout(30000)]
fn test_ground_pool_flush_empty_pool_returns_zero() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Pool is completely empty — no axioms, no entries
    let count = encoder
        .assert_ground_pool_instances()
        .expect("flushing an empty pool should succeed");
    assert_eq!(count, 0, "empty pool flush should return 0");

    // Second flush — still 0 (idempotent on emptiness)
    let count2 = encoder
        .assert_ground_pool_instances()
        .expect("second flush of empty pool should succeed");
    assert_eq!(count2, 0, "second empty pool flush should still return 0");
}

/// Verify that flushing a pool with axioms but NO ground entries returns 0
/// and does NOT error. The flush-needed flag is set by axiom registration,
/// but instantiation finds nothing to match.
#[test]
#[timeout(30000)]
fn test_ground_pool_flush_axioms_only_no_entries_returns_zero() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_orphan_axiom",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_orphan_axiom".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("x".to_string(), None),
        requires: vec![],
        func_decl,
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    // Pool has an axiom but no ground entries — needs_flush is true
    assert!(
        encoder.ground_pool.needs_flush(),
        "axiom registration should set needs_flush"
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("flush with axioms but no entries should succeed");
    assert_eq!(
        count, 0,
        "axiom with zero matching ground entries should produce 0 instances"
    );

    // After flush, needs_flush should be false
    assert!(
        !encoder.ground_pool.needs_flush(),
        "flush should clear the needs_flush flag even when 0 instances produced"
    );
}

/// Verify that arity filtering applies per-entry: when ALL entries for a
/// symbol have wrong arity, the axiom produces 0 instances (no errors).
#[test]
#[timeout(30000)]
fn test_ground_pool_arity_filter_all_entries_mismatch_returns_zero() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    // Axiom has 2 params (a, b)
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_binary",
        &[int_sort.clone(), int_sort.clone()],
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_binary".to_string(),
        params: vec!["a".to_string(), "b".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Var("b".to_string(), None)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    // Register 3 entries, all with 1 arg_expr (mismatch: axiom expects 2)
    for i in 1..=3 {
        let val = i64::from(i);
        let t = encoder.solver.int_const(val);
        let app = encoder.solver.apply(&func_decl, &[t, t]);
        encoder.ground_pool.register(
            "logic_fn_binary",
            app,
            vec![t, t],
            vec![PureExpr::Int(val)], // 1 arg_expr, axiom expects 2
        );
    }

    let count = encoder
        .assert_ground_pool_instances()
        .expect("all-mismatched arity should succeed without error");
    assert_eq!(
        count, 0,
        "all entries have wrong arity — should produce 0 instances"
    );
}

/// Verify that two axioms with different param counts sharing the same symbol
/// each match only entries with the correct arity.
///
/// Axiom A (1 param) matches 1-arg entries; axiom B (2 params) matches 2-arg
/// entries. Cross-matching is prevented by the arity filter.
#[test]
#[timeout(30000)]
fn test_ground_pool_multiple_axioms_different_arity_same_symbol() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl_1 = encoder.solver.declare_fun(
        "logic_fn_overloaded",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );
    let func_decl_2 = encoder.solver.declare_fun(
        "logic_fn_overloaded_2",
        &[int_sort.clone(), int_sort.clone()],
        int_sort.clone(),
    );

    // Axiom A: f(x) = x (1 param)
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_overloaded".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("x".to_string(), None),
        requires: vec![],
        func_decl: func_decl_1.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    // Axiom B: f(a, b) = a + b (2 params, same symbol name for pool lookup)
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_overloaded".to_string(),
        params: vec!["a".to_string(), "b".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Var("b".to_string(), None)),
        ),
        requires: vec![],
        func_decl: func_decl_2.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    // Register a 1-arg entry (matches axiom A only)
    let five = encoder.solver.int_const(5);
    let app1 = encoder.solver.apply(&func_decl_1, &[five]);
    encoder.ground_pool.register(
        "logic_fn_overloaded",
        app1,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    // Register a 2-arg entry (matches axiom B only)
    let three = encoder.solver.int_const(3);
    let seven = encoder.solver.int_const(7);
    let app2 = encoder.solver.apply(&func_decl_2, &[three, seven]);
    encoder.ground_pool.register(
        "logic_fn_overloaded",
        app2,
        vec![three, seven],
        vec![PureExpr::Int(3), PureExpr::Int(7)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("mixed-arity instantiation should succeed");
    assert_eq!(
        count, 2,
        "each axiom should match exactly one entry by arity"
    );

    // Verify axiom A: f(5) = 5
    let eq_a = encoder.solver.eq(app1, five);
    let neq_a = encoder.solver.not(eq_a);
    encoder.solver.assert_term(neq_a);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "axiom A should establish f(5) = 5, got {result:?}"
    );
}

/// Verify that a 3-parameter axiom instantiates correctly.
///
/// Sets up `h(a, b, c) = a + b + c`, registers `h(2, 3, 5)`, and checks
/// that `h(2, 3, 5) = 10`.
#[test]
#[timeout(30000)]
fn test_ground_pool_three_param_axiom() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_ternary",
        &[int_sort.clone(), int_sort.clone(), int_sort.clone()],
        int_sort.clone(),
    );

    // h(a, b, c) = (a + b) + c
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_ternary".to_string(),
        params: vec!["a".to_string(), "b".to_string(), "c".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("a".to_string(), None)),
                trust_wp_core::formula::BinOp::Add,
                Arc::new(PureExpr::Var("b".to_string(), None)),
            )),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Var("c".to_string(), None)),
        ),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Defining,
    });

    let two = encoder.solver.int_const(2);
    let three = encoder.solver.int_const(3);
    let five = encoder.solver.int_const(5);
    let h_2_3_5 = encoder.solver.apply(&func_decl, &[two, three, five]);
    encoder.ground_pool.register(
        "logic_fn_ternary",
        h_2_3_5,
        vec![two, three, five],
        vec![PureExpr::Int(2), PureExpr::Int(3), PureExpr::Int(5)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("3-param instantiation should succeed");
    assert_eq!(count, 1, "should instantiate 1 three-param ground instance");

    // Verify: h(2, 3, 5) = (2 + 3) + 5 = 10
    let ten = encoder.solver.int_const(10);
    let eq = encoder.solver.eq(h_2_3_5, ten);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground instance should establish h(2,3,5) = 10, got {result:?}"
    );
}

/// Verify that when one of multiple requires clauses is unsatisfied, the
/// entire conjunction is false and the guard is vacuously true.
///
/// Sets up `f(x)` with `requires(x > 0) && requires(x > 1000)` and
/// `ensures(false)`. With `f(5)`, `5 > 0` is true but `5 > 1000` is false,
/// so the conjunction is false and `false => false` is vacuously true.
#[test]
#[timeout(30000)]
fn test_ground_pool_partial_requires_unsatisfied_is_vacuous() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_partial_req",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_partial_req".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Bool(false), // ensures(false) — contradictory if unguarded
        requires: vec![
            // x > 0 (satisfied by x=5)
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                trust_wp_core::formula::BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ),
            // x > 1000 (NOT satisfied by x=5)
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                trust_wp_core::formula::BinOp::Gt,
                Arc::new(PureExpr::Int(1000)),
            ),
        ],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder.ground_pool.register(
        "logic_fn_partial_req",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert!(
        count <= 1,
        "latest ay may skip partially-vacuous guarded instances; got {count}"
    );

    // Conjunction is false (5 > 1000 fails), so ensures(false) is vacuously true
    let result = encoder.check_sat();
    assert!(
        !matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "partial requires failure should make guard vacuously true, got {result:?}"
    );
}

/// Verify that path conditions and requires clauses are combined as guards.
///
/// Sets up `f(x)` with `requires(x > 0)` and a path condition `cond`.
/// The ground instance is `(cond && x > 0) => ensures(...)`.
/// When cond=true and x=5 (>0), the guard is satisfied.
#[test]
#[timeout(30000)]
fn test_ground_pool_path_conditions_combined_with_requires() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_combined_guard",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_combined_guard".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Var("x".to_string(), None)),
        ),
        requires: vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    let cond = encoder
        .solver
        .declare_const("combined_cond", ay_dpll::api::Sort::Bool);

    encoder.ground_pool.register_with_path_conditions(
        "logic_fn_combined_guard",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
        vec![cond],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(count, 1);

    // Assert cond=true — both guards satisfied, f(5) > 5 must hold
    encoder.solver.assert_term(cond);
    let f5_gt_5 = encoder.solver.gt(f_of_5, five);
    let not_f5_gt_5 = encoder.solver.not(f5_gt_5);
    encoder.solver.assert_term(not_f5_gt_5);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "combined guard (path_cond=true, x>0) should enforce ensures, got {result:?}"
    );
}

/// Verify that when the path condition is false, even satisfied requires
/// don't make the guard effective — the path condition failure is sufficient
/// to make the entire implication vacuously true.
#[test]
#[timeout(30000)]
fn test_ground_pool_false_path_condition_overrides_satisfied_requires() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_path_override",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_path_override".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Bool(false), // ensures(false) — contradictory if unguarded
        requires: vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )],
        func_decl: func_decl.clone(),
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    let cond = encoder
        .solver
        .declare_const("path_override_cond", ay_dpll::api::Sort::Bool);

    encoder.ground_pool.register_with_path_conditions(
        "logic_fn_path_override",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
        vec![cond],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(count, 1);

    // Assert cond=false — even though requires(5>0) holds, the combined
    // guard is (false && true) = false, so ensures(false) is vacuously true
    let not_cond = encoder.solver.not(cond);
    encoder.solver.assert_term(not_cond);

    let result = encoder.check_sat();
    assert!(
        !matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "false path condition should override satisfied requires, got {result:?}"
    );
}

/// Verify that two Datatype sorts with the same name but different constructors
/// are treated as compatible by `ground_instance_arg_sort_compatible`.
///
/// This exercises the name-based Datatype-to-Datatype matching at
/// instantiation.rs:31-33, which only checks `actual_dt.name == expected_dt.name`.
#[test]
#[timeout(30000)]
fn test_ground_pool_sort_compatible_datatype_same_name_different_constructors() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Axiom declared with Datatype("MyType") with 2 Int fields
    let dt_sort_axiom = Sort::Datatype(DatatypeSort {
        name: "MyType".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk_mytype".to_string(),
            fields: vec![
                DatatypeField {
                    name: "field_a".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "field_b".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    });

    let func_decl = encoder.solver.declare_fun(
        "logic_fn_dt_same_name",
        std::slice::from_ref(&dt_sort_axiom),
        Sort::Int,
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_dt_same_name".to_string(),
        params: vec!["m".to_string()],
        body: PureExpr::Int(99),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: Sort::Int,
        kind: AxiomKind::Defining,
    });

    // Ground entry with same-name Datatype but different field layout
    let dt_sort_ground = Sort::Datatype(DatatypeSort {
        name: "MyType".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk_mytype_v2".to_string(),
            fields: vec![DatatypeField {
                name: "only_field".to_string(),
                sort: Sort::Bool,
            }],
        }],
    });
    let m = encoder.solver.fresh_var("m_drifted", dt_sort_ground);
    let f_of_m = encoder.solver.apply(&func_decl, &[m]);
    encoder.ground_pool.register(
        "logic_fn_dt_same_name",
        f_of_m,
        vec![m],
        vec![PureExpr::Var("m".to_string(), None)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("same-name different-constructor datatype should instantiate");
    assert_eq!(
        count, 1,
        "Datatype('MyType') should be compatible with Datatype('MyType') regardless of constructors"
    );

    // Verify: f(m) = 99
    let ninety_nine = encoder.solver.int_const(99);
    let eq = encoder.solver.eq(f_of_m, ninety_nine);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "compatible-sort instance should establish f(m) = 99, got {result:?}"
    );
}

/// Verify that TRUST_WP_CAP_PER_SYMBOL silently drops excess registrations: when more
/// than TRUST_WP_CAP_PER_SYMBOL entries are registered for a single symbol, the pool
/// count is capped and no error is returned.
#[test]
#[timeout(30000)]
fn test_ground_pool_cap_per_symbol_no_error_on_overflow() {
    let mut encoder = AYEncoder::new();
    let mut pool = GroundTermPool::new();

    let overflow = TRUST_WP_CAP_PER_SYMBOL + 10;
    for i in 0..overflow {
        let val = i64::try_from(i).expect("index should fit i64");
        let t = encoder.solver.int_const(val);
        pool.register("cap_test", t, vec![t], vec![PureExpr::Int(val)]);
    }

    assert_eq!(
        pool.ground_term_count(),
        TRUST_WP_CAP_PER_SYMBOL,
        "should cap at {TRUST_WP_CAP_PER_SYMBOL}, even after {overflow} registrations"
    );

    // Verify that only the first TRUST_WP_CAP_PER_SYMBOL entries are kept
    let entries = pool.entries_for("cap_test").expect("should have entries");
    assert_eq!(entries.len(), TRUST_WP_CAP_PER_SYMBOL);
    // First entry should be value 0
    assert_eq!(entries[0].arg_exprs[0], PureExpr::Int(0));
    // Last entry should be value TRUST_WP_CAP_PER_SYMBOL - 1
    let last_val = i64::try_from(TRUST_WP_CAP_PER_SYMBOL - 1).expect("index should fit i64");
    assert_eq!(
        entries[TRUST_WP_CAP_PER_SYMBOL - 1].arg_exprs[0],
        PureExpr::Int(last_val)
    );
}

/// Verify that quantifier_depth > 0 blocks registration at all depth levels,
/// not just depth 1. Depth 2, 3, etc. must also suppress registration.
#[test]
#[timeout(30000)]
fn test_ground_pool_quantifier_depth_blocks_at_all_levels() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let one = encoder.solver.int_const(1);
    let app = encoder.solver.add(one, one);

    // Depth 2 — should NOT register
    encoder.quantifier_state.set_quantifier_depth(2);
    encoder.register_standard_ground_application("deep_fn", app, vec![one]);
    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        0,
        "should NOT register at quantifier_depth 2"
    );

    // Depth 5 — should NOT register
    encoder.quantifier_state.set_quantifier_depth(5);
    encoder.register_standard_ground_application("deep_fn", app, vec![one]);
    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        0,
        "should NOT register at quantifier_depth 5"
    );

    // Depth 100 — should NOT register
    encoder.quantifier_state.set_quantifier_depth(100);
    encoder.register_standard_ground_application("deep_fn", app, vec![one]);
    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        0,
        "should NOT register at quantifier_depth 100"
    );

    // Back to depth 0 — should register
    encoder.quantifier_state.set_quantifier_depth(0);
    encoder.register_standard_ground_application("deep_fn", app, vec![one]);
    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        1,
        "should register at quantifier_depth 0"
    );
}

/// Verify that registering a new axiom (not new ground entry) also reactivates
/// the flush mechanism — the idempotent guard tracks both axiom and entry changes.
#[test]
#[timeout(30000)]
fn test_ground_pool_new_axiom_reactivates_flush() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let int_sort = ay_dpll::api::Sort::Int;
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_axiom_reactivate",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    // Register ground entry first
    let five = encoder.solver.int_const(5);
    let f_of_5 = encoder.solver.apply(&func_decl, &[five]);
    encoder.ground_pool.register(
        "logic_fn_axiom_reactivate",
        f_of_5,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    // Register first axiom and flush
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_axiom_reactivate".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("x".to_string(), None),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    let count1 = encoder
        .assert_ground_pool_instances()
        .expect("first flush should succeed");
    assert_eq!(count1, 1);

    // Second flush without changes — idempotent
    let count2 = encoder
        .assert_ground_pool_instances()
        .expect("second flush should succeed");
    assert_eq!(count2, 0, "second flush should be idempotent");

    // Register a NEW axiom for the same symbol — flush should reactivate
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_axiom_reactivate".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        requires: vec![],
        func_decl,
        return_sort: int_sort,
        kind: AxiomKind::Spec,
    });

    assert!(
        encoder.ground_pool.needs_flush(),
        "new axiom registration should reactivate the flush"
    );

    let count3 = encoder
        .assert_ground_pool_instances()
        .expect("third flush after new axiom should succeed");
    assert_eq!(
        count3, 2,
        "new axiom + existing ground entry should produce instances for BOTH axioms"
    );
}

/// Verify that Uninterpreted("X") does NOT match Uninterpreted("Y") when
/// names differ — only same-name cross-matching is supported.
#[test]
#[timeout(30000)]
fn test_ground_pool_sort_incompatible_different_uninterpreted_names() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let uninterp_alpha = ay_dpll::api::Sort::Uninterpreted("Alpha".to_string());
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_alpha",
        std::slice::from_ref(&uninterp_alpha),
        ay_dpll::api::Sort::Int,
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_alpha".to_string(),
        params: vec!["a".to_string()],
        body: PureExpr::Int(0),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: ay_dpll::api::Sort::Int,
        kind: AxiomKind::Defining,
    });

    // Register with Uninterpreted("Beta") — different name
    let uninterp_beta = ay_dpll::api::Sort::Uninterpreted("Beta".to_string());
    let b = encoder.solver.fresh_var("b_beta", uninterp_beta);
    let dummy_app = encoder.solver.int_const(0);
    encoder.ground_pool.register(
        "logic_fn_alpha",
        dummy_app,
        vec![b],
        vec![PureExpr::Var("b".to_string(), None)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("incompatible uninterpreted sorts should not error");
    assert_eq!(
        count, 0,
        "Uninterpreted('Alpha') should NOT match Uninterpreted('Beta')"
    );
}

// ─── TRUST_WP_TOTAL_INSTANCE_BUDGET tests (#2674) ─────────────────────────────────

/// Verify that the TRUST_WP_TOTAL_INSTANCE_BUDGET (300, #2676) caps the total
/// number of ground instances asserted across all axioms. When many axioms
/// each have many matching ground entries, the budget stops instantiation early.
#[test]
#[timeout(30000)]
fn test_total_instance_budget_caps_across_axioms() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;

    // Create 20 axioms, each with 50 ground entries.
    // Without budget: 20 * 50 = 1000 instances.
    // With budget of 300: should stop at 300.
    let n_axioms = 20;
    let n_entries = 50;

    for ax_idx in 0..n_axioms {
        let fn_name = format!("logic_fn_budget_{ax_idx}");
        let func_decl =
            encoder
                .solver
                .declare_fun(&fn_name, std::slice::from_ref(&int_sort), int_sort.clone());

        encoder.ground_pool.register_axiom(AxiomEntry {
            fn_symbol: fn_name.clone(),
            params: vec!["x".to_string()],
            body: PureExpr::Var("x".to_string(), None),
            requires: vec![],
            func_decl: func_decl.clone(),
            return_sort: int_sort.clone(),
            kind: AxiomKind::Defining,
        });

        for gt_idx in 0..n_entries {
            let val = i64::try_from(ax_idx * 1000 + gt_idx).expect("index fits i64");
            let t = encoder.solver.int_const(val);
            let app = encoder.solver.apply(&func_decl, &[t]);
            encoder
                .ground_pool
                .register(&fn_name, app, vec![t], vec![PureExpr::Int(val)]);
        }
    }

    let count = encoder
        .assert_ground_pool_instances()
        .expect("budget-capped instantiation should succeed");

    // TRUST_WP_TOTAL_INSTANCE_BUDGET is 300 (#2676, raised from 200);
    // n_axioms * n_entries = 1000. The budget should cap at 300.
    assert!(
        count <= 300,
        "total instances ({count}) should not exceed TRUST_WP_TOTAL_INSTANCE_BUDGET (300)"
    );
    assert!(
        count >= 280,
        "total instances ({count}) should be close to budget (280-300 range)"
    );
}

// ─── Ground entry deduplication tests (#2674) ────────────────────────────

/// Verify that registering the same ground application term twice for the
/// same symbol only stores it once, preventing duplicate solver assertions.
#[test]
#[timeout(30000)]
fn test_ground_pool_deduplicates_same_application() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;

    let func_decl = encoder.solver.declare_fun(
        "logic_fn_dedup",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    let five = encoder.solver.int_const(5);
    let app = encoder.solver.apply(&func_decl, &[five]);

    // Register the same application twice with different path conditions
    encoder
        .ground_pool
        .register("logic_fn_dedup", app, vec![five], vec![PureExpr::Int(5)]);
    encoder
        .ground_pool
        .register("logic_fn_dedup", app, vec![five], vec![PureExpr::Int(5)]);

    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        1,
        "duplicate application should be deduplicated"
    );
}

/// Verify that different application terms for the same symbol are NOT
/// deduplicated — only identical Term handles are skipped.
#[test]
#[timeout(30000)]
fn test_ground_pool_keeps_distinct_applications() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;

    let func_decl = encoder.solver.declare_fun(
        "logic_fn_distinct",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );

    let five = encoder.solver.int_const(5);
    let six = encoder.solver.int_const(6);
    let app1 = encoder.solver.apply(&func_decl, &[five]);
    let app2 = encoder.solver.apply(&func_decl, &[six]);

    encoder.ground_pool.register(
        "logic_fn_distinct",
        app1,
        vec![five],
        vec![PureExpr::Int(5)],
    );
    encoder
        .ground_pool
        .register("logic_fn_distinct", app2, vec![six], vec![PureExpr::Int(6)]);

    assert_eq!(
        encoder.ground_pool.ground_term_count(),
        2,
        "distinct applications should both be registered"
    );
}

// ─── Axiom priority scoring tests (#2674 Phase 2) ───────────────────────

/// Verify that defining axioms are instantiated before spec axioms when
/// the global budget is constrained. With priority scoring, the budget
/// is spent on defining axioms first (they produce equalities that enable
/// further E-matching), leaving spec axioms for last.
#[test]
#[timeout(30000)]
fn test_priority_scoring_defining_before_spec() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;

    // Register a Spec axiom first (would be instantiated first without priority)
    let spec_decl = encoder.solver.declare_fun(
        "logic_fn_spec_priority",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_spec_priority".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::BinOp(
            std::sync::Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Gt,
            std::sync::Arc::new(PureExpr::Int(0)),
        ),
        requires: vec![],
        func_decl: spec_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Spec,
    });

    // Register a Defining axiom second
    let def_decl = encoder.solver.declare_fun(
        "logic_fn_def_priority",
        std::slice::from_ref(&int_sort),
        int_sort.clone(),
    );
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_def_priority".to_string(),
        params: vec!["y".to_string()],
        body: PureExpr::Var("y".to_string(), None),
        requires: vec![],
        func_decl: def_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    // Register ground entries for both
    let five = encoder.solver.int_const(5);
    let app_spec = encoder.solver.apply(&spec_decl, &[five]);
    encoder.ground_pool.register(
        "logic_fn_spec_priority",
        app_spec,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let app_def = encoder.solver.apply(&def_decl, &[five]);
    encoder.ground_pool.register(
        "logic_fn_def_priority",
        app_def,
        vec![five],
        vec![PureExpr::Int(5)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("priority instantiation should succeed");
    // Both should be instantiated (budget is 300, only 2 instances needed)
    assert_eq!(count, 2, "both axioms should be instantiated within budget");
}

// ─── Parameter complexity gate tests (#2674 Phase 2) ────────────────────

/// Verify that axioms with more than TRUST_WP_MAX_AXIOM_PARAMS_FOR_GROUND (4)
/// parameters are skipped during ground instantiation. The quantified form
/// with triggers handles these via E-matching.
#[test]
#[timeout(30000)]
fn test_high_arity_axioms_skipped_by_complexity_gate() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;

    // Register a 5-parameter axiom (above the 4-param gate)
    let domain: Vec<ay_dpll::api::Sort> = vec![int_sort.clone(); 5];
    let func_decl = encoder
        .solver
        .declare_fun("logic_fn_high_arity", &domain, int_sort.clone());
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_high_arity".to_string(),
        params: vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
            "e".to_string(),
        ],
        body: PureExpr::Var("a".to_string(), None),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    // Register matching ground entries
    let args: Vec<ay_dpll::api::Term> = (0..5).map(|i| encoder.solver.int_const(i)).collect();
    let app = encoder.solver.apply(&func_decl, &args);
    let arg_exprs: Vec<PureExpr> = (0..5).map(PureExpr::Int).collect();
    encoder
        .ground_pool
        .register("logic_fn_high_arity", app, args, arg_exprs);

    let count = encoder
        .assert_ground_pool_instances()
        .expect("complexity-gated instantiation should succeed");
    assert_eq!(
        count, 0,
        "5-param axiom should be skipped by complexity gate (max=4)"
    );
}

/// Verify that axioms at exactly TRUST_WP_MAX_AXIOM_PARAMS_FOR_GROUND (4) are
/// still instantiated — the gate is strictly greater-than.
#[test]
#[timeout(30000)]
fn test_boundary_arity_axioms_not_skipped() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;

    // Register a 4-parameter axiom (at the boundary)
    let domain: Vec<ay_dpll::api::Sort> = vec![int_sort.clone(); 4];
    let func_decl =
        encoder
            .solver
            .declare_fun("logic_fn_boundary_arity", &domain, int_sort.clone());
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_boundary_arity".to_string(),
        params: vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
        ],
        body: PureExpr::Var("a".to_string(), None),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    // Register matching ground entries
    let args: Vec<ay_dpll::api::Term> = (0..4).map(|i| encoder.solver.int_const(i)).collect();
    let app = encoder.solver.apply(&func_decl, &args);
    let arg_exprs: Vec<PureExpr> = (0..4).map(PureExpr::Int).collect();
    encoder
        .ground_pool
        .register("logic_fn_boundary_arity", app, args, arg_exprs);

    let count = encoder
        .assert_ground_pool_instances()
        .expect("boundary-arity instantiation should succeed");
    assert_eq!(
        count, 1,
        "4-param axiom should be instantiated (gate is >4, not >=4)"
    );
}

// ── Postcondition-critical symbol exemption (#1296) ─────────────────

/// A 5-param axiom is normally skipped by the parameter complexity gate.
/// When its symbol is marked as postcondition-critical, it bypasses the gate
/// and gets instantiated.
#[test]
#[timeout(30000)]
fn test_postcondition_critical_bypasses_param_gate() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;

    // Declare f: (Int, Int, Int, Int, Int) -> Int  (5 params — above the gate)
    let domain = vec![int_sort.clone(); 5];
    let func_decl = encoder
        .solver
        .declare_fun("logic_fn_high_arity", &domain, int_sort.clone());

    // Register axiom with 5 params (would normally be skipped)
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_high_arity".to_string(),
        params: vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
            "e".to_string(),
        ],
        body: PureExpr::Var("a".to_string(), None),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    // Register matching ground entries
    let args: Vec<ay_dpll::api::Term> = (0..5).map(|i| encoder.solver.int_const(i)).collect();
    let app = encoder.solver.apply(&func_decl, &args);
    let arg_exprs: Vec<PureExpr> = (0..5).map(PureExpr::Int).collect();
    encoder
        .ground_pool
        .register("logic_fn_high_arity", app, args, arg_exprs);

    // Without postcondition marking: should produce 0 instances (gate skips it)
    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 0,
        "5-param axiom should be skipped by parameter gate without postcondition marking"
    );

    // Mark as postcondition-critical and retry
    encoder
        .ground_pool
        .mark_postcondition_symbol("logic_fn_high_arity".to_string());
    // Need to bump revision so flush is not a no-op
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_high_arity".to_string(),
        params: vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
            "e".to_string(),
        ],
        body: PureExpr::Var("a".to_string(), None),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    let count = encoder
        .assert_ground_pool_instances()
        .expect("postcondition-critical instantiation should succeed");
    assert!(
        count >= 1,
        "5-param postcondition-critical axiom should bypass parameter gate and be instantiated, \
         got {count}"
    );
}

/// Postcondition-critical axioms receive highest priority in the budget,
/// so they are instantiated before non-critical axioms even when the budget
/// is tight.
#[test]
#[timeout(30000)]
fn test_postcondition_critical_gets_priority_in_budget() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;

    // Register a postcondition-critical 2-param axiom
    let fd_critical = encoder.solver.declare_fun(
        "logic_fn_critical",
        &[int_sort.clone(), int_sort.clone()],
        int_sort.clone(),
    );
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_critical".to_string(),
        params: vec!["x".to_string(), "y".to_string()],
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::Var("y".to_string(), None)),
        ),
        requires: vec![],
        func_decl: fd_critical.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });
    encoder
        .ground_pool
        .mark_postcondition_symbol("logic_fn_critical".to_string());

    // Register a non-critical 1-param axiom (normally higher priority by arity)
    let fd_noncritical = encoder.solver.declare_fun(
        "logic_fn_noncritical",
        &[int_sort.clone()],
        int_sort.clone(),
    );
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_noncritical".to_string(),
        params: vec!["x".to_string()],
        body: PureExpr::Var("x".to_string(), None),
        requires: vec![],
        func_decl: fd_noncritical.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    // Register ground entries for both
    let one = encoder.solver.int_const(1);
    let two = encoder.solver.int_const(2);
    let app_critical = encoder.solver.apply(&fd_critical, &[one, two]);
    encoder.ground_pool.register(
        "logic_fn_critical",
        app_critical,
        vec![one, two],
        vec![PureExpr::Int(1), PureExpr::Int(2)],
    );

    let app_noncritical = encoder.solver.apply(&fd_noncritical, &[one]);
    encoder.ground_pool.register(
        "logic_fn_noncritical",
        app_noncritical,
        vec![one],
        vec![PureExpr::Int(1)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("mixed critical/non-critical instantiation should succeed");
    assert_eq!(
        count, 2,
        "both critical and non-critical axioms should be instantiated"
    );

    // Verify the critical axiom was applied: f_critical(1, 2) = 3
    let three = encoder.solver.int_const(3);
    let eq = encoder.solver.eq(app_critical, three);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    let result = encoder.solver.check_sat();
    assert!(
        matches!(result.result(), ay_dpll::api::SolveResult::Unsat(_)),
        "postcondition-critical axiom should provide f(1,2) = 1+2 = 3: got {result:?}"
    );
}

/// `mark_postcondition_logic_fn_symbols` called with requires expressions also
/// marks logic function symbols as critical, allowing high-arity axioms in
/// requires clauses to bypass the parameter complexity gate. (#1296)
///
/// The SMT symbol name is produced by `logic_fn_smt_name`: underscores are
/// doubled, so `req_check` becomes `logic_req__check`. The axiom fn_symbol
/// and the ground pool registration must use the same SMT name.
#[test]
#[timeout(30000)]
fn test_requires_clause_logic_fn_marked_critical_bypasses_param_gate() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;

    // The SMT symbol that logic_fn_smt_name("req_check") produces
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("req_check");
    assert_eq!(smt_name, "logic_req__check");

    // Declare a 5-parameter logic function (exceeds TRUST_WP_MAX_AXIOM_PARAMS_FOR_GROUND=4)
    let func_decl = encoder.solver.declare_fun(
        &smt_name,
        &[
            int_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
            int_sort.clone(),
        ],
        int_sort.clone(),
    );

    // Register a 5-param axiom: forall a,b,c,d,e. f(a,b,c,d,e) = a
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: smt_name.clone(),
        params: vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
            "e".to_string(),
        ],
        body: PureExpr::Var("a".to_string(), None),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    // Register a ground entry
    let one = encoder.solver.int_const(1);
    let two = encoder.solver.int_const(2);
    let three = encoder.solver.int_const(3);
    let four = encoder.solver.int_const(4);
    let five = encoder.solver.int_const(5);
    let app = encoder
        .solver
        .apply(&func_decl, &[one, two, three, four, five]);
    encoder.ground_pool.register(
        &smt_name,
        app,
        vec![one, two, three, four, five],
        vec![
            PureExpr::Int(1),
            PureExpr::Int(2),
            PureExpr::Int(3),
            PureExpr::Int(4),
            PureExpr::Int(5),
        ],
    );

    // Without marking: should produce 0 instances (param gate skips 5-param axiom)
    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 0,
        "5-param axiom should be skipped without critical marking"
    );

    // Mark via requires clause (simulating what the solver_tail now does)
    // The LogicFnCall name is the source-level name ("req_check"), and
    // mark_postcondition_logic_fn_symbols internally converts it to
    // the SMT name ("logic_req__check") via logic_fn_smt_name.
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "req_check".to_string(),
            args: vec![
                PureExpr::Var("a".to_string(), None),
                PureExpr::Var("b".to_string(), None),
                PureExpr::Var("c".to_string(), None),
                PureExpr::Var("d".to_string(), None),
                PureExpr::Var("e".to_string(), None),
            ],
        }),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    encoder.mark_postcondition_logic_fn_symbols(&requires);

    // Verify the symbol was marked
    assert!(
        encoder.ground_pool.is_postcondition_symbol(&smt_name),
        "requires-referenced logic fn should be marked critical"
    );

    // Need to re-register the axiom since revision tracking makes flush a no-op
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: smt_name.clone(),
        params: vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
            "e".to_string(),
        ],
        body: PureExpr::Var("a".to_string(), None),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: int_sort.clone(),
        kind: AxiomKind::Defining,
    });

    let count = encoder
        .assert_ground_pool_instances()
        .expect("requires-marked instantiation should succeed");
    assert!(
        count >= 1,
        "5-param axiom marked critical via requires should bypass parameter gate, got {count}"
    );
}

/// `mark_postcondition_logic_fn_symbols` correctly extracts logic function names
/// from postcondition expressions and marks them as critical.
#[test]
#[timeout(30000)]
fn test_mark_postcondition_logic_fn_symbols_extracts_names() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Postcondition: result == my_fn(x) && other_fn(y) > 0
    let ensures = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "my_fn".to_string(),
                args: vec![PureExpr::Var("x".to_string(), None)],
            }),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: "other_fn".to_string(),
                args: vec![PureExpr::Var("y".to_string(), None)],
            }),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
    ];

    encoder.mark_postcondition_logic_fn_symbols(&ensures);

    // The SMT names should be marked
    assert!(
        encoder.ground_pool.is_postcondition_symbol("logic_my__fn"),
        "my_fn should be marked as postcondition-critical (smt name: logic_my__fn)"
    );
    assert!(
        encoder
            .ground_pool
            .is_postcondition_symbol("logic_other__fn"),
        "other_fn should be marked as postcondition-critical (smt name: logic_other__fn)"
    );
    assert!(
        !encoder
            .ground_pool
            .is_postcondition_symbol("logic_unrelated"),
        "unrelated symbols should not be marked"
    );
}

#[test]
#[timeout(30000)]
fn test_mark_postcondition_logic_fn_symbols_marks_method_backed_logic_axioms() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;
    let bool_sort = ay_dpll::api::Sort::Bool;
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("good_bucket");
    let func_decl = encoder.solver.declare_fun(
        &smt_name,
        &[int_sort.clone(), int_sort.clone(), int_sort.clone()],
        bool_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: smt_name.clone(),
        params: vec!["self".to_string(), "bucket".to_string(), "i".to_string()],
        body: PureExpr::Bool(true),
        requires: vec![],
        func_decl,
        return_sort: bool_sort,
        kind: AxiomKind::Defining,
    });

    let ensures = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("old_self".to_string(), Some(ExprSort::Int))),
        method: "good_bucket".to_string(),
        args: vec![
            PureExpr::Var("l_prime".to_string(), Some(ExprSort::Int)),
            PureExpr::Var("i".to_string(), Some(ExprSort::Int)),
        ],
    }];

    encoder.mark_postcondition_logic_fn_symbols(&ensures);

    assert!(
        encoder.ground_pool.is_postcondition_symbol(&smt_name),
        "receiver-style logic function method calls should mark the registered axiom symbol"
    );
}

#[test]
#[timeout(30000)]
fn test_mark_postcondition_logic_fn_symbols_marks_method_before_axiom_registration() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("good_bucket");
    let ensures = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("old_self".to_string(), Some(ExprSort::Int))),
        method: "good_bucket".to_string(),
        args: vec![
            PureExpr::Var("l_prime".to_string(), Some(ExprSort::Int)),
            PureExpr::Var("i".to_string(), Some(ExprSort::Int)),
        ],
    }];

    encoder.mark_postcondition_logic_fn_symbols(&ensures);

    assert!(
        encoder.ground_pool.is_postcondition_symbol(&smt_name),
        "method-backed logic symbols must be remembered even if the axiom is registered later"
    );
}

/// Type-invariant method calls are encoded under sort-specialized method
/// symbols, so the raw method name in the generated invariant postcondition
/// must mark the registered axiom symbol as critical.
#[test]
#[timeout(30000)]
fn test_mark_postcondition_logic_fn_symbols_marks_type_invariant_method_axioms() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let int_sort = ay_dpll::api::Sort::Int;
    let bool_sort = ay_dpll::api::Sort::Bool;
    let method = "__trust_wp_invariant_implementation_P__P_PersistentArray";
    let smt_name =
        "method___trust_wp_invariant_implementation_P__P_PersistentArray_1_i".to_string();
    let func_decl = encoder.solver.declare_fun(
        &smt_name,
        std::slice::from_ref(&int_sort),
        bool_sort.clone(),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: smt_name.clone(),
        params: vec!["self".to_string()],
        body: PureExpr::Bool(true),
        requires: vec![],
        func_decl,
        return_sort: bool_sort,
        kind: AxiomKind::Defining,
    });

    let ensures = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("result".to_string(), None)),
        method: method.to_string(),
        args: vec![],
    }];

    encoder.mark_postcondition_logic_fn_symbols(&ensures);

    assert!(
        encoder.ground_pool.is_postcondition_symbol(&smt_name),
        "type-invariant postcondition should mark the registered sort-specialized method axiom"
    );
    assert!(
        !encoder
            .ground_pool
            .is_postcondition_symbol(&format!("logic_{method}")),
        "raw logic-function spelling is not the ground-pool axiom symbol"
    );
}

/// When `mark_postcondition_logic_fn_symbols` is called separately for ensures
/// and requires clauses (as the solver_tail does), logic function symbols from
/// both are marked as critical. This mirrors the production call pattern. (#1296)
#[test]
#[timeout(30000)]
fn test_mark_both_ensures_and_requires_logic_fn_symbols() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Ensures references "post_fn"
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        trust_wp_core::formula::BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "post_fn".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }),
    )];

    // Requires references "pre_fn"
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "pre_fn".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];

    // Mirror the production pattern: mark ensures first, then requires
    encoder.mark_postcondition_logic_fn_symbols(&ensures);
    encoder.mark_postcondition_logic_fn_symbols(&requires);

    assert!(
        encoder
            .ground_pool
            .is_postcondition_symbol("logic_post__fn"),
        "ensures-referenced post_fn should be marked critical"
    );
    assert!(
        encoder.ground_pool.is_postcondition_symbol("logic_pre__fn"),
        "requires-referenced pre_fn should be marked critical"
    );
    assert!(
        !encoder
            .ground_pool
            .is_postcondition_symbol("logic_body__fn"),
        "unmentioned body_fn should NOT be marked"
    );
}

/// Verify that `ground_instance_arg_sort_compatible` accepts Int as a
/// universal fallback sort. When a ground entry has Int sort (from sort
/// inference fallback) and the axiom expects Seq(Int), the instance should
/// still fire — the Int was a speculative default, not a genuine sort. (#2699)
#[test]
#[timeout(30000)]
fn test_ground_pool_sort_compatible_int_fallback_matches_seq() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let seq_sort = Sort::seq(Sort::Int);

    // Declare g: Seq(Int) -> Int
    let func_decl =
        encoder
            .solver
            .declare_fun("logic_fn_g_seq", std::slice::from_ref(&seq_sort), Sort::Int);

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_g_seq".to_string(),
        params: vec!["s".to_string()],
        body: PureExpr::Int(42),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: Sort::Int,
        kind: AxiomKind::Defining,
    });

    // Register a ground entry with Int-sorted arg (sort inference fallback).
    // In production, sort inference may yield Int for a variable that is
    // actually Seq-sorted, because the annotation was missing. The ground
    // pool should still instantiate. (#2699)
    //
    // We cannot use solver.apply(func_decl, [int_term]) because ay enforces
    // sort matching on apply. Use a dummy application term instead (same
    // pattern as test_ground_pool_sort_incompatible_skips_instance).
    let int_term = encoder.solver.int_const(0);
    let dummy_app = encoder.solver.int_const(99);
    encoder.ground_pool.register(
        "logic_fn_g_seq",
        dummy_app,
        vec![int_term],
        vec![PureExpr::Int(0)],
    );

    // The instance should fire despite Int vs Seq(Int) mismatch
    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 1,
        "Int fallback arg should be compatible with Seq(Int) param (#2699)"
    );
}

/// Verify that `ground_instance_arg_sort_compatible` accepts Seq vs
/// Uninterpreted("Vec") as compatible (same Seq family). (#2699)
#[test]
#[timeout(30000)]
fn test_ground_pool_sort_compatible_seq_vs_uninterpreted_vec() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let seq_sort = Sort::seq(Sort::Int);

    // Declare h: Seq(Int) -> Int
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_h_seq_vec",
        std::slice::from_ref(&seq_sort),
        Sort::Int,
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_h_seq_vec".to_string(),
        params: vec!["v".to_string()],
        body: PureExpr::Int(0),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: Sort::Int,
        kind: AxiomKind::Defining,
    });

    // Register ground entry with Uninterpreted("Vec")-sorted term.
    // In production, struct layout extraction may produce Uninterpreted("Vec")
    // but the axiom was declared with Seq(Int). (#2699)
    let vec_sort = Sort::Uninterpreted("Vec".to_string());
    let vec_term = encoder.solver.declare_const("test_vec", vec_sort);
    // Create application using a Seq-sorted term for the solver
    let seq_term = encoder.solver.declare_const("test_seq_for_app", seq_sort);
    let app = encoder.solver.apply(&func_decl, &[seq_term]);
    // Register with Vec-sorted term as the argument
    encoder.ground_pool.register(
        "logic_fn_h_seq_vec",
        app,
        vec![vec_term],
        vec![PureExpr::Var("v".to_string(), None)],
    );

    // The instance should fire: Vec is in the Seq family
    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 1,
        "Uninterpreted(Vec) should be compatible with Seq(Int) param (#2699)"
    );
}

/// Verify that `ground_instance_arg_sort_compatible` accepts Uninterpreted
/// sorts in the same structural family (e.g., "Option" vs "OptionInt"). (#2699)
#[test]
#[timeout(30000)]
fn test_ground_pool_sort_compatible_uninterpreted_same_family() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let option_sort = Sort::Uninterpreted("Option".to_string());

    // Declare k: Option -> Int
    let func_decl = encoder.solver.declare_fun(
        "logic_fn_k_option",
        std::slice::from_ref(&option_sort),
        Sort::Int,
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_fn_k_option".to_string(),
        params: vec!["o".to_string()],
        body: PureExpr::Int(1),
        requires: vec![],
        func_decl: func_decl.clone(),
        return_sort: Sort::Int,
        kind: AxiomKind::Defining,
    });

    // Register ground entry with Uninterpreted("OptionInt") sort.
    // In production, match encoding may produce OptionInt (monomorphized)
    // while the axiom declaration uses the generic Option. (#2699)
    let option_int_sort = Sort::Uninterpreted("OptionInt".to_string());
    let opt_term = encoder.solver.declare_const("test_opt", option_int_sort);
    let app_term = encoder.solver.declare_const("test_app_opt", option_sort);
    let app = encoder.solver.apply(&func_decl, &[app_term]);
    encoder.ground_pool.register(
        "logic_fn_k_option",
        app,
        vec![opt_term],
        vec![PureExpr::Var("o".to_string(), None)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("instantiation should succeed");
    assert_eq!(
        count, 1,
        "Uninterpreted(OptionInt) should be compatible with Uninterpreted(Option) (#2699)"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_good_bucket_ground_instance_derives_bucket_index() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&option_int);

    let map_sort = Sort::Uninterpreted("MyHashMap".to_string());
    let list_sort = Sort::Uninterpreted("List".to_string());
    let option_sort = Sort::Datatype(option_int.clone());
    let good_decl = encoder.get_or_declare_logic_func(
        "logic_good__bucket",
        &[map_sort.clone(), list_sort.clone(), Sort::Int],
        Sort::Bool,
    );
    let get_decl = encoder.get_or_declare_logic_func(
        "logic_get",
        &[list_sort.clone(), Sort::Int],
        option_sort,
    );
    let bucket_ix_decl = encoder.get_or_declare_logic_func(
        "logic_bucket__ix",
        &[map_sort.clone(), Sort::Int],
        Sort::Int,
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_good__bucket".to_string(),
        params: vec!["self".to_string(), "l".to_string(), "h".to_string()],
        // The hashmap-list specialization must not rely on the generic
        // defining-body equality, which would leave a nested forall here.
        body: PureExpr::Bool(true),
        requires: vec![],
        func_decl: good_decl.clone(),
        return_sort: Sort::Bool,
        kind: AxiomKind::Defining,
    });

    let map_term = encoder.solver.declare_const("test_map", map_sort.clone());
    let list_term = encoder.solver.declare_const("test_list", list_sort);
    let h = encoder.solver.int_const(7);
    let k = encoder.solver.int_const(11);
    let v = encoder.solver.int_const(3);
    let good_app = encoder.solver.apply(&good_decl, &[map_term, list_term, h]);
    let get_app = encoder.solver.apply(&get_decl, &[list_term, k]);
    let some_v = encoder
        .solver
        .datatype_constructor(&option_int, "Some", &[v]);
    encoder.assert_term(good_app);
    let get_is_some_v = encoder.eq_term(get_app, some_v);
    encoder.assert_term(get_is_some_v);

    encoder.ground_pool.register(
        "logic_good__bucket",
        good_app,
        vec![map_term, list_term, h],
        vec![
            PureExpr::Var("self".to_string(), None),
            PureExpr::Var("l".to_string(), None),
            PureExpr::Int(7),
        ],
    );
    encoder.ground_pool.register(
        "logic_get",
        get_app,
        vec![list_term, k],
        vec![PureExpr::Var("l".to_string(), None), PureExpr::Int(11)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("hashmap-list ground consequence should encode");
    assert_eq!(
        count, 1,
        "one observed logic_get call should produce one good_bucket ground consequence"
    );

    let bucket_ix_app = encoder.solver.apply(&bucket_ix_decl, &[map_term, k]);
    let bucket_ix_is_h = encoder.eq_term(bucket_ix_app, h);
    let not_bucket_ix_is_h = encoder.solver.not(bucket_ix_is_h);
    encoder.assert_term(not_bucket_ix_is_h);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "good_bucket ground consequence should prove bucket_ix(self, k) == h, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_type_invariant_ground_pool_skips_nested_forall_equality() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let map_sort = Sort::Uninterpreted("MyHashMap".to_string());
    let inv_symbol =
        "method___trust_wp_invariant_creusot__test_P__P_MyHashMap_1_d4d79486173684d6170";
    let inv_decl =
        encoder.get_or_declare_logic_func(inv_symbol, std::slice::from_ref(&map_sort), Sort::Bool);

    let i = PureExpr::Var("i".to_string(), Some(ExprSort::Int));
    let self_expr = PureExpr::Var("self".to_string(), None);
    let bucket = PureExpr::LogicFnCall {
        name: "__seq_index_restore_List".to_string(),
        args: vec![
            PureExpr::LogicFnCall {
                name: "myhashmap_buckets".to_string(),
                args: vec![self_expr.clone()],
            },
            i.clone(),
        ],
    };
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(0)),
            trust_wp_core::formula::BinOp::Lt,
            Arc::new(PureExpr::LogicFnCall {
                name: "seq_len".to_string(),
                args: vec![PureExpr::LogicFnCall {
                    name: "myhashmap_buckets".to_string(),
                    args: vec![self_expr.clone()],
                }],
            }),
        )),
        trust_wp_core::formula::BinOp::And,
        Arc::new(PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::LogicFnCall {
                    name: "good_bucket".to_string(),
                    args: vec![self_expr, bucket.clone(), i],
                }),
                trust_wp_core::formula::BinOp::And,
                Arc::new(PureExpr::LogicFnCall {
                    name: "no_double_binding".to_string(),
                    args: vec![bucket],
                }),
            )),
            triggers: vec![],
        }),
    );

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: inv_symbol.to_string(),
        params: vec!["self".to_string()],
        body,
        requires: vec![],
        func_decl: inv_decl.clone(),
        return_sort: Sort::Bool,
        kind: AxiomKind::Defining,
    });

    let map_term = encoder.solver.declare_const("test_map", map_sort.clone());
    let inv_app = encoder.solver.apply(&inv_decl, &[map_term]);
    let buckets_decl =
        encoder.get_or_declare_logic_func("myhashmap_buckets", &[map_sort], Sort::seq(Sort::Int));
    let buckets = encoder.solver.apply(&buckets_decl, &[map_term]);
    let buckets_len = encoder
        .seq_len_term(buckets)
        .expect("hashmap-list test buckets len");
    encoder.assert_term(inv_app);
    encoder.ground_pool.register(
        inv_symbol,
        inv_app,
        vec![map_term],
        vec![PureExpr::Var("self".to_string(), None)],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("hashmap-list invariant skip should not fail");
    assert_eq!(
        count, 1,
        "hashmap-list invariant ground pool should emit only the ground length consequence"
    );

    let zero = encoder.solver.int_const(0);
    let len_positive = encoder.solver.lt(zero, buckets_len);
    let not_len_positive = encoder.solver.not(len_positive);
    encoder.assert_term(not_len_positive);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "grounded invariant length fact should prove 0 < buckets.len(), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_type_invariant_ground_instance_derives_observed_bucket_facts() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let map_sort = Sort::Uninterpreted("MyHashMap".to_string());
    let list_sort = Sort::Uninterpreted("List".to_string());
    let inv_symbol =
        "method___trust_wp_invariant_creusot__test_P__P_MyHashMap_1_d4d79486173684d6170";
    let inv_decl =
        encoder.get_or_declare_logic_func(inv_symbol, std::slice::from_ref(&map_sort), Sort::Bool);
    let good_decl = encoder.get_or_declare_logic_func(
        "logic_good__bucket",
        &[map_sort.clone(), list_sort.clone(), Sort::Int],
        Sort::Bool,
    );
    let no_double_decl = encoder.get_or_declare_logic_func(
        "logic_no__double__binding",
        std::slice::from_ref(&list_sort),
        Sort::Bool,
    );
    let buckets_decl = encoder.get_or_declare_logic_func(
        "myhashmap_buckets",
        &[map_sort.clone()],
        Sort::seq(Sort::Int),
    );
    let index_decl = encoder.get_or_declare_logic_func(
        "__seq_index_restore_List",
        &[Sort::seq(Sort::Int), Sort::Int],
        list_sort.clone(),
    );

    let self_expr = PureExpr::Var("self".to_string(), None);
    let index_expr = PureExpr::Var("i".to_string(), None);
    let buckets_expr = PureExpr::LogicFnCall {
        name: "buckets".to_string(),
        args: vec![self_expr.clone()],
    };
    let len_positive = PureExpr::BinOp(
        Arc::new(PureExpr::Int(0)),
        trust_wp_core::formula::BinOp::Lt,
        Arc::new(PureExpr::LogicFnCall {
            name: "seq_len".to_string(),
            args: vec![buckets_expr.clone()],
        }),
    );
    let bucket_expr = PureExpr::LogicFnCall {
        name: "__seq_index_restore_List".to_string(),
        args: vec![buckets_expr, index_expr.clone()],
    };
    let bucket_predicates = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: "good_bucket".to_string(),
                args: vec![self_expr.clone(), bucket_expr.clone(), index_expr],
            }),
            trust_wp_core::formula::BinOp::And,
            Arc::new(PureExpr::LogicFnCall {
                name: "no_double_binding".to_string(),
                args: vec![bucket_expr],
            }),
        )),
        triggers: vec![],
    };
    let body = PureExpr::BinOp(
        Arc::new(len_positive),
        trust_wp_core::formula::BinOp::And,
        Arc::new(bucket_predicates),
    );
    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: inv_symbol.to_string(),
        params: vec!["self".to_string()],
        body,
        requires: vec![],
        func_decl: inv_decl.clone(),
        return_sort: Sort::Bool,
        kind: AxiomKind::Defining,
    });

    let map_term = encoder.solver.declare_const("test_map", map_sort);
    let zero = encoder.solver.int_const(0);
    let inv_app = encoder.solver.apply(&inv_decl, &[map_term]);
    let buckets = encoder.solver.apply(&buckets_decl, &[map_term]);
    let bucket_at_zero = encoder.solver.apply(&index_decl, &[buckets, zero]);
    let buckets_len = encoder
        .seq_len_term(buckets)
        .expect("hashmap-list test buckets len");
    let good_app = encoder
        .solver
        .apply(&good_decl, &[map_term, bucket_at_zero, zero]);
    let no_double_app = encoder.solver.apply(&no_double_decl, &[bucket_at_zero]);

    encoder.assert_term(inv_app);
    let zero_lt_len = encoder.solver.lt(zero, buckets_len);
    encoder.assert_term(zero_lt_len);
    encoder.ground_pool.register(
        inv_symbol,
        inv_app,
        vec![map_term],
        vec![PureExpr::Var("self".to_string(), None)],
    );
    encoder.ground_pool.register_term_application(
        "__seq_index_restore_List",
        bucket_at_zero,
        vec![buckets, zero],
    );

    let count = encoder
        .assert_ground_pool_instances()
        .expect("hashmap-list invariant ground consequence should encode");
    assert_eq!(
        count, 3,
        "observed bucket index should produce len, good_bucket, and no_double_binding facts"
    );

    let not_good = encoder.solver.not(good_app);
    encoder.assert_term(not_good);
    let not_no_double = encoder.solver.not(no_double_app);
    encoder.assert_term(not_no_double);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "grounded invariant facts should prove observed bucket predicates, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_get_cons_head_ground_instance_derives_some() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&option_int);

    let list_sort = Sort::Uninterpreted("List".to_string());
    let tuple_sort = Sort::Uninterpreted("Tuple2".to_string());
    let get_decl = encoder.solver.declare_fun(
        "logic_get",
        &[list_sort.clone(), Sort::Int],
        Sort::Datatype(option_int.clone()),
    );
    let cons_decl = encoder.solver.declare_fun(
        "Cons",
        &[tuple_sort.clone(), list_sort.clone()],
        list_sort.clone(),
    );
    let tuple_get_0 = encoder.get_or_declare_logic_func(
        "logic_____trust_wp__tuple__get__0__placeholder_u5475706c6532__ret_i",
        &[tuple_sort.clone()],
        Sort::Int,
    );
    let tuple_get_1 = encoder.get_or_declare_logic_func(
        "logic_____trust_wp__tuple__get__1__placeholder_u5475706c6532__ret_i",
        &[tuple_sort.clone()],
        Sort::Int,
    );
    let deep_model =
        encoder.get_or_declare_spec_fn("method_deep_model_1_i", &[Sort::Int], Sort::Int);

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_get".to_string(),
        params: vec!["self".to_string(), "index".to_string()],
        body: PureExpr::Bool(true),
        requires: vec![],
        func_decl: get_decl.clone(),
        return_sort: Sort::Datatype(option_int.clone()),
        kind: AxiomKind::Defining,
    });

    let tuple = encoder.solver.declare_const("head", tuple_sort);
    let tail = encoder.solver.declare_const("tail", list_sort);
    let cons = encoder.solver.apply(&cons_decl, &[tuple, tail]);
    let head_key = encoder.solver.apply(&tuple_get_0, &[tuple]);
    let key = encoder.solver.apply(&deep_model, &[head_key]);
    let head_value = encoder.solver.apply(&tuple_get_1, &[tuple]);
    let get_app = encoder.solver.apply(&get_decl, &[cons, key]);
    let head_key_deep_model = encoder.solver.apply(&deep_model, &[head_key]);
    let key_matches_head = encoder.eq_term(key, head_key_deep_model);
    encoder.assert_term(key_matches_head);

    encoder
        .ground_pool
        .register("logic_get", get_app, vec![cons, key], vec![]);

    let count = encoder
        .assert_ground_pool_instances()
        .expect("hashmap-list get/Cons ground consequence should encode");
    assert!(
        count >= 1,
        "one observed logic_get over a Cons head should produce a ground consequence, got {count}"
    );

    let some_head_value = encoder
        .solver
        .try_datatype_constructor(&option_int, "Some", &[head_value])
        .expect("Some(head value)");
    let get_is_some_head_value = encoder.eq_term(get_app, some_head_value);
    let not_some_head_value = encoder.solver.not(get_is_some_head_value);
    encoder.assert_term(not_some_head_value);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "Cons-head ground consequence should prove get(Cons((k,v), tl), k@) == Some(v), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_get_cons_tail_ground_instance_derives_recursive_get() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&option_int);

    let list_sort = Sort::Uninterpreted("List".to_string());
    let tuple_sort = Sort::Uninterpreted("Tuple2".to_string());
    let get_decl = encoder.solver.declare_fun(
        "logic_get",
        &[list_sort.clone(), Sort::Int],
        Sort::Datatype(option_int.clone()),
    );
    let cons_decl = encoder.solver.declare_fun(
        "Cons",
        &[tuple_sort.clone(), list_sort.clone()],
        list_sort.clone(),
    );
    let tuple_get_0 = encoder.get_or_declare_logic_func(
        "logic_____trust_wp__tuple__get__0__placeholder_u5475706c6532__ret_i",
        &[tuple_sort.clone()],
        Sort::Int,
    );
    let deep_model =
        encoder.get_or_declare_spec_fn("method_deep_model_1_i", &[Sort::Int], Sort::Int);

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_get".to_string(),
        params: vec!["self".to_string(), "index".to_string()],
        body: PureExpr::Bool(true),
        requires: vec![],
        func_decl: get_decl.clone(),
        return_sort: Sort::Datatype(option_int.clone()),
        kind: AxiomKind::Defining,
    });

    let tuple = encoder.solver.declare_const("head", tuple_sort);
    let tail = encoder.solver.declare_const("tail", list_sort);
    let cons = encoder.solver.apply(&cons_decl, &[tuple, tail]);
    let key = encoder.solver.declare_const("key", Sort::Int);
    let head_key = encoder.solver.apply(&tuple_get_0, &[tuple]);
    let head_key_deep_model = encoder.solver.apply(&deep_model, &[head_key]);
    let get_app = encoder.solver.apply(&get_decl, &[cons, key]);
    let tail_get_app = encoder.solver.apply(&get_decl, &[tail, key]);

    let key_eq_head = encoder.eq_term(key, head_key);
    let key_ne_head = encoder.solver.not(key_eq_head);
    let key_eq_deep_head = encoder.eq_term(key, head_key_deep_model);
    let key_ne_deep_head = encoder.solver.not(key_eq_deep_head);
    encoder.assert_term(key_ne_head);
    encoder.assert_term(key_ne_deep_head);
    encoder
        .ground_pool
        .register("logic_get", get_app, vec![cons, key], vec![]);

    let count = encoder
        .assert_ground_pool_instances()
        .expect("hashmap-list get/Cons tail consequence should encode");
    assert!(
        count >= 2,
        "observed logic_get over Cons should produce head and tail consequences, got {count}"
    );

    let get_equals_tail = encoder.eq_term(get_app, tail_get_app);
    let not_get_equals_tail = encoder.solver.not(get_equals_tail);
    encoder.assert_term(not_get_equals_tail);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "Cons-tail ground consequence should prove get(Cons(head, tl), k) == get(tl, k), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_get_cons_head_ground_instance_uses_selector_guard() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&option_int);

    let list_sort = Sort::Uninterpreted("List".to_string());
    let tuple_sort = Sort::Uninterpreted("Tuple2".to_string());
    let get_decl = encoder.solver.declare_fun(
        "logic_get",
        &[list_sort.clone(), Sort::Int],
        Sort::Datatype(option_int.clone()),
    );
    let is_cons =
        encoder
            .solver
            .declare_fun("is-Cons", std::slice::from_ref(&list_sort), Sort::Bool);
    let cons_head = encoder.get_or_declare_logic_func(
        "hashmap_list_cons_0",
        std::slice::from_ref(&list_sort),
        tuple_sort.clone(),
    );
    let tuple_get_0 = encoder.get_or_declare_logic_func(
        "logic_____trust_wp__tuple__get__0__placeholder_u5475706c6532__ret_i",
        &[tuple_sort.clone()],
        Sort::Int,
    );
    let tuple_get_1 = encoder.get_or_declare_logic_func(
        "logic_____trust_wp__tuple__get__1__placeholder_u5475706c6532__ret_i",
        &[tuple_sort],
        Sort::Int,
    );
    let deep_model =
        encoder.get_or_declare_spec_fn("method_deep_model_1_i", &[Sort::Int], Sort::Int);

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_get".to_string(),
        params: vec!["self".to_string(), "index".to_string()],
        body: PureExpr::Bool(true),
        requires: vec![],
        func_decl: get_decl.clone(),
        return_sort: Sort::Datatype(option_int.clone()),
        kind: AxiomKind::Defining,
    });

    let list = encoder.solver.declare_const("list", list_sort);
    let head = encoder.solver.apply(&cons_head, &[list]);
    let head_key = encoder.solver.apply(&tuple_get_0, &[head]);
    let key = encoder.solver.apply(&deep_model, &[head_key]);
    let head_value = encoder.solver.apply(&tuple_get_1, &[head]);
    let get_app = encoder.solver.apply(&get_decl, &[list, key]);

    let is_cons_list = encoder.solver.apply(&is_cons, &[list]);
    encoder.assert_term(is_cons_list);
    encoder
        .ground_pool
        .register("logic_get", get_app, vec![list, key], vec![]);

    let count = encoder
        .assert_ground_pool_instances()
        .expect("selector-guarded get/Cons consequence should encode");
    assert!(
        count >= 1,
        "one observed logic_get over an is-Cons list should produce a guarded consequence, got {count}"
    );

    let some_head_value = encoder
        .solver
        .try_datatype_constructor(&option_int, "Some", &[head_value])
        .expect("Some(head value)");
    let get_is_some_head_value = encoder.eq_term(get_app, some_head_value);
    let not_some_head_value = encoder.solver.not(get_is_some_head_value);
    encoder.assert_term(not_some_head_value);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "selector-guarded Cons-head consequence should prove get(l, k@) == Some(v), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_get_cons_tail_ground_instance_uses_selector_guard() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&option_int);

    let list_sort = Sort::Uninterpreted("List".to_string());
    let tuple_sort = Sort::Uninterpreted("Tuple2".to_string());
    let get_decl = encoder.solver.declare_fun(
        "logic_get",
        &[list_sort.clone(), Sort::Int],
        Sort::Datatype(option_int.clone()),
    );
    let is_cons =
        encoder
            .solver
            .declare_fun("is-Cons", std::slice::from_ref(&list_sort), Sort::Bool);
    let cons_head = encoder.get_or_declare_logic_func(
        "hashmap_list_cons_0",
        std::slice::from_ref(&list_sort),
        tuple_sort.clone(),
    );
    let cons_tail = encoder.get_or_declare_logic_func(
        "hashmap_list_cons_1",
        std::slice::from_ref(&list_sort),
        list_sort.clone(),
    );
    let tuple_get_0 = encoder.get_or_declare_logic_func(
        "logic_____trust_wp__tuple__get__0__placeholder_u5475706c6532__ret_i",
        &[tuple_sort],
        Sort::Int,
    );
    let deep_model =
        encoder.get_or_declare_spec_fn("method_deep_model_1_i", &[Sort::Int], Sort::Int);

    encoder.ground_pool.register_axiom(AxiomEntry {
        fn_symbol: "logic_get".to_string(),
        params: vec!["self".to_string(), "index".to_string()],
        body: PureExpr::Bool(true),
        requires: vec![],
        func_decl: get_decl.clone(),
        return_sort: Sort::Datatype(option_int.clone()),
        kind: AxiomKind::Defining,
    });

    let list = encoder.solver.declare_const("list", list_sort);
    let head = encoder.solver.apply(&cons_head, &[list]);
    let tail = encoder.solver.apply(&cons_tail, &[list]);
    let key = encoder.solver.declare_const("key", Sort::Int);
    let head_key = encoder.solver.apply(&tuple_get_0, &[head]);
    let head_key_deep_model = encoder.solver.apply(&deep_model, &[head_key]);
    let get_app = encoder.solver.apply(&get_decl, &[list, key]);
    let tail_get_app = encoder.solver.apply(&get_decl, &[tail, key]);

    let is_cons_list = encoder.solver.apply(&is_cons, &[list]);
    encoder.assert_term(is_cons_list);
    let key_eq_head = encoder.eq_term(key, head_key);
    let key_ne_head = encoder.solver.not(key_eq_head);
    encoder.assert_term(key_ne_head);
    let key_eq_deep_head = encoder.eq_term(key, head_key_deep_model);
    let key_ne_deep_head = encoder.solver.not(key_eq_deep_head);
    encoder.assert_term(key_ne_deep_head);
    encoder
        .ground_pool
        .register("logic_get", get_app, vec![list, key], vec![]);

    let count = encoder
        .assert_ground_pool_instances()
        .expect("selector-guarded get/Cons tail consequence should encode");
    assert!(
        count >= 2,
        "one observed logic_get over an is-Cons list should produce guarded head and tail consequences, got {count}"
    );
    assert!(
        encoder
            .ground_pool
            .entries_for("logic_get")
            .expect("logic_get entries")
            .iter()
            .any(|entry| entry.application == tail_get_app),
        "tail logic_get term should be registered for later finite instantiation"
    );

    let get_equals_tail = encoder.eq_term(get_app, tail_get_app);
    let not_get_equals_tail = encoder.solver.not(get_equals_tail);
    encoder.assert_term(not_get_equals_tail);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "selector-guarded Cons-tail consequence should prove get(l, k) == get(tail(l), k), got {result:?}"
    );
}
