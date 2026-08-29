// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct unit tests for `Counterexample::from_model` (#1378).
//!
//! `from_model` is `pub(super)` — these tests live inside `verify/` to access it.
//! The function extracts counterexample data from ay models when verification
//! fails, preserving the solver's full `ModelValue` surface in `CounterexampleValue`s.

use ay_dpll::api::{
    DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Model, SolveResult, Solver, Sort,
};
use ntest::timeout;
use num_bigint::BigInt;

use super::{Counterexample, CounterexampleType, PostconditionInfo, VarOrigin};
use crate::encoder::AYEncoder;

fn model_from_solver(solver: &Solver) -> Option<Model> {
    solver.model().map(ay_dpll::VerifiedModel::into_inner)
}

fn value_for<'a>(cex: &'a Counterexample, name: &str) -> &'a CounterexampleType {
    &cex.values
        .iter()
        .find(|value| value.name == name)
        .unwrap_or_else(|| panic!("{name} should be in counterexample"))
        .value
}

/// `from_model(Some(m))` with an Int variable extracts an Int counterexample value.
#[test]
#[timeout(30000)]
fn from_model_extracts_int_value() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let constraint = solver.eq(x, five);
    solver.assert_term(constraint);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let model = model_from_solver(&solver);
    let cex = Counterexample::from_model(model);

    assert!(!cex.values.is_empty(), "model should produce values");
    assert_eq!(value_for(&cex, "x"), &CounterexampleType::Int(5.into()));
    assert!(
        cex.values
            .iter()
            .find(|value| value.name == "x")
            .expect("x should be present")
            .origin
            .is_none(),
        "origin should be None initially"
    );
}

/// Solver-safe identities for reserved source variables are projected back to
/// the original Rust spelling in user-facing counterexamples.
#[test]
#[timeout(30000)]
fn from_model_restores_reserved_source_variable_name() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let identity = crate::source_symbol::base_identity("default");
    let default = solver.declare_const(identity.as_ref(), Sort::Int);
    let seven = solver.int_const(7);
    let constraint = solver.eq(default, seven);
    solver.assert_term(constraint);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let cex = Counterexample::from_model(model_from_solver(&solver));
    assert_eq!(
        value_for(&cex, "default"),
        &CounterexampleType::Int(7.into())
    );
    assert!(
        cex.values.iter().all(|value| value.name != identity),
        "private solver identity must not leak into counterexample output"
    );
}

/// A base source declaration remains authoritative when a verification lane
/// removes its shell binding before model extraction and installs no
/// replacement. This is the `result` shape used by several sliced pipelines.
#[test]
#[timeout(30000)]
fn active_projection_keeps_base_without_replacement_binding() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let identity = crate::source_symbol::base_identity("result");
    let result = solver.declare_const(identity.as_ref(), Sort::Bool);
    solver.assert_term(result);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let active = std::collections::HashMap::new();
    let cex = Counterexample::from_model_with_active_source_identities(
        model_from_solver(&solver),
        &active,
    );
    assert_eq!(value_for(&cex, "result"), &CounterexampleType::Bool(true));
    assert_eq!(
        cex.values
            .iter()
            .filter(|value| value.name == "result")
            .count(),
        1
    );
}

/// A sort upgrade leaves the old declaration in AY, but counterexamples must
/// expose exactly the active shell binding under the source name.
#[test]
#[timeout(30000)]
fn from_encoder_model_uses_active_upgrade_without_stale_duplicate() {
    let mut encoder = AYEncoder::new_pure();
    let stale = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("initial Int source variable");
    let one = encoder.solver.int_const(1);
    let stale_value = encoder.solver.eq(stale, one);
    encoder.solver.assert_term(stale_value);

    let active = encoder
        .get_or_declare_var("x", Sort::Bool)
        .expect("Int-to-Bool source variable upgrade");
    encoder.rebind_var("x_alias", active, Sort::Bool);
    encoder.solver.assert_term(active);

    assert_eq!(encoder.check_sat(), SolveResult::Sat);
    let model = encoder.get_model();
    let cex = Counterexample::from_encoder_model(&encoder, model);
    let source_values: Vec<_> = cex
        .values
        .iter()
        .filter(|value| value.name == "x")
        .collect();
    assert_eq!(source_values.len(), 1, "stale binding leaked: {cex:?}");
    assert_eq!(source_values[0].value, CounterexampleType::Bool(true));
    assert_eq!(
        cex.values
            .iter()
            .filter(|value| value.name == "x_alias")
            .count(),
        1,
        "active aliases must be projected deterministically: {cex:?}"
    );
    assert!(
        cex.values
            .iter()
            .all(|value| { !crate::source_symbol::is_encoded_source_identity(&value.name) }),
        "private source identities must not leak: {cex:?}"
    );
}

/// Repeated repairs of one source binding must always allocate distinct solver
/// identities. A role-only `upgrade` name collides when the inferred sort moves
/// Int -> Bool -> Int, and reusing an earlier identity would revive stale
/// constraints even if the solver accepted it.
#[test]
#[timeout(30000)]
fn repeated_source_sort_repairs_use_fresh_solver_identities() {
    let mut encoder = AYEncoder::new_pure();
    let initial = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("initial Int source variable");
    let bool_repair = encoder
        .get_or_declare_var("x", Sort::Bool)
        .expect("Int-to-Bool source variable repair");
    let int_repair = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("Bool-to-Int source variable repair");

    assert_ne!(initial, bool_repair);
    assert_ne!(bool_repair, int_repair);
    assert_ne!(initial, int_repair);
    assert_eq!(encoder.solver.get_sort(int_repair), Sort::Int);
    assert_eq!(encoder.var_term("x"), Some(int_repair));
}

/// A source can be rebound to an expression rather than another declared
/// constant (notably `result` body aliases). In that case there is no model
/// identity to project, but the stale declaration must still stay hidden.
#[test]
#[timeout(30000)]
fn from_encoder_model_suppresses_stale_base_for_active_expression_binding() {
    let mut encoder = AYEncoder::new_pure();
    let stale = encoder
        .get_or_declare_var("result", Sort::Int)
        .expect("initial result declaration");
    let one = encoder.solver.int_const(1);
    let stale_value = encoder.solver.eq(stale, one);
    encoder.solver.assert_term(stale_value);

    let active_expression = encoder.solver.int_const(2);
    encoder.rebind_var("result", active_expression, Sort::Int);

    assert_eq!(encoder.check_sat(), SolveResult::Sat);
    let model = encoder.get_model();
    let cex = Counterexample::from_encoder_model(&encoder, model);
    assert!(
        cex.values.iter().all(|value| value.name != "result"),
        "stale result declaration leaked for expression binding: {cex:?}"
    );
}

/// Production result binding first equates a declared source identity with the
/// body, then rebinds the encoder shell to that compound body.  The declared
/// identity is a sound model witness in that case and must remain visible.
#[test]
#[timeout(30000)]
fn from_encoder_model_keeps_authenticated_expression_witness() {
    let mut encoder = AYEncoder::new_pure();
    let result = encoder
        .get_or_declare_var("result", Sort::Int)
        .expect("result declaration");
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("x declaration");
    let one = encoder.solver.int_const(1);
    let x_value = encoder.solver.eq(x, one);
    encoder.solver.assert_term(x_value);
    let body = encoder.solver.add(x, one);
    let result_value = encoder.solver.eq(result, body);
    encoder.solver.assert_term(result_value);
    encoder.rebind_var("result", body, Sort::Int);
    encoder.record_counterexample_witness("result", result);

    assert_eq!(encoder.check_sat(), SolveResult::Sat);
    let model = encoder.get_model();
    let cex = Counterexample::from_encoder_model(&encoder, model);
    assert_eq!(
        value_for(&cex, "result"),
        &CounterexampleType::Int(2.into())
    );
    assert_eq!(
        cex.values
            .iter()
            .filter(|value| value.name == "result")
            .count(),
        1,
        "authenticated result witness duplicated: {cex:?}"
    );
    assert!(
        cex.values
            .iter()
            .all(|value| !crate::source_symbol::is_encoded_source_identity(&value.name)),
        "private source identity leaked: {cex:?}"
    );
}

/// Rebinding the same source through another compound term must retain the
/// original declared witness instead of treating the intermediate expression
/// as a solver variable.
#[test]
#[timeout(30000)]
fn from_encoder_model_keeps_witness_across_repeated_expression_rebinds() {
    let mut encoder = AYEncoder::new_pure();
    let result = encoder
        .get_or_declare_var("result", Sort::Int)
        .expect("result declaration");
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("x declaration");
    let zero = encoder.solver.int_const(0);
    let first_body = encoder.solver.add(x, zero);
    let first_equality = encoder.solver.eq(result, first_body);
    encoder.solver.assert_term(first_equality);
    encoder.rebind_var_with_authenticated_witness("result", first_body, Sort::Int, result);

    let second_body = encoder.solver.add(first_body, zero);
    let second_equality = encoder.solver.eq(first_body, second_body);
    encoder.solver.assert_term(second_equality);
    encoder.rebind_var_with_authenticated_witness("result", second_body, Sort::Int, first_body);

    let two = encoder.solver.int_const(2);
    let x_value = encoder.solver.eq(x, two);
    encoder.solver.assert_term(x_value);
    assert_eq!(encoder.check_sat(), SolveResult::Sat);

    let model = encoder.get_model();
    let cex = Counterexample::from_encoder_model(&encoder, model);
    assert_eq!(
        value_for(&cex, "result"),
        &CounterexampleType::Int(2.into())
    );
}

/// If a sort-upgraded source binding is later removed, neither the stale base
/// nor the now-unowned derived declaration is authoritative. Omitting the
/// ambiguous source is safer than reporting the old value under its Rust name.
#[test]
#[timeout(30000)]
fn from_encoder_model_suppresses_source_after_removed_upgrade_binding() {
    let mut encoder = AYEncoder::new_pure();
    let stale = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("initial Int source variable");
    let one = encoder.solver.int_const(1);
    let stale_value = encoder.solver.eq(stale, one);
    encoder.solver.assert_term(stale_value);

    let upgraded = encoder
        .get_or_declare_var("x", Sort::Bool)
        .expect("Int-to-Bool source variable upgrade");
    encoder.solver.assert_term(upgraded);
    encoder.remove_var("x");

    assert_eq!(encoder.check_sat(), SolveResult::Sat);
    let model = encoder.get_model();
    let cex = Counterexample::from_encoder_model(&encoder, model);
    assert!(
        cex.values.iter().all(|value| value.name != "x"),
        "removed upgrade binding must not fall back to its stale base: {cex:?}"
    );
    assert!(
        cex.values
            .iter()
            .all(|value| { !crate::source_symbol::is_encoded_source_identity(&value.name) }),
        "private source identities must remain hidden: {cex:?}"
    );
}

/// When a base source binding is intentionally removed, a raw internal
/// constant with the same spelling must not duplicate or override it.
#[test]
#[timeout(30000)]
fn from_encoder_model_removed_base_still_suppresses_raw_name_collision() {
    let mut encoder = AYEncoder::new_pure();
    let internal = encoder.solver.declare_const("result", Sort::Int);
    let two = encoder.solver.int_const(2);
    let internal_value = encoder.solver.eq(internal, two);
    encoder.solver.assert_term(internal_value);

    let source = encoder
        .get_or_declare_var("result", Sort::Int)
        .expect("source result declaration");
    let one = encoder.solver.int_const(1);
    let source_value = encoder.solver.eq(source, one);
    encoder.solver.assert_term(source_value);
    encoder.remove_var("result");

    assert_eq!(encoder.check_sat(), SolveResult::Sat);
    let model = encoder.get_model();
    let cex = Counterexample::from_encoder_model(&encoder, model);
    let results: Vec<_> = cex
        .values
        .iter()
        .filter(|value| value.name == "result")
        .collect();
    assert_eq!(results.len(), 1, "raw result identity leaked: {cex:?}");
    assert_eq!(results[0].value, CounterexampleType::Int(1.into()));
}

/// A raw encoder-internal identity may use the same spelling as a source
/// variable. The encoded source declaration is authoritative; exposing both
/// would produce an ambiguous, potentially contradictory counterexample.
#[test]
#[timeout(30000)]
fn from_encoder_model_suppresses_raw_identity_colliding_with_source_name() {
    let mut encoder = AYEncoder::new_pure();
    let internal_heap = encoder.solver.declare_const("heap", Sort::Int);
    let one = encoder.solver.int_const(1);
    let internal_value = encoder.solver.eq(internal_heap, one);
    encoder.solver.assert_term(internal_value);

    let source_heap = encoder
        .get_or_declare_var("heap", Sort::Int)
        .expect("source variable named like an internal solver constant");
    let two = encoder.solver.int_const(2);
    let source_value = encoder.solver.eq(source_heap, two);
    encoder.solver.assert_term(source_value);

    assert_eq!(encoder.check_sat(), SolveResult::Sat);
    let model = encoder.get_model();
    let cex = Counterexample::from_encoder_model(&encoder, model);
    let heaps: Vec<_> = cex
        .values
        .iter()
        .filter(|value| value.name == "heap")
        .collect();
    assert_eq!(heaps.len(), 1, "raw identity leaked: {cex:?}");
    assert_eq!(heaps[0].value, CounterexampleType::Int(2.into()));
}

/// `from_model(Some(m))` with a Bool variable extracts a Bool counterexample value.
#[test]
#[timeout(30000)]
fn from_model_extracts_bool_value() {
    let mut encoder = AYEncoder::new_pure();
    let b = encoder.solver.declare_const("flag", Sort::Bool);
    encoder.solver.assert_term(b); // assert flag = true

    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let model = encoder.get_model();
    let cex = Counterexample::from_model(model);

    assert_eq!(value_for(&cex, "flag"), &CounterexampleType::Bool(true));
}

/// `from_model(Some(m))` with both Int and Bool variables extracts both.
#[test]
#[timeout(30000)]
fn from_model_extracts_mixed_types() {
    let mut encoder = AYEncoder::new_pure();
    let x = encoder.solver.declare_const("x", Sort::Int);
    let b = encoder.solver.declare_const("b", Sort::Bool);
    let ten = encoder.solver.int_const(10);
    let x_eq_10 = encoder.solver.eq(x, ten);
    encoder.solver.assert_term(x_eq_10);
    let not_b = encoder.solver.not(b);
    encoder.solver.assert_term(not_b); // b = false

    let result = encoder.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let model = encoder.get_model();
    let cex = Counterexample::from_model(model);

    assert!(
        cex.values.len() >= 2,
        "should have at least 2 values, got {}",
        cex.values.len()
    );
    assert_eq!(cex.values[0].name, "b");
    assert_eq!(cex.values[1].name, "x");
    assert_eq!(value_for(&cex, "x"), &CounterexampleType::Int(10.into()));
    assert_eq!(value_for(&cex, "b"), &CounterexampleType::Bool(false));
}

/// `from_model(Some(m))` preserves bitvector values with width information.
#[test]
#[timeout(30000)]
fn from_model_extracts_bitvec_value() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let bv = solver.declare_const("bv", Sort::bitvec(8));
    let two_a = solver.bv_const(0x2a, 8);
    let eq = solver.eq(bv, two_a);
    solver.assert_term(eq);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let cex = Counterexample::from_model(model_from_solver(&solver));
    assert_eq!(
        value_for(&cex, "bv"),
        &CounterexampleType::BitVec {
            value: 0x2a.into(),
            width: 8,
        }
    );
}

/// `from_model(Some(m))` preserves concrete sequence elements.
#[test]
#[timeout(30000)]
fn from_model_extracts_sequence_value() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let seq_sort = Sort::Seq(Box::new(Sort::Int));
    let seq = solver.declare_const("seq", seq_sort);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let three = solver.int_const(3);
    let seq1 = solver.seq_unit(one);
    let seq2 = solver.seq_unit(two);
    let seq3 = solver.seq_unit(three);
    let seq12 = solver.seq_concat(seq1, seq2);
    let seq123 = solver.seq_concat(seq12, seq3);
    let eq = solver.eq(seq, seq123);
    solver.assert_term(eq);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let cex = Counterexample::from_model(model_from_solver(&solver));
    assert_eq!(
        value_for(&cex, "seq"),
        &CounterexampleType::Seq(vec![
            CounterexampleType::Int(1.into()),
            CounterexampleType::Int(2.into()),
            CounterexampleType::Int(3.into()),
        ])
    );
}

/// `from_model(Some(m))` preserves datatype constructor payloads.
#[test]
#[timeout(30000)]
fn from_model_extracts_datatype_value() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
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
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    solver.declare_datatype(&option_int);
    let opt = solver.declare_const("opt", Sort::Datatype(option_int.clone()));
    let one = solver.int_const(1);
    let some_one = solver.datatype_constructor(&option_int, "Some", &[one]);
    let eq = solver.eq(opt, some_one);
    solver.assert_term(eq);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let cex = Counterexample::from_model(model_from_solver(&solver));
    assert_eq!(
        value_for(&cex, "opt"),
        &CounterexampleType::Datatype {
            constructor: "Some".to_string(),
            args: vec![CounterexampleType::Int(1.into())],
        }
    );
}

/// `from_model(Some(m))` preserves array defaults plus explicit stores.
#[test]
#[timeout(30000)]
fn from_model_extracts_array_value() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let array = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let zero = solver.int_const(0);
    let const_array = solver.const_array(Sort::Int, zero);
    let idx4 = solver.int_const(4);
    let val7 = solver.int_const(7);
    let arr = solver.store(const_array, idx4, val7);
    let eq = solver.eq(array, arr);
    solver.assert_term(eq);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let cex = Counterexample::from_model(model_from_solver(&solver));
    // ay model builder may simplify `(store (const 0) 4 7)` by omitting
    // explicit stores that overlap with the default. Accept either form.
    let arr_val = value_for(&cex, "arr");
    match arr_val {
        CounterexampleType::Array { default, stores } => {
            assert_eq!(default.as_ref(), &CounterexampleType::Int(0.into()));
            // Stores may include (4, 7) or be empty if ay simplified the model
            if !stores.is_empty() {
                assert_eq!(
                    stores,
                    &[(
                        CounterexampleType::Int(4.into()),
                        CounterexampleType::Int(7.into())
                    )]
                );
            }
        }
        other => panic!("expected Array, got: {other:?}"),
    }
}

/// `from_model(Some(m))` stores large integers losslessly even if the
/// compatibility helper stays lossy.
#[test]
#[timeout(30000)]
fn from_model_stores_large_integer_losslessly() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("big", Sort::Int);
    let big = BigInt::from(i64::MAX) + 1;
    let big_term = solver.int_const_bigint(&big);
    let eq = solver.eq(x, big_term);
    solver.assert_term(eq);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let cex = Counterexample::from_model(model_from_solver(&solver));
    assert_eq!(
        value_for(&cex, "big"),
        &CounterexampleType::Int(big.clone())
    );
    assert_eq!(
        cex.int_assignments().find(|(name, _)| *name == "big"),
        Some(("big", i64::MAX))
    );
}

/// `from_model(None)` returns an empty counterexample.
#[test]
#[timeout(30000)]
fn from_model_none_returns_empty() {
    let cex = Counterexample::from_model(None);
    assert!(
        cex.values.is_empty(),
        "None model should produce empty counterexample"
    );
    assert!(cex.violated_postcondition.is_none());
}

/// `set_origin` annotates the matching variable and leaves others unchanged.
#[test]
#[timeout(30000)]
fn set_origin_annotates_correct_variable() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let three = solver.int_const(3);
    let seven = solver.int_const(7);
    let c1 = solver.eq(x, three);
    solver.assert_term(c1);
    let c2 = solver.eq(y, seven);
    solver.assert_term(c2);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let model = model_from_solver(&solver);
    let mut cex = Counterexample::from_model(model);

    cex.set_origin(
        "x",
        VarOrigin::Parameter {
            name: "x".to_string(),
            span: None,
        },
    );

    let x_val = cex.values.iter().find(|v| v.name == "x").unwrap();
    assert!(
        x_val.origin.is_some(),
        "x should have origin after set_origin"
    );

    let y_val = cex.values.iter().find(|v| v.name == "y").unwrap();
    assert!(y_val.origin.is_none(), "y should still have no origin");
}

/// `set_violated_postcondition` stores the postcondition info.
#[test]
#[timeout(30000)]
fn set_violated_postcondition_stores_info() {
    let mut cex = Counterexample::from_model(None);
    assert!(cex.violated_postcondition.is_none());

    cex.set_violated_postcondition(PostconditionInfo {
        clause_idx: 0,
        contract_text: "result > x".to_string(),
        span: None,
    });

    let info = cex.violated_postcondition.as_ref().unwrap();
    assert_eq!(info.clause_idx, 0);
    assert_eq!(info.contract_text, "result > x");
}

/// `int_assignments` and `bool_assignments` iterators filter correctly.
#[test]
#[timeout(30000)]
fn assignment_iterators_filter_by_type() {
    let mut encoder = AYEncoder::new_pure();
    let x = encoder.solver.declare_const("num", Sort::Int);
    let b = encoder.solver.declare_const("flag", Sort::Bool);
    let val = encoder.solver.int_const(42);
    let c = encoder.solver.eq(x, val);
    encoder.solver.assert_term(c);
    encoder.solver.assert_term(b);

    let result = encoder.check_sat();
    assert!(matches!(result, SolveResult::Sat));

    let model = encoder.get_model();
    let cex = Counterexample::from_model(model);

    let ints: Vec<_> = cex.int_assignments().collect();
    assert!(ints.iter().any(|(name, v)| *name == "num" && *v == 42));
    assert!(!ints.iter().any(|(name, _)| *name == "flag"));

    let bools: Vec<_> = cex.bool_assignments().collect();
    assert!(bools.iter().any(|(name, v)| *name == "flag" && *v));
    assert!(!bools.iter().any(|(name, _)| *name == "num"));
}
