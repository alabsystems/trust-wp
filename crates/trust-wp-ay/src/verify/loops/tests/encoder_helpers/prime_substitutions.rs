// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use super::*;

// ── build_prime_substitutions coverage (#2133) ─────────────────────

/// Direct body effect: var_prime is declared and constrained to effect.
#[test]
#[timeout(30000)]
fn build_prime_substitutions_direct_effect() {
    let mut encoder = setup_loop_encoder(
        &[i_ge_zero(), i_le_n()],
        Some(&i_lt_n()),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    // Pre-declare i (needed for body effect encoding)
    encoder
        .get_or_declare_var("i", Sort::Int)
        .expect("declaring i should succeed");

    let body_effect = i_effect(1); // i → i + 1
    let empty = HashMap::new();
    let sort_plan = collect_loop_sort_plan(&mut encoder, &["i"], &body_effect);
    sort_plan
        .apply(&mut encoder)
        .expect("applying loop sort plan should succeed");
    let prime_subs = build_prime_substitutions(
        &mut encoder,
        &sort_plan,
        &["i"],
        effects(&body_effect, &empty, &empty),
    )
    .expect("build_prime_substitutions should succeed");

    assert!(
        prime_subs.contains_key("i"),
        "prime substitution should contain entry for `i`"
    );
    match &prime_subs["i"] {
        PureExpr::Var(name, sort) => {
            assert_eq!(name, "i_prime", "substitution should use i_prime");
            // Int sort maps to None (backward compat)
            assert_eq!(*sort, None, "Int sort should map to None ExprSort");
        }
        other => panic!("expected Var(i_prime, _), got {other:?}"),
    }
}

/// MIR tuple-return lowering can wrap scalar loop effects as
/// `tuple_get_0(effect)`. For scalar Int variables that wrapper is just the
/// return-value projection, so the prime bridge must constrain the variable to
/// the projected value itself rather than to an uninterpreted tuple accessor.
#[test]
#[timeout(30000)]
fn build_prime_substitutions_normalizes_int_value_projection_effect() {
    let mut encoder = setup_loop_encoder(
        &[i_ge_zero(), i_le_n()],
        Some(&i_lt_n()),
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    encoder
        .get_or_declare_var("i", Sort::Int)
        .expect("declaring i should succeed");

    let increment = PureExpr::BinOp(Arc::new(i_var()), BinOp::Add, Arc::new(PureExpr::Int(1)));
    let projected_increment = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![increment.clone()],
    };
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), projected_increment);

    let empty = HashMap::new();
    let sort_plan = collect_loop_sort_plan(&mut encoder, &["i"], &body_effect);
    sort_plan
        .apply(&mut encoder)
        .expect("applying loop sort plan should succeed");
    build_prime_substitutions(
        &mut encoder,
        &sort_plan,
        &["i"],
        effects(&body_effect, &empty, &empty),
    )
    .expect("build_prime_substitutions should succeed");

    let i_prime = encoder
        .get_or_declare_var("i_prime", Sort::Int)
        .expect("declaring i_prime should succeed");
    let increment_term = encoder
        .encode_pure(&increment)
        .expect("increment should encode");
    let eq = encoder.solver_mut().eq(i_prime, increment_term);
    let negated = encoder.solver_mut().not(eq);
    encoder.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "Int projection wrapper should normalize to i_prime = i + 1, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn build_prime_substitutions_preserves_declared_datatype_sort_for_box_tail_effect() {
    let mut encoder = crate::encoder::AYEncoder::new_all();
    let list_dt = ay_dpll::api::DatatypeSort {
        name: "List".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    ay_dpll::api::DatatypeField {
                        name: "list_cons_0".to_string(),
                        sort: Sort::Uninterpreted("Tuple2".to_string()),
                    },
                    ay_dpll::api::DatatypeField {
                        name: "list_cons_1".to_string(),
                        sort: Sort::Uninterpreted("List".to_string()),
                    },
                ],
            },
        ],
    };
    encoder.ensure_datatype_declared(&list_dt);
    encoder
        .get_or_declare_var("l", Sort::Datatype(list_dt.clone()))
        .expect("declaring list loop variable should succeed");

    let l_var = PureExpr::Var(
        "l".to_string(),
        Some(ExprSort::Datatype(
            trust_wp_core::formula::intern_sort_name("List"),
        )),
    );
    let tail = PureExpr::Deref(Arc::new(PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![l_var],
    }));
    let mut body_effect = HashMap::new();
    body_effect.insert("l".to_string(), tail);

    let empty = HashMap::new();
    let sort_plan = collect_loop_sort_plan(&mut encoder, &["l"], &body_effect);
    sort_plan
        .apply(&mut encoder)
        .expect("applying datatype loop sort plan should succeed");
    build_prime_substitutions(
        &mut encoder,
        &sort_plan,
        &["l"],
        effects(&body_effect, &empty, &empty),
    )
    .expect("datatype body effect should not redeclare l as Int");

    assert!(
        matches!(encoder.var_sort("l_prime"), Some(Sort::Datatype(dt)) if dt.name == "List"),
        "l_prime should preserve List datatype sort, got {:?}",
        encoder.var_sort("l_prime")
    );
}

/// Havoc path: modified var not in any body_effect map gets unconstrained prime.
#[test]
#[timeout(30000)]
fn build_prime_substitutions_havoc() {
    // Use a realistic invariant formula (x >= 0) so "x" is in value position,
    // not formula position, avoiding erroneous Bool classification. (#2195)
    let invariant = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let mut encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("encoder setup should succeed");

    let empty = HashMap::new();
    let sort_plan = collect_loop_sort_plan(&mut encoder, &["x"], &empty);
    sort_plan
        .apply(&mut encoder)
        .expect("applying havoc loop sort plan should succeed");
    let prime_subs = build_prime_substitutions(
        &mut encoder,
        &sort_plan,
        &["x"],
        effects(&empty, &empty, &empty),
    )
    .expect("havoc build_prime_substitutions should succeed");

    assert!(
        prime_subs.contains_key("x"),
        "havoc should still produce prime substitution"
    );
    match &prime_subs["x"] {
        PureExpr::Var(name, _) => {
            assert_eq!(name, "x_prime", "havoc substitution should use x_prime");
        }
        other => panic!("expected Var(x_prime, _), got {other:?}"),
    }
}

/// Deref body effect: constrains var_prime_current instead of var_prime.
#[test]
#[timeout(30000)]
fn build_prime_substitutions_deref_effect() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Var("b".to_string(), Some(ExprSort::Bool))],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    // Variable `b` was pre-declared as Bool from the invariant context
    // (invariants are formula-position, and `Var("b", Some(Bool))` is
    // the entire invariant). Use Sort::Bool to match pre-declaration.
    encoder
        .get_or_declare_var("b", Sort::Bool)
        .expect("declaring b should succeed");

    let empty = HashMap::new();
    let mut deref_effect = HashMap::new();
    deref_effect.insert("b".to_string(), PureExpr::Bool(true));

    let sort_plan = collect_loop_sort_plan(&mut encoder, &["b"], &empty);
    sort_plan
        .apply(&mut encoder)
        .expect("applying deref loop sort plan should succeed");
    let prime_subs = build_prime_substitutions(
        &mut encoder,
        &sort_plan,
        &["b"],
        effects(&empty, &deref_effect, &empty),
    )
    .expect("deref build_prime_substitutions should succeed");

    assert!(
        prime_subs.contains_key("b"),
        "deref effect should produce prime substitution for b"
    );
    match &prime_subs["b"] {
        PureExpr::Var(name, _) => {
            assert_eq!(name, "b_prime", "deref sub should use b_prime");
        }
        other => panic!("expected Var(b_prime, _), got {other:?}"),
    }
}

/// Double-deref body effect uses the full verification pipeline to confirm
/// correct priming through `verify_preservation`. Integration test for #1295.
/// Testing `build_prime_substitutions` double-deref path directly requires
/// careful intermediate-level sort setup; the pipeline handles this correctly.
#[test]
#[timeout(30000)]
fn build_prime_substitutions_double_deref_asserts_second_current_bridge() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declaring x should succeed");
    encoder
        .get_or_declare_var("x_current", Sort::Int)
        .expect("declaring x_current should succeed");

    let empty = HashMap::new();
    let mut double_deref_body_effect = HashMap::new();
    double_deref_body_effect.insert("x".to_string(), int(0));

    let sort_plan = collect_loop_sort_plan(&mut encoder, &["x"], &empty);
    sort_plan
        .apply(&mut encoder)
        .expect("applying double-deref loop sort plan should succeed");
    let prime_subs = build_prime_substitutions(
        &mut encoder,
        &sort_plan,
        &["x"],
        effects(&empty, &empty, &double_deref_body_effect),
    )
    .expect("double-deref build_prime_substitutions should succeed");

    match &prime_subs["x"] {
        PureExpr::Var(name, sort) => {
            assert_eq!(name, "x_prime", "double-deref sub should use x_prime");
            assert_eq!(*sort, None, "Int sort should map to None ExprSort");
        }
        other => panic!("expected Var(x_prime, _), got {other:?}"),
    }

    encoder
        .get_or_declare_var("x_prime_current", Sort::Int)
        .expect("declaring x_prime_current should succeed");
    let x_prime_current_current = encoder
        .get_or_declare_var("x_prime_current_current", Sort::Int)
        .expect("declaring x_prime_current_current should succeed");
    let zero = encoder.solver_mut().int_const(0);
    let eq_zero = encoder.solver_mut().eq(x_prime_current_current, zero);
    let negated = encoder.solver_mut().not(eq_zero);
    encoder.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "double-deref bridge should assert x_prime_current_current = 0, got {result:?}"
    );
}

/// Double-deref body effect uses the full verification pipeline to confirm
/// correct priming through `verify_preservation`. Integration test for #1295.
/// The direct helper test above proves the second-current bridge is asserted;
/// this integration test keeps the full loop-preservation path covered.
#[test]
#[timeout(30000)]
fn build_prime_substitutions_double_deref_via_preservation() {
    // Model: fn clear(x: &mut &mut i32) with loop { **x = 0 }
    // Invariant: true (trivial — we just test the priming doesn't crash)
    let invariants = vec![PureExpr::Bool(true)];
    let body_effect = HashMap::new();
    let mut double_deref_body_effect = HashMap::new();
    double_deref_body_effect.insert("x".to_string(), PureExpr::Int(0));

    let result = verify_preservation_with_config(
        &invariants,
        None,
        false,
        &["x"],
        effects(&body_effect, &HashMap::new(), &double_deref_body_effect),
        &LoopEncoderConfig::default(),
    )
    .expect("preservation with double-deref effect should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "trivial invariant with double-deref effect should verify, got {result:?}"
    );
}

/// Seq-typed body effect preserves ExprSort::Seq annotation on prime var
/// through the full preservation pipeline. (#1301)
/// Uses `verify_preservation_with_config` since direct `build_prime_substitutions`
/// with Seq sort requires careful encoder setup for the eq/iff constraint.
#[test]
#[timeout(30000)]
fn build_prime_substitutions_seq_sort_via_preservation() {
    // Model: loop that reassigns a Seq-typed variable.
    // Invariant: true (trivial — we test that Seq priming doesn't error)
    let invariants = vec![PureExpr::Bool(true)];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "v".to_string(),
        PureExpr::Var("w".to_string(), Some(ExprSort::Seq)),
    );

    let result = verify_preservation_with_config(
        &invariants,
        None,
        false,
        &["v"],
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("preservation with Seq-typed body effect should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "trivial invariant with Seq body effect should verify, got {result:?}"
    );
}

/// Seq push_back effects need an explicit prime-length bridge so primed
/// invariants over `len(v_prime)` can use the `len(push_back(v, x)) = len(v)+1`
/// ground fact without relying on congruence propagation. (#2323)
#[test]
#[timeout(30000)]
fn build_prime_substitutions_seq_push_back_prime_len_bridge() {
    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let elem = PureExpr::Var("elem".to_string(), None);
    let counter = PureExpr::Var("counter".to_string(), None);
    let base = PureExpr::Var("base".to_string(), None);

    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "len".to_string(),
        args: vec![],
    };
    let invariant = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(produced_len),
            BinOp::Add,
            Arc::new(base.clone()),
        )),
        BinOp::Eq,
        Arc::new(counter.clone()),
    );

    let push_back_effect = PureExpr::MethodCall {
        receiver: Arc::new(produced.clone()),
        method: "push_back".to_string(),
        args: vec![elem],
    };
    let counter_effect = PureExpr::BinOp(
        Arc::new(counter.clone()),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    let effects_vec = vec![push_back_effect.clone(), counter_effect.clone()];

    let mut encoder = setup_loop_encoder(
        &[invariant.clone()],
        None,
        &[&effects_vec],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");
    encoder
        .get_or_declare_var("produced", Sort::seq(Sort::Int))
        .expect("declaring produced should succeed");
    encoder
        .get_or_declare_var("counter", Sort::Int)
        .expect("declaring counter should succeed");
    encoder
        .get_or_declare_var("base", Sort::Int)
        .expect("declaring base should succeed");
    encoder
        .get_or_declare_var("elem", Sort::Int)
        .expect("declaring elem should succeed");

    let mut body_effect = HashMap::new();
    body_effect.insert("produced".to_string(), push_back_effect);
    body_effect.insert("counter".to_string(), counter_effect);

    let empty = HashMap::new();
    let sort_plan = collect_loop_sort_plan(&mut encoder, &["produced", "counter"], &body_effect);
    sort_plan
        .apply(&mut encoder)
        .expect("applying seq push_back sort plan should succeed");
    let prime_subs = build_prime_substitutions(
        &mut encoder,
        &sort_plan,
        &["produced", "counter"],
        effects(&body_effect, &empty, &empty),
    )
    .expect("build_prime_substitutions should succeed");

    let invariant_term = encoder
        .encode_pure(&invariant)
        .expect("invariant should encode");
    encoder.assert_term(invariant_term);
    encoder.assert_seq_ground_instances(
        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
    );

    let modified_set: std::collections::HashSet<&str> =
        ["produced", "counter"].into_iter().collect();
    let primed_invariant = invariant.substitute_filtered(&modified_set, &prime_subs);
    encoder.register_sort_hints(std::slice::from_ref(&primed_invariant));
    let primed_term = encoder
        .encode_pure(&primed_invariant)
        .expect("primed invariant should encode");
    let negated = encoder.solver_mut().not(primed_term);
    encoder.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "seq prime len bridge should make the primed len obligation UNSAT, got {result:?}"
    );
}

/// FMap insert body effects should register the primed proxy as an eager
/// `fmap_insert` ground application so partition proofs can query
/// `contains(result_prime, k)`/`lookup(result_prime, k)` directly. (#2116)
#[test]
#[timeout(30000)]
fn build_prime_substitutions_registers_fmap_insert_alias_application() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Bool(true)],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    encoder.record_sort_hint("result".to_string(), ExprSort::FMap);
    encoder
        .get_or_declare_var("result", Sort::Uninterpreted("FMap".to_string()))
        .expect("declaring result should succeed");
    encoder
        .get_or_declare_var("entry_key", Sort::Int)
        .expect("declaring entry_key should succeed");
    encoder
        .get_or_declare_var("entry_value", Sort::Int)
        .expect("declaring entry_value should succeed");

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "result".to_string(),
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("result".to_string(), Some(ExprSort::FMap))),
            method: "insert".to_string(),
            args: vec![
                PureExpr::Var("entry_key".to_string(), None),
                PureExpr::Var("entry_value".to_string(), None),
            ],
        },
    );

    let empty = HashMap::new();
    let sort_plan = collect_loop_sort_plan(&mut encoder, &["result"], &body_effect);
    sort_plan
        .apply(&mut encoder)
        .expect("applying loop sort plan should succeed");
    let prime_subs = build_prime_substitutions(
        &mut encoder,
        &sort_plan,
        &["result"],
        effects(&body_effect, &empty, &empty),
    )
    .expect("build_prime_substitutions should succeed");

    let PureExpr::Var(prime_name, _) = &prime_subs["result"] else {
        panic!("expected result prime substitution");
    };
    let result_prime = encoder
        .get_or_declare_var(prime_name, Sort::Uninterpreted("FMap".to_string()))
        .expect("declaring result_prime should succeed");
    let insert_entries = encoder
        .ground_pool_for_test()
        .entries_for("fmap_insert")
        .expect("fmap_insert should be registered in the ground pool");
    assert!(
        insert_entries
            .iter()
            .any(|entry| entry.application == result_prime),
        "build_prime_substitutions should register result_prime as an fmap_insert alias application"
    );
}

/// Verify that `sort_to_expr_sort` and `infer_expr_sort` round-trip
/// correctly for Seq sort — the annotation pipeline that #1301 depends on.
#[test]
#[timeout(30000)]
fn build_prime_substitutions_seq_sort_annotation_chain() {
    use crate::encoder::infer_expr_sort;

    // infer_expr_sort on a Seq-annotated var returns Sort::Seq(Int) (#2080)
    let seq_var = PureExpr::Var("v".to_string(), Some(ExprSort::Seq));
    let sort = infer_expr_sort(&seq_var);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "Seq-annotated var should infer to Sort::Seq(Int)"
    );

    // sort_to_expr_sort maps it back to ExprSort::Seq
    let expr_sort = sort_to_expr_sort(&sort);
    assert_eq!(
        expr_sort,
        Some(ExprSort::Seq),
        "Sort::Seq(Int) should round-trip back to ExprSort::Seq (#1301, #2080)"
    );
}

/// Bool-typed body effect infers Sort::Bool via is_bool_var.
#[test]
#[timeout(30000)]
fn build_prime_substitutions_bool_sort_inference() {
    let mut encoder = setup_loop_encoder(
        &[PureExpr::Var("done".to_string(), Some(ExprSort::Bool))],
        None,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("encoder setup should succeed");

    encoder.mark_bool_var("done");
    encoder
        .get_or_declare_var("done", Sort::Bool)
        .expect("declaring done as Bool should succeed");

    let mut body_effect = HashMap::new();
    body_effect.insert("done".to_string(), PureExpr::Bool(true));

    let empty = HashMap::new();
    let sort_plan = collect_loop_sort_plan(&mut encoder, &["done"], &body_effect);
    sort_plan
        .apply(&mut encoder)
        .expect("applying Bool loop sort plan should succeed");
    let prime_subs = build_prime_substitutions(
        &mut encoder,
        &sort_plan,
        &["done"],
        effects(&body_effect, &empty, &empty),
    )
    .expect("Bool build_prime_substitutions should succeed");

    match &prime_subs["done"] {
        PureExpr::Var(name, sort) => {
            assert_eq!(name, "done_prime");
            assert_eq!(
                *sort,
                Some(ExprSort::Bool),
                "Bool-typed prime var must carry ExprSort::Bool annotation"
            );
        }
        other => panic!("expected Var(done_prime, Some(Bool)), got {other:?}"),
    }
}
