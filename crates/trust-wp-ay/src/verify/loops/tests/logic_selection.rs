// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

/// Match constructor patterns (Some/None/Ok/Err) in loop invariants
/// require a quantifier-capable encoder. Without this detection the
/// encoder uses QF_LIA which cannot represent native datatypes. (#1364)
#[test]
#[timeout(30000)]
fn new_loop_encoder_selects_quantifiers_for_match_constructors() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    // Invariant using a Match with Constructor pattern:
    // match opt { Some(v) => v > 0, None => true }
    let invariant = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("opt".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Var("v".to_string(), None)),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                ),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: PureExpr::Bool(true),
            },
        ],
    };

    // This should NOT panic with a QF_LIA sort error.
    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("loop encoder should handle match constructors in invariants");
    assert!(
        encoder.supports_quantifiers(),
        "match constructor invariants require quantifier-capable logic, \
         but encoder has logic {:?}",
        encoder.logic()
    );
}
/// Regression test for #994/#1944: match constructor patterns in loop
/// invariants should route to Logic::All when combined with quantifiers.
/// This ensures parity with `setup_verification_encoder` (setup.rs).
#[test]
#[timeout(30000)]
fn new_loop_encoder_routes_to_logic_all_for_match_constructors() {
    use ay_dpll::api::Logic;
    use trust_wp_core::formula::{MatchArm, Pattern};

    // Invariant using a Match with Constructor pattern:
    // match opt { Some(v) => v > 0, _ => true }
    let invariant = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("opt".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Var("v".to_string(), None)),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                ),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Bool(true),
            },
        ],
    };

    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("loop encoder should handle match constructors");
    assert_eq!(
        encoder.logic(),
        Logic::All,
        "match constructor in loop invariant should route to Logic::All (#994)"
    );
}

/// Negative test: plain arithmetic loop invariants should NOT route to Logic::All.
#[test]
#[timeout(30000)]
fn new_loop_encoder_plain_arithmetic_does_not_use_logic_all() {
    use ay_dpll::api::Logic;

    let invariant = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );

    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("loop encoder should handle plain arithmetic");
    assert_ne!(
        encoder.logic(),
        Logic::All,
        "plain arithmetic loop invariant should not use Logic::All"
    );
}

/// Regression test for #994: datatype spec methods (is_some, unwrap) in loop
/// invariants should route to Logic::All.
#[test]
#[timeout(30000)]
fn new_loop_encoder_datatype_spec_method_routes_to_logic_all() {
    use ay_dpll::api::Logic;

    let invariant = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("opt".to_string(), None)),
        method: "is_some".to_string(),
        args: vec![],
    };

    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("loop encoder should handle datatype spec methods");
    assert_eq!(
        encoder.logic(),
        Logic::All,
        "datatype spec method in loop invariant should route to Logic::All (#994)"
    );
}
// ── loop encoder feature detection coverage (#2133, #2195) ─────────

/// Bitwise ops (BitAnd, Shl, etc.) require quantifier-capable encoder
/// because they are encoded as UFs with quantified axioms. (#1922)
#[test]
#[timeout(30000)]
fn new_loop_encoder_selects_quantifiers_for_bitwise_ops() {
    let invariant = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::BitAnd,
            Arc::new(PureExpr::Int(0xFF)),
        )),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("bitwise ops should not cause encoder creation to fail");
    assert!(
        encoder.supports_quantifiers(),
        "bitwise ops require quantifier-capable encoder for UF axioms (#1922), \
         but got logic {:?}",
        encoder.logic()
    );
}

/// UF-injecting method calls (ext_eq, fset_contains, deep_model, etc.)
/// require quantifier-capable encoder. (#1923)
#[test]
#[timeout(30000)]
fn new_loop_encoder_selects_quantifiers_for_uf_methods() {
    let invariant = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
        method: "ext_eq".to_string(),
        args: vec![PureExpr::Var("t".to_string(), None)],
    };
    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("UF method should not cause encoder creation to fail");
    assert!(
        encoder.supports_quantifiers(),
        "UF-injecting methods require quantifier-capable encoder (#1923), \
         but got logic {:?}",
        encoder.logic()
    );
}

/// Seq methods needing quantifiers (push_back, reverse, etc.) should
/// trigger both quantifier support AND Array theory. (#1581)
#[test]
#[timeout(30000)]
fn new_loop_encoder_selects_quantifiers_and_arrays_for_seq_methods() {
    use ay_dpll::api::Logic;

    let invariant = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".to_string(), Some(ExprSort::Seq))),
        method: "push_back".to_string(),
        args: vec![PureExpr::Int(1)],
    };
    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("Seq method should not cause encoder creation to fail");
    assert!(
        encoder.supports_quantifiers(),
        "Seq quantifier methods need quantifier support (#1581)"
    );
    // Seq methods need Array theory (AUFLIA, not just UFLIA)
    assert_eq!(
        encoder.logic(),
        Logic::Auflia,
        "Seq methods require Array theory for store/select (#1581)"
    );
}

/// Closure spec methods (postcondition_once, precondition, etc.)
/// require quantifier-capable encoder for closure axiom instantiation.
#[test]
#[timeout(30000)]
fn new_loop_encoder_selects_quantifiers_for_closure_specs() {
    let invariant = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(2)],
    };
    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("closure spec method should not cause encoder creation to fail");
    assert!(
        encoder.supports_quantifiers(),
        "closure spec methods require quantifier-capable encoder, \
         but got logic {:?}",
        encoder.logic()
    );
}

/// Tuple logic functions (__trust_wp_tuple2, __trust_wp_tuple_get_0) require
/// quantifier-capable encoder.
#[test]
#[timeout(30000)]
fn new_loop_encoder_selects_quantifiers_for_tuple_fns() {
    let invariant = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple2".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(2)],
    };
    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("tuple fn should not cause encoder creation to fail");
    assert!(
        encoder.supports_quantifiers(),
        "tuple logic functions require quantifier-capable encoder, \
         but got logic {:?}",
        encoder.logic()
    );
}

/// Type invariants trigger quantifier support (body axioms use forall).
#[test]
#[timeout(30000)]
fn new_loop_encoder_selects_quantifiers_for_type_invariants() {
    let inv = trust_wp_core::type_invariant_def! {
        type_name: "u32_nonneg".to_string(),
        self_param: "x".to_string(),
        param_sort: None,
        body: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        is_newtype: false,
        element_invariant_method: None,
    };
    let simple_expr = PureExpr::Var("x".to_string(), None);
    let invs = [inv];
    let config = LoopEncoderConfig::default().with_type_invariants(&invs);
    let encoder = setup_loop_encoder(&[simple_expr], None, &[], &config)
        .expect("type invariant should not cause encoder creation to fail");
    assert!(
        encoder.supports_quantifiers(),
        "type invariants require quantifier-capable encoder for body axioms, \
         but got logic {:?}",
        encoder.logic()
    );
}

/// Logic function definitions trigger quantifier support (defining axioms).
#[test]
#[timeout(30000)]
fn new_loop_encoder_selects_quantifiers_for_logic_fns() {
    let logic_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Mul,
            Arc::new(PureExpr::Int(2)),
        ),
    );
    let simple_expr = PureExpr::Var("x".to_string(), None);
    let fns = [logic_fn];
    let config = LoopEncoderConfig::default().with_logic_fns(&fns);
    let encoder = setup_loop_encoder(&[simple_expr], None, &[], &config)
        .expect("logic fn should not cause encoder creation to fail");
    assert!(
        encoder.supports_quantifiers(),
        "logic function definitions require quantifier-capable encoder, \
         but got logic {:?}",
        encoder.logic()
    );
}

/// Explicit quantifiers (Forall/Exists) in invariant exprs trigger
/// quantifier support.
#[test]
#[timeout(30000)]
fn new_loop_encoder_selects_quantifiers_for_explicit_forall() {
    let invariant = PureExpr::Forall {
        var: "j".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("j".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )),
        triggers: vec![],
    };
    let encoder = setup_loop_encoder(&[invariant], None, &[], &LoopEncoderConfig::default())
        .expect("forall expr should not cause encoder creation to fail");
    assert!(
        encoder.supports_quantifiers(),
        "explicit Forall requires quantifier-capable encoder"
    );
}

/// Track level Ptr/Mem should produce heap-aware encoder (AUFLIA family).
#[test]
#[timeout(30000)]
fn new_loop_encoder_heap_aware_for_ptr_track() {
    use ay_dpll::api::Logic;
    use trust_wp_core::TrackLevel;

    let simple_expr = PureExpr::Var("x".to_string(), None);
    let config = LoopEncoderConfig::default().with_track(TrackLevel::Ptr);
    let encoder = setup_loop_encoder(&[simple_expr], None, &[], &config)
        .expect("Ptr track should not cause encoder creation to fail");
    // Ptr/Mem without quantifiers → QfAuflia
    assert_eq!(
        encoder.logic(),
        Logic::QfAuflia,
        "Ptr track requires heap-aware encoder (QfAuflia), got {:?}",
        encoder.logic()
    );
}
