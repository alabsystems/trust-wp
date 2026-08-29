// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

use super::contract_transform::make_parsed_contract;
use crate::{
    callbacks::verification::contract_transform::transform_contract, mir_analysis::MutBorrowBody,
};

#[test]
fn transform_contract_adds_inv_assumption_for_mut_ref_params() {
    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Bool(true)];
    parsed.ensures = vec![PureExpr::Bool(true)];
    parsed.arg_names = vec!["x".to_string()];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["x".to_string()]);

    let transformed = transform_contract(&parsed);
    assert!(
        transformed.effective_requires.iter().any(|expr| matches!(
            expr,
            PureExpr::LogicFnCall { name, args }
            if name == "inv"
                && matches!(
                    args.first(),
                    Some(PureExpr::Var(v, _)) if v == "x"
                )
        )),
        "mut-ref params should inject whole-borrow inv(x) into effective requires"
    );
    assert!(
        transformed.effective_requires.iter().any(|expr| matches!(
            expr,
            PureExpr::LogicFnCall { name, args }
            if name == "inv"
                && matches!(
                    args.first(),
                    Some(PureExpr::Deref(inner)) if matches!(inner.as_ref(), PureExpr::Var(v, _) if v == "x")
                )
        )),
        "mut-ref params should inject inv(*x) into effective requires"
    );
}

#[test]
fn transform_contract_uses_typed_whole_borrow_inv_for_generic_mut_ref_params() {
    let t_id = intern_sort_name("T");
    let typed_x = PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)))),
    );
    let mut parsed = make_parsed_contract();
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["x".to_string()]);
    parsed.mut_borrow.mut_borrow_body = Some(MutBorrowBody {
        final_values: HashMap::from([(
            "x".to_string(),
            PureExpr::Deref(Arc::new(typed_x.clone())),
        )]),
        indexed_writes: vec![],
        resolve_results: None,
        finality: HashMap::new(),
        borrow_id_origins: HashMap::new(),
        delayed_writeback_assumptions: vec![],
        mutation_continued_params: HashSet::new(),
        nested_slot_resolutions: vec![],
        nested_transfer_params: HashSet::new(),
    });

    let transformed = transform_contract(&parsed);

    assert!(
        transformed.effective_requires.iter().any(|expr| matches!(
            expr,
            PureExpr::LogicFnCall { name, args }
            if name == "inv" && args.first() == Some(&typed_x)
        )),
        "whole-borrow inv should keep the typed &mut T parameter; got {:?}",
        transformed.effective_requires
    );
}

#[test]
fn transform_contract_grounds_generic_deref_mut_precondition_quantifier() {
    let t_id = intern_sort_name("T");
    let typed_x = PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)))),
    );
    let y = PureExpr::Var("y".to_string(), None);
    let receiver = PureExpr::Var("T::deref_mut".to_string(), None);

    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Forall {
        var: "y".to_string(),
        var_sort: Some(ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)))),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::LogicFnCall {
                    name: "inv".to_string(),
                    args: vec![y.clone()],
                }),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Deref(Arc::new(y))),
                    BinOp::Eq,
                    Arc::new(PureExpr::Deref(Arc::new(typed_x.clone()))),
                )),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(receiver.clone()),
                method: "precondition".to_string(),
                args: vec![PureExpr::Var("y".to_string(), None)],
            }),
        )),
        triggers: vec![],
    }];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["x".to_string()]);
    parsed.mut_borrow.mut_borrow_body = Some(MutBorrowBody {
        final_values: HashMap::from([(
            "x".to_string(),
            PureExpr::Deref(Arc::new(typed_x.clone())),
        )]),
        indexed_writes: vec![],
        resolve_results: None,
        finality: HashMap::new(),
        borrow_id_origins: HashMap::new(),
        delayed_writeback_assumptions: vec![],
        mutation_continued_params: HashSet::new(),
        nested_slot_resolutions: vec![],
        nested_transfer_params: HashSet::new(),
    });

    let transformed = transform_contract(&parsed);

    assert!(
        transformed.effective_requires.iter().any(|expr| matches!(
            expr,
            PureExpr::MethodCall { receiver, method, args }
            if matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "T::deref_mut")
                && method == "precondition"
                && args.first() == Some(&typed_x)
        )),
        "generic DerefMut quantified precondition should be grounded for x; got {:?}",
        transformed.effective_requires
    );
}

/// Call-site assumptions from spec_apply bind `self` to the reference directly
/// (#2578). The postcondition transform must NOT be applied to them, or `x`
/// would be transformed to `^x` (Final), mismatching the ensures form. (#717)
#[test]
fn transform_contract_preserves_call_assumption_reference_form() {
    // After #2578: spec_apply binds self to x directly (no Deref wrapping)
    let call_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("T::deref_mut".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![
            PureExpr::Var("x".to_string(), None),
            PureExpr::Var("call_3".to_string(), None),
        ],
    };

    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Bool(true)];
    parsed.ensures = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("T::deref_mut".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![
            PureExpr::Var("x".to_string(), None),
            PureExpr::Var("result".to_string(), None),
        ],
    }];
    parsed.result_expr = Some(PureExpr::Var("call_3".to_string(), None));
    parsed.arg_names = vec!["x".to_string()];
    parsed.call_assumptions = vec![call_assumption];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["x".to_string()]);

    let transformed = transform_contract(&parsed);

    // Ensures: DerefMut specs use the whole-borrow receiver, so x stays x
    // rather than being normalized to *x.
    let ensures_has_var_x = transformed.effective_ensures.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { args, .. }
            if matches!(args.first(), Some(PureExpr::Var(v, _)) if v == "x")
        )
    });
    assert!(
        ensures_has_var_x,
        "DerefMut ensures should preserve whole-borrow x"
    );

    // Call-site assumption: should preserve x (Var), NOT transform to ^x (Final)
    let assumption_has_var_x = transformed.effective_requires.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { method, args, .. }
            if method == "postcondition"
                && matches!(args.first(), Some(PureExpr::Var(v, _)) if v == "x")
        )
    });
    assert!(
        assumption_has_var_x,
        "call-site assumption should preserve x (Var) from spec_apply, not transform to ^x; \
         got effective_requires: {:?}",
        transformed.effective_requires
    );

    // Bridged assumption (call_3 -> result) should also preserve x
    let bridged_has_var_x = transformed.effective_requires.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { method, args, .. }
            if method == "postcondition"
                && matches!(args.first(), Some(PureExpr::Var(v, _)) if v == "x")
                && matches!(args.get(1), Some(PureExpr::Var(name, _)) if name == "result")
        )
    });
    assert!(
        bridged_has_var_x,
        "bridged assumption should also have x and result"
    );
}

#[test]
fn transform_contract_preserves_annotated_whole_mut_ref_form_for_generic_deref() {
    let t_id = intern_sort_name("T");
    let x = PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)))),
    );

    let call_assumption = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("T::deref_mut".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![x.clone(), PureExpr::Var("call_3".to_string(), None)],
    };

    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Bool(true)];
    parsed.ensures = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("T::deref_mut".to_string(), None)),
        method: "postcondition".to_string(),
        args: vec![x.clone(), PureExpr::Var("result".to_string(), None)],
    }];
    parsed.result_expr = Some(PureExpr::Var("call_3".to_string(), None));
    parsed.arg_names = vec!["x".to_string()];
    parsed.call_assumptions = vec![call_assumption];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["x".to_string()]);

    let transformed = transform_contract(&parsed);

    let ensure_preserves_annotated_x = transformed.effective_ensures.iter().any(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { method, args, .. }
            if method == "postcondition"
                && matches!(
                    args.first(),
                    Some(PureExpr::Var(name, Some(ExprSort::MutRef(inner))))
                        if name == "x" && matches!(inner.as_ref(), ExprSort::TypeParam(id) if *id == t_id)
                )
        )
    });
    assert!(
        ensure_preserves_annotated_x,
        "annotated generic &mut arg should stay whole-borrow in ensures; got {:?}",
        transformed.effective_ensures
    );

    let requires_preserve_annotated_x = transformed.effective_requires.iter().filter(|expr| {
        matches!(
            expr,
            PureExpr::MethodCall { method, args, .. }
            if method == "postcondition"
                && matches!(
                    args.first(),
                    Some(PureExpr::Var(name, Some(ExprSort::MutRef(inner))))
                        if name == "x" && matches!(inner.as_ref(), ExprSort::TypeParam(id) if *id == t_id)
                )
        )
    });
    assert!(
        requires_preserve_annotated_x.count() >= 2,
        "call assumption and bridged assumption should both preserve annotated whole-borrow x; got {:?}",
        transformed.effective_requires
    );
}
