// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use ay_dpll::api::{SolveResult, TermKind};
use ntest::timeout;
use trust_wp_core::{
    formula::{BinOp, ExprSort, PureExpr},
    logic::{LogicFnDef, LogicMode},
};

use super::*;

fn make_invariant(type_name: &str) -> TypeInvariantDef {
    make_invariant_with_body(type_name, PureExpr::Bool(true))
}

fn make_invariant_with_body(type_name: &str, body: PureExpr) -> TypeInvariantDef {
    trust_wp_core::type_invariant_def! {
        type_name: type_name.to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: body,
        is_newtype: false,
        element_invariant_method: None,
    }
}

#[cfg(test)]
mod bootstrap_detection;

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn fmap_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::FMap))
}

fn fmap_contains(receiver: PureExpr, key: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: std::sync::Arc::new(receiver),
        method: "contains".to_string(),
        args: vec![key],
    }
}

fn eq(left: PureExpr, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        std::sync::Arc::new(left),
        BinOp::Eq,
        std::sync::Arc::new(right),
    )
}

fn ne(left: PureExpr, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        std::sync::Arc::new(left),
        BinOp::Ne,
        std::sync::Arc::new(right),
    )
}

fn seq_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
}

fn final_seq(name: &str) -> PureExpr {
    PureExpr::Final(std::sync::Arc::new(seq_var(name)))
}

fn implies(left: PureExpr, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        std::sync::Arc::new(left),
        BinOp::Implies,
        std::sync::Arc::new(right),
    )
}

#[test]
#[timeout(30000)]
fn encode_requires_grounds_fmap_frame_forall_without_asserting_quantifier() {
    let inserted = var("inserted");
    let other = var("other");
    let bound = var("k2");
    let base = fmap_var("base");
    let final_map = fmap_var("final_map");

    let frame = PureExpr::Forall {
        var: "k2".to_string(),
        var_sort: None,
        body: std::sync::Arc::new(implies(
            ne(bound.clone(), inserted.clone()),
            eq(
                fmap_contains(final_map.clone(), bound.clone()),
                fmap_contains(base.clone(), bound),
            ),
        )),
        triggers: Vec::new(),
    };

    let requires = vec![
        ne(other.clone(), inserted),
        fmap_contains(base, other.clone()),
        frame,
    ];

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encode_and_assert_requires(&mut encoder, &requires).expect("preconditions should encode");

    let forall_assertions = encoder
        .solver()
        .assertions()
        .iter()
        .filter(|&&term| matches!(encoder.solver().term_kind(term), TermKind::Forall))
        .count();
    assert_eq!(
        forall_assertions, 0,
        "standard FMap frame forall should be replaced by ground instances"
    );

    let final_other = encoder
        .encode_pure(&fmap_contains(final_map, other))
        .expect("ground contains should encode");
    let not_final_other = encoder.solver.not(final_other);
    encoder.assert_term(not_final_other);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "grounded FMap frame instance should preserve the observed-key consequence"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_good_bucket_precondition_stays_ground_predicate() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let good_bucket = LogicFnDef::new(
        "good_bucket".to_string(),
        "test::good_bucket".to_string(),
        vec!["self".to_string(), "l".to_string(), "h".to_string()],
        PureExpr::Forall {
            var: "k".to_string(),
            var_sort: Some(ExprSort::Int),
            body: std::sync::Arc::new(PureExpr::Bool(true)),
            triggers: vec![],
        },
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![
        Some(ExprSort::Int),
        Some(ExprSort::Int),
        Some(ExprSort::Int),
    ]);
    encoder
        .register_logic_fn(&good_bucket)
        .expect("good_bucket registration should encode");

    let requires = vec![PureExpr::LogicFnCall {
        name: "good_bucket".to_string(),
        args: vec![var("map"), var("bucket"), PureExpr::Int(0)],
    }];
    encode_and_assert_requires(&mut encoder, &requires).expect("precondition should encode");

    let forall_assertions = encoder
        .solver()
        .assertions()
        .iter()
        .filter(|&&term| matches!(encoder.solver().term_kind(term), TermKind::Forall))
        .count();
    assert_eq!(
        forall_assertions, 0,
        "hashmap-list good_bucket preconditions should rely on ground consequences"
    );
}

#[test]
fn free_seq_carrier_alias_planner_accepts_both_equality_directions() {
    let forward = plan_free_seq_carrier_aliases(&[eq(seq_var("v"), final_seq("call"))]);
    let reverse = plan_free_seq_carrier_aliases(&[eq(final_seq("call"), seq_var("v"))]);

    assert_eq!(forward.get("v"), Some(&final_seq("call")));
    assert_eq!(reverse, forward);
}

#[test]
fn free_seq_carrier_alias_planner_resolves_chains_in_either_requirement_order() {
    let chain = eq(seq_var("v"), seq_var("middle"));
    let terminal = eq(seq_var("middle"), final_seq("call"));
    let forward = plan_free_seq_carrier_aliases(&[chain.clone(), terminal.clone()]);
    let reverse = plan_free_seq_carrier_aliases(&[terminal, chain]);

    for plan in [&forward, &reverse] {
        assert_eq!(plan.get("v"), Some(&final_seq("call")));
        assert_eq!(plan.get("middle"), Some(&final_seq("call")));
    }
}

#[test]
fn free_seq_carrier_alias_planner_refuses_recursive_cycles() {
    let cycle = [
        eq(seq_var("left"), final_seq("right")),
        eq(seq_var("right"), final_seq("left")),
    ];

    assert!(plan_free_seq_carrier_aliases(&cycle).is_empty());
}

#[test]
fn free_seq_carrier_alias_planner_leaves_disequality_and_nonvar_equality_untouched() {
    let requirements = [
        ne(seq_var("v"), final_seq("call")),
        eq(final_seq("left"), final_seq("right")),
    ];

    assert!(plan_free_seq_carrier_aliases(&requirements).is_empty());
}

#[test]
fn free_seq_carrier_alias_planner_ignores_equalities_nested_under_connectives() {
    let alias = eq(seq_var("v"), final_seq("call"));
    let nested = [
        PureExpr::BinOp(
            std::sync::Arc::new(PureExpr::Bool(false)),
            BinOp::Or,
            std::sync::Arc::new(alias.clone()),
        ),
        implies(PureExpr::Bool(true), alias),
    ];

    assert!(plan_free_seq_carrier_aliases(&nested).is_empty());
}

#[test]
fn free_seq_alias_component_retains_additional_target_constraints() {
    let first_target = final_seq("first");
    let second_target = final_seq("second");
    let requirements = [
        eq(seq_var("v"), first_target.clone()),
        eq(seq_var("v"), second_target.clone()),
        ne(first_target, second_target),
    ];
    let mut encoder = AYEncoder::new_all();
    let seq_sort = ay_dpll::api::Sort::Seq(Box::new(ay_dpll::api::Sort::Int));
    for name in ["v", "first", "second"] {
        encoder
            .get_or_declare_var(name, seq_sort.clone())
            .expect("Seq carrier should declare");
    }

    install_free_seq_carrier_aliases(
        &mut encoder,
        &requirements,
        &[],
        &[],
        Some(std::slice::from_ref(&requirements[0])),
    )
    .expect("alias installation should encode");
    encode_and_assert_requires(&mut encoder, &requirements)
        .expect("all target constraints should encode");

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "choosing one defining target must retain equality to every additional target"
    );
}

#[test]
fn installed_free_seq_alias_has_one_solver_identity_and_no_distinct_bare_equality() {
    let alias = eq(seq_var("v"), final_seq("call"));
    let mut encoder = AYEncoder::new_all();
    let seq_sort = ay_dpll::api::Sort::Seq(Box::new(ay_dpll::api::Sort::Int));
    encoder
        .get_or_declare_var("v", seq_sort.clone())
        .expect("source Seq should declare");
    encoder
        .get_or_declare_var("call", seq_sort)
        .expect("target Seq should declare");

    install_free_seq_carrier_aliases(
        &mut encoder,
        std::slice::from_ref(&alias),
        &[],
        &[],
        Some(std::slice::from_ref(&alias)),
    )
    .expect("alias installation should encode");
    let installed_source = encoder.var_term("v").expect("source should install");
    let installed_target = encoder
        .encode_pure(&final_seq("call"))
        .expect("target final carrier should encode");
    assert_eq!(
        installed_source,
        installed_target,
        "alias must share the exact solver term immediately after installation; vars={:?}; SMT:\n{}",
        encoder.var_names(),
        encoder.solver().to_smtlib2()
    );
    encode_and_assert_requires(&mut encoder, std::slice::from_ref(&alias))
        .expect("aliased premise should encode");

    let source = encoder.var_term("v").expect("source should stay bound");
    let target = encoder
        .encode_pure(&final_seq("call"))
        .expect("target final carrier should remain encodable");
    assert_eq!(
        source,
        target,
        "alias must retain the exact solver term; vars={:?}; SMT:\n{}",
        encoder.var_names(),
        encoder.solver().to_smtlib2()
    );

    for assertion in encoder.solver().assertions() {
        let TermKind::App { name, num_args: 2 } = encoder.solver().term_kind(assertion) else {
            continue;
        };
        if name != "=" {
            continue;
        }
        let children = encoder.solver().term_children(assertion);
        if children.len() == 2
            && matches!(
                encoder.solver().get_sort(children[0]),
                ay_dpll::api::Sort::Seq(_)
            )
            && matches!(
                encoder.solver().get_sort(children[1]),
                ay_dpll::api::Sort::Seq(_)
            )
        {
            assert_eq!(
                children[0],
                children[1],
                "alias elimination must not leave a distinct bare Seq equality: {}",
                encoder.solver().format_term(assertion)
            );
        }
    }
}

#[test]
fn free_seq_alias_installation_requires_an_isolated_ghost_source() {
    let alias = eq(seq_var("v"), final_seq("call"));
    let source_use = eq(
        PureExpr::MethodCall {
            receiver: std::sync::Arc::new(seq_var("v")),
            method: "len".to_string(),
            args: vec![],
        },
        PureExpr::Int(0),
    );

    for (ghost_context, ensures) in [
        (None, Vec::new()),
        (Some(std::slice::from_ref(&alias)), vec![source_use.clone()]),
    ] {
        let mut encoder = AYEncoder::new_all();
        let seq_sort = ay_dpll::api::Sort::Seq(Box::new(ay_dpll::api::Sort::Int));
        encoder
            .get_or_declare_var("v", seq_sort.clone())
            .expect("source Seq should declare");
        encoder
            .get_or_declare_var("call", seq_sort)
            .expect("target Seq should declare");
        let original = encoder.var_term("v").expect("source should exist");

        install_free_seq_carrier_aliases(
            &mut encoder,
            std::slice::from_ref(&alias),
            &ensures,
            &[],
            ghost_context,
        )
        .expect("gated alias installation should not fail");

        assert_eq!(
            encoder.var_term("v"),
            Some(original),
            "non-ghost or observably used source must retain its own temporal identity"
        );
    }
}
