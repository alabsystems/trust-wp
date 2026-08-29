// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for the BINDER-SCOPED VIEW COLLAPSE.
//!
//! A match-arm pattern binder (`a` in `Node(tl, a, tr) => tl.sum() + a@ +
//! tr.sum()`) is a pure logical value scoped to the arm. Its view `a@` must
//! encode as the bound payload-projection term of THAT arm instantiation — not
//! as a single global `a_view` constant shared by every instantiation of the
//! same match body. The global constant asserted that the middle payload of
//! `self`, `^self`, `mtl`, `mtr`, ... are all EQUAL, an unsound assumption set
//! through which a false obligation could be discharged (rusthorn
//! inc_some_tree `take_some` decode; #1635 analog for match arms).

use std::sync::Arc;

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use ntest::timeout;
use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use super::super::AYEncoder;

fn tree_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "Tree".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Node".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "tree_node_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "tree_node_1".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "tree_node_2".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Leaf".to_string(),
                fields: vec![],
            },
        ],
    }
}

/// `match <scrutinee> { Node(tl, a, tr) => tl + a@ + tr, Leaf => 0 }`
fn sum_body_match(scrutinee: &str) -> PureExpr {
    let add = |lhs: PureExpr, rhs: PureExpr| {
        PureExpr::BinOp(
            Arc::new(lhs),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(rhs),
        )
    };
    PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var(scrutinee.to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Node".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("tl".to_string()),
                        Pattern::Binding("a".to_string()),
                        Pattern::Binding("tr".to_string()),
                    ]))),
                },
                body: add(
                    add(
                        PureExpr::Var("tl".to_string(), None),
                        PureExpr::View(Arc::new(PureExpr::Var("a".to_string(), None))),
                    ),
                    PureExpr::Var("tr".to_string(), None),
                ),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Int(0),
            },
        ],
    }
}

#[test]
#[timeout(30000)]
fn match_arm_binder_view_does_not_declare_global_view_constant() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let datatype = tree_datatype();
    encoder.ensure_datatype_declared(&datatype);
    let sort = Sort::Datatype(datatype);
    encoder
        .get_or_declare_var("x", sort.clone())
        .expect("declare x");

    let term = encoder
        .encode_pure(&sum_body_match("x"))
        .expect("encode match with binder view");

    assert!(
        encoder.var_term("a_view").is_none(),
        "binder view `a@` must collapse to the arm's payload projection, \
         not synthesize a global `a_view` constant"
    );
    let rendered = encoder.solver.format_term(term);
    assert!(
        rendered.contains("tree_node_1"),
        "binder view `a@` should encode as the middle field selector; got: {rendered}"
    );
}

#[test]
#[timeout(30000)]
fn match_arm_binder_view_is_distinct_per_instantiation() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let datatype = tree_datatype();
    encoder.ensure_datatype_declared(&datatype);
    let sort = Sort::Datatype(datatype);
    encoder
        .get_or_declare_var("x", sort.clone())
        .expect("declare x");
    encoder
        .get_or_declare_var("y", sort.clone())
        .expect("declare y");

    let term_x = encoder
        .encode_pure(&sum_body_match("x"))
        .expect("encode match over x");
    let term_y = encoder
        .encode_pure(&sum_body_match("y"))
        .expect("encode match over y");

    assert!(
        encoder.var_term("a_view").is_none(),
        "no shared global `a_view` across instantiations"
    );
    // The two instantiations must NOT share their middle element: the encoded
    // bodies differ because each reads the field of its own scrutinee.
    assert_ne!(
        term_x, term_y,
        "unfolds at distinct scrutinees must produce distinct middle terms"
    );
    let rendered_x = encoder.solver.format_term(term_x);
    let rendered_y = encoder.solver.format_term(term_y);
    let x_identity = crate::source_symbol::base_identity("x");
    let y_identity = crate::source_symbol::base_identity("y");
    assert!(
        rendered_x.contains(x_identity.as_ref()) && !rendered_x.contains(y_identity.as_ref()),
        "instantiation at x must only read x: {rendered_x}"
    );
    assert!(
        rendered_y.contains(y_identity.as_ref()) && !rendered_y.contains(x_identity.as_ref()),
        "instantiation at y must only read y: {rendered_y}"
    );
}
