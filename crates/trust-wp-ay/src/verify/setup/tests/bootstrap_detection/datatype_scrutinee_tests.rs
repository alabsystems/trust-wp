// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::PureExpr;
/// Regression test for #994/#2002: `collect_datatype_scrutinee_vars` should
/// detect match scrutinees that are `Var` or `Deref(Var)` with user-defined
/// constructor patterns, and collect the variable → DatatypeSort mapping.
#[test]
#[timeout(30000)]
fn collect_datatype_scrutinee_vars_finds_enum_match() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    // match self { Cons(a, l) => ..., Nil => ... }
    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("self".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("a".to_string()),
                        Pattern::Binding("l".to_string()),
                    ]))),
                },
                body: PureExpr::Int(1),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Nil".to_string(),
                    inner: None,
                },
                body: PureExpr::Int(0),
            },
        ],
    };

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_datatype_scrutinee_vars(&match_expr, &[], &mut dt_vars);

    assert!(
        dt_vars.contains_key("self"),
        "should find 'self' as datatype variable from match scrutinee"
    );
    let dt = &dt_vars["self"];
    assert_eq!(
        dt.constructors.len(),
        2,
        "should have Cons and Nil constructors"
    );
}

/// Regression test for #994/#2002: `Deref(Var("self"))` should map to
/// the variable name `self_current` (the RustHorn encoding convention).
#[test]
#[timeout(30000)]
fn collect_datatype_scrutinee_vars_deref_var_maps_to_current() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    // match *self { Node(..) => ..., Leaf => ... }
    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self".to_string(),
            None,
        )))),
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
                body: PureExpr::Int(1),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Leaf".to_string(),
                    inner: None,
                },
                body: PureExpr::Int(0),
            },
        ],
    };

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_datatype_scrutinee_vars(&match_expr, &[], &mut dt_vars);

    assert!(
        !dt_vars.contains_key("self"),
        "should NOT have 'self' — Deref(Var(self)) maps to self_current"
    );
    assert!(
        dt_vars.contains_key("self_current"),
        "should have 'self_current' from Deref(Var(self))"
    );
    let dt = &dt_vars["self_current"];
    assert_eq!(
        dt.constructors.len(),
        2,
        "should have Node and Leaf constructors"
    );
}

/// Negative test: Option/Result match patterns should NOT be collected
/// as user-defined datatypes.
#[test]
#[timeout(30000)]
fn collect_datatype_scrutinee_vars_skips_option_result() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("opt".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                body: PureExpr::Int(1),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: PureExpr::Int(0),
            },
        ],
    };

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_datatype_scrutinee_vars(&match_expr, &[], &mut dt_vars);

    assert!(
        dt_vars.is_empty(),
        "Option (Some/None) match should not produce user-defined datatype vars"
    );
}
