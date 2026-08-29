// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

/// Parameters forwarded into already-declared Datatype-domain logic functions
/// must reuse that declared domain instead of silently defaulting to Int.
/// (#2002)
#[test]
#[timeout(30000)]
fn test_cross_function_datatype_passthrough_reuses_declared_domain() {
    use trust_wp_core::{
        formula::{MatchArm, Pattern},
        logic::logic_fn_smt_name,
    };

    let mut encoder = AYEncoder::new_with_quantifiers();

    let sum_body = PureExpr::Match {
        scrutinee: Arc::new(var("self")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("a".to_string()),
                        Pattern::Binding("l".to_string()),
                    ]))),
                },
                body: var("a"),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Nil".to_string(),
                    inner: None,
                },
                body: int(0),
            },
        ],
    };

    let sum = LogicFnDef::new(
        "sum".to_string(),
        "List::sum".to_string(),
        vec!["self".to_string()],
        sum_body,
    )
    .with_mode(LogicMode::Open);

    let is_nonempty = LogicFnDef::new(
        "is_nonempty".to_string(),
        "List::is_nonempty".to_string(),
        vec!["self".to_string()],
        gt(logic_fn_call("sum", vec![var("self")]), int(0)),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fns(&[sum, is_nonempty])
        .expect("cross-function Datatype passthrough should register");

    let smt_name = logic_fn_smt_name("is_nonempty");
    let decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .unwrap_or_else(|| panic!("{smt_name} should be declared"));
    assert!(
        matches!(decl.domain().first(), Some(Sort::Datatype(_))),
        "forwarded Datatype param should reuse declared domain, got: {:?}",
        decl.domain()
    );
}
