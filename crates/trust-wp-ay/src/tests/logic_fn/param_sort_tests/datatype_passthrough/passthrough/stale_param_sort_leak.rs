// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

/// Preseeded declaration-side parameter domains must not leak through the
/// shared `var_sorts` table into later unrelated logic-function signatures.
/// (#2002)
#[test]
#[timeout(30000)]
fn test_cross_function_datatype_passthrough_does_not_leak_stale_param_sort() {
    use trust_wp_core::{
        formula::{MatchArm, Pattern},
        logic::logic_fn_smt_name,
    };

    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    let mut encoder = AYEncoder::new_with_quantifiers();

    let sum = LogicFnDef::new(
        "sum".to_string(),
        "List::sum".to_string(),
        vec!["self".to_string()],
        PureExpr::Match {
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
        },
    )
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&sum)
        .expect("List::sum should register");

    unsoundness::reset();
    let before = unsoundness::snapshot();

    let fallback = LogicFnDef::new(
        "fallback".to_string(),
        "crate::fallback".to_string(),
        vec!["self".to_string()],
        int(0),
    )
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&fallback)
        .expect("fallback should still register");

    let decl = encoder
        .decls()
        .get_logic_func(&logic_fn_smt_name("fallback"))
        .expect("fallback should be declared");
    assert_eq!(
        decl.domain().first(),
        Some(&Sort::Int),
        "stale Datatype param sorts from earlier logic functions must not leak \
         into later declarations"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
        Some(&1),
        "fallback registration should still take the explicit logic-fn Int \
         fallback path, got: {delta:?}"
    );
}
