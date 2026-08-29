// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

/// Datatype return sort hint propagation: when a logic function returns a
/// Datatype (via match-pattern inference), the declared return sort should be
/// recorded as a sort hint so that dependent functions calling it can resolve
/// the return sort through the `sort_hints` fallback. (#1943)
///
/// Without this fix, `declare_logic_fn_signature` only propagated Bool, Seq,
/// and FMap return sort hints. A dependent function whose body is a
/// `LogicFnCall` to a Datatype-returning function would infer `Sort::Int`
/// (the default), causing a sort mismatch between the declared return sort
/// and the caller's expectation.
#[test]
#[timeout(30000)]
fn test_datatype_return_sort_hint_propagates_to_dependent_function() {
    use trust_wp_core::{
        formula::{MatchArm, Pattern},
        logic::logic_fn_smt_name,
    };

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Define list_identity: match self { Cons(a, l) => Cons(a, l), Nil => Nil }
    // This function returns a Datatype (List) via match-pattern inference.
    let body = PureExpr::Match {
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
                // Return 0 for simplicity — the return sort is inferred from
                // the match scrutinee Datatype, but the body sort inference
                // alone won't know it's Datatype. The critical path is the
                // sort hint propagation after declaration.
                body: int(0),
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

    let list_identity = LogicFnDef::new(
        "list_identity".to_string(),
        "List::list_identity".to_string(),
        vec!["self".to_string()],
        body,
    )
    .with_mode(LogicMode::Open);

    // A dependent function that calls list_identity and forwards the result.
    // Its body is just `list_identity(self)` — a LogicFnCall that defaults
    // to Sort::Int in infer_expr_sort. The sort hint from list_identity's
    // declaration should override this default.
    let double_identity = LogicFnDef::new(
        "double_identity".to_string(),
        "List::double_identity".to_string(),
        vec!["self".to_string()],
        logic_fn_call("list_identity", vec![var("self")]),
    )
    .with_mode(LogicMode::Open);

    // Register both in order — list_identity first, then double_identity.
    encoder
        .register_logic_fns(&[list_identity, double_identity])
        .expect("Datatype-returning logic fns should register (#1943)");

    // Verify list_identity was declared with Datatype parameter.
    let li_smt = logic_fn_smt_name("list_identity");
    let li_decl = encoder
        .decls()
        .get_logic_func(&li_smt)
        .unwrap_or_else(|| panic!("{li_smt} should be declared"));
    assert!(
        matches!(li_decl.domain().first(), Some(Sort::Datatype(_))),
        "list_identity param should be Datatype, got: {:?}",
        li_decl.domain()
    );

    // Verify the sort hint was propagated for dependent resolution.
    // double_identity's parameter should also be Datatype (from cross-function
    // domain passthrough), confirming the sort hint cascade works for Datatype
    // return sorts.
    let di_smt = logic_fn_smt_name("double_identity");
    let di_decl = encoder
        .decls()
        .get_logic_func(&di_smt)
        .unwrap_or_else(|| panic!("{di_smt} should be declared"));
    assert!(
        matches!(di_decl.domain().first(), Some(Sort::Datatype(_))),
        "double_identity param should inherit Datatype sort from \
         list_identity's declared domain, got: {:?}",
        di_decl.domain()
    );
}
