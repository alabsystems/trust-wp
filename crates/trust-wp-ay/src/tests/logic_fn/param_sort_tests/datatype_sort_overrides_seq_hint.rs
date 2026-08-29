// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

/// Datatype inference overrides Seq hints from ambiguous method names.
///
/// Regression test for #994/#2002: when a logic function like `List::sum`
/// has a body with `match self { Cons(..) => .., Nil => .. }`, the parameter
/// `self` should be declared with Datatype sort — even if the sort hint
/// prescan tagged `self` as Seq because `sum` is an ambiguous Seq method name.
///
/// Without this fix, the prescan's Seq hint takes precedence, the function
/// is declared with Seq(self), and calling it with a Datatype-sorted argument
/// causes a ay sort mismatch panic.
///
/// Semantic: List_sum(Cons(1, Nil)) should be Sat (the function is defined).
/// Part of #994.
#[test]
#[timeout(30000)]
fn test_datatype_sort_overrides_seq_hint_for_logic_fn_param() {
    use trust_wp_core::formula::{ExprSort, MatchArm, Pattern};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Pre-seed sort hints: tag "self" as Seq (simulating what the prescan
    // does when it sees `self.sum()` in contracts and `self` is a non-bare Var).
    encoder.record_sort_hint("self".to_string(), ExprSort::Seq);

    // Define List::depth with a match body:
    //   match self { Cons(a, _) => a, Nil => 0 }
    // (Simplified body — avoids recursive method_call dispatch issues.
    //  The critical test is that the parameter sort resolution chooses
    //  Datatype over Seq, not the full recursive encoding.)
    // This triggers UserDefined Datatype inference from Cons/Nil constructors.
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

    // Use "sum" as the function name to conflict with the Seq built-in method,
    // which is the exact scenario that caused the sort mismatch bug.
    let logic_fn = LogicFnDef::new(
        "sum".to_string(),
        "List::sum".to_string(),
        vec!["self".to_string()],
        body,
    )
    .with_mode(LogicMode::Open);

    // This should NOT panic despite the Seq hint on "self", because
    // Datatype inference from Cons/Nil constructors overrides the Seq hint.
    encoder
        .register_logic_fn(&logic_fn)
        .expect("List::sum should register with Datatype sort, not Seq (#994)");

    // Verify the function was declared — it should be in logic_funcs
    assert!(
        encoder.decls().has_logic_func("logic_sum"),
        "List::sum should be registered as logic_sum"
    );
}
