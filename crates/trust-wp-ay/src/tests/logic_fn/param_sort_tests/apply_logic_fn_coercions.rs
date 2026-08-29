// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

mod datatype_seq_coercion;
mod int_seq_coercion;
mod sort_resolution;
mod uninterpreted_mismatch;

/// Test that calling a Datatype-parameterized logic function with a
/// Seq-sorted argument does not panic. (#2002)
///
/// When List::sum(self) is declared with Sort::Datatype parameter (from
/// match-pattern inference), but the call-site variable `l` was declared
/// as Seq (from View encoding or first-declaration-wins lock-in), the
/// apply_logic_fn coercion should produce a fresh constant instead of
/// crashing with a ay sort mismatch.
#[test]
#[timeout(30000)]
fn test_apply_logic_fn_coerces_seq_arg_to_datatype_param() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register the List datatype and sum function (same as above test)
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

    let logic_fn = LogicFnDef::new(
        "sum".to_string(),
        "List::sum".to_string(),
        vec!["self".to_string()],
        body,
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("register List::sum");

    // Now simulate a call-site where `l` is Seq-sorted (from View encoding).
    // Use the canonical native Seq sort that current inference produces.
    let seq_sort = Sort::seq(Sort::Int);
    let l_term = encoder
        .get_or_declare_var("l_view", seq_sort)
        .expect("declare l_view as Seq");

    // Calling apply_logic_fn with a Seq-sorted term should NOT panic —
    // the coercion should replace it with a fresh Datatype-sorted constant.
    let result = encoder.apply_logic_fn("sum", &[l_term], None, None);
    assert!(
        result.is_ok(),
        "apply_logic_fn should coerce Seq→Datatype without panic (#2002): {result:?}"
    );
}
