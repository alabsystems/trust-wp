// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for closure body inlining substitution (#2151 Phase 2).

use std::{collections::HashMap, sync::Arc};

use ntest::timeout;
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, BinOp, PureExpr,
};

use super::{
    substitution::{
        apply_substitution, conjoin_with_ensures, extract_receiver_name, substitute_closure_body,
        substitute_closure_body_mut, substitute_closure_ensures,
    },
    AYEncoder,
};
use crate::{
    encoder::{unsoundness, MAX_ENCODING_DEPTH},
    expr::expr_mentions_var,
};

#[test]
#[timeout(30000)]
fn test_apply_substitution_var() {
    let subst = HashMap::from([("x".to_string(), PureExpr::Int(42))]);
    let expr = PureExpr::Var("x".to_string(), None);
    let result = apply_substitution(&expr, &subst);
    assert_eq!(result, PureExpr::Int(42));
}

#[test]
#[timeout(30000)]
fn test_apply_substitution_no_match() {
    let subst = HashMap::from([("x".to_string(), PureExpr::Int(42))]);
    let expr = PureExpr::Var("y".to_string(), None);
    let result = apply_substitution(&expr, &subst);
    assert_eq!(result, PureExpr::Var("y".to_string(), None));
}

#[test]
#[timeout(30000)]
fn test_apply_substitution_binop() {
    let subst = HashMap::from([
        ("x".to_string(), PureExpr::Int(1)),
        ("y".to_string(), PureExpr::Int(2)),
    ]);
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Var("y".to_string(), None)),
    );
    let result = apply_substitution(&expr, &subst);
    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::Int(1)),
            BinOp::Add,
            Arc::new(PureExpr::Int(2))
        )
    );
}

#[test]
#[timeout(30000)]
fn test_apply_substitution_respects_shadowing() {
    let subst = HashMap::from([("x".to_string(), PureExpr::Int(42))]);
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Int(0)),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    let result = apply_substitution(&expr, &subst);
    // x should NOT be substituted in the body because the Let shadows it
    assert_eq!(
        result,
        PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::Int(0)),
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
        }
    );
}

#[test]
#[timeout(30000)]
fn test_substitute_closure_body_nullary() {
    // Closure: || 42
    // postcondition(env, result) → result == 42
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    );
    let result_var = PureExpr::Var("r".to_string(), None);
    let substituted = substitute_closure_body(&body, &[], &[], std::slice::from_ref(&result_var));
    assert_eq!(
        substituted,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("r".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(42)),
        )
    );
}

#[test]
#[timeout(30000)]
fn test_substitute_closure_body_with_param() {
    // Closure: |x| x + 1
    // postcondition(env, x_arg, result) → result == x_arg + 1
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    let x_arg = PureExpr::Int(5);
    let result_var = PureExpr::Var("r".to_string(), None);
    let substituted = substitute_closure_body(&body, &[], &["x".to_string()], &[x_arg, result_var]);
    assert_eq!(
        substituted,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("r".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(5)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        )
    );
}

#[test]
#[timeout(30000)]
fn test_apply_substitution_match_arm_shadows_pattern_binding() {
    // match scrutinee { Some(x) => x + 1, None => 0 }
    // with subst x → 99: the x inside Some(x) arm body should NOT be
    // substituted because the pattern binding shadows it.
    use trust_wp_core::formula::Pattern;

    let subst = HashMap::from([("x".to_string(), PureExpr::Int(99))]);
    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("s".to_string(), None)),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                },
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                ),
            },
            trust_wp_core::formula::MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                // x is NOT shadowed here — should be substituted
                body: PureExpr::Var("x".to_string(), None),
            },
        ],
    };
    let result = apply_substitution(&expr, &subst);
    match result {
        PureExpr::Match { arms, .. } => {
            // Some(x) arm: x should NOT be substituted (shadowed by pattern)
            assert_eq!(
                arms[0].body,
                PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                ),
                "pattern-bound x should not be substituted in Some arm"
            );
            // None arm: x SHOULD be substituted (not shadowed)
            assert_eq!(
                arms[1].body,
                PureExpr::Int(99),
                "free x should be substituted in None arm"
            );
        }
        other => panic!("expected Match, got {:?}", other),
    }
}

/// Closure substitution must alpha-rename quantified binders so the free
/// variables in substitution values do not get captured.
#[test]
#[timeout(30000)]
fn test_apply_substitution_forall_alpha_renames_to_avoid_capture() {
    // subst: y → Var("x")
    let subst = HashMap::from([("y".to_string(), PureExpr::Var("x".to_string(), None))]);
    // expr: forall x. (y > x)
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Var("x".to_string(), None)),
        )),
        triggers: vec![],
    };
    let result = apply_substitution(&expr, &subst);
    match result {
        PureExpr::Forall { var, body, .. } => {
            assert_ne!(var, "x", "forall binder should alpha-rename");
            match body.as_ref() {
                PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
                    assert_eq!(
                        lhs.as_ref(),
                        &PureExpr::Var("x".to_string(), None),
                        "lhs should be the free x introduced by substitution"
                    );
                    assert_eq!(
                        rhs.as_ref(),
                        &PureExpr::Var(var, None),
                        "rhs should reference the renamed bound variable"
                    );
                }
                other => panic!("expected BinOp(Gt), got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_extract_receiver_name() {
    assert_eq!(
        extract_receiver_name(&PureExpr::Var("c".to_string(), None)),
        Some("c")
    );
    assert_eq!(
        extract_receiver_name(&PureExpr::Deref(Arc::new(PureExpr::Var(
            "c".to_string(),
            None
        )))),
        Some("c")
    );
    assert_eq!(extract_receiver_name(&PureExpr::Int(42)), None);
}

#[test]
#[timeout(30000)]
fn test_substitute_closure_body_mut_with_param() {
    // Closure: |x| x + 1 (pure body, called via FnMut)
    // postcondition_mut(c, x_arg, ^c, result)
    // args = [x_arg, final_state, result]
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    let x_arg = PureExpr::Int(5);
    let final_state = PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None)));
    let result_var = PureExpr::Var("r".to_string(), None);
    let substituted = substitute_closure_body_mut(
        &body,
        &[],
        &["x".to_string()],
        &[x_arg, final_state, result_var],
    );
    // x → 5, result → r, final_state is ignored by body
    assert_eq!(
        substituted,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("r".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(5)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        )
    );
}

#[test]
#[timeout(30000)]
fn test_substitute_closure_body_mut_nullary() {
    // Closure: || 42 (called via FnMut)
    // postcondition_mut(c, ^c, result)
    // args = [final_state, result] (no formal params)
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    );
    let final_state = PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None)));
    let result_var = PureExpr::Var("r".to_string(), None);
    let substituted = substitute_closure_body_mut(&body, &[], &[], &[final_state, result_var]);
    // result → r
    assert_eq!(
        substituted,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("r".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(42)),
        )
    );
}

/// Test that `substitute_closure_body_mut` preserves `Final(Var(capture))` in the
/// body — this is the distinguishing feature of the `postcondition_mut` path.
///
/// Models a counter closure: `let mut count = 0; let c = |x| { count += x; result == Final(count) }`
/// The body references `Final(Var("count"))` to express the post-call state of the
/// captured variable. The substitution must NOT replace `count` (it's a capture, not
/// a formal param) and must preserve the `Final` wrapper so the encoder can resolve
/// it to the caller-side `_count_final` variable.
///
/// Without this test, `substitute_closure_body_mut` could be replaced by
/// `substitute_closure_body` and all existing tests would still pass (P1-90 finding).
///
/// Part of #2007
#[test]
#[timeout(30000)]
fn test_substitute_closure_body_mut_preserves_final_var_capture() {
    // Closure body: result == x + Final(count)
    // This represents a closure that adds x to count and returns the new total.
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "count".to_string(),
                None,
            )))),
        )),
    );

    // postcondition_mut(c, x_arg=3, ^c, result)
    // args = [3, Final(c), r]
    let x_arg = PureExpr::Int(3);
    let final_state = PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None)));
    let result_var = PureExpr::Var("r".to_string(), None);

    let substituted = substitute_closure_body_mut(
        &body,
        &["count".to_string()],
        &["x".to_string()],
        &[x_arg, final_state, result_var],
    );

    // x → 3, result → r, count remains as Var("count"), Final wrapper preserved
    assert_eq!(
        substituted,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("r".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(3)),
                BinOp::Add,
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    "count".to_string(),
                    None,
                )))),
            )),
        ),
        "Final(Var(\"count\")) must survive substitution for encoder-side resolution"
    );
}

/// Verify that `substitute_closure_body_mut` with 2 params correctly maps arguments
/// despite the extra `final_state` element in the args layout.
///
/// With 2+ params, the `final_state` at `args[param_count]` must be skipped so that
/// `result` maps to `args.last()` — not to `final_state`. This exercises the layout
/// difference between postcondition (params..., result) and postcondition_mut
/// (params..., final_state, result) with a body containing `Final(Var(capture))`.
///
/// Part of #2007
#[test]
#[timeout(30000)]
fn test_substitute_mut_two_params_with_final_body() {
    // Body: result == (x + y) + Final(count)
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
            BinOp::Add,
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "count".to_string(),
                None,
            )))),
        )),
    );

    let captures = &["count".to_string()];
    let params = &["x".to_string(), "y".to_string()];

    // Non-mut: postcondition(c, 3, 7, r) — args = [3, 7, r]
    let non_mut_args = vec![
        PureExpr::Int(3),
        PureExpr::Int(7),
        PureExpr::Var("r".to_string(), None),
    ];
    let result_non_mut = substitute_closure_body(&body, captures, params, &non_mut_args);

    // Mut: postcondition_mut(c, 3, 7, ^c, r) — args = [3, 7, Final(c), r]
    let mut_args = vec![
        PureExpr::Int(3),
        PureExpr::Int(7),
        PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
        PureExpr::Var("r".to_string(), None),
    ];
    let result_mut = substitute_closure_body_mut(&body, captures, params, &mut_args);

    // Both should produce: r == (3 + 7) + Final(count)
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("r".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(3)),
                BinOp::Add,
                Arc::new(PureExpr::Int(7)),
            )),
            BinOp::Add,
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "count".to_string(),
                None,
            )))),
        )),
    );

    assert_eq!(
        result_non_mut, expected,
        "non-mut substitution should produce r == (3 + 7) + Final(count)"
    );
    assert_eq!(
        result_mut, expected,
        "mut substitution should produce r == (3 + 7) + Final(count)"
    );
}

/// Documents the "result" param name collision in `substitute_closure_body`.
///
/// When a closure has a formal parameter named "result" (valid Rust identifier),
/// the parameter mapping `param_names[i] → args[i]` correctly maps it first.
/// Then the "result" → `args.last()` mapping OVERWRITES the parameter binding,
/// causing the formal parameter to be substituted with the result variable
/// instead of its actual argument.
///
/// Closure: `|result: i32| result + 1`
/// postcondition(env, arg_for_result, actual_result)
/// Expected: actual_result == arg_for_result + 1
/// Bug: actual_result == actual_result + 1  (result param overwritten by result var)
///
/// P1-95 algorithm_audit finding
#[test]
#[timeout(30000)]
fn test_substitute_closure_body_result_param_name_collision() {
    // Closure: |result: i32| result + 1
    // Body format: `result == (result + 1)` where:
    //   LHS "result" = return value keyword → should map to args.last()
    //   RHS "result" = formal param → should map to args[0]
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    // postcondition(env, 5, r)  — arg for "result" param is 5, actual result is r
    let param_arg = PureExpr::Int(5);
    let result_var = PureExpr::Var("r".to_string(), None);
    let substituted = substitute_closure_body(
        &body,
        &[],
        &["result".to_string()],
        &[param_arg, result_var],
    );

    // FIXED (#2193): two-phase substitution disambiguates:
    //   LHS "result" → Var("r") (return variable, args.last())
    //   RHS "result" → Int(5)   (param arg, args[0])
    // Result: r == (5 + 1)
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("r".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(5)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    assert_eq!(
        substituted, expected,
        "When 'result' is a formal param, LHS should map to return variable (r) \
         and RHS should map to param's actual arg (5)"
    );
}

/// Same collision fix for `substitute_closure_body_mut` (#2193).
///
/// P1-95 algorithm_audit finding, fixed by #2193.
#[test]
#[timeout(30000)]
fn test_substitute_closure_body_mut_result_param_name_collision() {
    // Body: `result == (result + 1)` — same collision as postcondition path
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    // postcondition_mut(env, 5, ^env, r) — param "result" → 5, result → r
    let param_arg = PureExpr::Int(5);
    let final_state = PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None)));
    let result_var = PureExpr::Var("r".to_string(), None);
    let substituted = substitute_closure_body_mut(
        &body,
        &[],
        &["result".to_string()],
        &[param_arg, final_state, result_var],
    );

    // FIXED (#2193): two-phase substitution. LHS → r, RHS → 5.
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("r".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(5)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    assert_eq!(
        substituted, expected,
        "When 'result' is a formal param in postcondition_mut, LHS should map \
         to return variable (r) and RHS should map to param's actual arg (5)"
    );
}

/// Phase 4: conjoin_with_ensures augments body substitution with side effects.
///
/// For unannotated FnMut closure `|| { x += 1; 5 }` called via postcondition_once:
/// - body substitution: `result == 5`
/// - ensures: `x == old(x) + 1`
/// - conjoined: `(result == 5) AND (x == old(x) + 1)`
#[test]
#[timeout(30000)]
fn test_conjoin_with_ensures_adds_side_effects() {
    // Body substitution: result == 5
    let body_sub = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );

    // Synthesized ensures: x == old(x) + 1
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )];

    let result = conjoin_with_ensures(&body_sub, &ensures);

    // Expected: (result == 5) AND (x == old(x) + 1)
    let expected = PureExpr::BinOp(
        Arc::new(body_sub.clone()),
        BinOp::And,
        Arc::new(ensures[0].clone()),
    );

    assert_eq!(
        result, expected,
        "conjoin_with_ensures should AND the body substitution with ensures"
    );
}

/// Phase 4: conjoin_with_ensures is identity when ensures is empty.
#[test]
#[timeout(30000)]
fn test_conjoin_with_ensures_empty_is_identity() {
    let body_sub = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    );

    let result = conjoin_with_ensures(&body_sub, &[]);

    assert_eq!(
        result, body_sub,
        "conjoin_with_ensures with empty ensures should return body unchanged"
    );
}

#[test]
#[timeout(30000)]
fn test_substitute_closure_ensures_threads_final_receiver_state() {
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )];

    let pre_state = PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None)));
    let post_state = PureExpr::Final(Arc::new(pre_state.clone()));
    let substituted =
        substitute_closure_ensures(&ensures, &["x".to_string()], &pre_state, &post_state);

    let expected = vec![PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![post_state.clone()],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![pre_state.clone()],
            }),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )];

    assert_eq!(
        substituted, expected,
        "sequential postcondition_once calls should project captures from the \
         concrete receiver states (^c and ^^c), not reuse the caller's base x binding"
    );
}

#[test]
#[timeout(30000)]
fn test_register_closure_body_preserves_missing_body_without_unsoundness() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    let mut encoder = AYEncoder::new_pure();
    let capture_info = crate::closure_capture_info! {
        def_id: "ensures_only_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("f".to_string()),
        body_expr: None,
        param_names: Some(vec!["x".to_string()]),
        ensures_exprs: Some(vec![PureExpr::Var("result".to_string(), None)]),
    };

    encoder.register_closure_body(&capture_info);

    let stored = encoder
        .closure_state
        .get_body("ensures_only_test::closure#0")
        .expect("closure body info should be stored");
    assert_eq!(stored.body, None);
    assert_eq!(
        unsoundness::delta(&before, &unsoundness::snapshot())
            .get(&unsoundness::UnsoundnessCategory::ClosureBodyTrueDefault),
        None
    );
    unsoundness::reset();
}

/// Raw body substitution: when body has no "result" variable, it represents
/// a raw return value (e.g., from `try_extract_closure_body_with_effects`).
/// The substitution must wrap it as `result_var == body` to produce a Bool.
///
/// Closure: `|x| x + 1` with raw body `x + 1` (no `result == ...` wrapper).
/// postcondition(env, 5, r) → should produce `r == (5 + 1)`.
///
/// P1-1193 proof_coverage finding: the `body_has_result == false` branch
/// (closure_inline.rs:259-274) had no direct test.
#[test]
#[timeout(30000)]
fn test_substitute_closure_body_raw_body_wraps_with_result_eq() {
    // Raw body: just the return expression, no "result" reference
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    let x_arg = PureExpr::Int(5);
    let result_var = PureExpr::Var("r".to_string(), None);
    let substituted = substitute_closure_body(&body, &[], &["x".to_string()], &[x_arg, result_var]);

    // Should wrap as: r == (5 + 1)
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("r".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(5)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );

    assert_eq!(
        substituted, expected,
        "raw body (no result var) should be wrapped as result_var == substituted_body"
    );
}

/// Raw body substitution for postcondition_mut: same wrapping as postcondition
/// but with the extra final_state argument in the layout.
///
/// P1-1193 proof_coverage finding.
#[test]
#[timeout(30000)]
fn test_substitute_closure_body_mut_raw_body_wraps_with_result_eq() {
    // Raw body: `x * 2`
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Mul,
        Arc::new(PureExpr::Int(2)),
    );

    // postcondition_mut(c, 7, ^c, r) → args = [7, Final(c), r]
    let x_arg = PureExpr::Int(7);
    let final_state = PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None)));
    let result_var = PureExpr::Var("r".to_string(), None);
    let substituted = substitute_closure_body_mut(
        &body,
        &[],
        &["x".to_string()],
        &[x_arg, final_state, result_var],
    );

    // Should wrap as: r == (7 * 2)
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("r".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(7)),
            BinOp::Mul,
            Arc::new(PureExpr::Int(2)),
        )),
    );

    assert_eq!(
        substituted, expected,
        "raw body in postcondition_mut should wrap as result_var == body, with x correctly mapped past final_state"
    );
}

/// `extract_receiver_name` strips `Final` wrappers in addition to `Deref`.
///
/// The driver produces `Final(Var("f"))` for closure receivers in postcondition
/// contexts. Without handling `Final`, `find_body_for_receiver` falls through
/// to the single-body shortcut instead of doing a direct param_name lookup.
///
/// P1-1193 proof_coverage finding.
#[test]
#[timeout(30000)]
fn test_extract_receiver_name_final_wrapper() {
    // Final(Var("f")) → "f"
    assert_eq!(
        extract_receiver_name(&PureExpr::Final(Arc::new(PureExpr::Var(
            "f".to_string(),
            None
        )))),
        Some("f")
    );

    // Final(Deref(Var("f"))) → "f"
    assert_eq!(
        extract_receiver_name(&PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Var("f".to_string(), None)
        ))))),
        Some("f")
    );

    // Deref(Final(Var("f"))) → "f"
    assert_eq!(
        extract_receiver_name(&PureExpr::Deref(Arc::new(PureExpr::Final(Arc::new(
            PureExpr::Var("f".to_string(), None)
        ))))),
        Some("f")
    );
}

/// `extract_receiver_name` returns None for non-variable expressions.
///
/// MethodCall, View, and other wrappers are not stripped — only Var, Deref,
/// Final, and Old. View is intentionally excluded (it changes semantics, not
/// identity).
///
/// P1-1193 proof_coverage finding. Updated for #2668 (Old handling added).
#[test]
#[timeout(30000)]
fn test_extract_receiver_name_unsupported_wrappers_return_none() {
    // View(Var("f")) → None (View not handled — it changes semantics)
    assert_eq!(
        extract_receiver_name(&PureExpr::View(Arc::new(PureExpr::Var(
            "f".to_string(),
            None
        )))),
        None
    );

    // Old(Var("f")) → Some("f") since #2668 (Old is identity for receiver lookup)
    assert_eq!(
        extract_receiver_name(&PureExpr::Old(Arc::new(PureExpr::Var(
            "f".to_string(),
            None
        )))),
        Some("f")
    );

    // MethodCall → None
    assert_eq!(
        extract_receiver_name(&PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
            method: "call".to_string(),
            args: vec![],
        }),
        None
    );
}

/// `expr_mentions_var` correctly respects quantifier binding shadows.
///
/// In `forall x. (x + y)`, "x" is bound (should not be found as free),
/// while "y" is free (should be found).
///
/// P1-1193 proof_coverage finding.
#[test]
#[timeout(30000)]
fn test_expr_mentions_var_respects_quantifier_shadow() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("y".to_string(), None)),
        )),
        triggers: vec![],
    };

    // "x" is bound by forall — should NOT be found
    assert!(
        !expr_mentions_var(&expr, "x"),
        "bound variable should not be found by expr_mentions_var"
    );

    // "y" is free — should be found
    assert!(
        expr_mentions_var(&expr, "y"),
        "free variable should be found by expr_mentions_var"
    );
}

/// `expr_mentions_var` handles Let binding: finds var in value but not
/// in shadowed body.
///
/// P1-1193 proof_coverage finding.
#[test]
#[timeout(30000)]
fn test_expr_mentions_var_let_value_vs_body() {
    // let x = y in x + z
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Var("y".to_string(), None)),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("z".to_string(), None)),
        )),
    };

    // "y" appears in the value (before binding) — should be found
    assert!(expr_mentions_var(&expr, "y"));

    // "x" is bound by let — should NOT be found in body
    assert!(!expr_mentions_var(&expr, "x"));

    // "z" is free in the body — should be found
    assert!(expr_mentions_var(&expr, "z"));
}

/// `expr_mentions_var` must fail closed (return true) once the tree is deeper
/// than `MAX_ENCODING_DEPTH`, so closure-body result detection stays bounded
/// while conservatively assuming the variable exists.
#[test]
#[timeout(30000)]
#[allow(clippy::cast_possible_wrap)] // test data: small usize values safely fit i64
fn test_expr_mentions_var_depth_limit_fails_closed() {
    let mut expr = PureExpr::Var("result".to_string(), None);
    for depth in 0..=(MAX_ENCODING_DEPTH + 8) {
        expr = PureExpr::Let {
            var: format!("tmp_{depth}"),
            value: Arc::new(PureExpr::Int(depth as i64)),
            body: Arc::new(expr),
        };
    }

    assert!(
        expr_mentions_var(&expr, "result"),
        "too-deep scans must return true (fail-closed) at depth limit"
    );
}

/// Below depth limit with no matching variable, `expr_mentions_var` returns false.
#[test]
#[timeout(30000)]
fn test_expr_mentions_var_depth_guard_normal_false() {
    let shallow = {
        let mut e = PureExpr::Int(0);
        for i in 0..10 {
            e = PureExpr::BinOp(Arc::new(e), BinOp::Add, Arc::new(PureExpr::Int(i)));
        }
        e
    };
    assert!(
        !expr_mentions_var(&shallow, "nonexistent"),
        "expr_mentions_var should return false for missing var below depth limit"
    );
}

/// At depth > MAX_ENCODING_DEPTH with NO matching variable, `expr_mentions_var`
/// must still return true (fail-closed).
#[test]
#[timeout(30000)]
#[allow(clippy::cast_possible_wrap)] // test data: small usize values safely fit i64
fn test_expr_mentions_var_depth_guard_fails_closed_no_var() {
    let mut expr = PureExpr::Int(0);
    for i in 0..=(MAX_ENCODING_DEPTH + 10) {
        expr = PureExpr::BinOp(
            Arc::new(expr),
            BinOp::Add,
            Arc::new(PureExpr::Int(i as i64)),
        );
    }
    assert!(
        expr_mentions_var(&expr, "nonexistent"),
        "expr_mentions_var must return true at depth limit even when var is absent (fail-closed)"
    );
}

/// `substitute_with_result_param_collision` fallback: when "result" is a
/// formal param but the body doesn't have the expected `result == ...` top-level
/// structure, the function falls back to applying param-only substitution to
/// the whole body. The "result" → return variable mapping is NOT applied.
///
/// This exercises the fallback at closure_inline.rs:318-321.
///
/// P1-1193 proof_coverage finding.
#[test]
#[timeout(30000)]
fn test_substitute_result_param_collision_non_eq_body_fallback() {
    // Body: result + 1 (NOT `result == ...` — just a raw expression using "result")
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    // postcondition(env, 5, r) — param "result" → 5, actual result → r
    let param_arg = PureExpr::Int(5);
    let result_var = PureExpr::Var("r".to_string(), None);
    let substituted = substitute_closure_body(
        &body,
        &[],
        &["result".to_string()],
        &[param_arg, result_var],
    );

    // Fallback: body doesn't have `result == ...` structure, so param-only
    // substitution applies to the whole body. "result" → Int(5).
    // The result keyword is NOT separately mapped (it would need a different
    // body structure). Result: 5 + 1.
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Int(5)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    assert_eq!(
        substituted, expected,
        "when body is not `result == ...`, result-param collision fallback should apply param-only substitution"
    );
}

/// Raw body with no params and no result: edge case where args is empty.
///
/// This exercises the `else` branch at closure_inline.rs:271 where
/// `args.last()` returns None, so the raw body is returned as-is.
///
/// P1-1193 proof_coverage finding.
#[test]
#[timeout(30000)]
fn test_substitute_closure_body_raw_body_no_args_returns_body() {
    // Raw body: Int(42), no params, no args
    let body = PureExpr::Int(42);
    let substituted = substitute_closure_body(&body, &[], &[], &[]);

    // With no args, can't construct `result == body`, returns body as-is
    assert_eq!(
        substituted,
        PureExpr::Int(42),
        "raw body with no args should return body unchanged"
    );
}

// ── Old wrapper handling for extract_receiver_name (#2668) ──────────

/// `extract_receiver_name` strips `Old` wrappers for receiver lookup.
///
/// Closure ensures clauses can reference `old(receiver)` for pre-state values.
/// When the receiver appears inside `Old()`, the param_name lookup must still
/// find the base variable name. Without this, `find_body_for_receiver` falls
/// through to shortcut paths unnecessarily.
///
/// Part of #2668.
#[test]
#[timeout(30000)]
fn test_extract_receiver_name_old_wrapper() {
    // Old(Var("c")) → "c"
    assert_eq!(
        extract_receiver_name(&PureExpr::Old(Arc::new(PureExpr::Var(
            "c".to_string(),
            None
        )))),
        Some("c"),
        "Old(Var) should extract the base variable name"
    );

    // Deref(Old(Var("f"))) → "f" (Box deref + old)
    assert_eq!(
        extract_receiver_name(&PureExpr::Deref(Arc::new(PureExpr::Old(Arc::new(
            PureExpr::Var("f".to_string(), None)
        ))))),
        Some("f"),
        "Deref(Old(Var)) should strip both layers"
    );

    // Old(Deref(Deref(Var("f")))) → "f" (old + Box<Box<F>>)
    assert_eq!(
        extract_receiver_name(&PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Deref(Arc::new(PureExpr::Var("f".to_string(), None)))
        ))))),
        Some("f"),
        "Old(Deref(Deref(Var))) should strip all wrapper layers"
    );

    // Final(Old(Deref(Var("c")))) → "c" (postcondition + old + Box)
    assert_eq!(
        extract_receiver_name(&PureExpr::Final(Arc::new(PureExpr::Old(Arc::new(
            PureExpr::Deref(Arc::new(PureExpr::Var("c".to_string(), None)))
        ))))),
        Some("c"),
        "Final(Old(Deref(Var))) should strip all wrapper layers"
    );
}

// ── Double-Box postcondition_once inlining (#2668) ──────────────────

/// Inline postcondition_once for a closure with synthesized ensures through
/// double-Box wrapping.
///
/// Pattern from `test_fnmut3box` in closures/07_mutable_capture.rs:
/// `call_fnonce(Box::new(Box::new(c)))` where c is an unannotated FnMut
/// closure with synthesized ensures from body effects (`x == old(x) + 1`).
///
/// The ay encoder normalizes Box deref layers so the receiver resolves to
/// the base variable "c", which matches the registered closure body.
///
/// Part of #2668 — verifies encoder-level handling is correct.
/// The remaining compat failures are in the driver MIR pipeline.
#[test]
#[timeout(30000)]
fn test_postcondition_once_inline_double_box_receiver() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register a closure body simulating `c = || { x += 1; 5 }`
    // with synthesized ensures from body effect analysis.
    let closure_info = trust_wp_core::closure::ClosureCaptureInfo::new(
        "test::closure#0".to_string(),
        vec![trust_wp_core::closure::CaptureField::new(
            "x",
            trust_wp_core::formula::ExprSort::Int,
            trust_wp_core::closure::CaptureKind::ByMutRef,
        )],
    )
    .with_param_name(Some("c".to_string()))
    .with_body_expr(Some(PureExpr::Int(5)))
    .with_param_names(Some(vec![]))
    .with_ensures_exprs(Some(vec![
        // Synthesized: x == old(x) + 1
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                    "x".to_string(),
                    None,
                )))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        ),
    ]));
    encoder.register_closure_body(&closure_info);

    // Simulate the double-Box-wrapped postcondition_once call:
    // (***c).postcondition_once((), result)
    // Three derefs: outer Box, inner Box, Fn::call (*self)
    let triple_deref_receiver = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(
        PureExpr::Deref(Arc::new(PureExpr::Var("c".to_string(), None))),
    ))));
    let result_var = PureExpr::Var("result".to_string(), None);
    let postcondition_once_call = PureExpr::MethodCall {
        receiver: Arc::new(triple_deref_receiver),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Int(0), result_var], // unit arg + result
    };

    // The inline path should successfully find the body through triple-deref
    // normalization and produce a ground term.
    let result = encoder.encode_pure(&postcondition_once_call);
    assert!(
        result.is_ok(),
        "triple-deref postcondition_once should inline: {result:?}"
    );

    // Verify NO UF symbol was declared — inlining should prevent UF fallback.
    assert!(
        !encoder.has_closure_postcondition_once_symbols(),
        "postcondition_once should be inlined (no UF symbol), not fall through to UF path"
    );
}

/// postcondition_once inline with Old-wrapped receiver falls through gracefully.
///
/// When the postcondition_once receiver is wrapped in Old() (e.g., from a
/// spec that references `old(f).postcondition_once(...)`), the inline path
/// should still match the registered closure body via `extract_receiver_name`.
///
/// Part of #2668.
#[test]
#[timeout(30000)]
fn test_postcondition_once_inline_old_wrapped_receiver() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register a simple closure body.
    let closure_info =
        trust_wp_core::closure::ClosureCaptureInfo::new("test::closure#0".to_string(), vec![])
            .with_param_name(Some("f".to_string()))
            .with_body_expr(Some(PureExpr::Int(42)))
            .with_param_names(Some(vec![]));
    encoder.register_closure_body(&closure_info);

    // Old-wrapped receiver: old(f).postcondition_once((), result)
    let old_receiver = PureExpr::Old(Arc::new(PureExpr::Var("f".to_string(), None)));
    let result_var = PureExpr::Var("r".to_string(), None);
    let call = PureExpr::MethodCall {
        receiver: Arc::new(old_receiver),
        method: "postcondition_once".to_string(),
        args: vec![PureExpr::Int(0), result_var],
    };

    // Should encode — either via inlining or UF fallback.
    let result = encoder.encode_pure(&call);
    assert!(
        result.is_ok(),
        "Old-wrapped postcondition_once should encode: {result:?}"
    );
}

/// `find_body_for_receiver` should treat `View` as an identity wrapper for
/// lookup, even though `extract_receiver_name` intentionally leaves it alone.
///
/// This keeps closure body inlining aligned with the driver-side receiver
/// identity helpers, which already strip `View` when matching registered
/// closure bodies to postcondition calls.
#[test]
#[timeout(30000)]
fn test_find_body_for_receiver_view_wrapped_lookup() {
    let mut encoder = AYEncoder::new_pure();
    let closure_info = crate::closure_capture_info! {
        def_id: "view_lookup_test::closure#0".to_string(),
        captures: vec![],
        param_name: Some("c_view".to_string()),
        body_expr: Some(PureExpr::Int(7)),
        param_names: Some(vec![]),
        ensures_exprs: None,
    };
    encoder.register_closure_body(&closure_info);

    let receiver = PureExpr::View(Arc::new(PureExpr::Var("c".to_string(), None)));
    assert_eq!(
        extract_receiver_name(&receiver),
        None,
        "View should remain excluded from the low-level extractor"
    );

    let body_info = encoder
        .find_body_for_receiver(&receiver)
        .expect("View-wrapped receiver should resolve to the registered body");
    assert_eq!(body_info.body, Some(PureExpr::Int(7)));

    let nested_receiver = PureExpr::Final(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
        "c".to_string(),
        None,
    )))));
    let nested_body_info = encoder
        .find_body_for_receiver(&nested_receiver)
        .expect("Final(View(...)) receiver should resolve to the registered body");
    assert_eq!(nested_body_info.body, Some(PureExpr::Int(7)));

    let final_view_lookup = crate::closure_capture_info! {
        def_id: "view_lookup_test::closure#1".to_string(),
        captures: vec![],
        param_name: Some("final_c_view".to_string()),
        body_expr: Some(PureExpr::Int(9)),
        param_names: Some(vec![]),
        ensures_exprs: None,
    };
    encoder.register_closure_body(&final_view_lookup);

    let final_view_receiver = PureExpr::Final(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
        "c".to_string(),
        None,
    )))));
    let final_view_body_info = encoder
        .find_body_for_receiver(&final_view_receiver)
        .expect("Final(View(...)) receiver should resolve via the derived lookup");
    assert_eq!(final_view_body_info.body, Some(PureExpr::Int(9)));
}

/// `find_body_for_receiver` should keep derived `_current` lookup working when
/// `View` is nested under `Deref`.
///
/// This covers the normalization path used by iterator adapter receivers that
/// carry both a borrow wrapper and a logical view wrapper.
#[test]
#[timeout(30000)]
fn test_find_body_for_receiver_view_nested_under_deref_lookup() {
    let mut encoder = AYEncoder::new_pure();
    let closure_info = crate::closure_capture_info! {
        def_id: "view_lookup_test::closure#2".to_string(),
        captures: vec![],
        param_name: Some("c_current".to_string()),
        body_expr: Some(PureExpr::Int(13)),
        param_names: Some(vec![]),
        ensures_exprs: None,
    };
    encoder.register_closure_body(&closure_info);

    let receiver = PureExpr::Deref(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
        "c".to_string(),
        None,
    )))));
    let body_info = encoder
        .find_body_for_receiver(&receiver)
        .expect("Deref(View(...)) receiver should resolve to the registered body");
    assert_eq!(body_info.body, Some(PureExpr::Int(13)));
}
