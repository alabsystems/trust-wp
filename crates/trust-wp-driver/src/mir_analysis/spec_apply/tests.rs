// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for spec_apply module — extracted from inline tests (#1669).

use std::sync::Arc;

use trust_wp_driver::StdSpec;

use super::*;
use crate::mir_analysis::effects::{CallEffects, DroppedClauseKind};

fn apply_postconditions(
    ensures: &[String],
    result_var: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    record_predicate_assumptions: bool,
) -> PureExpr {
    apply_postconditions_capture(
        ensures,
        result_var,
        translated_args,
        param_names,
        record_predicate_assumptions,
    )
    .0
}

fn apply_postconditions_capture(
    ensures: &[String],
    result_var: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    record_predicate_assumptions: bool,
) -> (PureExpr, CallEffects) {
    let mut effects = CallEffects::new();
    let result = apply_postconditions_with_effects(
        ensures,
        result_var,
        translated_args,
        param_names,
        &mut effects,
        record_predicate_assumptions,
    );
    (result, effects)
}

fn apply_postconditions_for_loop_body(
    ensures: &[String],
    result_var: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
) -> PureExpr {
    let mut effects = CallEffects::new();
    apply_postconditions_for_loop_body_with_effects(
        ensures,
        result_var,
        translated_args,
        param_names,
        &mut effects,
    )
}

fn apply_postconditions_with_self(
    ensures: &[String],
    result_var: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    explicit_self_expr: Option<&PureExpr>,
) -> PureExpr {
    apply_postconditions_with_self_capture(
        ensures,
        result_var,
        translated_args,
        param_names,
        explicit_self_expr,
    )
    .0
}

fn apply_postconditions_with_self_capture(
    ensures: &[String],
    result_var: &PureExpr,
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    explicit_self_expr: Option<&PureExpr>,
) -> (PureExpr, CallEffects) {
    let mut effects = CallEffects::new();
    let result = apply_postconditions_with_self_and_effects(
        ensures,
        result_var,
        translated_args,
        param_names,
        explicit_self_expr,
        &mut effects,
    );
    (result, effects)
}

fn apply_preconditions(
    requires: &[String],
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
) -> CallEffects {
    let mut effects = CallEffects::new();
    apply_preconditions_with_effects(requires, translated_args, param_names, &mut effects);
    effects
}

fn apply_preconditions_with_self(
    requires: &[String],
    translated_args: &[TranslatedArg],
    param_names: Option<&[String]>,
    explicit_self_expr: Option<&PureExpr>,
) -> CallEffects {
    let mut effects = CallEffects::new();
    apply_preconditions_with_self_and_effects(
        requires,
        translated_args,
        param_names,
        explicit_self_expr,
        &mut effects,
    );
    effects
}

// Tests for apply_postconditions (#67)
mod apply_postconditions_tests {
    use super::*;

    #[test]
    fn test_result_equals_expr() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == self + 1".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("arg0".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        assert!(matches!(
            &result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "arg0")
            && matches!(rhs.as_ref(), PureExpr::Int(1))
        ));
    }

    #[test]
    fn test_expr_equals_result() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["self + 1 == result".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("arg0".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        assert!(matches!(
            &result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "arg0")
            && matches!(rhs.as_ref(), PureExpr::Int(1))
        ));
    }

    #[test]
    fn test_with_value_arg() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == value".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("receiver".to_string(), None)),
            TranslatedArg::new(PureExpr::Int(42)),
        ];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        assert_eq!(result, PureExpr::Int(42));
    }

    #[test]
    fn test_single_arg_associated_fn_aliases_bind_to_arg0() {
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Int(7))];

        for clause in [
            "result == value",
            "result == default",
            "result == arg",
            "result == rhs",
        ] {
            let spec = StdSpec {
                requires: vec![],
                ensures: vec![clause.to_string()],
                param_names: None,
            };
            let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
            assert_eq!(result, PureExpr::Int(7), "alias in clause `{clause}`");
        }
    }

    #[test]
    fn test_method_aliases_prefer_non_self_slot_even_when_fallback() {
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("receiver".to_string(), None)),
            TranslatedArg::fallback(PureExpr::Var("arg1".to_string(), None)),
        ];

        for clause in [
            "result == value",
            "result == default",
            "result == arg",
            "result == rhs",
        ] {
            let spec = StdSpec {
                requires: vec![],
                ensures: vec![clause.to_string()],
                param_names: None,
            };
            let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
            assert_eq!(
                result,
                PureExpr::Var("arg1".to_string(), None),
                "alias in clause `{clause}`"
            );
        }
    }

    #[test]
    fn test_indexed_arg_aliases_bind_positionally() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == arg0 + arg1".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Int(5)),
            TranslatedArg::new(PureExpr::Int(9)),
        ];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        assert!(matches!(
            result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs) if matches!(lhs.as_ref(), PureExpr::Int(5)) && matches!(rhs.as_ref(), PureExpr::Int(9))
        ));
    }

    #[test]
    fn test_indexed_arg_aliases_keep_fallback_placeholders() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == arg1".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("receiver".to_string(), None)),
            TranslatedArg::fallback(PureExpr::Var("arg1".to_string(), None)),
        ];

        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        assert_eq!(result, PureExpr::Var("arg1".to_string(), None));
    }

    #[test]
    fn test_no_result_pattern_returns_unconstrained() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["x > 0".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("arg0".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        assert_eq!(result, PureExpr::Var("call_0".to_string(), None));
    }

    #[test]
    fn test_predicate_postconditions_not_recorded_with_false_flag() {
        // When record_predicate_assumptions is false, predicate-style
        // postconditions should NOT be recorded as assumptions (#1310).
        // This prevents the substitution-extraction pass (pass 1) from
        // double-pushing assumptions that the full extraction (pass 2)
        // will record with correctly advanced receiver state.
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["self.postcondition(arg, result)".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("f".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("x".to_string(), None)),
        ];
        let (result, effects) =
            apply_postconditions_capture(&spec.ensures, &result_var, &args, None, false);

        assert_eq!(result, PureExpr::Var("call_0".to_string(), None));
        assert!(
            effects.assumptions.is_empty(),
            "false flag should suppress assumption recording"
        );
    }

    #[test]
    fn test_predicate_postconditions_keep_indexed_fallback_aliases() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["self.contains(arg1)".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("set".to_string(), None)),
            TranslatedArg::fallback(PureExpr::Var("arg1".to_string(), None)),
        ];

        let (result, effects) =
            apply_postconditions_capture(&spec.ensures, &result_var, &args, None, true);
        assert_eq!(result, PureExpr::Var("call_0".to_string(), None));

        assert_eq!(effects.assumptions.len(), 1);
        assert!(matches!(
            effects.assumptions.first(),
            Some(PureExpr::MethodCall { receiver, method, args })
                if method == "contains"
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "set")
                    && matches!(args.first(), Some(PureExpr::Var(name, _)) if name == "arg1")
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_predicate_postcondition_mut_witness_binds_to_final_self() {
        fn contains_final_self(expr: &PureExpr, name: &str) -> bool {
            match expr {
                PureExpr::Final(inner) => {
                    matches!(inner.as_ref(), PureExpr::Var(var, _) if var == name)
                        || contains_final_self(inner, name)
                }
                PureExpr::BinOp(left, _, right) => {
                    contains_final_self(left, name) || contains_final_self(right, name)
                }
                PureExpr::UnOp(_, inner)
                | PureExpr::Old(inner)
                | PureExpr::Deref(inner)
                | PureExpr::View(inner) => contains_final_self(inner, name),
                PureExpr::Ite(cond, then_expr, else_expr) => {
                    contains_final_self(cond, name)
                        || contains_final_self(then_expr, name)
                        || contains_final_self(else_expr, name)
                }
                PureExpr::MethodCall { receiver, args, .. } => {
                    contains_final_self(receiver, name)
                        || args.iter().any(|arg| contains_final_self(arg, name))
                }
                PureExpr::Forall {
                    var,
                    body,
                    triggers,
                    ..
                }
                | PureExpr::Exists {
                    var,
                    body,
                    triggers,
                    ..
                } => {
                    if var == name {
                        return false;
                    }
                    contains_final_self(body, name)
                        || triggers
                            .iter()
                            .flat_map(|trig| trig.iter())
                            .any(|arg| contains_final_self(arg, name))
                }
                PureExpr::Match { scrutinee, arms } => {
                    contains_final_self(scrutinee, name)
                        || arms.iter().any(|arm| {
                            !arm.pattern.binds_name(name) && contains_final_self(&arm.body, name)
                        })
                }
                PureExpr::LogicFnCall { args, .. } => {
                    args.iter().any(|arg| contains_final_self(arg, name))
                }
                PureExpr::Let { var, value, body } => {
                    contains_final_self(value, name)
                        || (var != name && contains_final_self(body, name))
                }
                PureExpr::LetAssume { assumption, body } => {
                    contains_final_self(assumption, name) || contains_final_self(body, name)
                }
                PureExpr::LetObligation { obligation, body } => {
                    contains_final_self(obligation, name) || contains_final_self(body, name)
                }
                PureExpr::Closure { params, body } => {
                    !params.iter().any(|(p, _)| p == name) && contains_final_self(body, name)
                }
                PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(_, _) => false,
                // PureExpr is #[non_exhaustive]; required for cross-crate match.
                #[allow(unreachable_patterns)]
                _ => false,
            }
        }

        fn contains_var(expr: &PureExpr, needle: &str) -> bool {
            match expr {
                PureExpr::Var(name, _) => name == needle,
                PureExpr::BinOp(left, _, right) => {
                    contains_var(left, needle) || contains_var(right, needle)
                }
                PureExpr::UnOp(_, inner)
                | PureExpr::Old(inner)
                | PureExpr::Deref(inner)
                | PureExpr::Final(inner)
                | PureExpr::View(inner) => contains_var(inner, needle),
                PureExpr::Ite(cond, then_expr, else_expr) => {
                    contains_var(cond, needle)
                        || contains_var(then_expr, needle)
                        || contains_var(else_expr, needle)
                }
                PureExpr::MethodCall { receiver, args, .. } => {
                    contains_var(receiver, needle)
                        || args.iter().any(|arg| contains_var(arg, needle))
                }
                PureExpr::Forall {
                    var,
                    body,
                    triggers,
                    ..
                }
                | PureExpr::Exists {
                    var,
                    body,
                    triggers,
                    ..
                } => {
                    if var == needle {
                        return false;
                    }
                    contains_var(body, needle)
                        || triggers
                            .iter()
                            .flat_map(|trig| trig.iter())
                            .any(|arg| contains_var(arg, needle))
                }
                PureExpr::Match { scrutinee, arms } => {
                    contains_var(scrutinee, needle)
                        || arms.iter().any(|arm| {
                            !arm.pattern.binds_name(needle) && contains_var(&arm.body, needle)
                        })
                }
                PureExpr::LogicFnCall { args, .. } => {
                    args.iter().any(|arg| contains_var(arg, needle))
                }
                PureExpr::Let { var, value, body } => {
                    contains_var(value, needle) || (var != needle && contains_var(body, needle))
                }
                PureExpr::LetAssume { assumption, body } => {
                    contains_var(assumption, needle) || contains_var(body, needle)
                }
                PureExpr::LetObligation { obligation, body } => {
                    contains_var(obligation, needle) || contains_var(body, needle)
                }
                PureExpr::Closure { params, body } => {
                    !params.iter().any(|(p, _)| p == needle) && contains_var(body, needle)
                }
                PureExpr::Bool(_) | PureExpr::Int(_) => false,
                // PureExpr is #[non_exhaustive]; required for cross-crate match.
                #[allow(unreachable_patterns)]
                _ => false,
            }
        }

        let forall_shadowed = PureExpr::Forall {
            var: "st2".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Var("st2".to_string(), None)),
            triggers: vec![],
        };
        assert!(
            !contains_var(&forall_shadowed, "st2"),
            "forall binder should shadow st2"
        );

        let match_shadowed = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Int(0)),
            arms: vec![MatchArm {
                pattern: Pattern::Binding("st2".to_string()),
                body: PureExpr::Var("st2".to_string(), None),
            }],
        };
        assert!(
            !contains_var(&match_shadowed, "st2"),
            "match pattern binding should shadow st2"
        );

        let let_shadowed = PureExpr::Let {
            var: "st2".to_string(),
            value: Arc::new(PureExpr::Int(0)),
            body: Arc::new(PureExpr::Var("st2".to_string(), None)),
        };
        assert!(
            !contains_var(&let_shadowed, "st2"),
            "let binder should shadow st2 in body"
        );

        let closure_shadowed = PureExpr::Closure {
            params: vec![("st2".to_string(), None)],
            body: Arc::new(PureExpr::Var("st2".to_string(), None)),
        };
        assert!(
            !contains_var(&closure_shadowed, "st2"),
            "closure param should shadow st2 in body"
        );

        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["exists<st1, st2, r> f.postcondition_mut((), st1, r) && \
                 st1.postcondition_mut((), st2, result) && resolve(st2)"
                .to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple1".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        })];

        let (result, effects) =
            apply_postconditions_capture(&spec.ensures, &result_var, &args, None, true);
        assert_eq!(result, result_var);

        assert_eq!(effects.assumptions.len(), 1);
        assert!(
            contains_final_self(&effects.assumptions[0], "x"),
            "mutating predicate assumption should bind witness to Final(x): {:?}",
            effects.assumptions[0]
        );
        assert!(
            !contains_var(&effects.assumptions[0], "st2"),
            "state witness variable should be substituted out: {:?}",
            effects.assumptions[0]
        );
    }

    #[test]
    fn test_final_receiver_state_expr_nests_existing_final_non_tuple_receiver() {
        let expr = PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None)));
        let advanced = final_receiver_state_expr(&expr);

        assert_eq!(
            advanced,
            PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "f".to_string(),
                None,
            )))))
        );
    }

    #[test]
    fn test_empty_ensures_returns_unconstrained() {
        let spec = StdSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("arg0".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        assert_eq!(result, PureExpr::Var("call_0".to_string(), None));
    }

    #[test]
    fn test_unparseable_ensures_returns_unconstrained_and_fails_closed() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["invalid ((( syntax".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("arg0".to_string(), None))];
        let mut effects = CallEffects::new();
        let result = apply_postconditions_with_effects(
            &spec.ensures,
            &result_var,
            &args,
            None,
            &mut effects,
            true,
        );
        // Return value is unconstrained (no parseable postcondition)
        assert_eq!(result, PureExpr::Var("call_0".to_string(), None));
        // Fail-closed: synthetic false obligation ensures verification fails (#1671, #1739).
        // Single obligation: the merged parse pass (#1935) detects the parse failure once,
        // whereas the old two-pass design double-counted it.
        assert_eq!(effects.obligations.len(), 1);
        assert!(effects
            .obligations
            .iter()
            .all(|o| *o == PureExpr::Bool(false)));
        assert_eq!(effects.dropped_clauses.len(), 1);
        assert!(effects
            .dropped_clauses
            .iter()
            .all(|dc| dc.kind == DroppedClauseKind::Postcondition));
    }

    #[test]
    fn test_empty_args_returns_unconstrained() {
        // Edge case: no translated args available
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == self + 1".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args: Vec<TranslatedArg> = vec![]; // Empty args
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        // Missing args means we can't substitute `self`, so we avoid the postcondition.
        assert_eq!(result, PureExpr::Var("call_0".to_string(), None));
    }

    #[test]
    fn test_deref_pattern_supported() {
        // The parser supports deref (*self) patterns
        // Example: "result == (*self != None)" from Option::is_some
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == (*self != None)".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("opt".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        // Parser handles *self, substitutes to *opt, returns `(*opt != None)`
        // Note: `None` is parsed as Var("None") - enum variants need special handling
        assert!(matches!(
            &result,
            PureExpr::BinOp(lhs, BinOp::Ne, _)
            if matches!(lhs.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "opt"))
        ));
    }

    #[test]
    fn test_model_access_supported() {
        // Std specs use self@ for model access - parser now supports this (Part of #110)
        // Example: "result == self@.len()" from Vec::len
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == self@.len()".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("vec".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        // Parser can handle self@.len() and substitutes self → vec
        assert_eq!(
            result,
            PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "vec".to_string(),
                    None
                )))),
                method: "len".to_string(),
                args: vec![],
            }
        );
    }

    #[test]
    fn test_view_result_equality_extracts_rhs_in_loop_body() {
        // Vec::len actual spec: "result@ == self@.len()"
        // The `@` on result is the view operator. For primitives (usize),
        // view is identity, so result@ == x means result == x.
        // apply_postconditions_for_loop_body matches this pattern. (#1463)
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result@ == self@.len()".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("vec".to_string(), None))];
        let result = apply_postconditions_for_loop_body(&spec.ensures, &result_var, &args, None);
        // Should extract self@.len() with self → vec, NOT return unconstrained
        assert_eq!(
            result,
            PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "vec".to_string(),
                    None
                )))),
                method: "len".to_string(),
                args: vec![],
            }
        );
    }

    #[test]
    fn test_view_result_equality_extracted_by_normal_path() {
        // Normal apply_postconditions now extracts result@ == <expr> patterns.
        // Previously (#1463) these fell through to predicate-style handler,
        // leaving results unconstrained. Fixed by #1673.
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result@ == self@.len()".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("vec".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        // Normal path should now extract self@.len() with self → vec
        assert_eq!(
            result,
            PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "vec".to_string(),
                    None
                )))),
                method: "len".to_string(),
                args: vec![],
            }
        );
    }

    #[test]
    fn test_view_result_equality_symmetric_in_normal_path() {
        // Symmetric form: self@.len() == result@ — now extracted in normal path (#1673)
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["self@.len() == result@".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("vec".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        assert_eq!(
            result,
            PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "vec".to_string(),
                    None
                )))),
                method: "len".to_string(),
                args: vec![],
            }
        );
    }

    #[test]
    fn test_view_result_is_empty_extracted_by_normal_path() {
        // Vec::is_empty spec: result@ == (self@.len() == 0)
        // This should now be extracted in the normal path (#1673)
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result@ == (self@.len() == 0)".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("vec".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        // Should NOT return unconstrained call_0
        assert_ne!(result, PureExpr::Var("call_0".to_string(), None));
    }

    #[test]
    fn test_view_result_equality_symmetric_in_loop_body() {
        // Symmetric form: self@.len() == result@
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["self@.len() == result@".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("vec".to_string(), None))];
        let result = apply_postconditions_for_loop_body(&spec.ensures, &result_var, &args, None);
        assert_eq!(
            result,
            PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "vec".to_string(),
                    None
                )))),
                method: "len".to_string(),
                args: vec![],
            }
        );
    }

    #[test]
    fn test_view_result_extraction_preserves_view_for_non_primitive_return() {
        // BUG DOCUMENTATION: result@ == <expr> extraction assumes View is
        // identity, but for non-primitive types (HashMap::iter, HashSet::intersection)
        // View maps to a different logical type (e.g., iterator → FMap/FSet).
        //
        // HashSet::intersection spec: "result@ == self@.intersection(other@)"
        // Return type: Intersection<'_, T> (iterator), View → FSet<T>
        //
        // The extraction should preserve the view wrapper instead of
        // assigning the raw iterator variable the collection-model RHS.
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result@ == self@.intersection(other@)".to_string()],
            param_names: Some(vec!["self".to_string(), "other".to_string()]),
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("set_a".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("set_b".to_string(), None)),
        ];
        let result = apply_postconditions_for_loop_body(
            &spec.ensures,
            &result_var,
            &args,
            Some(spec.param_names.as_ref().unwrap()),
        );

        assert_eq!(
            result,
            PureExpr::View(Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "set_a".to_string(),
                    None,
                )))),
                method: "intersection".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                    "set_b".to_string(),
                    None,
                )))],
            })),
            "non-primitive result@ extraction should preserve the view wrapper"
        );
    }

    #[test]
    fn test_view_result_extraction_peels_transparent_adapter_before_view_wrap() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result@ == Copied(self@.intersection(other@))".to_string()],
            param_names: Some(vec!["self".to_string(), "other".to_string()]),
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("set_a".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("set_b".to_string(), None)),
        ];
        let result = apply_postconditions_for_loop_body(
            &spec.ensures,
            &result_var,
            &args,
            Some(spec.param_names.as_ref().unwrap()),
        );

        assert_eq!(
            result,
            PureExpr::View(Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "set_a".to_string(),
                    None,
                )))),
                method: "intersection".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                    "set_b".to_string(),
                    None,
                )))],
            })),
            "transparent adapters should keep the view witness around the inner iterator/view term"
        );
    }

    #[test]
    fn test_result_extraction_preserves_transparent_adapter_witness_in_plain_result_clause() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == Copied(self@.intersection(other@))".to_string()],
            param_names: Some(vec!["self".to_string(), "other".to_string()]),
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("set_a".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("set_b".to_string(), None)),
        ];
        let result = apply_postconditions(
            &spec.ensures,
            &result_var,
            &args,
            Some(spec.param_names.as_ref().unwrap()),
            true,
        );

        assert_eq!(
            result,
            PureExpr::View(Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "set_a".to_string(),
                    None,
                )))),
                method: "intersection".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                    "set_b".to_string(),
                    None,
                )))],
            })),
            "plain result clauses should preserve the transparent adapter witness around the inner iterator/view term"
        );
    }

    #[test]
    fn test_fallback_arg_used_as_self() {
        // Fallback args should still be usable as `self` so that
        // postconditions are not silently dropped for ZST receivers
        // like Ghost<T> and Snapshot<T>. (#1572)
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == self + 1".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::fallback(PureExpr::Var(
            "arg0".to_string(),
            None,
        ))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        // With fallback self accepted, the postcondition applies:
        // result == arg0 + 1
        assert!(matches!(
            &result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "arg0")
            && matches!(rhs.as_ref(), PureExpr::Int(1))
        ));
    }

    #[test]
    fn test_result_substitution_is_respected() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == result + 1".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("arg0".to_string(), None))];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        assert!(matches!(
            result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "call_0") && matches!(rhs.as_ref(), PureExpr::Int(1))
        ));
    }

    #[test]
    fn test_unresolved_symbolic_names_fallback() {
        // Regression test: If postcondition has unresolved known symbolic names
        // (self, value, default, result) after substitution, fall back (#87)
        let spec = StdSpec {
            requires: vec![],
            // "default" is a known symbolic name but we don't provide it in args
            ensures: vec!["result == default + 1".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        // No args provided, so "default" remains unresolved.
        let args: Vec<TranslatedArg> = vec![];
        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
        // Should fall back to unconstrained because "default" can't be resolved
        assert_eq!(result, PureExpr::Var("call_0".to_string(), None));
    }

    // User-defined function contract tests (Part of #152)
    // Tests for param_names argument used in user-defined spec substitution

    #[test]
    fn test_user_spec_named_param_substitution() {
        // User-defined function: fn add(x: i32, y: i32) -> i32
        // ensures: result == x + y
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == x + y".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Int(5)),
            TranslatedArg::new(PureExpr::Int(3)),
        ];
        let param_names = vec!["x".to_string(), "y".to_string()];
        let result =
            apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
        // Should substitute x -> 5, y -> 3, yielding 5 + 3
        assert!(matches!(
            result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs) if matches!(lhs.as_ref(), PureExpr::Int(5)) && matches!(rhs.as_ref(), PureExpr::Int(3))
        ));
    }

    #[test]
    fn test_user_spec_single_param() {
        // User-defined function: fn increment(n: i32) -> i32
        // ensures: result == n + 1
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == n + 1".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("input".to_string(), None))];
        let param_names = vec!["n".to_string()];
        let result =
            apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
        // Should substitute n -> input, yielding input + 1
        assert!(matches!(
            result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "input") && matches!(rhs.as_ref(), PureExpr::Int(1))
        ));
    }

    #[test]
    fn test_user_spec_fallback_arg_substituted() {
        // Fallback args still have meaningful expressions (e.g., PureExpr::Var("arg1", None))
        // that should be substituted for the parameter name in the postcondition.
        // This ensures user param names don't leak into the output (#169).
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == x + y".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Int(5)),
            TranslatedArg::fallback(PureExpr::Var("arg1".to_string(), None)),
        ];
        let param_names = vec!["x".to_string(), "y".to_string()];
        let result =
            apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
        // x gets substituted to 5, y gets substituted to fallback expr "arg1".
        // This avoids leaking user param name "y" into the output.
        assert!(matches!(
            result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::Int(5)) && matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == "arg1")
        ));
    }

    #[test]
    fn test_user_spec_empty_param_names() {
        // Edge case: param_names is Some but empty
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == 42".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Int(1))];
        let param_names: Vec<String> = vec![];
        let result =
            apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
        // No param names to substitute, but result == 42 should still work
        assert_eq!(result, PureExpr::Int(42));
    }

    #[test]
    fn test_user_spec_more_params_than_args() {
        // Edge case: param_names has more entries than actual args
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == x".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Int(7))];
        let param_names = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        let result =
            apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
        // Only x gets substituted (args[0]), y and z have no corresponding args
        assert_eq!(result, PureExpr::Int(7));
    }

    #[test]
    fn test_user_spec_missing_param_falls_back() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == y".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Int(7))];
        let param_names = vec!["x".to_string(), "y".to_string()];
        let result =
            apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
        assert_eq!(result, PureExpr::Var("call_0".to_string(), None));
    }

    #[test]
    fn test_user_spec_self_param_override() {
        // User-defined method: fn my_method(&self, x: i32) -> i32
        // where param_names = ["self", "x"]
        // The param_names should take precedence over std symbolic "self"
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == self + x".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Int(10)), // self
            TranslatedArg::new(PureExpr::Int(5)),  // x
        ];
        // Explicit param names: first arg is "self", second is "x"
        let param_names = vec!["self".to_string(), "x".to_string()];
        let result =
            apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
        // Both self (via param_names) and x should be substituted
        assert!(matches!(
            result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs) if matches!(lhs.as_ref(), PureExpr::Int(10)) && matches!(rhs.as_ref(), PureExpr::Int(5))
        ));
    }

    #[test]
    fn test_deref_mut_postcondition_substitutes_self_directly() {
        // After #2578 fix: deref_mut clauses bind self to the reference x
        // directly, NOT to Deref(x). This matches the deref (immutable) path
        // and ensures call-site assumptions and user postconditions use the
        // same term structure.
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["T::deref_mut.postcondition((self,), result)".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("x".to_string(), None))];

        let (result, effects) =
            apply_postconditions_capture(&spec.ensures, &result_var, &args, None, true);
        assert_eq!(result, result_var);

        assert_eq!(effects.assumptions.len(), 1);
        assert!(matches!(
            effects.assumptions[0],
            PureExpr::MethodCall {
                args: ref call_args,
                ..
            } if matches!(
                call_args.first(),
                Some(PureExpr::Var(name, _)) if name == "x"
            )
        ));
    }

    #[test]
    fn test_mixed_postconditions_only_rewrite_self_for_deref_mut_clause() {
        let ensures = vec![
            "result == self + 1".to_string(),
            "T::deref_mut.postcondition((self,), result)".to_string(),
        ];
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("x".to_string(), None))];

        let result = apply_postconditions(&ensures, &result_var, &args, None, true);
        assert!(matches!(
            result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "x") && matches!(rhs.as_ref(), PureExpr::Int(1))
        ));
    }

    #[test]
    fn test_closure_capture_projection_uses_explicit_self_expr() {
        let ensures = vec!["result == self.0 + arg".to_string()];
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Int(1))];
        let param_names = vec!["arg".to_string()];
        let closure_env = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple1".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        };

        let result = apply_postconditions_with_self(
            &ensures,
            &result_var,
            &args,
            Some(&param_names),
            Some(&closure_env),
        );

        assert!(matches!(
            result,
            PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "x") && matches!(rhs.as_ref(), PureExpr::Int(1))
        ));
    }

    #[test]
    fn test_closure_capture_projection_supports_nested_fields() {
        let ensures = vec!["result == self.0.1".to_string()];
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args: Vec<TranslatedArg> = vec![];
        let nested_env = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple1".to_string(),
            args: vec![PureExpr::LogicFnCall {
                name: "__trust_wp_tuple2".to_string(),
                args: vec![PureExpr::Int(10), PureExpr::Int(20)],
            }],
        };

        let result =
            apply_postconditions_with_self(&ensures, &result_var, &args, None, Some(&nested_env));

        assert_eq!(result, PureExpr::Int(20));
    }
}

// Regression test: trait method postcondition with named params (#470)
// Before fix, trait_specs paths passed None for param_names, so named
// parameters like 'x' and 'y' in trait postconditions were not substituted.
// The postcondition was applied but with raw parameter names (Var("x"), Var("y"))
// instead of actual argument values.
#[test]
fn test_trait_spec_named_param_substitution_regression_470() {
    // Simulates: trait Adder { #[ensures(result == x + y)] fn add(&self, x: i32, y: i32) -> i32; }
    // Called at generic site: a.add(1, 2)
    let spec = StdSpec {
        requires: vec![],
        ensures: vec!["result == x + y".to_string()],
        param_names: None,
    };
    let result_var = PureExpr::Var("call_0".to_string(), None);
    let args = vec![
        TranslatedArg::new(PureExpr::Var("a".to_string(), None)), // &self
        TranslatedArg::new(PureExpr::Int(1)),                     // x
        TranslatedArg::new(PureExpr::Int(2)),                     // y
    ];
    // With param_names (the fix): x and y are substituted to actual args
    let param_names = vec!["self".to_string(), "x".to_string(), "y".to_string()];
    let result_with_names =
        apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
    assert!(matches!(
        result_with_names,
        PureExpr::BinOp(lhs, BinOp::Add, rhs) if matches!(lhs.as_ref(), PureExpr::Int(1)) && matches!(rhs.as_ref(), PureExpr::Int(2))
    ));

    // Without param_names (the bug): x and y are not known symbolic names,
    // so the postcondition is applied but with raw Var("x") and Var("y")
    // instead of the actual argument values — producing an incorrect result.
    let result_without_names = apply_postconditions(&spec.ensures, &result_var, &args, None, true);
    assert!(
        matches!(
            &result_without_names,
            PureExpr::BinOp(lhs, BinOp::Add, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(x, _) if x == "x")
            && matches!(rhs.as_ref(), PureExpr::Var(y, _) if y == "y")
        ),
        "Without param_names, x and y leak as raw Var names: {result_without_names:?}"
    );
}

// Tests for `result@` / `*result` / `^result` postcondition patterns (#1126)
//
// Specs like `result@ == *self` (RC_AS_REF) and `*result == value` (RC_NEW)
// have a wrapped result variable (View/Deref/Final) on the LHS, which does NOT
// match the `result == <expr>` shortcut pattern. Instead, they fall through to
// the predicate-style handler and are recorded as assumptions. This is correct
// behavior: the view/deref of the result is constrained, not the result itself.
mod wrapped_result_postcondition_tests {
    use super::*;

    #[test]
    fn test_view_result_extracted_in_normal_path() {
        // RC_AS_REF: `result@ == *self`
        // Since #1673, result@ patterns are extracted in the normal path.
        // The RHS (*self → Deref(rc)) is returned as the constrained result.
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result@ == *self".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("rc".to_string(), None))];
        let (result, effects) =
            apply_postconditions_capture(&spec.ensures, &result_var, &args, None, true);

        // Result should be Deref(rc) — directly constrained (#1673)
        assert_eq!(
            result,
            PureExpr::Deref(Arc::new(PureExpr::Var("rc".to_string(), None)))
        );

        // The extracted `result@ == *self` clause is ALSO recorded as an
        // assumption to provide the solver with a ground binding for
        // the result variable, enabling quantifier instantiation. (#1581)
        assert_eq!(
            effects.assumptions.len(),
            1,
            "result@ == *self should produce 1 call assumption (ground binding for solver)"
        );
    }

    #[test]
    fn test_deref_result_falls_through_to_predicate_style() {
        // RC_NEW: `*result == value`
        // Deref(Var("result")) != Var("result"), so falls through.
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["*result == value".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("receiver".to_string(), None)),
            TranslatedArg::new(PureExpr::Int(42)),
        ];
        let (result, effects) =
            apply_postconditions_capture(&spec.ensures, &result_var, &args, None, true);

        assert_eq!(result, PureExpr::Var("call_0".to_string(), None));

        assert_eq!(
            effects.assumptions.len(),
            1,
            "*result == value should produce exactly 1 call assumption"
        );
        // The assumption should be Deref(result_var) == Int(42)
        assert!(
            matches!(
                &effects.assumptions[0],
                PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                if matches!(lhs.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "call_0"))
                && matches!(rhs.as_ref(), PureExpr::Int(42))
            ),
            "assumption should be Deref(call_0) == 42, got: {:?}",
            effects.assumptions[0]
        );
    }

    #[test]
    fn test_view_result_with_arithmetic_rhs() {
        // ADD_DURATION: `result@ == self@ + rhs@`
        // Since #1673, result@ is directly extracted.
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result@ == self@ + rhs@".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("instant".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("duration".to_string(), None)),
        ];
        let (result, effects) =
            apply_postconditions_capture(&spec.ensures, &result_var, &args, None, true);

        // Result should be View(instant) + View(duration) (#1673)
        assert_eq!(
            result,
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "instant".to_string(),
                    None
                )))),
                BinOp::Add,
                Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "duration".to_string(),
                    None
                )))),
            )
        );

        // The extracted `result@ == self@ + rhs@` clause is ALSO recorded
        // as an assumption for ground binding. (#1581)
        assert_eq!(
            effects.assumptions.len(),
            1,
            "result@ == self@ + rhs@ should produce 1 call assumption (ground binding for solver)"
        );
    }

    #[test]
    fn test_multiple_ensures_with_view_result() {
        // ADD_DURATION has 3 ensures clauses.
        // Since #1673, the first clause (result@ == self@ + rhs@) is directly
        // extracted. The remaining 2 clauses are recorded as assumptions
        // so the solver has the full postcondition context.
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "result@ == self@ + rhs@".to_string(),
                "rhs@ == 0 ==> result@ == self@".to_string(),
                "rhs@ > 0 ==> result@ > self@".to_string(),
            ],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("instant".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("duration".to_string(), None)),
        ];
        let (result, effects) =
            apply_postconditions_capture(&spec.ensures, &result_var, &args, None, true);

        // First clause extracts directly: View(instant) + View(duration) (#1673)
        assert_eq!(
            result,
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "instant".to_string(),
                    None
                )))),
                BinOp::Add,
                Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "duration".to_string(),
                    None
                )))),
            )
        );

        // All 3 clauses should be recorded as assumptions: the
        // extracted clause plus the remaining 2. (#1581)
        assert_eq!(
            effects.assumptions.len(),
            3,
            "all 3 ensures clauses should be pushed as call assumptions (including extracted)"
        );
    }

    #[test]
    fn test_multi_ensures_mutation_clause_not_dropped() {
        // mem::replace pattern: first clause constrains result, second
        // constrains mutation. Before this fix, the second clause was
        // silently dropped by the early return. (#1673 follow-up)
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "result == old(*dest)".to_string(),
                "(^dest) == src".to_string(),
            ],
            param_names: Some(vec!["dest".to_string(), "src".to_string()]),
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("ptr".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("new_val".to_string(), None)),
        ];
        let result = apply_postconditions(
            &spec.ensures,
            &result_var,
            &args,
            Some(spec.param_names.as_ref().unwrap()),
            true,
        );

        // First clause extracts: old(*dest) with dest → ptr
        assert_ne!(
            result,
            PureExpr::Var("call_0".to_string(), None),
            "result should be constrained, not unconstrained call_0"
        );

        // Both clauses should be recorded as assumptions: the extracted
        // clause (result == old(*dest)) plus the mutation clause (^dest == src). (#1581)
        let (_, effects) = apply_postconditions_capture(
            &spec.ensures,
            &result_var,
            &args,
            Some(spec.param_names.as_ref().unwrap()),
            true,
        );
        assert_eq!(
            effects.assumptions.len(),
            2,
            "both clauses (extracted + mutation) must be preserved as call assumptions"
        );
    }

    /// Verify that a non-fallback LogicFnCall("None") self argument resolves
    /// correctly in postconditions that reference `*self`. This exercises the
    /// fix for #1264 where nullary ADT variants (None, etc.) now translate to
    /// LogicFnCall expressions instead of being dropped.
    #[test]
    fn test_nullary_variant_self_resolves_in_postcondition() {
        // Simulate ok_or spec: `ensures: match *self { Some(v) => result == Ok(v), None => result == Err(err) }`
        // Simplified to test self resolution: `ensures: result == self`
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == self".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);

        // Before fix: translated_args[0] would be fallback Var("arg0")
        // because Option::None (nullary ADT) couldn't be translated.
        // After fix: translated_args[0] is LogicFnCall { name: "None", args: [] }.
        let none_expr = PureExpr::LogicFnCall {
            name: "None".to_string(),
            args: vec![],
        };
        let args = vec![
            TranslatedArg::new(none_expr.clone()),
            TranslatedArg::new(PureExpr::Bool(true)),
        ];

        let result = apply_postconditions_with_self(&spec.ensures, &result_var, &args, None, None);

        // Self should resolve to the None expression, so result == None
        assert_eq!(
            result, none_expr,
            "self should resolve to LogicFnCall(None) for nullary variant"
        );
    }

    #[test]
    fn test_match_postcondition_extracts_none_branch_result_expr() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "match *self { Some(v) => result == Ok(v), None => result == Err(err), }"
                    .to_string(),
            ],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let param_names = vec!["self".to_string(), "err".to_string()];
        let args = vec![
            TranslatedArg::new(PureExpr::LogicFnCall {
                name: "None".to_string(),
                args: vec![],
            }),
            TranslatedArg::new(PureExpr::Bool(true)),
        ];

        let result = apply_postconditions_with_self(
            &spec.ensures,
            &result_var,
            &args,
            Some(&param_names),
            None,
        );
        assert_eq!(
            result,
            PureExpr::LogicFnCall {
                name: "Err".to_string(),
                args: vec![PureExpr::Bool(true)],
            }
        );
    }

    #[test]
    fn test_match_postcondition_extracts_some_branch_result_expr() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "match *self { Some(v) => result == Ok(v), None => result == Err(err), }"
                    .to_string(),
            ],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let param_names = vec!["self".to_string(), "err".to_string()];
        let args = vec![
            TranslatedArg::new(PureExpr::LogicFnCall {
                name: "Some".to_string(),
                args: vec![PureExpr::Int(1)],
            }),
            TranslatedArg::new(PureExpr::Bool(false)),
        ];

        let result = apply_postconditions_with_self(
            &spec.ensures,
            &result_var,
            &args,
            Some(&param_names),
            None,
        );
        assert_eq!(
            result,
            PureExpr::LogicFnCall {
                name: "Ok".to_string(),
                args: vec![PureExpr::Int(1)],
            }
        );
    }

    #[test]
    fn test_match_postcondition_alias_pattern_binds_whole_value() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "match *self { whole @ Some(v) => result == Ok(whole), None => result == Err(err), }"
                    .to_string(),
            ],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let param_names = vec!["self".to_string(), "err".to_string()];
        let some_expr = PureExpr::LogicFnCall {
            name: "Some".to_string(),
            args: vec![PureExpr::Int(1)],
        };
        let args = vec![
            TranslatedArg::new(some_expr.clone()),
            TranslatedArg::new(PureExpr::Bool(false)),
        ];

        let result = apply_postconditions_with_self(
            &spec.ensures,
            &result_var,
            &args,
            Some(&param_names),
            None,
        );
        assert_eq!(
            result,
            PureExpr::LogicFnCall {
                name: "Ok".to_string(),
                args: vec![some_expr],
            }
        );
    }

    /// Regression test for #2366: ITE postconditions with `result == <expr>` in
    /// And-conjunct branches extract correctly, and Deref(Var(...)) patterns in
    /// the condition are stripped after substitution.
    ///
    /// Models the `take_max` postcondition:
    ///   `if *ma >= *mb { *mb == ^mb && result == ma } else { *ma == ^ma && result == mb }`
    /// where `ma → a`, `mb → b` (value-typed call-site locals).
    #[test]
    fn test_ite_and_conjunct_result_extraction_with_deref_stripping() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "if *ma >= *mb { *mb == ^mb && result == ma } else { *ma == ^ma && result == mb }"
                    .to_string(),
            ],
            param_names: Some(vec!["ma".to_string(), "mb".to_string()]),
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("a".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("b".to_string(), None)),
        ];
        let result = apply_postconditions_with_self(
            &spec.ensures,
            &result_var,
            &args,
            spec.param_names.as_deref(),
            None,
        );

        // The extracted result should be an ITE over the condition:
        //   Ite(a >= b, Var("a"), Var("b"))
        // NOT Ite(Deref(Var("a")) >= Deref(Var("b")), ...) — the Deref
        // must be stripped because a/b are value-typed locals, not references.
        match &result {
            PureExpr::Ite(cond, then_rhs, else_rhs) => {
                // Condition should be `a >= b` (no Deref wrappers)
                assert_eq!(
                    **cond,
                    PureExpr::BinOp(
                        Arc::new(PureExpr::Var("a".to_string(), None)),
                        BinOp::Ge,
                        Arc::new(PureExpr::Var("b".to_string(), None)),
                    ),
                    "condition should have Deref stripped: {cond:?}"
                );
                // Then branch: result == ma → Var("a")
                assert_eq!(
                    **then_rhs,
                    PureExpr::Var("a".to_string(), None),
                    "then branch should be Var(\"a\"): {then_rhs:?}"
                );
                // Else branch: result == mb → Var("b")
                assert_eq!(
                    **else_rhs,
                    PureExpr::Var("b".to_string(), None),
                    "else branch should be Var(\"b\"): {else_rhs:?}"
                );
            }
            _ => panic!("expected ITE result, got: {result:?}"),
        }
    }

    /// Regression test for ref-typed closure captures: `Deref(Var(..))`
    /// should not be stripped when the inner variable already carries a
    /// reference sort. That deref is the only thing distinguishing the
    /// pointee current value from the carrier variable.
    #[test]
    fn test_ite_result_extraction_preserves_deref_for_ref_typed_var() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == if *b { Some(false) } else { None }".to_string()],
            param_names: Some(vec!["b".to_string()]),
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var(
            "b".to_string(),
            Some(trust_wp_core::formula::ExprSort::Ref(Box::new(
                trust_wp_core::formula::ExprSort::Bool,
            ))),
        ))];
        let result = apply_postconditions_with_self(
            &spec.ensures,
            &result_var,
            &args,
            spec.param_names.as_deref(),
            None,
        );

        match &result {
            PureExpr::Ite(cond, then_rhs, else_rhs) => {
                assert!(
                    matches!(
                        cond.as_ref(),
                        PureExpr::Deref(inner)
                            if matches!(
                                inner.as_ref(),
                                PureExpr::Var(name, Some(trust_wp_core::formula::ExprSort::Ref(inner_sort)))
                                    if name == "b"
                                        && matches!(inner_sort.as_ref(), trust_wp_core::formula::ExprSort::Bool)
                            )
                    ),
                    "ref-typed guard should preserve Deref(Var(b: &bool)), got: {cond:?}"
                );
                assert_eq!(
                    **then_rhs,
                    PureExpr::LogicFnCall {
                        name: "Some".to_string(),
                        args: vec![PureExpr::Bool(false)],
                    }
                );
                assert_eq!(
                    **else_rhs,
                    PureExpr::LogicFnCall {
                        name: "None".to_string(),
                        args: vec![],
                    }
                );
            }
            other => panic!("expected ITE result, got: {other:?}"),
        }
    }
}

// Tests for match-style postcondition warning (#1477)
mod match_postcondition_warning_tests {
    use super::*;

    #[test]
    fn test_match_postcondition_warns_when_no_arm_pattern_matches_scrutinee() {
        // When the scrutinee value (an Int) doesn't match any constructor
        // pattern (Some/None), all arms fail pattern matching and the
        // postcondition is silently dropped. After #1477, this emits a
        // warning. The function falls back to unconstrained result.
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "match *self { Some(v) => result == v, None => result == 0, }".to_string(),
            ],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            // Scrutinee is a plain Int — won't match Some(...) or None pattern
            TranslatedArg::new(PureExpr::Int(42)),
        ];

        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, false);
        // With no arm matching, the function returns the unconstrained result
        assert_eq!(
            result,
            PureExpr::Var("call_0".to_string(), None),
            "Match postcondition should fall back to unconstrained result \
             when no arm pattern matches the scrutinee (#1477)"
        );
    }

    /// Test warning path 1: arm pattern matches but body doesn't produce
    /// `result == <expr>`. When the match arm body is a predicate (e.g.,
    /// `result > v`) rather than an equality, the postcondition should
    /// fall back to the unconstrained result and fire the "no arm produced
    /// result == <expr> extraction" warning. (#1477, #904)
    #[test]
    fn test_match_postcondition_warns_when_arm_matches_but_body_not_equality() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "match *self { Some(v) => result > v, None => result >= 0, }".to_string(),
            ],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            // Arg is Some(5) — the Some(v) pattern will match, binding v = 5,
            // but `result > v` is not `result == <expr>` so extraction fails.
            TranslatedArg::new(PureExpr::LogicFnCall {
                name: "Some".to_string(),
                args: vec![PureExpr::Int(5)],
            }),
        ];

        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, false);
        // Arm matched structurally but body is predicate-style, not equality —
        // result should be unconstrained (warning path 1).
        assert_eq!(
            result,
            PureExpr::Var("call_0".to_string(), None),
            "Match postcondition should fall back to unconstrained result \
             when arm matches but body is not result == <expr> (#1477)"
        );
    }
}

// Tests for match-style postcondition variable scrutinee fallback
mod match_postcondition_variable_scrutinee_tests {
    use super::*;

    /// When the scrutinee is a variable and all arms produce `result == <expr>`,
    /// the fallback should build a Match expression with simplified arm bodies.
    ///
    /// Models `Option::ok_or`:
    ///   `match *self { Some(v) => result == Ok(v), None => result == Err(err) }`
    /// where self is `Var("opt")` — a variable, not a known constructor.
    #[test]
    fn test_match_variable_scrutinee_extracts_result_match() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "match *self { Some(v) => result == Ok(v), None => result == Err(err), }"
                    .to_string(),
            ],
            param_names: Some(vec!["self".to_string(), "err".to_string()]),
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let param_names = vec!["self".to_string(), "err".to_string()];
        let args = vec![
            // self is a variable (not a known constructor)
            TranslatedArg::new(PureExpr::Var("opt".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("my_err".to_string(), None)),
        ];

        let result = apply_postconditions_with_self(
            &spec.ensures,
            &result_var,
            &args,
            Some(&param_names),
            None,
        );

        // Should produce a Match expression representing what result equals:
        //   match opt { Some(v) => Ok(v), None => Err(my_err) }
        match &result {
            PureExpr::Match { scrutinee, arms } => {
                assert_eq!(
                    **scrutinee,
                    PureExpr::Var("opt".to_string(), None),
                    "scrutinee should be the substituted self variable"
                );
                assert_eq!(arms.len(), 2, "should have 2 arms (Some + None)");

                // Arm 0: Some(v) => Ok(v)
                assert!(
                    matches!(&arms[0].pattern, Pattern::Constructor { name, .. } if name == "Some"),
                    "first arm should be Some pattern: {:?}",
                    arms[0].pattern
                );
                assert_eq!(
                    arms[0].body,
                    PureExpr::LogicFnCall {
                        name: "Ok".to_string(),
                        args: vec![PureExpr::Var("v".to_string(), None)],
                    },
                    "first arm body should be Ok(v)"
                );

                // Arm 1: None => Err(my_err)
                assert!(
                    matches!(&arms[1].pattern, Pattern::Constructor { name, .. } if name == "None"),
                    "second arm should be None pattern: {:?}",
                    arms[1].pattern
                );
                assert_eq!(
                    arms[1].body,
                    PureExpr::LogicFnCall {
                        name: "Err".to_string(),
                        args: vec![PureExpr::Var("my_err".to_string(), None)],
                    },
                    "second arm body should be Err(my_err)"
                );
            }
            _ => panic!("expected Match result, got: {result:?}"),
        }
    }

    /// When the scrutinee is a variable but NOT all arms produce `result == <expr>`,
    /// the fallback should return None (fail-closed), leaving result unconstrained.
    #[test]
    fn test_match_variable_scrutinee_fails_closed_when_arm_body_not_equality() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "match *self { Some(v) => result > v, None => result == 0, }".to_string(),
            ],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Var("opt".to_string(), None))];

        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, false);
        // First arm body is `result > v` (not equality), so fallback should fail.
        assert_eq!(
            result,
            PureExpr::Var("call_0".to_string(), None),
            "should fall back to unconstrained result when not all arms have result == <expr>"
        );
    }

    /// Test the unwrap_or pattern: `match *self { Some(v) => result == v, None => result == default }`
    /// with a variable scrutinee.
    #[test]
    fn test_match_variable_scrutinee_unwrap_or_pattern() {
        let spec = StdSpec {
            requires: vec![],
            ensures: vec![
                "match *self { Some(v) => result == v, None => result == default, }".to_string(),
            ],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Var("opt".to_string(), None)),
            TranslatedArg::new(PureExpr::Int(42)),
        ];

        let result = apply_postconditions(&spec.ensures, &result_var, &args, None, false);

        match &result {
            PureExpr::Match { scrutinee, arms } => {
                assert_eq!(
                    **scrutinee,
                    PureExpr::Var("opt".to_string(), None),
                    "scrutinee should be the variable"
                );
                assert_eq!(arms.len(), 2);
                // Some(v) => v (pattern-bound, stays as Var)
                assert_eq!(
                    arms[0].body,
                    PureExpr::Var("v".to_string(), None),
                    "Some arm body should be Var(v)"
                );
                // None => 42 (substituted from default)
                assert_eq!(
                    arms[1].body,
                    PureExpr::Int(42),
                    "None arm body should be the default value"
                );
            }
            _ => panic!("expected Match result, got: {result:?}"),
        }
    }
}

// Tests for apply_preconditions (#478)
mod apply_preconditions_tests {
    use super::*;

    #[test]
    fn test_precondition_generates_obligation() {
        let requires = vec!["self > 0".to_string()];
        let args = vec![TranslatedArg::new(PureExpr::Var("x".to_string(), None))];

        let effects = apply_preconditions(&requires, &args, None);

        let obligations = effects.obligations;
        assert_eq!(obligations.len(), 1);
        // self -> x, so "self > 0" becomes "x > 0"
        assert!(matches!(
            &obligations[0],
            PureExpr::BinOp(lhs, BinOp::Gt, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "x") && matches!(rhs.as_ref(), PureExpr::Int(0))
        ));
    }

    #[test]
    fn test_empty_requires_generates_no_obligations() {
        let requires: Vec<String> = vec![];
        let args = vec![TranslatedArg::new(PureExpr::Var("x".to_string(), None))];

        let effects = apply_preconditions(&requires, &args, None);

        assert!(effects.obligations.is_empty());
    }

    #[test]
    fn test_precondition_with_named_params() {
        let requires = vec!["n > 0".to_string()];
        let args = vec![
            TranslatedArg::new(PureExpr::Var("self_arg".to_string(), None)),
            TranslatedArg::new(PureExpr::Int(42)),
        ];
        let param_names = vec!["self".to_string(), "n".to_string()];

        let effects = apply_preconditions(&requires, &args, Some(&param_names));

        let obligations = effects.obligations;
        assert_eq!(obligations.len(), 1);
        // n -> 42, so "n > 0" becomes "42 > 0"
        assert!(matches!(
            &obligations[0],
            PureExpr::BinOp(lhs, BinOp::Gt, rhs) if matches!(lhs.as_ref(), PureExpr::Int(42)) && matches!(rhs.as_ref(), PureExpr::Int(0))
        ));
    }

    #[test]
    fn test_multiple_preconditions() {
        let requires = vec!["self > 0".to_string(), "value < 100".to_string()];
        let args = vec![
            TranslatedArg::new(PureExpr::Var("a".to_string(), None)),
            TranslatedArg::new(PureExpr::Var("b".to_string(), None)),
        ];

        let effects = apply_preconditions(&requires, &args, None);

        assert_eq!(effects.obligations.len(), 2);
    }

    #[test]
    fn test_precondition_unresolved_names_generates_false_obligation() {
        // "default > 0" uses "default" which is a known symbolic name.
        // With no args available, "default" stays unresolved.
        // Fail-closed: unresolved preconditions generate false obligations (#1739).
        let requires = vec!["default > 0".to_string()];
        let args: Vec<TranslatedArg> = vec![];

        let effects = apply_preconditions(&requires, &args, None);

        let obligations = effects.obligations;
        // Fail-closed: unresolved precondition becomes `false` obligation
        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0], PureExpr::Bool(false));
    }

    #[test]
    fn test_precondition_single_arg_associated_fn_aliases_bind_to_arg0() {
        let requires = vec!["rhs > 0".to_string()];
        let args = vec![TranslatedArg::new(PureExpr::Int(3))];

        let effects = apply_preconditions(&requires, &args, None);

        let obligations = effects.obligations;
        assert_eq!(obligations.len(), 1);
        assert!(matches!(
            &obligations[0],
            PureExpr::BinOp(lhs, BinOp::Gt, rhs) if matches!(lhs.as_ref(), PureExpr::Int(3)) && matches!(rhs.as_ref(), PureExpr::Int(0))
        ));
    }

    #[test]
    fn test_deref_mut_precondition_substitutes_self_directly() {
        // After #2578: deref_mut binds self to the reference directly
        let requires = vec!["T::deref_mut.precondition((self,))".to_string()];
        let args = vec![TranslatedArg::new(PureExpr::Var("x".to_string(), None))];
        let param_names = vec!["self".to_string()];

        let effects = apply_preconditions(&requires, &args, Some(&param_names));

        let obligations = effects.obligations;
        assert_eq!(obligations.len(), 1);
        assert!(matches!(
            &obligations[0],
            PureExpr::MethodCall {
                args: ref call_args,
                ..
            } if matches!(
                call_args.first(),
                Some(PureExpr::Var(name, _)) if name == "x"
            )
        ));
    }

    #[test]
    fn test_mixed_preconditions_rewrite_self_per_clause() {
        // After #2578: all clauses bind self to x directly
        let requires = vec![
            "self > 0".to_string(),
            "T::deref_mut.precondition((self,))".to_string(),
        ];
        let args = vec![TranslatedArg::new(PureExpr::Var("x".to_string(), None))];

        let effects = apply_preconditions(&requires, &args, None);

        let obligations = effects.obligations;
        assert_eq!(obligations.len(), 2);
        assert!(matches!(
            &obligations[0],
            PureExpr::BinOp(lhs, BinOp::Gt, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "x") && matches!(rhs.as_ref(), PureExpr::Int(0))
        ));
        assert!(matches!(
            obligations[1],
            PureExpr::MethodCall {
                args: ref call_args,
                ..
            } if matches!(
                call_args.first(),
                Some(PureExpr::Var(name, _)) if name == "x"
            )
        ));
    }

    #[test]
    fn test_deref_precondition_keeps_self_raw() {
        let requires = vec!["T::deref.precondition((self,))".to_string()];
        let args = vec![TranslatedArg::new(PureExpr::Var("x".to_string(), None))];
        let param_names = vec!["self".to_string()];

        let effects = apply_preconditions(&requires, &args, Some(&param_names));

        let obligations = effects.obligations;
        assert_eq!(obligations.len(), 1);
        assert!(matches!(
            &obligations[0],
            PureExpr::MethodCall {
                args: ref call_args,
                ..
            } if matches!(
                call_args.first(),
                Some(PureExpr::Var(ref name, _)) if name == "x"
            )
        ));
    }

    #[test]
    fn test_collect_precondition_obligations_deref_mut_substitutes_self_directly() {
        // After #2578: deref_mut binds self to x directly
        let requires = vec!["T::deref_mut.precondition((self,))".to_string()];
        let args = vec![TranslatedArg::new(PureExpr::Var("x".to_string(), None))];
        let param_names = vec!["self".to_string()];
        let mut effects = CallEffects::new();

        collect_precondition_obligations(&requires, &args, Some(&param_names), &mut effects);

        assert_eq!(effects.obligations.len(), 1);
        assert!(matches!(
            &effects.obligations[0],
            PureExpr::MethodCall {
                args: ref call_args,
                ..
            } if matches!(
                call_args.first(),
                Some(PureExpr::Var(name, _)) if name == "x"
            )
        ));
    }

    #[test]
    fn test_apply_preconditions_with_self_projects_closure_capture() {
        let requires = vec!["self.0 > 0".to_string()];
        let args: Vec<TranslatedArg> = vec![];
        let closure_env = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple1".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        };

        let effects = apply_preconditions_with_self(&requires, &args, None, Some(&closure_env));

        let obligations = effects.obligations;
        assert_eq!(obligations.len(), 1);
        assert!(matches!(
            &obligations[0],
            PureExpr::BinOp(lhs, BinOp::Gt, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "x") && matches!(rhs.as_ref(), PureExpr::Int(0))
        ));
    }

    #[test]
    fn test_unparseable_requires_generates_false_obligation() {
        // Fail-closed: a parse error in a requires clause must generate a
        // `false` obligation so the calling function fails verification,
        // rather than silently dropping the precondition check. (#1671, #1739)
        let requires = vec!["invalid ((( syntax".to_string()];
        let args = vec![TranslatedArg::new(PureExpr::Var("x".to_string(), None))];
        let mut effects = CallEffects::new();

        collect_precondition_obligations(&requires, &args, None, &mut effects);

        assert_eq!(effects.obligations.len(), 1);
        assert_eq!(effects.obligations[0], PureExpr::Bool(false));
        assert_eq!(effects.dropped_clauses.len(), 1);
        assert_eq!(
            effects.dropped_clauses[0].kind,
            DroppedClauseKind::Precondition
        );
    }
}

// Algorithm audit tests: boundary conditions, off-by-one, correctness
// Filed by Prover during algorithm_audit phase.
mod algorithm_audit_tests {
    use trust_wp_core::formula::{MatchArm, Pattern};

    use super::*;

    // Fixed: param_names containing "result" no longer overrides the return
    // value binding. "result" is a reserved name that always maps to result_var.
    #[test]
    fn test_param_named_result_does_not_override_return_value_binding() {
        // fn foo(result: i32) -> i32  with  ensures: result == result + 1
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == result + 1".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![TranslatedArg::new(PureExpr::Int(99))];
        // param_names[0] = "result" — skipped because "result" is reserved
        let param_names = vec!["result".to_string()];
        let result =
            apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
        // "result" in the postcondition RHS resolves to call_0 (the return value),
        // so `result + 1` becomes `call_0 + 1`.
        assert!(
            matches!(
                &result,
                PureExpr::BinOp(lhs, BinOp::Add, rhs)
                if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "call_0")
                && matches!(rhs.as_ref(), PureExpr::Int(1))
            ),
            "reserved 'result' should map to return value call_0: got {result:?}"
        );
    }

    // Verified correct: param_names[0] named "value" maps to args[0],
    // overriding the positional alias "value" (which targets args[1]).
    // This is CORRECT for user specs: param_names are only provided for
    // user-defined functions where the user's actual parameter name should
    // take priority. Std specs pass param_names=None. (Self-audit #483)
    #[test]
    fn test_param_named_value_at_position_zero_overrides_positional_alias() {
        // fn push(value: i32, target: &mut Vec<i32>)
        // ensures: result == value  (user means args[0])
        let spec = StdSpec {
            requires: vec![],
            ensures: vec!["result == value".to_string()],
            param_names: None,
        };
        let result_var = PureExpr::Var("call_0".to_string(), None);
        let args = vec![
            TranslatedArg::new(PureExpr::Int(10)), // param "value" at position 0
            TranslatedArg::new(PureExpr::Int(20)), // some other arg at position 1
        ];
        let param_names = vec!["value".to_string(), "target".to_string()];
        let result =
            apply_postconditions(&spec.ensures, &result_var, &args, Some(&param_names), true);
        // param_names correctly maps "value" to args[0] = Int(10).
        // The positional alias also set "value" to args[1] = Int(20), but
        // param_names override is correct here (user's parameter IS "value").
        assert_eq!(result, PureExpr::Int(10));
    }

    // Regression: pattern-bound names in match arms are not free variables.
    #[test]
    fn test_collect_vars_expr_match_arm_pattern_bindings_removed() {
        // match x { Some(value) => value + 1, None => 0 }
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("value".to_string()))),
                    },
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Var("value".to_string(), None)),
                        BinOp::Add,
                        Arc::new(PureExpr::Int(1)),
                    ),
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
        let vars = expr.free_vars();
        assert!(
            !vars.contains("value"),
            "pattern-bound 'value' must not be treated as a free variable"
        );
        // "x" should always be collected (it's the scrutinee, genuinely free)
        assert!(vars.contains("x"));
    }

    // Regression test: unresolved_symbolic_names with match arm pattern
    // binding that collides with a symbolic name.
    #[test]
    fn test_unresolved_symbolic_names_match_pattern_collision() {
        // match *self { Some(value) => value, None => 0 }
        // "value" is pattern-bound and should not appear in unresolved names,
        // even though it matches a known symbolic alias.
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "self".to_string(),
                None,
            )))),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("value".to_string()))),
                    },
                    body: PureExpr::Var("value".to_string(), None),
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
        // Only self is in substitutions
        let mut substitutions = HashMap::new();
        substitutions.insert("self".to_string(), PureExpr::Var("arg0".to_string(), None));
        let unresolved = unresolved_symbolic_names(&expr, &substitutions, None);
        assert!(
            !unresolved.contains("value"),
            "pattern-bound 'value' must not be flagged as unresolved symbolic name"
        );
    }

    // Regression: a free variable in one arm must remain free even if a later
    // arm pattern binds the same identifier.
    #[test]
    fn test_collect_vars_expr_match_arm_binding_keeps_other_arm_free_var() {
        // match x { None => value, Some(value) => value }
        // In the None arm, `value` is an outer free variable.
        // In the Some arm, `value` is pattern-bound.
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Var("value".to_string(), None),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("value".to_string()))),
                    },
                    body: PureExpr::Var("value".to_string(), None),
                },
            ],
        };

        let vars = expr.free_vars();
        assert!(
            vars.contains("value"),
            "free var from one arm must not be removed by another arm's pattern binding"
        );
        assert!(vars.contains("x"));
    }
}

mod symbolic_name_tests {
    use super::*;

    #[test]
    fn test_unresolved_symbolic_names_filters_known_symbols() {
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("self".to_string(), None)),
        );
        let empty_subs = HashMap::new();
        let names = unresolved_symbolic_names(&expr, &empty_subs, None);
        assert!(names.contains("self"));
        assert!(!names.contains("x"));
    }

    #[test]
    fn test_collect_vars_expr_includes_wrapped_symbols() {
        let expr = PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Final(
            Arc::new(PureExpr::Var("value".to_string(), None)),
        )))));
        let vars = expr.free_vars();
        assert!(vars.contains("value"));
    }

    #[test]
    fn test_unresolved_symbolic_names_handles_nested_ite() {
        let expr = PureExpr::Ite(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            Arc::new(PureExpr::Var("default".to_string(), None)),
            Arc::new(PureExpr::Var("ignored".to_string(), None)),
        );
        let empty_subs = HashMap::new();
        let names = unresolved_symbolic_names(&expr, &empty_subs, None);
        assert!(names.contains("result"));
        assert!(names.contains("default"));
        assert!(!names.contains("ignored"));
    }

    #[test]
    fn test_unresolved_symbolic_names_handles_named_parameters() {
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("y".to_string(), None)),
        );
        let mut substitutions = HashMap::new();
        substitutions.insert("x".to_string(), PureExpr::Int(5));
        let param_names = vec!["x".to_string(), "y".to_string()];
        let names = unresolved_symbolic_names(&expr, &substitutions, Some(&param_names));
        assert!(!names.contains("x"));
        assert!(names.contains("y"));
    }

    #[test]
    fn test_unresolved_symbolic_names_quantifier_trigger_shadowing() {
        // x + forall x. #[trigger(f(x, y))] true
        // The sibling free x should be filtered out by substitution, the bound
        // trigger x must not leak back into unresolved names, and y should stay.
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Forall {
                var: "x".to_string(),
                var_sort: None,
                body: Arc::new(PureExpr::Bool(true)),
                triggers: vec![vec![PureExpr::LogicFnCall {
                    name: "f".to_string(),
                    args: vec![
                        PureExpr::Var("x".to_string(), None),
                        PureExpr::Var("y".to_string(), None),
                    ],
                }]],
            }),
        );
        let mut substitutions = HashMap::new();
        substitutions.insert("x".to_string(), PureExpr::Int(5));
        let param_names = vec!["x".to_string(), "y".to_string()];

        let names = unresolved_symbolic_names(&expr, &substitutions, Some(&param_names));

        assert!(
            !names.contains("x"),
            "substituted sibling x and bound trigger x must not remain unresolved"
        );
        assert!(
            names.contains("y"),
            "free trigger var y should remain unresolved"
        );
        assert_eq!(
            names.len(),
            1,
            "only free trigger y should remain unresolved"
        );
    }
}

mod replace_var_allow_bound_tests {
    use super::*;

    #[test]
    fn replaces_free_variable() {
        let expr = PureExpr::Var("st2".to_string(), None);
        let replacement = PureExpr::Int(42);
        let result = replace_var_allow_bound(&expr, "st2", &replacement);
        assert_eq!(result, PureExpr::Int(42));
    }

    #[test]
    fn leaves_non_target_variable_alone() {
        let expr = PureExpr::Var("other".to_string(), None);
        let replacement = PureExpr::Int(42);
        let result = replace_var_allow_bound(&expr, "st2", &replacement);
        assert_eq!(result, PureExpr::Var("other".to_string(), None));
    }

    #[test]
    fn replaces_inside_binop() {
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("st2".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );
        let replacement = PureExpr::Int(99);
        let result = replace_var_allow_bound(&expr, "st2", &replacement);
        match result {
            PureExpr::BinOp(left, BinOp::Add, _) => {
                assert_eq!(*left, PureExpr::Int(99));
            }
            other => panic!("expected BinOp, got {other:?}"),
        }
    }

    /// Forall binder shadows target — body is not substituted. (#1630)
    #[test]
    fn forall_binder_shadows_target() {
        // forall st2. st2 > 0  — replacing "st2" should leave body unchanged
        let expr = PureExpr::Forall {
            var: "st2".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("st2".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![],
        };
        let replacement = PureExpr::Var("final_self".to_string(), None);
        let result = replace_var_allow_bound(&expr, "st2", &replacement);
        // Body should remain unchanged — st2 is bound by forall
        assert_eq!(result, expr, "forall-bound variable must not be captured");
    }

    /// Exists binder intentionally allows capture — this is by design
    /// for `connect_final_receiver_state_witness` which targets the
    /// existential witness variable itself. (#1630)
    #[test]
    fn exists_binder_allows_capture_by_design() {
        // exists st2. st2 > 0  — replacing "st2" captures into body
        let expr = PureExpr::Exists {
            var: "st2".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("st2".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![],
        };
        let replacement = PureExpr::Var("final_self".to_string(), None);
        let result = replace_var_allow_bound(&expr, "st2", &replacement);
        // Exists capture is intentional — body's st2 is replaced
        match &result {
            PureExpr::Exists { body, .. } => match body.as_ref() {
                PureExpr::BinOp(left, BinOp::Gt, _) => {
                    assert_eq!(
                        **left, replacement,
                        "exists witness variable should be captured (by design)"
                    );
                }
                other => panic!("expected BinOp, got {other:?}"),
            },
            other => panic!("expected Exists, got {other:?}"),
        }
    }

    /// Let binder shadows target in body but not in value. (#1630)
    #[test]
    fn let_binder_shadows_target_in_body() {
        // let st2 = st2 + 1 in st2 > 0
        // Replacing "st2" should substitute in the value (st2 + 1 → final_self + 1)
        // but NOT in the body (st2 > 0 stays unchanged)
        let expr = PureExpr::Let {
            var: "st2".to_string(),
            value: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("st2".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("st2".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
        };
        let replacement = PureExpr::Var("final_self".to_string(), None);
        let result = replace_var_allow_bound(&expr, "st2", &replacement);
        match &result {
            PureExpr::Let { value, body, .. } => {
                // Value should be substituted: final_self + 1
                match value.as_ref() {
                    PureExpr::BinOp(left, BinOp::Add, _) => {
                        assert_eq!(**left, replacement, "value should be substituted");
                    }
                    other => panic!("expected BinOp in value, got {other:?}"),
                }
                // Body should NOT be substituted: st2 > 0
                match body.as_ref() {
                    PureExpr::BinOp(left, BinOp::Gt, _) => {
                        assert_eq!(
                            **left,
                            PureExpr::Var("st2".to_string(), None),
                            "body must not be substituted — let binding shadows target"
                        );
                    }
                    other => panic!("expected BinOp in body, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    /// Match arm pattern binding shadows target in that arm's body. (#1630)
    #[test]
    fn match_arm_pattern_shadows_target() {
        // match x { st2 => st2 > 0 }
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Binding("st2".to_string()),
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Var("st2".to_string(), None)),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                ),
            }],
        };
        let replacement = PureExpr::Var("final_self".to_string(), None);
        let result = replace_var_allow_bound(&expr, "st2", &replacement);
        match &result {
            PureExpr::Match { arms, .. } => match &arms[0].body {
                PureExpr::BinOp(left, BinOp::Gt, _) => {
                    assert_eq!(
                        **left,
                        PureExpr::Var("st2".to_string(), None),
                        "match arm body must not be substituted — pattern shadows target"
                    );
                }
                other => panic!("expected BinOp in arm body, got {other:?}"),
            },
            other => panic!("expected Match, got {other:?}"),
        }
    }

    /// Closure param shadows target in body. (#1630)
    #[test]
    fn closure_param_shadows_target() {
        // |st2: _| st2 > 0
        let expr = PureExpr::Closure {
            params: vec![("st2".to_string(), None)],
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("st2".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
        };
        let replacement = PureExpr::Var("final_self".to_string(), None);
        let result = replace_var_allow_bound(&expr, "st2", &replacement);
        assert_eq!(result, expr, "closure param must shadow target in body");
    }

    /// Non-shadowed forall still substitutes free occurrences. (#1630)
    #[test]
    fn forall_non_shadowed_substitutes_free() {
        // forall y. st2 > y  — "st2" is free, should be replaced
        let expr = PureExpr::Forall {
            var: "y".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("st2".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
            triggers: vec![],
        };
        let replacement = PureExpr::Int(42);
        let result = replace_var_allow_bound(&expr, "st2", &replacement);
        match &result {
            PureExpr::Forall { body, .. } => match body.as_ref() {
                PureExpr::BinOp(left, BinOp::Gt, _) => {
                    assert_eq!(**left, PureExpr::Int(42), "free var should be replaced");
                }
                other => panic!("expected BinOp, got {other:?}"),
            },
            other => panic!("expected Forall, got {other:?}"),
        }
    }
}
