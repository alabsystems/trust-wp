// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the formula module.

use std::{collections::HashMap, sync::Arc};

use super::{
    expr_has_free_occurrence,
    int_bounds::{pow2_expr, signed_bounds_expr, unsigned_max_expr},
    internal::tuple_lowering::{tuple_logic_fn_arity, tuple_logic_fn_name},
    rename_free_var, BinOp, CaptureAvoidingSubstOptions, ExprSort, FloatBits, Formula, Location,
    MatchArm, NamedBindingValue, Pattern, Permission, PureExpr, SourceSpan, SpannedExpr, UnOp,
    Value,
};

#[test]
fn test_tuple_logic_fn_name_roundtrip() {
    let name = tuple_logic_fn_name(2);
    assert_eq!(name, "__trust_wp_tuple2");
    assert_eq!(tuple_logic_fn_arity(&name), Some(2));
}

#[test]
fn test_tuple_logic_fn_arity_rejects_non_tuple_name() {
    assert_eq!(tuple_logic_fn_arity("max"), None);
}

#[test]
fn test_tuple_logic_fn_arity_allows_newtype_tuple1() {
    assert_eq!(tuple_logic_fn_arity("__trust_wp_tuple0"), None);
    assert_eq!(tuple_logic_fn_arity("__trust_wp_tuple1"), Some(1));
}

// =============================================================================
// Formula enum variant tests
// =============================================================================

mod formula_variant_tests {
    use super::*;

    #[test]
    fn test_formula_true_false() {
        let t = Formula::True;
        let f = Formula::False;
        assert_eq!(t, Formula::True);
        assert_eq!(f, Formula::False);
        assert_ne!(t, f);
    }

    #[test]
    fn test_formula_pure() {
        let expr = PureExpr::Bool(true);
        let formula = Formula::Pure(expr.clone());
        assert_eq!(formula, Formula::Pure(PureExpr::Bool(true)));
    }

    #[test]
    fn test_formula_mut_borrow() {
        let formula = Formula::MutBorrow {
            var: "ref".to_string(),
            current: Arc::new(PureExpr::Int(0)),
            final_val: Arc::new(PureExpr::Int(1)),
            id: Arc::new(PureExpr::Int(7)),
        };
        if let Formula::MutBorrow {
            var,
            current,
            final_val,
            id,
        } = formula
        {
            assert_eq!(var, "ref");
            assert_eq!(*current, PureExpr::Int(0));
            assert_eq!(*final_val, PureExpr::Int(1));
            assert_eq!(*id, PureExpr::Int(7));
        } else {
            panic!("Expected MutBorrow, got {formula:?}");
        }
    }

    #[test]
    fn test_formula_quantifiers() {
        let body = Formula::Pure(PureExpr::Var("x".to_string(), None));
        let exists = Formula::Exists {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(body.clone()),
            triggers: vec![],
        };
        let forall = Formula::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };

        if let Formula::Exists { var, .. } = &exists {
            assert_eq!(var, "x");
        } else {
            panic!("Expected Exists, got {exists:?}");
        }

        if let Formula::Forall { var, .. } = &forall {
            assert_eq!(var, "x");
        } else {
            panic!("Expected Forall, got {forall:?}");
        }
    }
}

// =============================================================================
// Helper type tests
// =============================================================================

mod helper_type_tests {
    use super::*;

    #[test]
    fn test_source_span_from_contract() {
        let span = SourceSpan::from_contract(5, 10);
        assert_eq!(span.start, 5);
        assert_eq!(span.end, 10);
        assert_eq!(span.file, None);
        assert_eq!(span.line, None);
        assert_eq!(span.column, None);
    }

    #[test]
    fn test_source_span_with_location() {
        let span = SourceSpan::with_location("test.rs", 42, 10);
        assert_eq!(span.file, Some("test.rs".to_string()));
        assert_eq!(span.line, Some(42));
        assert_eq!(span.column, Some(10));
    }

    #[test]
    fn test_source_span_default() {
        let span = SourceSpan::default();
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 0);
        assert_eq!(span.file, None);
    }

    #[test]
    fn test_spanned_expr_new() {
        let expr = PureExpr::Int(42);
        let span = SourceSpan::from_contract(0, 2);
        let spanned = SpannedExpr::new(expr.clone(), span.clone());
        assert_eq!(spanned.expr, expr);
        assert_eq!(spanned.span, Some(span));
    }

    #[test]
    fn test_spanned_expr_unspanned() {
        let expr = PureExpr::Bool(false);
        let spanned = SpannedExpr::unspanned(expr.clone());
        assert_eq!(spanned.expr, expr);
        assert_eq!(spanned.span, None);
    }

    #[test]
    fn test_spanned_expr_into_expr() {
        let expr = PureExpr::Var("x".to_string(), None);
        let spanned = SpannedExpr::unspanned(expr.clone());
        let extracted = spanned.into_expr();
        assert_eq!(extracted, expr);
    }

    #[test]
    fn test_spanned_expr_from_pure_expr() {
        let expr = PureExpr::Int(100);
        let spanned: SpannedExpr = expr.clone().into();
        assert_eq!(spanned.expr, expr);
        assert_eq!(spanned.span, None);
    }

    #[test]
    fn test_location() {
        let loc = Location("heap_ptr".to_string());
        assert_eq!(loc.0, "heap_ptr");
    }

    #[test]
    fn test_permission_constants() {
        assert_eq!(Permission::FULL.numerator, 1);
        assert_eq!(Permission::FULL.denominator.get(), 1);
        assert_eq!(Permission::HALF.numerator, 1);
        assert_eq!(Permission::HALF.denominator.get(), 2);
    }

    #[test]
    fn test_permission_custom() {
        let quarter = Permission::new(1, 4).expect("4 is non-zero");
        assert_eq!(quarter.numerator, 1);
        assert_eq!(quarter.denominator.get(), 4);
    }

    #[test]
    fn test_permission_new_zero_denominator() {
        // Zero denominator should return None
        assert!(Permission::new(1, 0).is_none());
    }
}

// =============================================================================
// PureExpr substitution tests
// =============================================================================

mod substitute_tests {
    use super::*;

    #[test]
    fn test_substitute_var() {
        let expr = PureExpr::Var("x".to_string(), None);
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(42));

        let result = expr.substitute(&subs);
        assert_eq!(result, PureExpr::Int(42));
    }

    #[test]
    fn test_substitute_var_not_found() {
        let expr = PureExpr::Var("y".to_string(), None);
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(42));

        let result = expr.substitute(&subs);
        assert_eq!(result, PureExpr::Var("y".to_string(), None));
    }

    #[test]
    fn test_substitute_binop() {
        // result + 1 with result -> x
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );
        let mut subs = HashMap::new();
        subs.insert("result".to_string(), PureExpr::Var("x".to_string(), None));

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )
        );
    }

    #[test]
    fn test_substitute_nested() {
        // (self + value) with self -> arg0, value -> arg1
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("value".to_string(), None)),
        );
        let mut subs = HashMap::new();
        subs.insert("self".to_string(), PureExpr::Var("arg0".to_string(), None));
        subs.insert("value".to_string(), PureExpr::Var("arg1".to_string(), None));

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("arg0".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("arg1".to_string(), None)),
            )
        );
    }

    #[test]
    fn test_substitute_literals_unchanged() {
        let int_expr = PureExpr::Int(42);
        let bool_expr = PureExpr::Bool(true);
        let subs = HashMap::new();

        assert_eq!(int_expr.substitute(&subs), PureExpr::Int(42));
        assert_eq!(bool_expr.substitute(&subs), PureExpr::Bool(true));
    }

    #[test]
    fn test_substitute_filtered_basic() {
        use std::collections::HashSet;

        let expr = PureExpr::Var("x".to_string(), None);
        let filter: HashSet<&str> = ["x"].into_iter().collect();
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(42));

        let result = expr.substitute_filtered(&filter, &subs);
        assert_eq!(result, PureExpr::Int(42));
    }

    #[test]
    fn test_substitute_filtered_not_in_filter() {
        use std::collections::HashSet;

        // Variable "x" is in subs but NOT in filter - should NOT be substituted
        let expr = PureExpr::Var("x".to_string(), None);
        let filter: HashSet<&str> = ["y"].into_iter().collect(); // x not in filter
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(42));

        let result = expr.substitute_filtered(&filter, &subs);
        assert_eq!(result, PureExpr::Var("x".to_string(), None)); // Not substituted
    }

    #[test]
    fn test_substitute_filtered_in_filter_not_in_subs() {
        use std::collections::HashSet;

        // Variable "x" is in filter but NOT in subs - should NOT be substituted
        let expr = PureExpr::Var("x".to_string(), None);
        let filter: HashSet<&str> = ["x"].into_iter().collect();
        let subs = HashMap::new(); // Empty subs

        let result = expr.substitute_filtered(&filter, &subs);
        assert_eq!(result, PureExpr::Var("x".to_string(), None)); // Not substituted
    }

    #[test]
    fn test_substitute_filtered_preserves_tuple_beta_behavior() {
        use std::collections::HashSet;

        let expr = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("t".to_string(), None)],
        };
        let filter: HashSet<&str> = ["t"].into_iter().collect();
        let mut subs = HashMap::new();
        subs.insert(
            "t".to_string(),
            PureExpr::LogicFnCall {
                name: "__trust_wp_tuple2".to_string(),
                args: vec![PureExpr::Int(1), PureExpr::Int(2)],
            },
        );

        let result = expr.substitute_filtered(&filter, &subs);

        assert_eq!(result, PureExpr::Int(1));
    }

    #[test]
    fn test_substitute_capture_avoiding_alpha_renames_forall() {
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
        let mut subs = HashMap::new();
        subs.insert("y".to_string(), PureExpr::Var("x".to_string(), None));

        let result =
            expr.substitute_capture_avoiding(&subs, &CaptureAvoidingSubstOptions::default());

        match result {
            PureExpr::Forall { var, body, .. } => {
                assert_ne!(var, "x", "forall binder should alpha-rename");
                match body.as_ref() {
                    PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
                        assert_eq!(lhs.as_ref(), &PureExpr::Var("x".to_string(), None));
                        assert_eq!(rhs.as_ref(), &PureExpr::Var(var, None));
                    }
                    other => panic!("expected BinOp(Gt), got {other:?}"),
                }
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_substitute_capture_avoiding_match_arm_shadows_pattern_binding() {
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("scrutinee".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Binding("x".to_string()),
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Add,
                    Arc::new(PureExpr::Var("y".to_string(), None)),
                ),
            }],
        };
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(42));
        subs.insert("y".to_string(), PureExpr::Int(10));

        let result =
            expr.substitute_capture_avoiding(&subs, &CaptureAvoidingSubstOptions::default());

        match result {
            PureExpr::Match { arms, .. } => match &arms[0].body {
                PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
                    assert_eq!(lhs.as_ref(), &PureExpr::Var("x".to_string(), None));
                    assert_eq!(rhs.as_ref(), &PureExpr::Int(10));
                }
                other => panic!("expected BinOp(Add), got {other:?}"),
            },
            other => panic!("expected Match, got {other:?}"),
        }
    }

    #[test]
    fn test_substitute_capture_avoiding_alpha_renames_closure_param() {
        let expr = PureExpr::Closure {
            params: vec![("x".to_string(), None)],
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("y".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("x".to_string(), None)),
            )),
        };
        let mut subs = HashMap::new();
        subs.insert("y".to_string(), PureExpr::Var("x".to_string(), None));

        let result =
            expr.substitute_capture_avoiding(&subs, &CaptureAvoidingSubstOptions::default());

        match result {
            PureExpr::Closure { params, body } => {
                let param_name = params[0].0.clone();
                assert_ne!(param_name, "x", "closure parameter should alpha-rename");
                match body.as_ref() {
                    PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
                        assert_eq!(lhs.as_ref(), &PureExpr::Var("x".to_string(), None));
                        assert_eq!(rhs.as_ref(), &PureExpr::Var(param_name, None));
                    }
                    other => panic!("expected BinOp(Add), got {other:?}"),
                }
            }
            other => panic!("expected Closure, got {other:?}"),
        }
    }

    #[test]
    fn test_substitute_reuses_unchanged_sibling_arc() {
        let shared_right = Arc::new(PureExpr::Var("y".to_string(), None));
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::clone(&shared_right),
        );
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(1));

        let result = expr.substitute(&subs);

        match result {
            PureExpr::BinOp(left, BinOp::Add, right) => {
                assert_eq!(left.as_ref(), &PureExpr::Int(1));
                assert!(
                    Arc::ptr_eq(&right, &shared_right),
                    "unchanged sibling should keep its existing Arc"
                );
            }
            other => panic!("expected BinOp(Add), got {other:?}"),
        }
    }

    #[test]
    fn test_substitute_capture_avoiding_reuses_unchanged_sibling_arc() {
        let shared_right = Arc::new(PureExpr::Var("y".to_string(), None));
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::clone(&shared_right),
        );
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(1));

        let result =
            expr.substitute_capture_avoiding(&subs, &CaptureAvoidingSubstOptions::default());

        match result {
            PureExpr::BinOp(left, BinOp::Add, right) => {
                assert_eq!(left.as_ref(), &PureExpr::Int(1));
                assert!(
                    Arc::ptr_eq(&right, &shared_right),
                    "unchanged sibling should keep its existing Arc"
                );
            }
            other => panic!("expected BinOp(Add), got {other:?}"),
        }
    }

    #[test]
    fn test_substitute_forall_shadows_bound_var() {
        // forall x. x + y - substituting x->42 should NOT affect bound x
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
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(42));
        subs.insert("y".to_string(), PureExpr::Int(10));

        let result = expr.substitute(&subs);
        // x should NOT be substituted (shadowed), y should be
        if let PureExpr::Forall { ref body, .. } = result {
            if let PureExpr::BinOp(left, _, right) = body.as_ref() {
                assert_eq!(left.as_ref(), &PureExpr::Var("x".to_string(), None)); // NOT substituted
                assert_eq!(right.as_ref(), &PureExpr::Int(10)); // Substituted
            } else {
                panic!("Expected BinOp in Forall body, got {body:?}");
            }
        } else {
            panic!("Expected Forall, got {result:?}");
        }
    }

    #[test]
    fn test_substitute_filtered_forall_shadows_bound_var() {
        use std::collections::HashSet;

        // forall x. x + y - even with x in filter, bound x should not be substituted
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
        let filter: HashSet<&str> = ["x", "y"].into_iter().collect();
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(42));
        subs.insert("y".to_string(), PureExpr::Int(10));

        let result = expr.substitute_filtered(&filter, &subs);
        // x should NOT be substituted (shadowed by forall), y should be
        if let PureExpr::Forall { ref body, .. } = result {
            if let PureExpr::BinOp(left, _, right) = body.as_ref() {
                assert_eq!(left.as_ref(), &PureExpr::Var("x".to_string(), None)); // NOT substituted
                assert_eq!(right.as_ref(), &PureExpr::Int(10)); // Substituted
            } else {
                panic!("Expected BinOp in Forall body, got {body:?}");
            }
        } else {
            panic!("Expected Forall, got {result:?}");
        }
    }

    // =========================================================================
    // ExprSort annotation preservation tests (#805)
    // =========================================================================

    #[test]
    fn test_substitute_preserves_expr_sort_on_unsubstituted_var() {
        // A Var with ExprSort::Bool that is NOT in the substitution map
        // should retain its ExprSort annotation after substitute().
        let expr = PureExpr::Var("flag".to_string(), Some(ExprSort::Bool));
        let subs = HashMap::new(); // Empty — "flag" not substituted

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::Var("flag".to_string(), Some(ExprSort::Bool)),
            "substitute() must preserve ExprSort annotation on non-substituted Var"
        );
    }

    #[test]
    fn test_substitute_preserves_expr_sort_int() {
        let expr = PureExpr::Var("count".to_string(), Some(ExprSort::Int));
        let mut subs = HashMap::new();
        subs.insert("other".to_string(), PureExpr::Int(99));

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::Var("count".to_string(), Some(ExprSort::Int)),
            "substitute() must preserve ExprSort::Int on non-substituted Var"
        );
    }

    #[test]
    fn test_substitute_preserves_expr_sort_seq() {
        let expr = PureExpr::Var("items".to_string(), Some(ExprSort::Seq));
        let subs = HashMap::new();

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::Var("items".to_string(), Some(ExprSort::Seq)),
            "substitute() must preserve ExprSort::Seq on non-substituted Var"
        );
    }

    #[test]
    fn test_substitute_filtered_preserves_expr_sort_on_unsubstituted_var() {
        use std::collections::HashSet;

        let expr = PureExpr::Var("flag".to_string(), Some(ExprSort::Bool));
        let filter: HashSet<&str> = ["other"].into_iter().collect();
        let subs = HashMap::new();

        let result = expr.substitute_filtered(&filter, &subs);
        assert_eq!(
            result,
            PureExpr::Var("flag".to_string(), Some(ExprSort::Bool)),
            "substitute_filtered() must preserve ExprSort annotation on non-substituted Var"
        );
    }

    #[test]
    fn test_substitute_preserves_expr_sort_in_binop_operands() {
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("flag".to_string(), Some(ExprSort::Bool))),
            BinOp::Add,
            Arc::new(PureExpr::Var("count".to_string(), Some(ExprSort::Int))),
        );
        let subs = HashMap::new();

        let result = expr.substitute(&subs);
        if let PureExpr::BinOp(left, _, right) = &result {
            assert_eq!(
                left.as_ref(),
                &PureExpr::Var("flag".to_string(), Some(ExprSort::Bool)),
                "Left operand ExprSort must be preserved"
            );
            assert_eq!(
                right.as_ref(),
                &PureExpr::Var("count".to_string(), Some(ExprSort::Int)),
                "Right operand ExprSort must be preserved"
            );
        } else {
            panic!("Expected BinOp, got {result:?}");
        }
    }

    #[test]
    fn test_substitute_forall_preserves_var_sort() {
        let expr = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: Some(ExprSort::Bool),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Bool))),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), Some(ExprSort::Int))),
            )),
            triggers: vec![],
        };
        let mut subs = HashMap::new();
        subs.insert("y".to_string(), PureExpr::Int(10));

        let result = expr.substitute(&subs);
        if let PureExpr::Forall {
            var_sort, ref body, ..
        } = result
        {
            assert_eq!(
                var_sort,
                Some(ExprSort::Bool),
                "Forall var_sort must be preserved through substitute"
            );
            if let PureExpr::BinOp(left, _, right) = body.as_ref() {
                assert_eq!(
                    left.as_ref(),
                    &PureExpr::Var("x".to_string(), Some(ExprSort::Bool)),
                    "Bound var ExprSort must be preserved"
                );
                assert_eq!(right.as_ref(), &PureExpr::Int(10));
            } else {
                panic!("Expected BinOp in Forall body");
            }
        } else {
            panic!("Expected Forall, got {result:?}");
        }
    }

    // =========================================================================
    // Deref key ("*name") substitution tests (#746)
    // =========================================================================

    #[test]
    fn test_substitute_deref_var_with_star_key() {
        // Deref(Var("a")) with "*a" -> Int(1) should substitute the whole Deref
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("a".to_string(), None)));
        let mut subs = HashMap::new();
        subs.insert("*a".to_string(), PureExpr::Int(1));

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::Int(1),
            "Deref(Var(\"a\")) must resolve via \"*a\" key"
        );
    }

    #[test]
    fn test_substitute_deref_var_no_star_key_recurses() {
        // Deref(Var("a")) without "*a" in subs, but "a" -> Var("b")
        // should produce Deref(Var("b")) — the deref is preserved, inner is substituted
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("a".to_string(), None)));
        let mut subs = HashMap::new();
        subs.insert("a".to_string(), PureExpr::Var("b".to_string(), None));

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::Deref(Arc::new(PureExpr::Var("b".to_string(), None))),
            "Without \"*a\" key, Deref should recurse into inner expression"
        );
    }

    #[test]
    fn test_substitute_deref_non_var_inner_no_star_lookup() {
        // Deref(BinOp(...)) — inner is not a Var, so no "*name" lookup should happen.
        // The deref recurses into the inner expression.
        let inner = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );
        let expr = PureExpr::Deref(Arc::new(inner));
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), PureExpr::Int(5));

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::Deref(Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(5)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ))),
            "Deref of non-Var inner should recurse, not attempt *name lookup"
        );
    }

    #[test]
    fn test_substitute_deref_star_key_takes_precedence_over_var_key() {
        // Both "a" and "*a" in subs. Deref(Var("a")) should use "*a" (the whole
        // Deref gets replaced), not "a" (which would only replace the inner Var).
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("a".to_string(), None)));
        let mut subs = HashMap::new();
        subs.insert("a".to_string(), PureExpr::Var("b".to_string(), None));
        subs.insert("*a".to_string(), PureExpr::Int(42));

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::Int(42),
            "\"*a\" key must take precedence over \"a\" for Deref(Var(\"a\"))"
        );
    }

    #[test]
    fn test_substitute_nested_deref_only_outer_resolves() {
        // Deref(Deref(Var("a"))) — only one level of Deref should resolve via "*a".
        // The outer Deref sees Deref(Var("a")) as inner, which is NOT a Var, so no
        // "*name" lookup on the outer level. But the inner Deref(Var("a")) DOES match.
        let expr = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "a".to_string(),
            None,
        )))));
        let mut subs = HashMap::new();
        subs.insert("*a".to_string(), PureExpr::Int(10));

        let result = expr.substitute(&subs);
        // Inner Deref(Var("a")) resolves to Int(10), outer Deref(Int(10)) stays
        assert_eq!(
            result,
            PureExpr::Deref(Arc::new(PureExpr::Int(10))),
            "Nested Deref: inner resolves via \"*a\" but outer Deref wraps the result"
        );
    }

    #[test]
    fn test_substitute_deref_preserves_var_sort_in_key_lookup() {
        // Deref(Var("a", Some(ExprSort::Int))) with "*a" key — the sort on the
        // inner Var should not affect the lookup (key is name-based, not sort-based)
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var(
            "a".to_string(),
            Some(ExprSort::Int),
        )));
        let mut subs = HashMap::new();
        subs.insert("*a".to_string(), PureExpr::Int(99));

        let result = expr.substitute(&subs);
        assert_eq!(
            result,
            PureExpr::Int(99),
            "Deref key lookup must work regardless of Var sort annotation"
        );
    }

    #[test]
    fn test_substitute_filtered_deref_respects_filter() {
        use std::collections::HashSet;

        // substitute_filtered with "*a" in subs but "a" NOT in filter:
        // the deref substitution should NOT fire (filter must be respected).
        // Fixed in #898: filter is now checked before deref key lookup.
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("a".to_string(), None)));
        let filter: HashSet<&str> = ["other"].into_iter().collect(); // "a" NOT in filter
        let mut subs = HashMap::new();
        subs.insert("*a".to_string(), PureExpr::Int(1));

        let result = expr.substitute_filtered(&filter, &subs);
        // Deref(Var("a")) stays unchanged because "a" is not in the filter.
        assert_eq!(
            result,
            PureExpr::Deref(Arc::new(PureExpr::Var("a".to_string(), None))),
            "Deref substitution must NOT fire when base var is not in filter"
        );
    }

    #[test]
    fn test_substitute_filtered_deref_with_var_in_filter() {
        use std::collections::HashSet;

        // substitute_filtered with "*a" in subs and "a" IN filter:
        // deref substitution should fire
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("a".to_string(), None)));
        let filter: HashSet<&str> = ["a"].into_iter().collect();
        let mut subs = HashMap::new();
        subs.insert("*a".to_string(), PureExpr::Int(1));

        let result = expr.substitute_filtered(&filter, &subs);
        assert_eq!(
            result,
            PureExpr::Int(1),
            "Deref substitution should fire when base var is in filter"
        );
    }

    // ── Overlay shadowing regression tests (#2484) ─────────────────────

    #[test]
    fn test_substitute_overlay_forall_shadows_body_and_triggers() {
        // forall x. (x + y) with subs {x -> 10, y -> 20}
        // x is bound — should NOT be substituted in body or triggers.
        let body = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("y".to_string(), None)),
        );
        let expr = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![vec![PureExpr::Var("x".to_string(), None)]],
        };
        let subs: HashMap<String, PureExpr> = [
            ("x".to_string(), PureExpr::Int(10)),
            ("y".to_string(), PureExpr::Int(20)),
        ]
        .into_iter()
        .collect();
        let result = expr.substitute(&subs);
        match &result {
            PureExpr::Forall { body, triggers, .. } => {
                // body: x + 20 (x NOT substituted, y IS substituted)
                if let PureExpr::BinOp(left, _, right) = body.as_ref() {
                    assert_eq!(
                        left.as_ref(),
                        &PureExpr::Var("x".to_string(), None),
                        "bound var x must NOT be substituted in body"
                    );
                    assert_eq!(right.as_ref(), &PureExpr::Int(20));
                } else {
                    panic!("expected BinOp in body");
                }
                // trigger: x (NOT substituted)
                assert_eq!(
                    triggers[0][0],
                    PureExpr::Var("x".to_string(), None),
                    "bound var x must NOT be substituted in triggers"
                );
            }
            _ => panic!("expected Forall"),
        }
    }

    #[test]
    fn test_substitute_overlay_let_shadows_body_not_value() {
        // let x = y in x + y with subs {x -> 10, y -> 20}
        // x shadows only the body, not the value.
        let expr = PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::Var("y".to_string(), None)),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };
        let subs: HashMap<String, PureExpr> = [
            ("x".to_string(), PureExpr::Int(10)),
            ("y".to_string(), PureExpr::Int(20)),
        ]
        .into_iter()
        .collect();
        let result = expr.substitute(&subs);
        match &result {
            PureExpr::Let { value, body, .. } => {
                // value: y → 20 (NOT shadowed)
                assert_eq!(value.as_ref(), &PureExpr::Int(20));
                // body: x + y → x + 20 (x IS shadowed)
                if let PureExpr::BinOp(left, _, right) = body.as_ref() {
                    assert_eq!(
                        left.as_ref(),
                        &PureExpr::Var("x".to_string(), None),
                        "let-bound var x must NOT be substituted in body"
                    );
                    assert_eq!(right.as_ref(), &PureExpr::Int(20));
                } else {
                    panic!("expected BinOp in body");
                }
            }
            _ => panic!("expected Let"),
        }
    }

    #[test]
    fn test_substitute_overlay_match_arm_shadows_pattern_bindings() {
        // match scrutinee { Arm(x) => x + y } with subs {x -> 10, y -> 20}
        // x is pattern-bound in the arm — should NOT be substituted.
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("scrutinee".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Arm".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                },
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Add,
                    Arc::new(PureExpr::Var("y".to_string(), None)),
                ),
            }],
        };
        let subs: HashMap<String, PureExpr> = [
            ("x".to_string(), PureExpr::Int(10)),
            ("y".to_string(), PureExpr::Int(20)),
        ]
        .into_iter()
        .collect();
        let result = expr.substitute(&subs);
        match &result {
            PureExpr::Match { arms, .. } => {
                if let PureExpr::BinOp(left, _, right) = &arms[0].body {
                    assert_eq!(
                        left.as_ref(),
                        &PureExpr::Var("x".to_string(), None),
                        "match-arm-bound var x must NOT be substituted in arm body"
                    );
                    assert_eq!(right.as_ref(), &PureExpr::Int(20));
                } else {
                    panic!("expected BinOp in arm body");
                }
            }
            _ => panic!("expected Match"),
        }
    }

    #[test]
    fn test_substitute_overlay_closure_shadows_params() {
        // |x| x + y with subs {x -> 10, y -> 20}
        // x is a closure param — should NOT be substituted.
        let expr = PureExpr::Closure {
            params: vec![("x".to_string(), None)],
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };
        let subs: HashMap<String, PureExpr> = [
            ("x".to_string(), PureExpr::Int(10)),
            ("y".to_string(), PureExpr::Int(20)),
        ]
        .into_iter()
        .collect();
        let result = expr.substitute(&subs);
        match &result {
            PureExpr::Closure { body, .. } => {
                if let PureExpr::BinOp(left, _, right) = body.as_ref() {
                    assert_eq!(
                        left.as_ref(),
                        &PureExpr::Var("x".to_string(), None),
                        "closure-param var x must NOT be substituted in body"
                    );
                    assert_eq!(right.as_ref(), &PureExpr::Int(20));
                } else {
                    panic!("expected BinOp in closure body");
                }
            }
            _ => panic!("expected Closure"),
        }
    }

    #[test]
    fn test_substitute_deref_key_survives_binder_shadowing() {
        // forall x. *x with subs {x -> 10, *x -> 42}
        // The bound "x" shadows the "x" key, but NOT the "*x" key.
        // Deref(*x) should still resolve via the "*x" entry.
        let expr = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            triggers: vec![],
        };
        let subs: HashMap<String, PureExpr> = [
            ("x".to_string(), PureExpr::Int(10)),
            ("*x".to_string(), PureExpr::Int(42)),
        ]
        .into_iter()
        .collect();
        let result = expr.substitute(&subs);
        match &result {
            PureExpr::Forall { body, .. } => {
                assert_eq!(
                    body.as_ref(),
                    &PureExpr::Int(42),
                    "deref-key *x must NOT be shadowed when x is bound"
                );
            }
            _ => panic!("expected Forall"),
        }
    }

    // =========================================================================
    // substitute_no_tuple_beta tests
    // =========================================================================

    #[test]
    fn test_substitute_no_tuple_beta_skips_reduction() {
        // tuple_get_0(tuple2(a, b)) should NOT reduce to a
        // when beta_reduce_tuples is false.
        let ctor = "__trust_wp_tuple2".to_string();
        let getter = "__trust_wp_tuple_get_0".to_string();
        let tuple_expr = PureExpr::LogicFnCall {
            name: ctor,
            args: vec![
                PureExpr::Var("a".to_string(), None),
                PureExpr::Var("b".to_string(), None),
            ],
        };
        let expr = PureExpr::LogicFnCall {
            name: getter,
            args: vec![tuple_expr],
        };
        let subs: HashMap<String, PureExpr> =
            [("a".to_string(), PureExpr::Int(10))].into_iter().collect();

        // With beta reduction: tuple_get_0(tuple2(10, b)) → 10
        let with_beta = expr.substitute(&subs);
        assert_eq!(with_beta, PureExpr::Int(10));

        // Without beta reduction: tuple_get_0(tuple2(10, b)) stays as-is
        let without_beta = expr.substitute_no_tuple_beta(&subs);
        match &without_beta {
            PureExpr::LogicFnCall { name, args } => {
                assert!(
                    name.contains("tuple_get_0"),
                    "outer should still be tuple_get_0"
                );
                assert_eq!(args.len(), 1);
                match &args[0] {
                    PureExpr::LogicFnCall { args: inner, .. } => {
                        assert_eq!(inner[0], PureExpr::Int(10), "substitution should apply");
                    }
                    _ => panic!("expected inner LogicFnCall (tuple constructor)"),
                }
            }
            _ => panic!("expected LogicFnCall, got {:?}", without_beta),
        }
    }

    #[test]
    fn test_substitute_no_tuple_beta_still_replaces_vars() {
        // Basic variable substitution still works without beta reduction.
        let expr = PureExpr::Var("x".to_string(), None);
        let subs: HashMap<String, PureExpr> =
            [("x".to_string(), PureExpr::Int(42))].into_iter().collect();
        let result = expr.substitute_no_tuple_beta(&subs);
        assert_eq!(result, PureExpr::Int(42));
    }

    // =========================================================================
    // rename_free_var tests
    // =========================================================================

    #[test]
    fn test_rename_free_var_basic() {
        let expr = PureExpr::Var("x".to_string(), None);
        let opts = CaptureAvoidingSubstOptions::default();
        let result = rename_free_var(&expr, "x", "y", &opts);
        assert_eq!(result, PureExpr::Var("y".to_string(), None));
    }

    #[test]
    fn test_rename_free_var_preserves_sort() {
        let expr = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
        let opts = CaptureAvoidingSubstOptions::default();
        let result = rename_free_var(&expr, "x", "y", &opts);
        assert_eq!(result, PureExpr::Var("y".to_string(), Some(ExprSort::Int)));
    }

    #[test]
    fn test_rename_free_var_noop_for_other_name() {
        let expr = PureExpr::Var("z".to_string(), None);
        let opts = CaptureAvoidingSubstOptions::default();
        let result = rename_free_var(&expr, "x", "y", &opts);
        assert_eq!(result, PureExpr::Var("z".to_string(), None));
    }

    #[test]
    fn test_rename_free_var_in_binop() {
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("x".to_string(), None)),
        );
        let opts = CaptureAvoidingSubstOptions::default();
        let result = rename_free_var(&expr, "x", "y", &opts);
        let expected = PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("y".to_string(), None)),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_rename_free_var_respects_forall_shadow() {
        // forall x. x + y  — renaming x should NOT touch bound x
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
        let opts = CaptureAvoidingSubstOptions::default();
        let result = rename_free_var(&expr, "x", "z", &opts);
        // Body should be unchanged since x is bound by forall
        match &result {
            PureExpr::Forall { body, .. } => match body.as_ref() {
                PureExpr::BinOp(left, _, _) => {
                    assert_eq!(
                        left.as_ref(),
                        &PureExpr::Var("x".to_string(), None),
                        "bound x should not be renamed"
                    );
                }
                _ => panic!("expected BinOp"),
            },
            _ => panic!("expected Forall"),
        }
    }

    #[test]
    fn test_rename_free_var_respects_let_shadow() {
        // let x = y in x  — renaming x should not touch body (shadowed)
        // but should not touch value (y is not x)
        let expr = PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::Var("y".to_string(), None)),
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
        };
        let opts = CaptureAvoidingSubstOptions::default();
        let result = rename_free_var(&expr, "x", "z", &opts);
        match &result {
            PureExpr::Let { var, body, .. } => {
                assert_eq!(var, "x");
                assert_eq!(
                    body.as_ref(),
                    &PureExpr::Var("x".to_string(), None),
                    "x in body is shadowed by let, should not be renamed"
                );
            }
            _ => panic!("expected Let"),
        }
    }

    #[test]
    fn test_rename_free_var_in_let_value() {
        // let y = x in y  — renaming x should affect the value
        let expr = PureExpr::Let {
            var: "y".to_string(),
            value: Arc::new(PureExpr::Var("x".to_string(), None)),
            body: Arc::new(PureExpr::Var("y".to_string(), None)),
        };
        let opts = CaptureAvoidingSubstOptions::default();
        let result = rename_free_var(&expr, "x", "z", &opts);
        match &result {
            PureExpr::Let { value, .. } => {
                assert_eq!(
                    value.as_ref(),
                    &PureExpr::Var("z".to_string(), None),
                    "x in value is free, should be renamed to z"
                );
            }
            _ => panic!("expected Let"),
        }
    }

    #[test]
    fn test_rename_free_var_respects_closure_shadow() {
        // |x| x + y — renaming x should not touch the closure body
        let expr = PureExpr::Closure {
            params: vec![("x".to_string(), None)],
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };
        let opts = CaptureAvoidingSubstOptions::default();
        let result = rename_free_var(&expr, "x", "z", &opts);
        // Should be unchanged — x is bound by closure param
        assert_eq!(result, expr);
    }

    // =========================================================================
    // expr_has_free_occurrence tests
    // =========================================================================

    #[test]
    fn test_expr_has_free_occurrence_in_var() {
        let expr = PureExpr::Var("x".to_string(), None);
        let opts = CaptureAvoidingSubstOptions::default();
        assert!(expr_has_free_occurrence(&expr, "x", &opts));
        assert!(!expr_has_free_occurrence(&expr, "y", &opts));
    }

    #[test]
    fn test_expr_has_free_occurrence_in_literal() {
        let opts = CaptureAvoidingSubstOptions::default();
        assert!(!expr_has_free_occurrence(&PureExpr::Int(42), "x", &opts));
        assert!(!expr_has_free_occurrence(&PureExpr::Bool(true), "x", &opts));
    }

    #[test]
    fn test_expr_has_free_occurrence_shadowed_by_forall() {
        // forall x. x — x is bound, not free
        let expr = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
            triggers: vec![],
        };
        let opts = CaptureAvoidingSubstOptions::default();
        assert!(
            !expr_has_free_occurrence(&expr, "x", &opts),
            "x is bound by forall"
        );
    }

    #[test]
    fn test_expr_has_free_occurrence_shadowed_by_exists() {
        let expr = PureExpr::Exists {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
            triggers: vec![],
        };
        let opts = CaptureAvoidingSubstOptions::default();
        assert!(
            !expr_has_free_occurrence(&expr, "x", &opts),
            "x is bound by exists"
        );
    }

    #[test]
    fn test_expr_has_free_occurrence_shadowed_by_closure() {
        let expr = PureExpr::Closure {
            params: vec![("x".to_string(), None)],
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
        };
        let opts = CaptureAvoidingSubstOptions::default();
        assert!(
            !expr_has_free_occurrence(&expr, "x", &opts),
            "x is bound by closure param"
        );
    }

    #[test]
    fn test_expr_has_free_occurrence_in_ite_branches() {
        let expr = PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(PureExpr::Int(1)),
            Arc::new(PureExpr::Var("x".to_string(), None)),
        );
        let opts = CaptureAvoidingSubstOptions::default();
        assert!(expr_has_free_occurrence(&expr, "x", &opts));
        assert!(!expr_has_free_occurrence(&expr, "y", &opts));
    }

    #[test]
    fn test_expr_has_free_occurrence_depth_limit_returns_true() {
        // depth_limit_exceeded checks depth > limit. With limit=0, depth=0
        // is NOT exceeded, but depth=1 is. Wrap in UnOp so inner Var is at depth 1.
        let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(PureExpr::Var("x".to_string(), None)));
        let opts = CaptureAvoidingSubstOptions {
            depth_limit: Some(0),
        };
        // At depth 0, processes UnOp. At depth 1 (> 0), returns true conservatively.
        assert!(
            expr_has_free_occurrence(&expr, "x", &opts),
            "depth limit exceeded returns true (conservative)"
        );
        assert!(
            expr_has_free_occurrence(&expr, "nonexistent", &opts),
            "depth limit exceeded returns true even for absent vars"
        );
    }

    // =========================================================================
    // capture-avoiding substitution: Exists, Let alpha-rename, depth limit
    // =========================================================================

    #[test]
    fn test_substitute_capture_avoiding_alpha_renames_exists() {
        // exists x. x + y  with {y -> x}
        // Must alpha-rename: exists x_α0. x_α0 + x
        let expr = PureExpr::Exists {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
            triggers: vec![],
        };
        let subs: HashMap<String, PureExpr> =
            [("y".to_string(), PureExpr::Var("x".to_string(), None))]
                .into_iter()
                .collect();
        let opts = CaptureAvoidingSubstOptions::default();
        let result = expr.substitute_capture_avoiding(&subs, &opts);
        match &result {
            PureExpr::Exists { var, body, .. } => {
                assert_ne!(var, "x", "bound var must be alpha-renamed to avoid capture");
                assert!(
                    var.starts_with("x_"),
                    "fresh name should be based on original"
                );
                // The body's RHS (formerly y) should now be x (the substitution value)
                match body.as_ref() {
                    PureExpr::BinOp(_, _, right) => {
                        assert_eq!(
                            right.as_ref(),
                            &PureExpr::Var("x".to_string(), None),
                            "y should be replaced with x"
                        );
                    }
                    _ => panic!("expected BinOp body"),
                }
            }
            _ => panic!("expected Exists"),
        }
    }

    #[test]
    fn test_substitute_capture_avoiding_alpha_renames_let() {
        // let x = 1 in x + y  with {y -> x}
        // Must alpha-rename: let x_α0 = 1 in x_α0 + x
        let expr = PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::Int(1)),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };
        let subs: HashMap<String, PureExpr> =
            [("y".to_string(), PureExpr::Var("x".to_string(), None))]
                .into_iter()
                .collect();
        let opts = CaptureAvoidingSubstOptions::default();
        let result = expr.substitute_capture_avoiding(&subs, &opts);
        match &result {
            PureExpr::Let { var, body, .. } => {
                assert_ne!(var, "x", "let-bound var must be alpha-renamed");
                assert!(
                    var.starts_with("x_"),
                    "fresh name should be based on original"
                );
                match body.as_ref() {
                    PureExpr::BinOp(left, _, right) => {
                        // left should use the fresh name (alpha-renamed)
                        match left.as_ref() {
                            PureExpr::Var(name, _) => {
                                assert_eq!(name, var, "left should use renamed binder");
                            }
                            _ => panic!("expected Var on left"),
                        }
                        // right should be x (the substitution for y)
                        assert_eq!(
                            right.as_ref(),
                            &PureExpr::Var("x".to_string(), None),
                            "y should be replaced with x"
                        );
                    }
                    _ => panic!("expected BinOp body"),
                }
            }
            _ => panic!("expected Let"),
        }
    }

    #[test]
    fn test_substitute_capture_avoiding_depth_limit_stops_recursion() {
        // depth_limit_exceeded checks depth > limit. With limit=0:
        // - depth 0: processes (outer BinOp)
        // - depth 1: exceeded → children cloned without substitution
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("x".to_string(), None)),
        );
        let subs: HashMap<String, PureExpr> =
            [("x".to_string(), PureExpr::Int(99))].into_iter().collect();
        let opts = CaptureAvoidingSubstOptions {
            depth_limit: Some(0),
        };
        let result = expr.substitute_capture_avoiding(&subs, &opts);
        // BinOp at depth 0 is processed, but children at depth 1 > 0 are cloned.
        match &result {
            PureExpr::BinOp(left, _, right) => {
                assert_eq!(
                    left.as_ref(),
                    &PureExpr::Var("x".to_string(), None),
                    "depth-limited: inner var not substituted"
                );
                assert_eq!(
                    right.as_ref(),
                    &PureExpr::Var("x".to_string(), None),
                    "depth-limited: inner var not substituted"
                );
            }
            _ => panic!("expected BinOp"),
        }

        // With no limit, same expr gets fully substituted.
        let opts_no_limit = CaptureAvoidingSubstOptions::default();
        let result_full = expr.substitute_capture_avoiding(&subs, &opts_no_limit);
        match &result_full {
            PureExpr::BinOp(left, _, right) => {
                assert_eq!(left.as_ref(), &PureExpr::Int(99), "fully substituted left");
                assert_eq!(
                    right.as_ref(),
                    &PureExpr::Int(99),
                    "fully substituted right"
                );
            }
            _ => panic!("expected BinOp"),
        }
    }

    #[test]
    fn test_rename_free_var_with_depth_limit() {
        // depth_limit=0 means depth_limit_exceeded(0, Some(0)) → 0 > 0 is false
        // So depth 0 processes, depth 1 does not.
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("x".to_string(), None)),
        );
        let opts = CaptureAvoidingSubstOptions {
            depth_limit: Some(0),
        };
        let result = rename_free_var(&expr, "x", "y", &opts);
        // At depth 0 we enter BinOp → children at depth 1 > limit → cloned
        match &result {
            PureExpr::BinOp(left, _, right) => {
                assert_eq!(
                    left.as_ref(),
                    &PureExpr::Var("x".to_string(), None),
                    "depth-limited: not renamed"
                );
                assert_eq!(right.as_ref(), &PureExpr::Var("x".to_string(), None));
            }
            _ => panic!("expected BinOp"),
        }
    }
}

// =============================================================================
// Display implementation tests
// =============================================================================

mod display_tests {
    use super::*;

    #[test]
    fn test_binop_display() {
        assert_eq!(format!("{}", BinOp::Add), "+");
        assert_eq!(format!("{}", BinOp::Sub), "-");
        assert_eq!(format!("{}", BinOp::Mul), "*");
        assert_eq!(format!("{}", BinOp::Div), "/");
        assert_eq!(format!("{}", BinOp::Mod), "%");
        assert_eq!(format!("{}", BinOp::Shl), "<<");
        assert_eq!(format!("{}", BinOp::Shr), ">>");
        assert_eq!(format!("{}", BinOp::BitAnd), "&");
        assert_eq!(format!("{}", BinOp::BitXor), "^");
        assert_eq!(format!("{}", BinOp::BitOr), "|");
        assert_eq!(format!("{}", BinOp::Eq), "==");
        assert_eq!(format!("{}", BinOp::Ne), "!=");
        assert_eq!(format!("{}", BinOp::Lt), "<");
        assert_eq!(format!("{}", BinOp::Le), "<=");
        assert_eq!(format!("{}", BinOp::Gt), ">");
        assert_eq!(format!("{}", BinOp::Ge), ">=");
        assert_eq!(format!("{}", BinOp::And), "&&");
        assert_eq!(format!("{}", BinOp::Or), "||");
        assert_eq!(format!("{}", BinOp::Implies), "==>");
    }

    #[test]
    fn test_unop_display() {
        assert_eq!(format!("{}", UnOp::Not), "!");
        assert_eq!(format!("{}", UnOp::Neg), "-");
    }

    #[test]
    fn test_pattern_display() {
        assert_eq!(format!("{}", Pattern::Wildcard), "_");
        assert_eq!(format!("{}", Pattern::Binding("x".to_string())), "x");
        assert_eq!(format!("{}", Pattern::Literal(PureExpr::Int(42))), "42");
        assert_eq!(
            format!(
                "{}",
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None
                }
            ),
            "None"
        );
        assert_eq!(
            format!(
                "{}",
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string())))
                }
            ),
            "Some(v)"
        );
    }

    #[test]
    fn test_pure_expr_display_basic() {
        assert_eq!(format!("{}", PureExpr::Bool(true)), "true");
        assert_eq!(format!("{}", PureExpr::Bool(false)), "false");
        assert_eq!(format!("{}", PureExpr::Int(42)), "42");
        assert_eq!(format!("{}", PureExpr::Int(-7)), "-7");
        assert_eq!(format!("{}", PureExpr::Var("x".to_string(), None)), "x");
    }

    #[test]
    fn test_pure_expr_display_binop() {
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );
        assert_eq!(format!("{expr}"), "(x + 1)");
    }

    #[test]
    fn test_pure_expr_display_unop() {
        let not_expr = PureExpr::UnOp(UnOp::Not, Arc::new(PureExpr::Bool(true)));
        assert_eq!(format!("{not_expr}"), "!true");

        let neg_expr = PureExpr::UnOp(UnOp::Neg, Arc::new(PureExpr::Int(5)));
        assert_eq!(format!("{neg_expr}"), "-5");
    }

    #[test]
    fn test_pure_expr_display_ite() {
        let expr = PureExpr::Ite(
            Arc::new(PureExpr::Var("cond".to_string(), None)),
            Arc::new(PureExpr::Int(1)),
            Arc::new(PureExpr::Int(0)),
        );
        assert_eq!(format!("{expr}"), "if cond { 1 } else { 0 }");
    }

    #[test]
    fn test_pure_expr_display_special() {
        let old = PureExpr::Old(Arc::new(PureExpr::Var("x".to_string(), None)));
        assert_eq!(format!("{old}"), "old(x)");

        let deref = PureExpr::Deref(Arc::new(PureExpr::Var("ptr".to_string(), None)));
        assert_eq!(format!("{deref}"), "*ptr");

        let final_val = PureExpr::Final(Arc::new(PureExpr::Var("r".to_string(), None)));
        assert_eq!(format!("{final_val}"), "^r");

        let view = PureExpr::View(Arc::new(PureExpr::Var("v".to_string(), None)));
        assert_eq!(format!("{view}"), "v@");
    }

    #[test]
    fn test_pure_expr_display_method_call() {
        let call = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "v".to_string(),
                None,
            )))),
            method: "len".to_string(),
            args: vec![],
        };
        assert_eq!(format!("{call}"), "v@.len()");

        let call_with_args = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("seq".to_string(), None)),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(0)],
        };
        assert_eq!(format!("{call_with_args}"), "seq.index_logic(0)");
    }

    #[test]
    fn test_pure_expr_display_quantifiers() {
        let forall = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".to_string(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![],
        };
        assert_eq!(format!("{forall}"), "forall<i: _> (i >= 0)");

        let exists = PureExpr::Exists {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Bool(true)),
            triggers: vec![],
        };
        assert_eq!(format!("{exists}"), "exists<x: _> true");
    }

    #[test]
    fn test_pure_expr_display_match() {
        let match_expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "self".to_string(),
                None,
            )))),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                    },
                    body: PureExpr::Var("v".to_string(), None),
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
        assert_eq!(
            format!("{match_expr}"),
            "match *self { Some(v) => v, None => 0 }"
        );
    }

    #[test]
    fn test_permission_display() {
        assert_eq!(format!("{}", Permission::FULL), "full");
        assert_eq!(format!("{}", Permission::HALF), "half");
        assert_eq!(format!("{}", Permission::new(1, 4).unwrap()), "1/4");
    }

    #[test]
    fn test_location_display() {
        let loc = Location("heap_ptr".to_string());
        assert_eq!(format!("{loc}"), "heap_ptr");
    }

    #[test]
    fn test_value_display() {
        assert_eq!(format!("{}", Value::Expr(PureExpr::Int(42))), "42");
        assert_eq!(format!("{}", Value::Unknown), "_");
    }

    #[test]
    fn test_formula_display_basic() {
        assert_eq!(format!("{}", Formula::True), "true");
        assert_eq!(format!("{}", Formula::False), "false");
        assert_eq!(format!("{}", Formula::Pure(PureExpr::Int(42))), "42");
    }

    #[test]
    fn test_formula_display_points_to() {
        let formula = Formula::PointsTo {
            location: Location("x".to_string()),
            value: Value::Expr(PureExpr::Int(42)),
            permission: Permission::FULL,
        };
        assert_eq!(format!("{formula}"), "x ↦[full] 42");
    }

    #[test]
    fn test_formula_display_mut_borrow() {
        let formula = Formula::MutBorrow {
            var: "r".to_string(),
            current: Arc::new(PureExpr::Int(0)),
            final_val: Arc::new(PureExpr::Int(1)),
            id: Arc::new(PureExpr::Int(2)),
        };
        assert_eq!(format!("{formula}"), "borrow(r: *=0, ^=1, id=2)");
    }

    #[test]
    fn test_formula_display_connectives() {
        let p = Formula::True;
        let q = Formula::False;

        let sep = Formula::SepConj(Arc::new(p.clone()), Arc::new(q.clone()));
        assert_eq!(format!("{sep}"), "(true * false)");

        let and = Formula::And(Arc::new(p.clone()), Arc::new(q.clone()));
        assert_eq!(format!("{and}"), "(true ∧ false)");

        let or = Formula::Or(Arc::new(p.clone()), Arc::new(q.clone()));
        assert_eq!(format!("{or}"), "(true ∨ false)");

        let imp = Formula::Implies(Arc::new(p.clone()), Arc::new(q.clone()));
        assert_eq!(format!("{imp}"), "(true → false)");

        let wand = Formula::MagicWand(Arc::new(p), Arc::new(q));
        assert_eq!(format!("{wand}"), "(true -* false)");
    }

    #[test]
    fn test_formula_display_quantifiers() {
        let forall = Formula::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(Formula::True),
            triggers: vec![],
        };
        assert_eq!(format!("{forall}"), "∀x. true");

        let exists = Formula::Exists {
            var: "y".to_string(),
            var_sort: None,
            body: Arc::new(Formula::False),
            triggers: vec![],
        };
        assert_eq!(format!("{exists}"), "∃y. false");
    }

    #[test]
    fn test_match_arm_display() {
        let arm = MatchArm {
            pattern: Pattern::Binding("x".to_string()),
            body: PureExpr::Var("x".to_string(), None),
        };
        assert_eq!(format!("{arm}"), "x => x");
    }

    #[test]
    fn test_pure_expr_display_nested_quantifiers() {
        // forall<i: Int> forall<j: Int> (i <= j)
        let nested = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Forall {
                var: "j".to_string(),
                var_sort: None,
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("i".to_string(), None)),
                    BinOp::Le,
                    Arc::new(PureExpr::Var("j".to_string(), None)),
                )),
                triggers: vec![],
            }),
            triggers: vec![],
        };
        assert_eq!(format!("{nested}"), "forall<i: _> forall<j: _> (i <= j)");
    }

    #[test]
    fn test_pure_expr_display_nested_unop() {
        // !!true
        let double_neg = PureExpr::UnOp(
            UnOp::Not,
            Arc::new(PureExpr::UnOp(UnOp::Not, Arc::new(PureExpr::Bool(true)))),
        );
        assert_eq!(format!("{double_neg}"), "!!true");

        // --5
        let double_minus = PureExpr::UnOp(
            UnOp::Neg,
            Arc::new(PureExpr::UnOp(UnOp::Neg, Arc::new(PureExpr::Int(5)))),
        );
        assert_eq!(format!("{double_minus}"), "--5");
    }

    #[test]
    fn test_pure_expr_display_method_call_multiple_args() {
        let call = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("seq".to_string(), None)),
            method: "set".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(42), PureExpr::Bool(true)],
        };
        assert_eq!(format!("{call}"), "seq.set(0, 42, true)");
    }

    #[test]
    fn test_permission_display_edge_cases() {
        // Zero numerator (still valid - no permission)
        let zero_perm = Permission::new(0, 1).unwrap();
        assert_eq!(format!("{zero_perm}"), "0/1");

        // Other fractions
        let third = Permission::new(1, 3).unwrap();
        assert_eq!(format!("{third}"), "1/3");
    }
}

// =============================================================================
// Postcondition transformation tests
// =============================================================================

mod postcond_transform_tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn test_transform_deref_to_final_simple() {
        // *x == old(*x) + 1
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("x".to_string(), None),
                ))))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        );

        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // Expected: ^x == old(*x) + 1
        // The *x outside Old should become ^x (Final)
        // The *x inside Old should stay as *x (Deref)
        if let PureExpr::BinOp(left, BinOp::Eq, right) = transformed {
            // Left should be Final(Var("x"))
            assert!(
                matches!(left.as_ref(), PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "x")),
                "Expected left to be Final(Var(x)), got {left:?}"
            );

            // Right should be BinOp(Old(Deref(Var(x))), Add, Int(1))
            if let PureExpr::BinOp(old_part, BinOp::Add, _one) = right.as_ref() {
                assert!(
                    matches!(old_part.as_ref(), PureExpr::Old(inner) if matches!(inner.as_ref(), PureExpr::Deref(_))),
                    "Expected old(*x), got {old_part:?}"
                );
            } else {
                panic!("Expected BinOp on right, got {right:?}");
            }
        } else {
            panic!("Expected BinOp at top level, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_preserves_non_mut_ref_deref() {
        // *y == 0 (where y is NOT in mut_refs)
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "y".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        );

        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // *y should stay as Deref (y is not in mut_refs)
        if let PureExpr::BinOp(ref left, _, _) = transformed {
            assert!(
                matches!(left.as_ref(), PureExpr::Deref(_)),
                "Expected Deref for non-mut-ref param, got {left:?}"
            );
        } else {
            panic!("Expected BinOp, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_keeps_old_deref_unchanged() {
        // old(*x) + 1 (just the old(*x) part, no outer *x)
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
                PureExpr::Var("x".to_string(), None),
            ))))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );

        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // old(*x) should stay as Old(Deref(Var(x)))
        if let PureExpr::BinOp(ref left, _, _) = transformed {
            assert!(
                matches!(left.as_ref(), PureExpr::Old(inner) if matches!(inner.as_ref(), PureExpr::Deref(_))),
                "old(*x) should remain unchanged, got {left:?}"
            );
        } else {
            panic!("Expected BinOp, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_preserves_explicit_final_style_for_same_param() {
        // ^v == *v + 1 should stay unchanged.
        // Here, *v intentionally refers to current value and ^v to final value.
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "v".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                    "v".to_string(),
                    None,
                )))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        );

        let mut_refs: HashSet<String> = ["v".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        assert_eq!(transformed, postcond);
    }

    #[test]
    fn test_transform_explicit_final_is_param_local() {
        // ^x == *y should still rewrite *y to ^y when y has no explicit final.
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "y".to_string(),
                None,
            )))),
        );

        let mut_refs: HashSet<String> = ["x".to_string(), "y".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        assert_eq!(
            transformed,
            PureExpr::BinOp(
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    "x".to_string(),
                    None
                )))),
                BinOp::Eq,
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    "y".to_string(),
                    None
                )))),
            )
        );
    }

    #[test]
    fn test_transform_closure_capture_postcondition() {
        // self.0 == old(self.0) + 1
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Var("self.0".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                    "self.0".to_string(),
                    None,
                )))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        );

        let capture_fields: HashSet<String> = ["self.0".to_string()].into_iter().collect();
        let transformed = postcond.transform_closure_capture_postcondition(&capture_fields);

        assert_eq!(
            transformed,
            PureExpr::BinOp(
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("self.0".to_string(), None),
                ))))),
                BinOp::Eq,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
                        PureExpr::Var("self.0".to_string(), None),
                    ))))),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                )),
            )
        );
    }

    #[test]
    fn test_transform_closure_capture_postcondition_view() {
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "self.0".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        );

        let capture_fields: HashSet<String> = ["self.0".to_string()].into_iter().collect();
        let transformed = postcond.transform_closure_capture_postcondition(&capture_fields);

        assert_eq!(
            transformed,
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                    PureExpr::Deref(Arc::new(PureExpr::Var("self.0".to_string(), None))),
                ))))),
                BinOp::Eq,
                Arc::new(PureExpr::Int(1)),
            )
        );
    }

    #[test]
    fn test_transform_closure_capture_postcondition_preserves_single_deref_shape() {
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                PureExpr::Var("self.0".to_string(), None),
            ))))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        );

        let capture_fields: HashSet<String> = ["self.0".to_string()].into_iter().collect();
        let transformed = postcond.transform_closure_capture_postcondition(&capture_fields);

        assert_eq!(
            transformed,
            PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                    PureExpr::Deref(Arc::new(PureExpr::Var("self.0".to_string(), None))),
                ))))),
                BinOp::Eq,
                Arc::new(PureExpr::Int(1)),
            )
        );
    }

    /// Regression test for #616: applying `mut_ref` transform to a closure capture
    /// field before the closure capture transform produces Deref(Final(Var("self.0")))
    /// instead of the correct Final(Deref(Var("self.0"))). The fix is to exclude
    /// capture fields from `mut_ref_params` before the `mut_ref` transform.
    #[test]
    fn test_double_transform_regression_616() {
        // self.0 == old(self.0) + 1
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Var("self.0".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                    "self.0".to_string(),
                    None,
                )))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        );

        let capture_fields: HashSet<String> = ["self.0".to_string()].into_iter().collect();

        // Correct path: only apply closure capture transform (mut_ref_params excludes captures)
        let correct = postcond.transform_closure_capture_postcondition(&capture_fields);
        // Outside old: Var("self.0") → Final(Deref(Var("self.0")))
        // Inside old: Var("self.0") → Deref(Var("self.0"))
        assert!(
            matches!(
                &correct,
                PureExpr::BinOp(lhs, _, _)
                    if matches!(
                        &**lhs,
                        PureExpr::Final(inner)
                            if matches!(&**inner, PureExpr::Deref(deref_inner)
                                if matches!(&**deref_inner, PureExpr::Var(name, _) if name == "self.0"))
                    )
            ),
            "Correct transform must wrap LHS in Final(Deref(...)): {correct:?}"
        );

        // Previously-wrong path (#616): applying mut_ref first then closure capture
        // used to produce Deref(Final(Var("self.0"))) instead of Final(Deref(Var("self.0"))).
        // The Deref case in the closure-capture transform now normalizes
        // Deref(Var("self.0")) → Final(Deref(Var("self.0"))), so both paths converge.
        let mut_ref_params: HashSet<String> = ["self.0".to_string()].into_iter().collect();
        let after_mut_ref = postcond.transform_postcondition_for_mut_refs(&mut_ref_params);
        let double_transformed =
            after_mut_ref.transform_closure_capture_postcondition(&capture_fields);
        assert_eq!(
            correct, double_transformed,
            "Double-transform must converge to the same result as single-path (#616 fix)"
        );
    }

    #[test]
    fn test_transform_closure_capture_precondition() {
        // self.0 < 1000
        let precond = PureExpr::BinOp(
            Arc::new(PureExpr::Var("self.0".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Int(1000)),
        );

        let capture_fields: HashSet<String> = ["self.0".to_string()].into_iter().collect();
        let transformed = precond.transform_closure_capture_precondition(&capture_fields);

        assert_eq!(
            transformed,
            PureExpr::BinOp(
                Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                    "self.0".to_string(),
                    None,
                )))),
                BinOp::Lt,
                Arc::new(PureExpr::Int(1000)),
            )
        );
    }

    #[test]
    fn test_transform_closure_capture_precondition_deref_is_not_double_wrapped() {
        let precond = PureExpr::Deref(Arc::new(PureExpr::Var("self.0".to_string(), None)));

        let capture_fields: HashSet<String> = ["self.0".to_string()].into_iter().collect();
        let transformed = precond.transform_closure_capture_precondition(&capture_fields);

        assert_eq!(
            transformed,
            PureExpr::Deref(Arc::new(PureExpr::Var("self.0".to_string(), None)))
        );
    }

    // =====================================================================
    // Nested expression tests (Part of #424)
    // =====================================================================

    #[test]
    fn test_transform_logic_fn_call_with_mut_ref() {
        // result == max(*x, *y) where x is mut ref, y is not
        // Should become: result == max(^x, *y)
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "crate::specs::max".to_string(),
                args: vec![
                    PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None))),
                    PureExpr::Deref(Arc::new(PureExpr::Var("y".to_string(), None))),
                ],
            }),
        );

        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // Check result == max(^x, *y)
        if let PureExpr::BinOp(_, BinOp::Eq, right) = transformed {
            if let PureExpr::LogicFnCall { name, args } = right.as_ref() {
                assert_eq!(name, "crate::specs::max");
                assert_eq!(args.len(), 2);
                // First arg should be Final(Var(x))
                assert!(
                    matches!(&args[0], PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "x")),
                    "Expected Final(Var(x)) for first arg, got {:?}",
                    args[0]
                );
                // Second arg should stay as Deref(Var(y))
                assert!(
                    matches!(&args[1], PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "y")),
                    "Expected Deref(Var(y)) for second arg (y not in mut_refs), got {:?}",
                    args[1]
                );
            } else {
                panic!("Expected LogicFnCall, got {right:?}");
            }
        } else {
            panic!("Expected BinOp at top level, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_preserves_annotated_whole_mut_ref_equality() {
        let mut_ref_int = Some(ExprSort::MutRef(Box::new(ExprSort::Int)));
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), mut_ref_int.clone())),
            BinOp::Eq,
            Arc::new(PureExpr::Var("input".to_string(), mut_ref_int.clone())),
        );

        let mut_refs: HashSet<String> = ["result".to_string(), "input".to_string()]
            .into_iter()
            .collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        assert_eq!(
            transformed, postcond,
            "annotated MutRef equality should stay whole-borrow, not rewrite to deref/current"
        );
    }

    #[test]
    fn test_transform_logic_fn_call_inside_old() {
        // old(max(*x, *y)) - both derefs inside Old should stay as Deref
        let postcond = PureExpr::Old(Arc::new(PureExpr::LogicFnCall {
            name: "max".to_string(),
            args: vec![
                PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None))),
                PureExpr::Deref(Arc::new(PureExpr::Var("y".to_string(), None))),
            ],
        }));

        let mut_refs: HashSet<String> = ["x".to_string(), "y".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // Both should stay as Deref inside Old
        if let PureExpr::Old(ref inner) = transformed {
            if let PureExpr::LogicFnCall { args, .. } = inner.as_ref() {
                assert!(
                    matches!(&args[0], PureExpr::Deref(_)),
                    "Expected Deref inside Old, got {:?}",
                    args[0]
                );
                assert!(
                    matches!(&args[1], PureExpr::Deref(_)),
                    "Expected Deref inside Old, got {:?}",
                    args[1]
                );
            } else {
                panic!("Expected LogicFnCall inside Old, got {inner:?}");
            }
        } else {
            panic!("Expected Old at top level, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_view_method_chain() {
        // (*v)@.len() == old((*v)@.len()) + 1 where v is mut ref
        // Should become: (^v)@.len() == old((*v)@.len()) + 1
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("v".to_string(), None),
                ))))),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Old(Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                        PureExpr::Var("v".to_string(), None),
                    ))))),
                    method: "len".to_string(),
                    args: vec![],
                }))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        );

        let mut_refs: HashSet<String> = ["v".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // Check left side: (^v)@.len()
        if let PureExpr::BinOp(ref left, BinOp::Eq, ref right) = transformed {
            if let PureExpr::MethodCall {
                receiver, method, ..
            } = left.as_ref()
            {
                assert_eq!(method, "len");
                // receiver should be View(Final(Var(v)))
                if let PureExpr::View(inner) = receiver.as_ref() {
                    assert!(
                        matches!(inner.as_ref(), PureExpr::Final(var) if matches!(var.as_ref(), PureExpr::Var(n, _) if n == "v")),
                        "Expected View(Final(Var(v))), got View({inner:?})"
                    );
                } else {
                    panic!("Expected View, got {receiver:?}");
                }
            } else {
                panic!("Expected MethodCall on left, got {left:?}");
            }

            // Check right side: old((*v)@.len()) + 1
            if let PureExpr::BinOp(old_part, BinOp::Add, _) = right.as_ref() {
                if let PureExpr::Old(inner_old) = old_part.as_ref() {
                    if let PureExpr::MethodCall { receiver, .. } = inner_old.as_ref() {
                        if let PureExpr::View(inner_view) = receiver.as_ref() {
                            // Inside Old, should stay as Deref
                            assert!(
                                matches!(inner_view.as_ref(), PureExpr::Deref(var) if matches!(var.as_ref(), PureExpr::Var(n, _) if n == "v")),
                                "Expected View(Deref(Var(v))) inside Old, got View({inner_view:?})"
                            );
                        } else {
                            panic!("Expected View inside Old, got {receiver:?}");
                        }
                    } else {
                        panic!("Expected MethodCall inside Old, got {inner_old:?}");
                    }
                } else {
                    panic!("Expected Old on right side, got {old_part:?}");
                }
            } else {
                panic!("Expected BinOp(old(...), Add, 1) on right, got {right:?}");
            }
        } else {
            panic!("Expected BinOp at top level, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_chained_method_calls() {
        // (*v)@.index_logic(0).unwrap() where v is mut ref
        // Should transform to (^v)@.index_logic(0).unwrap()
        let postcond = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("v".to_string(), None),
                ))))),
                method: "index_logic".to_string(),
                args: vec![PureExpr::Int(0)],
            }),
            method: "unwrap".to_string(),
            args: vec![],
        };

        let mut_refs: HashSet<String> = ["v".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // Navigate through: unwrap() -> index_logic() -> view -> final
        if let PureExpr::MethodCall {
            ref receiver,
            ref method,
            ..
        } = transformed
        {
            assert_eq!(method, "unwrap");
            if let PureExpr::MethodCall {
                receiver: inner_recv,
                method: inner_method,
                ..
            } = receiver.as_ref()
            {
                assert_eq!(inner_method, "index_logic");
                if let PureExpr::View(view_inner) = inner_recv.as_ref() {
                    assert!(
                        matches!(view_inner.as_ref(), PureExpr::Final(var) if matches!(var.as_ref(), PureExpr::Var(n, _) if n == "v")),
                        "Expected Final(Var(v)), got {view_inner:?}"
                    );
                } else {
                    panic!("Expected View, got {inner_recv:?}");
                }
            } else {
                panic!("Expected inner MethodCall, got {receiver:?}");
            }
        } else {
            panic!("Expected outer MethodCall, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_trait_path_postcondition_preserves_deref_mut_receiver_arg() {
        // Trait-path postcondition predicate: T::deref_mut.postcondition(x, result)
        // DerefMut specs quantify over the whole `&mut T` receiver, so bare x
        // must stay as x to align with call-site assumptions from trait specs.
        let postcond = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("T::deref_mut".to_string(), None)),
            method: "postcondition".to_string(),
            args: vec![
                PureExpr::Var("x".to_string(), None),
                PureExpr::Var("result".to_string(), None),
            ],
        };

        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        assert!(matches!(
            transformed,
            PureExpr::MethodCall { args, .. }
            if matches!(args.first(), Some(PureExpr::Var(name, _)) if name == "x")
                && matches!(args.get(1), Some(PureExpr::Var(name, _)) if name == "result")
        ));
    }

    #[test]
    fn test_transform_trait_path_postcondition_keeps_non_mut_arg_raw() {
        // Non-mut parameters should remain unchanged.
        let postcond = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("T::deref".to_string(), None)),
            method: "postcondition".to_string(),
            args: vec![
                PureExpr::Var("x".to_string(), None),
                PureExpr::Var("result".to_string(), None),
            ],
        };

        let mut_refs: HashSet<String> = HashSet::new();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);
        assert_eq!(transformed, postcond);
    }

    #[test]
    fn test_transform_nested_old_expressions() {
        // *x == old(old(*x) + 1) - nested Old should preserve inner Deref
        // Note: old(old(...)) is semantically questionable but syntactically valid
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Old(Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("x".to_string(), None),
                ))))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )))),
        );

        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // Left *x should become ^x
        if let PureExpr::BinOp(ref left, BinOp::Eq, ref right) = transformed {
            assert!(
                matches!(left.as_ref(), PureExpr::Final(var) if matches!(var.as_ref(), PureExpr::Var(n, _) if n == "x")),
                "Expected Final(Var(x)) on left, got {left:?}"
            );

            // Right side: old(old(*x) + 1) - inner *x should stay as Deref
            if let PureExpr::Old(outer_inner) = right.as_ref() {
                if let PureExpr::BinOp(inner_old, _, _) = outer_inner.as_ref() {
                    if let PureExpr::Old(inner_inner) = inner_old.as_ref() {
                        assert!(
                            matches!(inner_inner.as_ref(), PureExpr::Deref(_)),
                            "Expected Deref inside nested Old, got {inner_inner:?}"
                        );
                    } else {
                        panic!("Expected inner Old, got {inner_old:?}");
                    }
                } else {
                    panic!("Expected BinOp inside outer Old, got {outer_inner:?}");
                }
            } else {
                panic!("Expected outer Old on right, got {right:?}");
            }
        } else {
            panic!("Expected BinOp at top level, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_ite_with_mut_refs() {
        // if cond { *x } else { *y } where both x and y are mut refs
        // Should become: if cond { ^x } else { ^y }
        let postcond = PureExpr::Ite(
            Arc::new(PureExpr::Var("cond".to_string(), None)),
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "y".to_string(),
                None,
            )))),
        );

        let mut_refs: HashSet<String> = ["x".to_string(), "y".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        if let PureExpr::Ite(_, ref then_branch, ref else_branch) = transformed {
            assert!(
                matches!(then_branch.as_ref(), PureExpr::Final(var) if matches!(var.as_ref(), PureExpr::Var(n, _) if n == "x")),
                "Expected Final(Var(x)) in then branch, got {then_branch:?}"
            );
            assert!(
                matches!(else_branch.as_ref(), PureExpr::Final(var) if matches!(var.as_ref(), PureExpr::Var(n, _) if n == "y")),
                "Expected Final(Var(y)) in else branch, got {else_branch:?}"
            );
        } else {
            panic!("Expected Ite, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_bare_var_mut_ref_to_deref() {
        // `result == ma` where ma is a &mut param
        // Bare Var("ma") should become Deref(Var("ma")) so the SMT
        // encoder produces `ma_current` instead of an unconstrained `ma`. (#609)
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("ma".to_string(), None)),
        );

        let mut_refs: HashSet<String> = ["ma".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // result stays as Var("result") (not a mut ref param)
        // ma becomes Deref(Var("ma"))
        if let PureExpr::BinOp(left, BinOp::Eq, right) = &transformed {
            assert!(
                matches!(left.as_ref(), PureExpr::Var(n, _) if n == "result"),
                "Expected Var(result) on left, got {left:?}"
            );
            assert!(
                matches!(right.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "ma")),
                "Expected Deref(Var(ma)) on right, got {right:?}"
            );
        } else {
            panic!("Expected BinOp(Eq), got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_bare_var_mut_ref_with_explicit_final() {
        // take_max pattern: if *ma >= *mb { *mb == ^mb && result == ma }
        //                   else { *ma == ^ma && result == mb }
        // Both ma, mb have explicit ^, so Deref stays as Deref (current).
        // Bare Var("ma")/Var("mb") should also become Deref (current). (#609)
        let postcond = PureExpr::Ite(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                    "ma".to_string(),
                    None,
                )))),
                BinOp::Ge,
                Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                    "mb".to_string(),
                    None,
                )))),
            )),
            // then: *mb == ^mb && result == ma
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                        "mb".to_string(),
                        None,
                    )))),
                    BinOp::Eq,
                    Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                        "mb".to_string(),
                        None,
                    )))),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("result".to_string(), None)),
                    BinOp::Eq,
                    Arc::new(PureExpr::Var("ma".to_string(), None)),
                )),
            )),
            // else: *ma == ^ma && result == mb
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                        "ma".to_string(),
                        None,
                    )))),
                    BinOp::Eq,
                    Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                        "ma".to_string(),
                        None,
                    )))),
                )),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("result".to_string(), None)),
                    BinOp::Eq,
                    Arc::new(PureExpr::Var("mb".to_string(), None)),
                )),
            )),
        );

        let mut_refs: HashSet<String> = ["ma".to_string(), "mb".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        // Both ma and mb have explicit ^, so they're in explicit_final_vars.
        // Bare Var("ma") → Deref(Var("ma")), bare Var("mb") → Deref(Var("mb")).
        // Deref(Var("ma/mb")) stays as Deref (not Final) because of explicit_final_vars.
        if let PureExpr::Ite(_, then_branch, else_branch) = &transformed {
            // then: *mb == ^mb && result == *ma (Deref)
            if let PureExpr::BinOp(_, BinOp::And, ref_eq) = then_branch.as_ref() {
                if let PureExpr::BinOp(_, BinOp::Eq, rhs) = ref_eq.as_ref() {
                    assert!(
                        matches!(rhs.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "ma")),
                        "Expected Deref(Var(ma)) in then branch, got {rhs:?}"
                    );
                } else {
                    panic!("Expected BinOp(Eq) in then branch, got {ref_eq:?}");
                }
            } else {
                panic!("Expected BinOp(And) in then branch, got {then_branch:?}");
            }
            // else: *ma == ^ma && result == *mb (Deref)
            if let PureExpr::BinOp(_, BinOp::And, ref_eq) = else_branch.as_ref() {
                if let PureExpr::BinOp(_, BinOp::Eq, rhs) = ref_eq.as_ref() {
                    assert!(
                        matches!(rhs.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "mb")),
                        "Expected Deref(Var(mb)) in else branch, got {rhs:?}"
                    );
                } else {
                    panic!("Expected BinOp(Eq) in else branch, got {ref_eq:?}");
                }
            } else {
                panic!("Expected BinOp(And) in else branch, got {else_branch:?}");
            }
        } else {
            panic!("Expected Ite, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_forall_with_mut_ref_in_body() {
        // forall<i: Int> (*v)@.index_logic(i) >= 0 where v is mut ref
        // Should become: forall<i: Int> (^v)@.index_logic(i) >= 0
        let postcond = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                        PureExpr::Var("v".to_string(), None),
                    ))))),
                    method: "index_logic".to_string(),
                    args: vec![PureExpr::Var("i".to_string(), None)],
                }),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![],
        };

        let mut_refs: HashSet<String> = ["v".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        if let PureExpr::Forall {
            ref body, ref var, ..
        } = transformed
        {
            assert_eq!(var, "i");
            if let PureExpr::BinOp(left, BinOp::Ge, _) = body.as_ref() {
                if let PureExpr::MethodCall { receiver, .. } = left.as_ref() {
                    if let PureExpr::View(view_inner) = receiver.as_ref() {
                        assert!(
                            matches!(view_inner.as_ref(), PureExpr::Final(var) if matches!(var.as_ref(), PureExpr::Var(n, _) if n == "v")),
                            "Expected Final(Var(v)) inside forall body, got {view_inner:?}"
                        );
                    } else {
                        panic!("Expected View, got {receiver:?}");
                    }
                } else {
                    panic!("Expected MethodCall, got {left:?}");
                }
            } else {
                panic!("Expected BinOp in forall body, got {body:?}");
            }
        } else {
            panic!("Expected Forall, got {transformed:?}");
        }
    }

    #[test]
    fn test_transform_match_with_mut_ref() {
        // match *opt { Some(v) => *x, None => 0 } where x is mut ref
        // Should become: match *opt { Some(v) => ^x, None => 0 }
        let postcond = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "opt".to_string(),
                None,
            )))),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                    },
                    body: PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None))),
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

        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        if let PureExpr::Match {
            ref scrutinee,
            ref arms,
        } = transformed
        {
            // scrutinee *opt should stay as Deref (opt not in mut_refs)
            assert!(
                matches!(scrutinee.as_ref(), PureExpr::Deref(_)),
                "Expected Deref for scrutinee, got {scrutinee:?}"
            );

            // First arm body (*x) should become ^x
            assert!(
                matches!(&arms[0].body, PureExpr::Final(var) if matches!(var.as_ref(), PureExpr::Var(n, _) if n == "x")),
                "Expected Final(Var(x)) in Some arm, got {:?}",
                arms[0].body
            );

            // Second arm body should stay as Int(0)
            assert_eq!(arms[1].body, PureExpr::Int(0));
        } else {
            panic!("Expected Match, got {transformed:?}");
        }
    }

    // =====================================================================
    // ExprSort preservation through postcondition transforms (#805)
    // =====================================================================

    #[test]
    fn test_transform_postcond_preserves_expr_sort_on_non_mut_ref_var() {
        // Var("y", Some(ExprSort::Bool)) where y is NOT a mut ref param
        // should retain its ExprSort after postcondition transform
        let postcond = PureExpr::Var("y".to_string(), Some(ExprSort::Bool));
        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);
        assert_eq!(
            transformed,
            PureExpr::Var("y".to_string(), Some(ExprSort::Bool)),
            "Postcondition transform must preserve ExprSort on non-mut-ref Var"
        );
    }

    #[test]
    fn test_transform_postcond_preserves_expr_sort_on_mut_ref_deref() {
        // Deref(Var("x", Some(ExprSort::Int))) where x IS a mut ref param
        // should become Final(Var("x", Some(ExprSort::Int)))
        let postcond = PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::Int),
        )));
        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);
        assert_eq!(
            transformed,
            PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                Some(ExprSort::Int)
            ))),
            "Postcondition transform must preserve ExprSort when Deref(Var) → Final(Var)"
        );
    }

    #[test]
    fn test_transform_postcond_preserves_expr_sort_bare_mut_ref() {
        // Bare Var("x", Some(ExprSort::Int)) where x IS a mut ref param
        // should become Deref(Var("x", Some(ExprSort::Int))) per #609 semantics
        let postcond = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);
        assert_eq!(
            transformed,
            PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                Some(ExprSort::Int)
            ))),
            "Postcondition transform must preserve ExprSort when bare mut-ref Var → Deref(Var)"
        );
    }

    #[test]
    fn test_postcond_transform_reuses_unchanged_sibling_arc() {
        // BinOp(*x == y): left changes (Deref→Final for mut ref x),
        // but right (y) is not a mut ref param and should reuse its Arc.
        let right_arc = Arc::new(PureExpr::Var("y".to_string(), None));
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::clone(&right_arc),
        );
        let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
        let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);

        if let PureExpr::BinOp(_, _, ref new_right) = transformed {
            assert!(
                Arc::ptr_eq(&right_arc, new_right),
                "Unchanged sibling Arc should be reused, not reallocated"
            );
        } else {
            panic!("Expected BinOp");
        }
    }

    #[test]
    fn test_postcond_transform_returns_clone_when_no_mut_refs() {
        // When mut_ref_params is empty, no transformations occur.
        // The whole tree should be structurally cloned (reuse_node path).
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );
        let mut_refs: HashSet<String> = HashSet::new();
        let transformed = expr.transform_postcondition_for_mut_refs(&mut_refs);
        assert_eq!(transformed, expr);
    }

    #[test]
    fn test_closure_capture_transform_reuses_unchanged_sibling_arc() {
        // BinOp(self.0 + z): left changes (Var→Final(Deref(...)) for capture self.0),
        // but right (z) is not a capture field and should reuse its Arc.
        let right_arc = Arc::new(PureExpr::Var("z".to_string(), None));
        let postcond = PureExpr::BinOp(
            Arc::new(PureExpr::Var("self.0".to_string(), None)),
            BinOp::Add,
            Arc::clone(&right_arc),
        );
        let captures: HashSet<String> = ["self.0".to_string()].into_iter().collect();
        let transformed = postcond.transform_closure_capture_postcondition(&captures);

        if let PureExpr::BinOp(_, _, ref new_right) = transformed {
            assert!(
                Arc::ptr_eq(&right_arc, new_right),
                "Unchanged sibling Arc should be reused in closure capture transform"
            );
        } else {
            panic!("Expected BinOp");
        }
    }

    #[test]
    fn test_closure_capture_transform_returns_clone_when_no_captures() {
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );
        let captures: HashSet<String> = HashSet::new();
        let transformed = expr.transform_closure_capture_postcondition(&captures);
        assert_eq!(transformed, expr);
    }
}

// Permission scaling tests (Part of #741)
mod permission_scale_tests {
    use super::Permission;

    #[test]
    fn test_one_third_plus_two_thirds_equals_full() {
        // AC: Permission 1/3 + 2/3 sums to full permission
        let one_third = Permission::new(1, 3).unwrap();
        let two_thirds = Permission::new(2, 3).unwrap();
        assert_eq!(
            one_third.scaled_value() + two_thirds.scaled_value(),
            Permission::PERM_SCALE,
            "1/3 + 2/3 must equal PERM_SCALE ({})",
            Permission::PERM_SCALE
        );
    }

    #[test]
    fn test_three_way_one_third_split_equals_full() {
        // AC: Three-way 1/3 split sums to full permission
        let one_third = Permission::new(1, 3).unwrap();
        assert_eq!(
            one_third.scaled_value() * 3,
            Permission::PERM_SCALE,
            "3 × (1/3) must equal PERM_SCALE ({})",
            Permission::PERM_SCALE
        );
    }

    #[test]
    fn test_fractional_permission_round_trip_non_power_of_2() {
        // AC: Fractional permission round-trip for non-power-of-2 denominators
        // PERM_SCALE = 2520 = LCM(1..10), so all denominators 1-10 divide evenly.
        for denom in 1..=10u32 {
            for numer in 1..=denom {
                let perm = Permission::new(numer, denom).unwrap();
                let scaled = perm.scaled_value();
                // Verify no truncation: scaled * denom == numer * PERM_SCALE
                assert_eq!(
                    scaled * i64::from(denom),
                    i64::from(numer) * Permission::PERM_SCALE,
                    "Permission {numer}/{denom}: scaled_value {scaled} doesn't round-trip"
                );
            }
        }
    }

    #[test]
    fn test_half_plus_half_equals_full() {
        let half = Permission::HALF;
        assert_eq!(
            half.scaled_value() * 2,
            Permission::PERM_SCALE,
            "2 × (1/2) must equal PERM_SCALE"
        );
    }

    #[test]
    fn test_full_permission_equals_perm_scale() {
        assert_eq!(
            Permission::FULL.scaled_value(),
            Permission::PERM_SCALE,
            "FULL permission scaled value must equal PERM_SCALE"
        );
    }
}

// =============================================================================
// Performance proofs: substitute() scaling
// =============================================================================

mod performance_proofs {
    use std::{collections::HashMap, time::Instant};

    use super::*;

    /// Build a deeply nested Forall chain: forall x0. forall x1. ... forall xN. body
    fn nested_forall(depth: usize, body: PureExpr) -> PureExpr {
        let mut expr = body;
        for i in (0..depth).rev() {
            expr = PureExpr::Forall {
                var: format!("x{i}"),
                var_sort: None,
                body: Arc::new(expr),
                triggers: vec![],
            };
        }
        expr
    }

    /// Build a match with N arms, each binding a distinct variable.
    fn wide_match(n_arms: usize, body: &PureExpr) -> PureExpr {
        let arms: Vec<MatchArm> = (0..n_arms)
            .map(|i| MatchArm {
                pattern: Pattern::Constructor {
                    name: format!("Arm{i}"),
                    inner: Some(Box::new(Pattern::Binding(format!("arm_var_{i}")))),
                },
                body: body.clone(),
            })
            .collect();
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("scrutinee".to_string(), None)),
            arms,
        }
    }

    /// Substitute scaling: deeply nested Forall chain with large substitution map.
    ///
    /// At each `Forall` boundary, `substitute()` clones the substitution `HashMap` and
    /// removes the bound variable. The documented complexity is O(d × s) where
    /// d = nesting depth and s = substitution map size (#506 F4).
    ///
    /// This test verifies that scaling is at most linear in depth by comparing
    /// depth=10 vs depth=40. O(d): ratio ~4x. O(d²): ratio ~16x.
    /// Threshold: 8x catches quadratic regression.
    #[test]
    fn test_substitute_depth_scaling_linear() {
        let subs: HashMap<String, PureExpr> = (0..20)
            .map(|i| (format!("s{i}"), PureExpr::Int(i)))
            .collect();

        let body = PureExpr::BinOp(
            Arc::new(PureExpr::Var("s0".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("s1".to_string(), None)),
        );

        let small_depth = 10;
        let large_depth = 40;

        let small_expr = nested_forall(small_depth, body.clone());
        let large_expr = nested_forall(large_depth, body.clone());

        // Warm up
        let _ = small_expr.substitute(&subs);

        // Measure small
        let start = Instant::now();
        for _ in 0..100 {
            let _ = small_expr.substitute(&subs);
        }
        let small_time = start.elapsed();

        // Measure large
        let start = Instant::now();
        for _ in 0..100 {
            let _ = large_expr.substitute(&subs);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        let ratio = large_time.as_secs_f64() / small_secs;

        // O(d): expect ~4x (40/10). O(d²): expect ~16x.
        assert!(
            ratio < 8.0,
            "substitute() depth scaling: {large_depth}/{small_depth} = {ratio:.1}x. \
             Expected ~4x (O(d)), threshold 8x. If exceeded, HashMap cloning may \
             have regressed from O(d×s) to O(d²×s)."
        );
    }

    /// Substitute scaling: wide Match with many arms.
    ///
    /// Each match arm clones the substitution `HashMap`. For a match with `N` arms,
    /// this is `O(N × s)`. This test verifies linear scaling in arm count.
    #[test]
    fn test_substitute_match_arms_scaling_linear() {
        let subs: HashMap<String, PureExpr> = (0..20)
            .map(|i| (format!("s{i}"), PureExpr::Int(i)))
            .collect();

        let body = PureExpr::Var("s0".to_string(), None);

        let small_arms = 5;
        let large_arms = 20;

        let small_expr = wide_match(small_arms, &body);
        let large_expr = wide_match(large_arms, &body);

        // Warm up
        let _ = small_expr.substitute(&subs);

        // Measure small
        let start = Instant::now();
        for _ in 0..200 {
            let _ = small_expr.substitute(&subs);
        }
        let small_time = start.elapsed();

        // Measure large
        let start = Instant::now();
        for _ in 0..200 {
            let _ = large_expr.substitute(&subs);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        let ratio = large_time.as_secs_f64() / small_secs;

        // O(N): expect ~4x (20/5). O(N²): expect ~16x.
        assert!(
            ratio < 8.0,
            "substitute() match-arm scaling: {large_arms}/{small_arms} = {ratio:.1}x. \
             Expected ~4x (O(N)), threshold 8x."
        );
    }

    /// Substitute scaling: large substitution map size.
    ///
    /// `HashMap::clone()` is `O(s)` where `s` is the number of entries. This test
    /// verifies that `substitute()` with a large map at constant depth scales
    /// linearly in map size.
    #[test]
    fn test_substitute_map_size_scaling_linear() {
        let small_size = 10;
        let large_size = 40;

        let small_subs: HashMap<String, PureExpr> = (0..small_size)
            .map(|i| (format!("s{i}"), PureExpr::Int(i)))
            .collect();
        let large_subs: HashMap<String, PureExpr> = (0..large_size)
            .map(|i| (format!("s{i}"), PureExpr::Int(i)))
            .collect();

        // Fixed depth=5 Forall chain
        let body = PureExpr::Var("s0".to_string(), None);
        let expr = nested_forall(5, body);

        // Warm up
        let _ = expr.substitute(&small_subs);

        // Measure small
        let start = Instant::now();
        for _ in 0..200 {
            let _ = expr.substitute(&small_subs);
        }
        let small_time = start.elapsed();

        // Measure large
        let start = Instant::now();
        for _ in 0..200 {
            let _ = expr.substitute(&large_subs);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        let ratio = large_time.as_secs_f64() / small_secs;

        // O(s): expect ~4x (40/10). O(s²): expect ~16x.
        assert!(
            ratio < 8.0,
            "substitute() map-size scaling: {large_size}/{small_size} = {ratio:.1}x. \
             Expected ~4x (O(s)), threshold 8x."
        );
    }

    /// Capture-avoiding substitution scaling: many visible values all mentioning
    /// the same binder name.
    ///
    /// Before #2484, each binder boundary rescanned every visible value AST to
    /// check for captures. With the free-var cache, the capture check is O(1)
    /// from the aggregate counter. This test verifies that scaling remains
    /// linear when the number of visible substitution values grows.
    #[test]
    fn test_capture_avoiding_visible_values_scaling_linear() {
        use crate::formula::substitute::CaptureAvoidingSubstOptions;

        // Build substitution maps of different sizes where every value
        // mentions "x" as a free variable. The capture-avoiding engine must
        // check whether "x" (the binder name) appears free in any visible
        // substitution value at each binder boundary.
        let small_size = 10usize;
        let large_size = 40usize;

        let make_subs = |n: usize| -> HashMap<String, PureExpr> {
            (0..n)
                .map(|i| {
                    (
                        format!("s{i}"),
                        PureExpr::BinOp(
                            Arc::new(PureExpr::Var("x".to_string(), None)),
                            BinOp::Add,
                            Arc::new(PureExpr::Int(i64::try_from(i).unwrap())),
                        ),
                    )
                })
                .collect()
        };

        let small_subs = make_subs(small_size);
        let large_subs = make_subs(large_size);
        let options = CaptureAvoidingSubstOptions::default();

        // Expr: forall x. forall x. ... forall x. (s0 + s1)
        // 5 nested quantifiers all binding "x", triggering capture checks.
        let body = PureExpr::BinOp(
            Arc::new(PureExpr::Var("s0".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("s1".to_string(), None)),
        );
        let expr = nested_forall(5, body);

        // Warm up
        let _ = expr.substitute_capture_avoiding(&small_subs, &options);

        // Measure small
        let start = Instant::now();
        for _ in 0..100 {
            let _ = expr.substitute_capture_avoiding(&small_subs, &options);
        }
        let small_time = start.elapsed();

        // Measure large
        let start = Instant::now();
        for _ in 0..100 {
            let _ = expr.substitute_capture_avoiding(&large_subs, &options);
        }
        let large_time = start.elapsed();

        let small_secs = small_time.as_secs_f64().max(1e-12);
        let ratio = large_time.as_secs_f64() / small_secs;

        // Without cache: O(s × d) per binder → O(s² × d) total. Ratio ~16x.
        // With cache: O(s) precompute + O(1) per binder. Ratio ~4x.
        // Threshold 8x catches quadratic regression.
        assert!(
            ratio < 8.0,
            "capture-avoiding visible-values scaling: {large_size}/{small_size} = {ratio:.1}x. \
             Expected ~4x (O(s) precompute), threshold 8x. If exceeded, the \
             free-var cache may have regressed to per-binder AST scanning."
        );
    }
}

// ====================================================================
// Named struct constructor encoding/parsing tests (#1819)
// ====================================================================

#[test]
fn test_named_struct_ctor_name_roundtrip() {
    use super::{named_struct_ctor_name, parse_named_struct_ctor};

    let fields = vec!["x".to_string(), "y".to_string()];
    let name = named_struct_ctor_name("Point", &fields);
    assert_eq!(name, "Point{x,y}");

    let parsed = parse_named_struct_ctor(&name);
    assert_eq!(parsed, Some(("Point", vec!["x", "y"])));
}

#[test]
fn test_named_struct_ctor_single_field() {
    use super::{named_struct_ctor_name, parse_named_struct_ctor};

    let fields = vec!["val".to_string()];
    let name = named_struct_ctor_name("Wrapper", &fields);
    assert_eq!(name, "Wrapper{val}");

    let parsed = parse_named_struct_ctor(&name);
    assert_eq!(parsed, Some(("Wrapper", vec!["val"])));
}

#[test]
fn test_named_struct_ctor_qualified_path() {
    use super::{named_struct_ctor_name, parse_named_struct_ctor};

    let fields = vec!["b".to_string()];
    let name = named_struct_ctor_name("Sum::B", &fields);
    assert_eq!(name, "Sum::B{b}");

    let parsed = parse_named_struct_ctor(&name);
    assert_eq!(parsed, Some(("Sum::B", vec!["b"])));
}

#[test]
fn test_parse_named_struct_ctor_rejects_plain_name() {
    use super::parse_named_struct_ctor;

    // Plain constructor names (no braces) should return None
    assert_eq!(parse_named_struct_ctor("Point"), None);
    assert_eq!(parse_named_struct_ctor("Some"), None);
    assert_eq!(parse_named_struct_ctor("Sum::A"), None);
}

#[test]
fn test_named_struct_ctor_empty_fields() {
    use super::{named_struct_ctor_name, parse_named_struct_ctor};

    let fields: Vec<String> = vec![];
    let name = named_struct_ctor_name("Unit", &fields);
    assert_eq!(name, "Unit{}");

    let parsed = parse_named_struct_ctor(&name);
    assert_eq!(parsed, Some(("Unit", vec![])));
}

// ─── Recursive Drop depth tests (#2130) ──────────────────────────────────────
//
// PureExpr and Formula use derived `Drop` which recurses one stack frame per
// `Box<_>` nesting level. Left-recursive chains (e.g., And(And(And(...), _), _))
// can cause stack overflow during drop if sufficiently deep.
//
// These tests establish the current depth limits. They are NOT expected to fail
// under normal verification (MAX_ENCODING_DEPTH = 128 bounds production trees),
// but document the vulnerability for pathological inputs.

/// Build a left-recursive `Formula::And` chain of the given depth.
fn make_left_recursive_and_chain(depth: usize) -> Formula {
    let mut f = Formula::True;
    for _ in 0..depth {
        f = Formula::And(Arc::new(f), Arc::new(Formula::True));
    }
    f
}

/// Build a left-recursive `PureExpr::BinOp` chain of the given depth.
fn make_left_recursive_binop_chain(depth: usize) -> PureExpr {
    let mut e = PureExpr::Bool(true);
    for _ in 0..depth {
        e = PureExpr::BinOp(Arc::new(e), BinOp::And, Arc::new(PureExpr::Bool(true)));
    }
    e
}

#[test]
fn recursive_drop_formula_and_chain_within_encoding_depth() {
    // 128 = MAX_ENCODING_DEPTH — this is the maximum depth the encoder will produce.
    // This MUST succeed without stack overflow.
    let chain = make_left_recursive_and_chain(128);
    drop(chain);
}

#[test]
fn recursive_drop_pure_expr_binop_chain_within_encoding_depth() {
    let chain = make_left_recursive_binop_chain(128);
    drop(chain);
}

#[test]
fn recursive_drop_formula_1000_depth_on_default_stack() {
    // 1000 depth is well within normal 2MB thread stack limits.
    // This tests that moderate over-depth trees are safe to drop.
    let chain = make_left_recursive_and_chain(1000);
    drop(chain);
}

#[test]
fn recursive_drop_pure_expr_1000_depth_on_default_stack() {
    let chain = make_left_recursive_binop_chain(1000);
    drop(chain);
}

/// Verify that left-recursive `Formula` chains at `10x MAX_ENCODING_DEPTH`
/// (1280) can be safely constructed and dropped on the default test thread
/// stack (2MB). This is well beyond the maximum depth the encoder will
/// produce in practice.
///
/// NOTE: A much deeper chain (50,000+) on a small stack (256KB) causes
/// SIGABRT (stack overflow during recursive Drop). Rust's derived Drop
/// recurses one frame per Box nesting level, and stack overflow is not
/// catchable via `catch_unwind` - it aborts the process. An iterative `Drop`
/// that walks the left spine in a loop (as done by the `syn` crate) would
/// fix this. Filed as a known limitation.
#[test]
fn recursive_drop_formula_10x_encoding_depth_safe() {
    let chain = make_left_recursive_and_chain(1280);
    drop(chain);
}

#[test]
fn recursive_drop_pure_expr_10x_encoding_depth_safe() {
    let chain = make_left_recursive_binop_chain(1280);
    drop(chain);
}

/// Clone a deep Formula chain and verify both copies drop safely.
/// This tests that derived Clone + derived Drop interact correctly —
/// no double-free or pointer invalidation when both copies are dropped.
#[test]
fn recursive_drop_formula_clone_and_drop_both_copies() {
    let chain = make_left_recursive_and_chain(500);
    let clone = chain.clone();
    drop(chain);
    drop(clone);
}

#[test]
fn recursive_drop_pure_expr_clone_and_drop_both_copies() {
    let chain = make_left_recursive_binop_chain(500);
    let clone = chain.clone();
    drop(chain);
    drop(clone);
}

// =============================================================================
// FloatBits tests
// =============================================================================

#[test]
#[allow(clippy::approx_constant)]
fn float_bits_from_f64_roundtrip() {
    let fb = FloatBits::from_f64(3.14);
    let v = fb.to_f64();
    assert!((v - 3.14).abs() < f64::EPSILON);
}

#[test]
fn float_bits_from_f32_lossless_promotion() {
    let fb = FloatBits::from_f32(1.5_f32);
    assert!((fb.to_f64() - 1.5).abs() < f64::EPSILON);
}

#[test]
#[allow(clippy::float_cmp)]
fn float_bits_zero() {
    let fb = FloatBits::from_f64(0.0);
    assert_eq!(fb.to_f64(), 0.0);
    assert_eq!(fb.0, 0);
}

#[test]
fn float_bits_negative_zero() {
    let fb = FloatBits::from_f64(-0.0);
    // -0.0 has a different bit pattern than +0.0
    assert_ne!(fb, FloatBits::from_f64(0.0));
}

#[test]
fn float_bits_nan_representable() {
    let fb = FloatBits::from_f64(f64::NAN);
    assert!(fb.to_f64().is_nan());
}

#[test]
fn float_bits_infinity() {
    let fb_pos = FloatBits::from_f64(f64::INFINITY);
    let fb_neg = FloatBits::from_f64(f64::NEG_INFINITY);
    assert!(fb_pos.to_f64().is_infinite());
    assert!(fb_neg.to_f64().is_infinite());
    assert_ne!(fb_pos, fb_neg);
}

#[test]
fn float_bits_display() {
    let fb = FloatBits::from_f64(2.5);
    assert_eq!(format!("{fb}"), "2.5");
}

#[test]
fn float_bits_equality_matches_bits() {
    let a = FloatBits::from_f64(1.0);
    let b = FloatBits::from_f64(1.0);
    assert_eq!(a, b);
    assert_eq!(a.0, b.0);
}

// =============================================================================
// int_bounds tests
// =============================================================================

#[test]
fn pow2_expr_zero() {
    assert_eq!(pow2_expr(0), PureExpr::Int(1));
}

#[test]
fn pow2_expr_one() {
    assert_eq!(pow2_expr(1), PureExpr::Int(2));
}

#[test]
fn pow2_expr_two() {
    // 2^2 = 4 = 2*2 (via squaring)
    let result = pow2_expr(2);
    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::Int(2)),
            BinOp::Mul,
            Arc::new(PureExpr::Int(2)),
        )
    );
}

#[test]
fn pow2_expr_three() {
    // 2^3 = 2 * (2^1)^2 = 2 * (2*2)
    let squared = PureExpr::BinOp(
        Arc::new(PureExpr::Int(2)),
        BinOp::Mul,
        Arc::new(PureExpr::Int(2)),
    );
    assert_eq!(
        pow2_expr(3),
        PureExpr::BinOp(Arc::new(PureExpr::Int(2)), BinOp::Mul, Arc::new(squared),)
    );
}

#[test]
fn unsigned_max_expr_zero_bits() {
    assert_eq!(unsigned_max_expr(0), PureExpr::Int(0));
}

#[test]
fn unsigned_max_expr_8_bits() {
    // u8::MAX = 255
    assert_eq!(unsigned_max_expr(8), PureExpr::Int(255));
}

#[test]
fn unsigned_max_expr_32_bits() {
    // u32::MAX = 4294967295
    assert_eq!(unsigned_max_expr(32), PureExpr::Int(4_294_967_295));
}

#[test]
fn unsigned_max_expr_63_bits_literal() {
    // 63 bits => literal path (fits in i64)
    let result = unsigned_max_expr(63);
    assert!(matches!(result, PureExpr::Int(_)));
}

#[test]
fn unsigned_max_expr_64_bits_symbolic() {
    // 64 bits => symbolic path (doesn't fit in i64)
    let result = unsigned_max_expr(64);
    assert!(matches!(result, PureExpr::BinOp(_, BinOp::Sub, _)));
}

#[test]
fn signed_bounds_expr_zero_bits() {
    let (min, max) = signed_bounds_expr(0);
    assert_eq!(min, PureExpr::Int(0));
    assert_eq!(max, PureExpr::Int(0));
}

#[test]
fn signed_bounds_expr_8_bits() {
    let (min, max) = signed_bounds_expr(8);
    assert_eq!(min, PureExpr::Int(-128));
    assert_eq!(max, PureExpr::Int(127));
}

#[test]
fn signed_bounds_expr_32_bits() {
    let (min, max) = signed_bounds_expr(32);
    assert_eq!(min, PureExpr::Int(-2_147_483_648));
    assert_eq!(max, PureExpr::Int(2_147_483_647));
}

#[test]
fn signed_bounds_expr_64_bits_literal() {
    let (min, max) = signed_bounds_expr(64);
    assert_eq!(min, PureExpr::Int(i64::MIN));
    assert_eq!(max, PureExpr::Int(i64::MAX));
}

#[test]
fn signed_bounds_expr_128_bits_symbolic() {
    let (min, max) = signed_bounds_expr(128);
    // 128-bit => symbolic (> 64)
    assert!(matches!(min, PureExpr::BinOp(_, BinOp::Sub, _)));
    assert!(matches!(max, PureExpr::BinOp(_, BinOp::Sub, _)));
}

// =============================================================================
// NamedBindingValue tests
// =============================================================================

#[test]
fn named_binding_value_new() {
    let nbv = NamedBindingValue::new(Some(ExprSort::Int), PureExpr::Int(42));
    assert_eq!(nbv.sort, Some(ExprSort::Int));
    assert_eq!(nbv.value, PureExpr::Int(42));
}

#[test]
fn named_binding_value_untyped() {
    let nbv = NamedBindingValue::untyped(PureExpr::Bool(true));
    assert_eq!(nbv.sort, None);
    assert_eq!(nbv.value, PureExpr::Bool(true));
}

#[test]
fn named_binding_value_lhs_var_with_sort() {
    let nbv = NamedBindingValue::new(Some(ExprSort::Seq), PureExpr::Int(0));
    let lhs = nbv.lhs_var("my_seq");
    assert_eq!(
        lhs,
        PureExpr::Var("my_seq".to_string(), Some(ExprSort::Seq))
    );
}

#[test]
fn named_binding_value_lhs_var_untyped() {
    let nbv = NamedBindingValue::untyped(PureExpr::Int(0));
    let lhs = nbv.lhs_var("x");
    assert_eq!(lhs, PureExpr::Var("x".to_string(), None));
}
