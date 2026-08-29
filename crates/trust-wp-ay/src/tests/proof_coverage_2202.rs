// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof coverage tests for untested code paths identified in P1-107 audit.
//!
//! Coverage gaps addressed:
//! 1. `canonicalize_mut_ref_vars` — soundness-critical bare Var→Deref rewriting (#431, #598)
//! 2. `produces_axioms` visited_sort != seq_sort early return
//!
//! `skolemize_negated_universal` tests are in `proof_coverage_skolemize.rs`.
//! `aggregate_slice_results` tests are inline in `verify/obligation_slices.rs`.
//!
//! Part of #2202, #2106

// ─── canonicalize_mut_ref_vars tests ────────────────────────────────

mod canonicalize_mut_ref_vars {
    use std::{collections::HashSet, sync::Arc};

    use ntest::timeout;
    use trust_wp_core::formula::{BinOp, ExprSort, MatchArm, Pattern, PureExpr, UnOp};

    use crate::verify::mut_borrow::helpers::canonicalize_mut_ref_vars;

    #[test]
    #[timeout(30000)]
    fn bare_mut_ref_param_becomes_deref() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Var("x".to_string(), None);
        let result = canonicalize_mut_ref_vars(&expr, &params);
        assert!(
            matches!(&result, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, None) if name == "x")),
            "bare Var(x) where x is a mut-ref param should become Deref(Var(x)), got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn non_param_var_unchanged() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Var("y".to_string(), None);
        let result = canonicalize_mut_ref_vars(&expr, &params);
        assert_eq!(result, expr, "non-param Var(y) should be unchanged");
    }

    #[test]
    #[timeout(30000)]
    fn deref_param_not_double_wrapped() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));
        let result = canonicalize_mut_ref_vars(&expr, &params);
        assert!(
            matches!(&result, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "x")),
            "already-deref'd Var should not be double-wrapped, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn final_param_not_wrapped() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)));
        let result = canonicalize_mut_ref_vars(&expr, &params);
        assert!(
            matches!(&result, PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "x")),
            "Final(Var(x)) should not be modified, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn recurses_through_binop() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        );
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::BinOp(l, BinOp::Gt, _) => {
                assert!(
                    matches!(l.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "x")),
                    "lhs should be Deref(Var(x)), got {l:?}"
                );
            }
            _ => panic!("expected BinOp, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn recurses_through_method_call() {
        let params: HashSet<&str> = ["v"].into_iter().collect();
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
            method: "len".to_string(),
            args: vec![],
        };
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::MethodCall { receiver, .. } => {
                assert!(
                    matches!(receiver.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "v")),
                    "receiver should be Deref(Var(v)), got {receiver:?}"
                );
            }
            _ => panic!("expected MethodCall, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn let_binding_shadows_param() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::Int(42)),
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
        };
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::Let { body, .. } => {
                assert!(
                    matches!(body.as_ref(), PureExpr::Var(name, _) if name == "x"),
                    "shadowed x in let body should remain Var(x), got {body:?}"
                );
            }
            _ => panic!("expected Let, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn forall_binding_shadows_param() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![],
        };
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::Forall { body, .. } => match body.as_ref() {
                PureExpr::BinOp(lhs, _, _) => {
                    assert!(
                        matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "x"),
                        "quantified x should remain Var(x), got {lhs:?}"
                    );
                }
                _ => panic!("expected BinOp in forall body, got {body:?}"),
            },
            _ => panic!("expected Forall, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn exists_binding_shadows_param() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Exists {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
            triggers: vec![],
        };
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::Exists { body, .. } => {
                assert!(
                    matches!(body.as_ref(), PureExpr::Var(name, _) if name == "x"),
                    "quantified x should remain Var(x), got {body:?}"
                );
            }
            _ => panic!("expected Exists, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn match_arm_binding_shadows_param() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("y".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Binding("x".to_string()),
                body: PureExpr::Var("x".to_string(), None),
            }],
        };
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::Match { arms, .. } => {
                assert!(
                    matches!(&arms[0].body, PureExpr::Var(name, _) if name == "x"),
                    "pattern-bound x should remain Var(x), got {:?}",
                    arms[0].body
                );
            }
            _ => panic!("expected Match, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn closure_param_shadows_mut_ref_param() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Closure {
            params: vec![("x".to_string(), None)],
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
        };
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::Closure { body, .. } => {
                assert!(
                    matches!(body.as_ref(), PureExpr::Var(name, _) if name == "x"),
                    "closure-param x should remain Var(x), got {body:?}"
                );
            }
            _ => panic!("expected Closure, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn multiple_params_all_rewritten() {
        let params: HashSet<&str> = ["a", "b"].into_iter().collect();
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("b".to_string(), None)),
        );
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::BinOp(l, _, r) => {
                assert!(
                    matches!(l.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "a")),
                    "a should be Deref(Var(a)), got {l:?}"
                );
                assert!(
                    matches!(r.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "b")),
                    "b should be Deref(Var(b)), got {r:?}"
                );
            }
            _ => panic!("expected BinOp, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn empty_params_no_rewriting() {
        let params: HashSet<&str> = HashSet::new();
        let expr = PureExpr::Var("x".to_string(), None);
        let result = canonicalize_mut_ref_vars(&expr, &params);
        assert_eq!(result, expr, "empty params should produce no rewriting");
    }

    #[test]
    #[timeout(30000)]
    fn sort_annotation_preserved() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Var("x".to_string(), Some(ExprSort::Bool));
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::Deref(inner) => {
                assert!(
                    matches!(inner.as_ref(), PureExpr::Var(_, Some(ExprSort::Bool))),
                    "sort annotation should be preserved, got {inner:?}"
                );
            }
            _ => panic!("expected Deref, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn old_wrapper_recurses() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::Old(Arc::new(PureExpr::Var("x".to_string(), None)));
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::Old(inner) => {
                assert!(
                    matches!(inner.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "x")),
                    "Old should recurse into Deref(Var(x)), got {inner:?}"
                );
            }
            _ => panic!("expected Old, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn unop_recurses() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(PureExpr::Var("x".to_string(), None)));
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::UnOp(UnOp::Neg, inner) => {
                assert!(
                    matches!(inner.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "x")),
                    "UnOp should recurse into Deref(Var(x)), got {inner:?}"
                );
            }
            _ => panic!("expected UnOp, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn let_assume_recurses() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::Var("x".to_string(), None)),
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
        };
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::LetAssume { assumption, body } => {
                assert!(
                    matches!(assumption.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "x")),
                    "assumption should be Deref(Var(x)), got {assumption:?}"
                );
                assert!(
                    matches!(body.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "x")),
                    "body should be Deref(Var(x)), got {body:?}"
                );
            }
            _ => panic!("expected LetAssume, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn let_obligation_recurses() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::LetObligation {
            obligation: Arc::new(PureExpr::Var("x".to_string(), None)),
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
        };
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::LetObligation { obligation, body } => {
                assert!(
                    matches!(obligation.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "x")),
                    "obligation should be Deref(Var(x)), got {obligation:?}"
                );
                assert!(
                    matches!(body.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "x")),
                    "body should be Deref(Var(x)), got {body:?}"
                );
            }
            _ => panic!("expected LetObligation, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn view_wrapper_recurses() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)));
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::View(inner) => {
                assert!(
                    matches!(inner.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "x")),
                    "View should recurse into Deref(Var(x)), got {inner:?}"
                );
            }
            _ => panic!("expected View, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn logic_fn_call_recurses_args() {
        let params: HashSet<&str> = ["x"].into_iter().collect();
        let expr = PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        };
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::LogicFnCall { args, .. } => {
                assert!(
                    matches!(&args[0], PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "x")),
                    "arg should be Deref(Var(x)), got {:?}",
                    args[0]
                );
            }
            _ => panic!("expected LogicFnCall, got {result:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn ite_recurses_all_branches() {
        let params: HashSet<&str> = ["c", "t", "e"].into_iter().collect();
        let expr = PureExpr::Ite(
            Arc::new(PureExpr::Var("c".to_string(), None)),
            Arc::new(PureExpr::Var("t".to_string(), None)),
            Arc::new(PureExpr::Var("e".to_string(), None)),
        );
        let result = canonicalize_mut_ref_vars(&expr, &params);
        match &result {
            PureExpr::Ite(c, t, e) => {
                assert!(
                    matches!(c.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "c")),
                    "cond should be Deref(Var(c)), got {c:?}"
                );
                assert!(
                    matches!(t.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "t")),
                    "then should be Deref(Var(t)), got {t:?}"
                );
                assert!(
                    matches!(e.as_ref(), PureExpr::Deref(v) if matches!(v.as_ref(), PureExpr::Var(name, _) if name == "e")),
                    "else should be Deref(Var(e)), got {e:?}"
                );
            }
            _ => panic!("expected Ite, got {result:?}"),
        }
    }
}

// ─── produces_axioms wrong-sort early returns ───────────────────────

mod produces_axioms_guards {
    use ntest::timeout;

    use crate::{tests::helpers::*, AYEncoder, EncodingError};

    /// Produces with a non-Seq visited arg should surface an EncodingError
    /// instead of letting the ay sort mismatch unwind past the encoder.
    ///
    /// Regression for #994: the sort-drift retry may widen receiver / successor
    /// state slots, but it must keep the `visited` slot pinned to Seq.
    #[test]
    #[timeout(30000)]
    fn produces_with_non_seq_visited_sort_returns_error_without_unwind() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let non_seq_produces = method_call(var("iter"), "produces", vec![int(42), var("iter2")]);

        let err = encoder
            .encode_pure(&non_seq_produces)
            .expect_err("produces with Int-sorted visited arg should return an EncodingError");

        match err {
            EncodingError::SolverError { message, .. } => {
                assert!(
                    message.contains("sort mismatch in method_call::produces"),
                    "expected produces sort mismatch to stay on the EncodingError path: {message}"
                );
            }
            other => panic!("expected SolverError for non-Seq visited arg, got {other:?}"),
        }
    }

    /// Produces with heterogeneous state sorts (state_sort != succ_sort)
    /// should skip axiom assertion.
    #[test]
    #[timeout(30000)]
    fn produces_heterogeneous_state_sorts_no_panic() {
        use crate::ExprSort;

        let mut encoder = AYEncoder::new_with_quantifiers();

        let bool_state = var_with_sort("b_iter", ExprSort::Bool);
        let het_produces = method_call(
            bool_state,
            "produces",
            vec![view(var("visited")), var("int_iter")],
        );
        encoder.register_sort_hints(std::slice::from_ref(&het_produces));
        let result = encoder.encode_pure(&het_produces);
        assert!(
            result.is_ok(),
            "produces with heterogeneous state sorts should encode without panic: {result:?}"
        );
    }
}
