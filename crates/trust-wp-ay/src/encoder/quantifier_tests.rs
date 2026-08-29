// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for quantifier encoding: constructor equality elimination, constructor
//! argument sort inference, and formula trigger synthesis.
//!
//! Extracted from `quantifier.rs` as part of #1669 structural decomposition.

#[cfg(test)]
mod multi_var_constructor_eq_tests {
    use std::sync::Arc;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use ntest::timeout;
    use trust_wp_core::formula::{BinOp, PureExpr};

    use crate::{
        encoder::{quantifier::QuantifierKind, quantifier_ctor_elim::ConstructorEqInfo, AYEncoder},
        tests::helpers::{and, eq, gt, implies, logic_fn_call, var},
    };

    fn pair_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "MyPair".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Pair".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "fst".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "snd".to_string(),
                        sort: Sort::Int,
                    },
                ],
            }],
        }
    }

    fn triple_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "Triple".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Triple".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "a".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "b".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "c".to_string(),
                        sort: Sort::Int,
                    },
                ],
            }],
        }
    }

    fn state_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "State".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "On".to_string(),
                    fields: vec![],
                },
                DatatypeConstructor {
                    name: "Off".to_string(),
                    fields: vec![],
                },
            ],
        }
    }

    /// exists<k, v> x == Pair(k, v) should eliminate to the reconstruction
    /// equality for a single-constructor datatype.
    #[test]
    #[timeout(30000)]
    fn exists_two_var_pair_eliminates_to_reconstruction_eq() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = pair_datatype();
        encoder.ensure_datatype_declared(&dt);
        let x_term = encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let body_inner = eq(
            var("x"),
            logic_fn_call("MyPair::Pair", vec![var("k"), var("v")]),
        );
        let inner = PureExpr::Exists {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(body_inner),
            triggers: vec![],
        };
        let outer = PureExpr::Exists {
            var: "k".to_string(),
            var_sort: None,
            body: Arc::new(inner),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&outer);
        assert!(result.is_ok(), "encoding should succeed: {result:?}");

        let fst = encoder
            .solver
            .try_datatype_selector("fst", x_term, Sort::Int)
            .expect("fst selector");
        let snd = encoder
            .solver
            .try_datatype_selector("snd", x_term, Sort::Int)
            .expect("snd selector");
        let reconstructed =
            encoder
                .solver
                .datatype_constructor(&pair_datatype(), "Pair", &[fst, snd]);
        let expected = encoder.eq_term(x_term, reconstructed);
        assert_eq!(
            result.unwrap(),
            expected,
            "should eliminate to reconstruction equality"
        );
    }

    /// forall<k, v> x == Pair(k, v) ==> k > v should eliminate to
    /// is_pair(x) ==> fst(x) > snd(x).
    #[test]
    #[timeout(30000)]
    fn forall_two_var_pair_eliminates_with_selectors() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = pair_datatype();
        encoder.ensure_datatype_declared(&dt);
        let x_term = encoder
            .get_or_declare_var("x", Sort::Datatype(dt.clone()))
            .expect("declare x");

        let consequent = gt(var("k"), var("v"));
        let guard = eq(
            var("x"),
            logic_fn_call("MyPair::Pair", vec![var("k"), var("v")]),
        );
        let body_inner = implies(guard, consequent);
        let inner = PureExpr::Forall {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(body_inner),
            triggers: vec![],
        };
        let outer = PureExpr::Forall {
            var: "k".to_string(),
            var_sort: None,
            body: Arc::new(inner),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&outer);
        assert!(result.is_ok(), "encoding should succeed: {result:?}");

        let tester = encoder
            .solver
            .try_datatype_tester("Pair", x_term)
            .expect("tester");
        let fst = encoder
            .solver
            .try_datatype_selector("fst", x_term, Sort::Int)
            .expect("fst selector");
        let snd = encoder
            .solver
            .try_datatype_selector("snd", x_term, Sort::Int)
            .expect("snd selector");
        let expected_consequent = encoder.solver.gt(fst, snd);
        let expected = encoder.solver.implies(tester, expected_consequent);
        assert_eq!(result.unwrap(), expected, "should eliminate with selectors");
    }

    /// exists<a, b, c> x == Triple(a, b, c) should eliminate to the
    /// reconstruction equality for a single-constructor datatype.
    #[test]
    #[timeout(30000)]
    fn exists_three_var_triple_eliminates_to_reconstruction_eq() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = triple_datatype();
        encoder.ensure_datatype_declared(&dt);
        let x_term = encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let body = eq(
            var("x"),
            logic_fn_call("Triple::Triple", vec![var("a"), var("b"), var("c")]),
        );
        let level_c = PureExpr::Exists {
            var: "c".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };
        let level_b = PureExpr::Exists {
            var: "b".to_string(),
            var_sort: None,
            body: Arc::new(level_c),
            triggers: vec![],
        };
        let level_a = PureExpr::Exists {
            var: "a".to_string(),
            var_sort: None,
            body: Arc::new(level_b),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&level_a);
        assert!(result.is_ok(), "encoding should succeed: {result:?}");

        let fst = encoder
            .solver
            .try_datatype_selector("a", x_term, Sort::Int)
            .expect("a selector");
        let snd = encoder
            .solver
            .try_datatype_selector("b", x_term, Sort::Int)
            .expect("b selector");
        let trd = encoder
            .solver
            .try_datatype_selector("c", x_term, Sort::Int)
            .expect("c selector");
        let reconstructed =
            encoder
                .solver
                .datatype_constructor(&triple_datatype(), "Triple", &[fst, snd, trd]);
        let expected = encoder.eq_term(x_term, reconstructed);
        assert_eq!(
            result.unwrap(),
            expected,
            "should eliminate to reconstruction equality"
        );
    }

    /// exists<v> x == On should eliminate to is_on(x) even when the parser
    /// produced the nullary constructor as a bare Var. (#1982)
    #[test]
    #[timeout(30000)]
    fn exists_nullary_bare_var_constructor_eliminates_to_tester() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = state_datatype();
        encoder.ensure_datatype_declared(&dt.clone());
        let x_term = encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let body = eq(var("x"), var("On"));
        let outer = PureExpr::Exists {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&outer);
        assert!(result.is_ok(), "encoding should succeed: {result:?}");

        let tester = encoder
            .solver
            .try_datatype_tester("On", x_term)
            .expect("tester should exist");
        assert_eq!(result.unwrap(), tester, "should eliminate to is_on(x)");
    }

    /// Qualified nullary constructors should follow the same elimination path
    /// as the bare parser token when the datatype is already declared. (#1982)
    #[test]
    #[timeout(30000)]
    fn exists_nullary_logic_fn_constructor_eliminates_to_tester() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = state_datatype();
        encoder.ensure_datatype_declared(&dt.clone());
        let x_term = encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let body = eq(var("x"), logic_fn_call("State::On", vec![]));
        let outer = PureExpr::Exists {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&outer);
        assert!(result.is_ok(), "encoding should succeed: {result:?}");

        let tester = encoder
            .solver
            .try_datatype_tester("On", x_term)
            .expect("tester should exist");
        assert_eq!(result.unwrap(), tester, "should eliminate to is_on(x)");
    }

    /// Mixed pattern: exists<k, v> x == Some(k) should NOT fire multi-var
    /// elimination because Some takes 1 arg but we have 2 quantifier variables.
    #[test]
    #[timeout(30000)]
    fn mixed_var_count_does_not_eliminate_multi() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "None".to_string(),
                    fields: vec![],
                },
                DatatypeConstructor {
                    name: "Some".to_string(),
                    fields: vec![DatatypeField {
                        name: "value".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        };
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        // exists<k> exists<v> x == Some(k) — v unused, single-var fires for k
        let body = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("k")]));
        let inner = PureExpr::Exists {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };
        let outer = PureExpr::Exists {
            var: "k".to_string(),
            var_sort: None,
            body: Arc::new(inner),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&outer);
        assert!(result.is_ok(), "encoding should succeed: {result:?}");
    }

    /// forall<v> x == Some(v) (non-Implies body) must NOT silently reduce to
    /// is_some(x). The correct encoding is a full quantifier. (#1781)
    #[test]
    #[timeout(30000)]
    fn forall_non_implies_body_does_not_discard_body() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "None".to_string(),
                    fields: vec![],
                },
                DatatypeConstructor {
                    name: "Some".to_string(),
                    fields: vec![DatatypeField {
                        name: "value".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        };
        encoder.ensure_datatype_declared(&dt.clone());
        let x_term = encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        // forall<v> x == Some(v) — body is Eq, not Implies.
        // Semantically: "for every v, x equals Some(v)" — this is false for
        // any x when the domain has more than one element. It must NOT be
        // weakened to just is_some(x).
        let body = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));
        let outer = PureExpr::Forall {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&outer);
        assert!(result.is_ok(), "encoding should succeed: {result:?}");

        // The result should NOT be just the tester — that would be the bug.
        let tester = encoder
            .solver
            .try_datatype_tester("Some", x_term)
            .expect("tester should exist");
        assert_ne!(
            result.unwrap(),
            tester,
            "forall<v> x == Some(v) must not reduce to just is_some(x) (#1781)"
        );
    }

    /// forall<v> x == Some(v) && v > 0 (non-Implies body) must not be
    /// weakened to just is_some(x). This mirrors the issue impact shape (#1781).
    #[test]
    #[timeout(30000)]
    fn forall_non_implies_conjunction_does_not_discard_body() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "None".to_string(),
                    fields: vec![],
                },
                DatatypeConstructor {
                    name: "Some".to_string(),
                    fields: vec![DatatypeField {
                        name: "value".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        };
        encoder.ensure_datatype_declared(&dt.clone());
        let x_term = encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let body = and(
            eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")])),
            gt(var("v"), PureExpr::Int(0)),
        );
        let outer = PureExpr::Forall {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&outer);
        assert!(result.is_ok(), "encoding should succeed: {result:?}");

        let tester = encoder
            .solver
            .try_datatype_tester("Some", x_term)
            .expect("tester should exist");
        assert_ne!(
            result.unwrap(),
            tester,
            "forall<v> x == Some(v) && v > 0 must not reduce to just is_some(x) (#1781)"
        );
    }

    /// Defense-in-depth: the elimination helper itself must error if called on
    /// a Forall body that is not Implies-shaped (#1781).
    #[test]
    #[timeout(30000)]
    fn forall_non_implies_direct_elimination_returns_error() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "None".to_string(),
                    fields: vec![],
                },
                DatatypeConstructor {
                    name: "Some".to_string(),
                    fields: vec![DatatypeField {
                        name: "value".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        };
        encoder.ensure_datatype_declared(&dt.clone());
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt.clone()))
            .expect("declare x");

        let body = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));
        let scrutinee = match &body {
            PureExpr::BinOp(lhs, BinOp::Eq, _) => lhs.as_ref(),
            _ => panic!("test fixture must build an Eq body"),
        };
        let info = ConstructorEqInfo {
            scrutinee,
            ctor_name: "OptionInt::Some",
            datatype: dt,
            var_field_map: vec![("v", 0)],
            inner_ctor: None,
        };

        let result =
            encoder.eliminate_constructor_eq_quantifier(QuantifierKind::Forall, &body, &info, None);
        let err = result.expect_err("non-Implies Forall elimination must return error");
        assert!(
            err.to_string()
                .contains("Forall body is not Implies-shaped"),
            "unexpected error: {err}",
        );
    }

    /// forall<k, v> x == Pair(k, v) (non-Implies body) must NOT silently
    /// reduce to is_pair(x). Multi-variable variant of #1781.
    #[test]
    #[timeout(30000)]
    fn forall_multi_var_non_implies_body_does_not_discard_body() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = pair_datatype();
        encoder.ensure_datatype_declared(&dt.clone());
        let x_term = encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        // forall<k, v> x == Pair(k, v) — body is Eq, not Implies.
        let body = eq(
            var("x"),
            logic_fn_call("MyPair::Pair", vec![var("k"), var("v")]),
        );
        let inner = PureExpr::Forall {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };
        let outer = PureExpr::Forall {
            var: "k".to_string(),
            var_sort: None,
            body: Arc::new(inner),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&outer);
        assert!(result.is_ok(), "encoding should succeed: {result:?}");

        let tester = encoder
            .solver
            .try_datatype_tester("Pair", x_term)
            .expect("tester should exist");
        assert_ne!(
            result.unwrap(),
            tester,
            "forall<k, v> x == Pair(k, v) must not reduce to just is_pair(x) (#1781)"
        );
    }

    /// Regression for #1752: constructor elimination scrutinee pre-seeding
    /// must unwrap View wrappers (`self@ == OwnResult::Ok(t)`).
    #[test]
    #[timeout(30000)]
    fn exists_view_scrutinee_constructor_elimination_no_sort_mismatch() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = DatatypeSort {
            name: "OwnResult".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Ok".to_string(),
                    fields: vec![DatatypeField {
                        name: "ok_value".to_string(),
                        sort: Sort::Int,
                    }],
                },
                DatatypeConstructor {
                    name: "Err".to_string(),
                    fields: vec![DatatypeField {
                        name: "err_value".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        };
        encoder.ensure_datatype_declared(&dt);

        let body = eq(
            PureExpr::View(Arc::new(var("self"))),
            logic_fn_call("OwnResult::Ok", vec![var("t")]),
        );
        let exists = PureExpr::Exists {
            var: "t".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };

        let result = encoder.encode_pure(&exists);
        assert!(
            result.is_ok(),
            "exists<t> self@ == OwnResult::Ok(t) should encode: {result:?}"
        );
        assert!(
            encoder.solver_panic_reason().is_none(),
            "view scrutinee elimination should not trigger sort mismatch panic: {:?}",
            encoder.solver_panic_reason()
        );
        match encoder.var_sort("self_view") {
            Some(Sort::Datatype(dt_sort)) => {
                assert_eq!(
                    dt_sort.name, "OwnResult",
                    "self_view should keep OwnResult sort after elimination preseed"
                );
            }
            other => panic!("expected self_view to be Datatype(OwnResult), got: {other:?}"),
        }
    }
}

#[cfg(test)]
mod constructor_arg_sort_inference_tests {
    use std::sync::Arc;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use ntest::timeout;
    use trust_wp_core::formula::{ExprSort, PureExpr};

    use crate::{
        encoder::{quantifier_ctor_elim::infer_constructor_arg_sort, AYEncoder},
        tests::helpers::{logic_fn_call, var},
    };

    #[test]
    #[timeout(30000)]
    fn infer_constructor_arg_sort_returns_constructor_field_sort() {
        let mut encoder = AYEncoder::new();
        let dt = DatatypeSort {
            name: "MyPair".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Pair".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "left".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "right".to_string(),
                        sort: Sort::Bool,
                    },
                ],
            }],
        };
        encoder.ensure_datatype_declared(&dt);

        let body = logic_fn_call(
            "MyPair::Pair",
            vec![PureExpr::Deref(Arc::new(var("x"))), var("flag")],
        );

        assert_eq!(
            infer_constructor_arg_sort(&encoder, &body, "x"),
            Some(Sort::Int),
            "x should inherit constructor field sort Int"
        );
        assert_eq!(
            infer_constructor_arg_sort(&encoder, &body, "flag"),
            Some(Sort::Bool),
            "flag should inherit constructor field sort Bool"
        );
    }

    #[test]
    #[timeout(30000)]
    fn infer_constructor_arg_sort_ignores_shadowed_nested_quantifier_var() {
        let mut encoder = AYEncoder::new();
        let dt = DatatypeSort {
            name: "MyBox".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Wrap".to_string(),
                fields: vec![DatatypeField {
                    name: "payload".to_string(),
                    sort: Sort::Int,
                }],
            }],
        };
        encoder.ensure_datatype_declared(&dt);

        let nested = PureExpr::Forall {
            var: "t".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(logic_fn_call("MyBox::Wrap", vec![var("t")])),
            triggers: vec![],
        };

        assert_eq!(
            infer_constructor_arg_sort(&encoder, &nested, "t"),
            None,
            "inner quantifier binding should shadow outer t"
        );
    }
}

#[cfg(test)]
mod formula_trigger_synthesis_tests {
    use std::sync::Arc;

    use ay_dpll::api::Sort;
    use ntest::timeout;
    use trust_wp_core::{formula::Formula, logic::LogicFnDef};

    use crate::{
        encoder::AYEncoder,
        tests::helpers::{add, gt, int, logic_fn_call, points_to, pure, var},
    };

    #[test]
    #[timeout(30000)]
    fn sep_value_arithmetic_term_is_not_used_as_trigger() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let qx = encoder.solver.fresh_var("qx", Sort::Int);
        encoder.insert_var("x".to_string(), qx);

        let body = points_to("slot", add(var("x"), int(1)));
        let patterns = encoder
            .synthesize_formula_trigger_terms("x", &body)
            .expect("synthesis should succeed");

        assert!(
            patterns.is_empty(),
            "arithmetic-only sep value should not synthesize formula trigger patterns: {patterns:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn sep_and_pure_trigger_sources_merge_within_budget() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let f_def = LogicFnDef::new(
            "f".to_string(),
            "crate::quantifier::f".to_string(),
            vec!["x".to_string()],
            var("x"),
        );
        encoder
            .register_logic_fn(&f_def)
            .expect("register f logic fn");

        let g_def = LogicFnDef::new(
            "g".to_string(),
            "crate::quantifier::g".to_string(),
            vec!["x".to_string()],
            var("x"),
        );
        encoder
            .register_logic_fn(&g_def)
            .expect("register g logic fn");

        let qx = encoder.solver.fresh_var("qx", Sort::Int);
        encoder.insert_var("x".to_string(), qx);

        let body = Formula::And(
            Arc::new(points_to("slot", logic_fn_call("g", vec![var("x")]))),
            Arc::new(pure(gt(logic_fn_call("f", vec![var("x")]), int(0)))),
        );

        let patterns = encoder
            .synthesize_formula_trigger_terms("x", &body)
            .expect("synthesis should succeed");

        let g_x = encoder
            .encode_pure(&logic_fn_call("g", vec![var("x")]))
            .expect("encode g(x)");
        let f_x = encoder
            .encode_pure(&logic_fn_call("f", vec![var("x")]))
            .expect("encode f(x)");

        assert_eq!(
            patterns.len(),
            2,
            "sep + pure trigger synthesis should fill both pattern slots: {patterns:?}"
        );
        assert!(
            patterns.iter().any(|p| p.len() == 1 && p[0] == g_x),
            "missing sep-derived trigger term g(x): {patterns:?}"
        );
        assert!(
            patterns.iter().any(|p| p.len() == 1 && p[0] == f_x),
            "missing pure-derived fallback trigger term f(x): {patterns:?}"
        );
    }
}

#[cfg(test)]
mod resolve_quantifier_var_sort_tests {
    use std::collections::HashSet;

    use ay_dpll::api::Sort;
    use ntest::timeout;
    use trust_wp_core::formula::ExprSort;

    use crate::{encoder::AYEncoder, tests::helpers::var};

    #[test]
    #[timeout(30000)]
    fn test_resolve_quantifier_var_sort_fallback_int() {
        let mut encoder = AYEncoder::new();
        let bool_names = HashSet::new();
        let body = var("x");

        let sort = encoder.resolve_quantifier_var_sort("x", None, &bool_names, &body);
        assert_eq!(sort, Sort::Int, "with no hints, fallback should be Int");
    }

    #[test]
    #[timeout(30000)]
    fn test_resolve_quantifier_var_sort_bool_hint() {
        let mut encoder = AYEncoder::new();
        let mut bool_names = HashSet::new();
        bool_names.insert("b".to_string());
        let body = var("b");

        let sort = encoder.resolve_quantifier_var_sort("b", None, &bool_names, &body);
        assert_eq!(
            sort,
            Sort::Bool,
            "variable in bool_names should resolve Bool"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_resolve_quantifier_var_sort_explicit_bool_annotation() {
        let mut encoder = AYEncoder::new();
        let bool_names = HashSet::new();
        let body = var("b");
        let es = ExprSort::Bool;

        let sort = encoder.resolve_quantifier_var_sort("b", Some(&es), &bool_names, &body);
        assert_eq!(
            sort,
            Sort::Bool,
            "explicit Bool annotation should resolve Bool"
        );
    }

    /// Regression test for #2186: Phase 6 previously used only 3 sort
    /// resolution levels and missed the `{var}_view` Seq hint (level 4).
    /// The unified `resolve_quantifier_var_sort` includes all 6 levels.
    #[test]
    #[timeout(30000)]
    fn test_resolve_quantifier_var_sort_view_seq_hint() {
        let mut encoder = AYEncoder::new();
        let bool_names = HashSet::new();
        let body = var("x");

        // Register x_view with Seq sort to simulate the {var}_view hint path.
        let seq_sort = Sort::seq(Sort::Int);
        let dummy_term = encoder.solver.int_const(0);
        encoder.rebind_var("x_view", dummy_term, seq_sort.clone());

        let sort = encoder.resolve_quantifier_var_sort("x", None, &bool_names, &body);
        assert_eq!(
            sort, seq_sort,
            "variable with x_view Seq hint should resolve to Seq, not Int"
        );
    }

    /// P1-95 algorithm_audit: When `var_sort` is `Some(ExprSort::Int)`, the
    /// Bool hint check (`bool_names.contains(var_name)`) is SKIPPED because
    /// the `if let Some(es)` branch at line 55 takes priority. In contrast,
    /// when `var_sort` is `None`, the Bool hint IS checked (line 71).
    ///
    /// This creates a silent behavioral discrepancy: `forall<b: Int>` used
    /// in Bool context resolves to Int (wrong), while `forall<b>` (no annotation)
    /// in the same context resolves to Bool (correct).
    ///
    /// The parser emits `Some(ExprSort::Int)` as a default when the user writes
    /// `forall<b: Int>` or when the type cannot be resolved. Bool-typed quantifier
    /// variables with this annotation get the wrong sort.
    #[test]
    #[timeout(30000)]
    fn test_resolve_quantifier_var_sort_explicit_int_skips_bool_hint() {
        let mut encoder = AYEncoder::new();
        let mut bool_names = HashSet::new();
        bool_names.insert("b".to_string());
        let body = var("b");

        // With None annotation + Bool hint → Bool (correct)
        let sort_none = encoder.resolve_quantifier_var_sort("b", None, &bool_names, &body);
        assert_eq!(sort_none, Sort::Bool, "None annotation + Bool hint → Bool");

        // With Some(Int) annotation + Bool hint → BUG: Int (should be Bool)
        let es = ExprSort::Int;
        let sort_int = encoder.resolve_quantifier_var_sort("b", Some(&es), &bool_names, &body);

        // Document the current (buggy) behavior: Some(Int) skips bool_names check
        assert_eq!(
            sort_int,
            Sort::Int,
            "BUG: Some(ExprSort::Int) skips bool_names check — resolves Int instead of Bool. \
             The `if let Some(es)` branch does not consult bool_names."
        );
        // The correct behavior would be for both to resolve Bool:
        assert_ne!(
            sort_none, sort_int,
            "Discrepancy: None annotation resolves Bool but Some(Int) resolves Int for same variable"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_resolve_quantifier_var_sort_explicit_int_with_seq_hint_override() {
        let mut encoder = AYEncoder::new();
        let bool_names = HashSet::new();
        let body = var("prod");

        // Register prod with Seq sort hint — simulates the parser's Int
        // fallback being overridden by a Seq sort discovered from body analysis.
        let seq_sort = Sort::seq(Sort::Int);
        let dummy_term = encoder.solver.int_const(0);
        encoder.rebind_var("prod", dummy_term, seq_sort.clone());

        let es = ExprSort::Int;
        let sort = encoder.resolve_quantifier_var_sort("prod", Some(&es), &bool_names, &body);
        assert_eq!(
            sort, seq_sort,
            "explicit Int annotation should be overridden by Seq sort hint (#967)"
        );
    }
}

#[cfg(test)]
mod trigger_fallback_tests {
    use ay_dpll::api::{Logic, SolveResult, Solver, SolverError, Sort};
    use ntest::timeout;

    use crate::encoder::quantifier::QuantifierKind;

    #[test]
    #[timeout(30000)]
    fn synthesized_invalid_trigger_falls_back_to_triggerless_exists() {
        let mut solver = Solver::try_new(Logic::Auflia).unwrap();
        let x = solver.fresh_var("x", Sort::Int);
        let body = solver.bool_const(true);
        let unrelated = solver.declare_const("a", Sort::Int);
        let trigger_decl = solver.declare_fun("free_trigger", &[Sort::Int], Sort::Int);
        let invalid_trigger = solver.apply(&trigger_decl, &[unrelated]);

        let (term, fell_back) = QuantifierKind::Exists
            .apply_with_optional_invalid_trigger_fallback(
                &mut solver,
                &[x],
                body,
                &[&[invalid_trigger]],
                true,
            )
            .expect("synthesized invalid trigger should fall back to triggerless exists");
        assert!(
            fell_back,
            "invalid synthesized trigger should trigger fallback"
        );

        let negated = solver.not(term);
        solver.assert_term(negated);
        // ay-dpll quantifier handling changes may return Unknown instead of
        // Unsat for this trivial negated exists. Accept both. (#2594)
        let sat_result = solver.check_sat().into_inner();
        assert!(
            matches!(sat_result, SolveResult::Unsat(_) | SolveResult::Unknown),
            "NOT(exists x. true) should be Unsat (or Unknown from ay quantifier change): got {sat_result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn explicit_invalid_trigger_is_still_rejected() {
        let mut solver = Solver::try_new(Logic::Auflia).unwrap();
        let x = solver.fresh_var("x", Sort::Int);
        let body = solver.bool_const(true);
        let unrelated = solver.declare_const("a", Sort::Int);
        let trigger_decl = solver.declare_fun("free_trigger", &[Sort::Int], Sort::Int);
        let invalid_trigger = solver.apply(&trigger_decl, &[unrelated]);

        let err = QuantifierKind::Forall
            .apply_with_optional_invalid_trigger_fallback(
                &mut solver,
                &[x],
                body,
                &[&[invalid_trigger]],
                false,
            )
            .expect_err("explicit invalid trigger should stay an error");
        assert!(
            matches!(err, SolverError::InvalidTrigger { .. }),
            "expected InvalidTrigger, got {err:?}"
        );
    }
}

/// Regression tests for #2346 quadratic scaling fixes.
#[cfg(test)]
mod scaling_regression_tests {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use ntest::timeout;
    use trust_wp_core::formula::PureExpr;

    use crate::{
        encoder::{
            quantifier::QuantifierKind,
            quantifier_ctor_elim::{
                detect_constructor_eq, infer_constructor_arg_sort,
                infer_constructor_arg_sorts_batch,
            },
            AYEncoder,
        },
        tests::helpers::{eq, logic_fn_call, var},
    };

    fn wide_datatype(n: usize) -> DatatypeSort {
        DatatypeSort {
            name: "Wide".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Wide".to_string(),
                fields: (0..n)
                    .map(|i| DatatypeField {
                        name: format!("f{i}"),
                        sort: Sort::Int,
                    })
                    .collect(),
            }],
        }
    }

    /// Batch constructor arg sort inference must produce identical results to
    /// per-variable inference for a datatype with many fields.
    #[test]
    #[timeout(30000)]
    fn batch_ctor_sort_inference_matches_per_variable() {
        let n = 20;
        let mut encoder = AYEncoder::new();
        let dt = wide_datatype(n);
        encoder.ensure_datatype_declared(&dt);

        let var_names: Vec<String> = (0..n).map(|i| format!("v{i}")).collect();
        let args: Vec<PureExpr> = var_names.iter().map(|v| var(v)).collect();
        let body = logic_fn_call("Wide::Wide", args);

        let qvars: Vec<&str> = var_names.iter().map(String::as_str).collect();
        let batch_result = infer_constructor_arg_sorts_batch(&encoder, &body, &qvars);

        for v in &var_names {
            let single = infer_constructor_arg_sort(&encoder, &body, v);
            let batched = batch_result.get(v.as_str()).cloned();
            assert_eq!(
                single, batched,
                "batch and single inference must agree for variable {v}"
            );
        }
        assert_eq!(
            batch_result.len(),
            n,
            "batch should resolve all {n} variables"
        );
    }

    /// Constructor equality detection with many qvars must use O(1) HashSet
    /// membership tests. This test verifies correctness of the HashSet-based
    /// path by exercising detection with a wide datatype.
    #[test]
    #[timeout(30000)]
    fn detect_ctor_eq_wide_datatype_uses_hashset_lookup() {
        let n = 10;
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = wide_datatype(n);
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let var_names: Vec<String> = (0..n).map(|i| format!("v{i}")).collect();
        let args: Vec<PureExpr> = var_names.iter().map(|v| var(v)).collect();
        let body = eq(var("x"), logic_fn_call("Wide::Wide", args));

        let qvars: Vec<&str> = var_names.iter().map(String::as_str).collect();
        let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &qvars);
        assert!(
            info.is_some(),
            "should detect constructor equality with {n} qvars"
        );
        let info = info.unwrap();
        assert_eq!(
            info.var_field_map.len(),
            n,
            "all {n} variables should be mapped to constructor fields"
        );
        assert_eq!(info.ctor_name, "Wide::Wide");
    }

    /// Ensure detect_constructor_eq rejects non-qvar arguments even with the
    /// HashSet path. An argument that is not in qvars should cause detection
    /// to fail.
    #[test]
    #[timeout(30000)]
    fn detect_ctor_eq_rejects_non_qvar_argument() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = wide_datatype(3);
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        // body: x == Wide(v0, v1, INTRUDER) — INTRUDER is not in qvars
        let args = vec![var("v0"), var("v1"), var("intruder")];
        let body = eq(var("x"), logic_fn_call("Wide::Wide", args));

        let qvars = vec!["v0", "v1"]; // "intruder" deliberately omitted
        let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &qvars);
        assert!(
            info.is_none(),
            "detection must reject when a constructor arg is not a qvar"
        );
    }
}

/// Tests for nested quantifier combinations and trigger annotations.
#[cfg(test)]
mod nested_quantifier_and_trigger_tests {
    use std::sync::Arc;

    use ntest::timeout;
    use trust_wp_core::formula::PureExpr;

    use crate::{
        encoder::AYEncoder,
        tests::helpers::{
            and, eq, exists, exists_with_triggers, forall, forall_with_triggers, gt, implies, int,
            logic_fn_call, lt, or, var,
        },
    };

    /// Nested forall<x> exists<y> (x > 0 ==> y == x) should encode
    /// without error. The outer forall wraps an inner exists.
    #[test]
    #[timeout(30000)]
    fn nested_forall_exists_encodes_successfully() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let inner_body = eq(var("y"), var("x"));
        let inner = exists("y", inner_body);
        let outer_body = implies(gt(var("x"), int(0)), inner);
        let outer = forall("x", outer_body);

        let result = encoder.encode_pure(&outer);
        assert!(
            result.is_ok(),
            "nested forall/exists should encode: {result:?}"
        );
    }

    /// Nested exists<x> forall<y> (y > 0 ==> x > y) should encode
    /// without error. The outer exists wraps an inner forall.
    #[test]
    #[timeout(30000)]
    fn nested_exists_forall_encodes_successfully() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let inner_body = implies(gt(var("y"), int(0)), gt(var("x"), var("y")));
        let inner = forall("y", inner_body);
        let outer = exists("x", inner);

        let result = encoder.encode_pure(&outer);
        assert!(
            result.is_ok(),
            "nested exists/forall should encode: {result:?}"
        );
    }

    /// Three-level nesting: forall<x> exists<y> forall<z> body.
    /// Verifies that deeply nested quantifiers do not cause stack overflow
    /// or encoding errors.
    #[test]
    #[timeout(30000)]
    fn three_level_nesting_forall_exists_forall() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // forall<x> exists<y> forall<z> (z > 0 ==> x + y > z)
        let innermost_body = implies(
            gt(var("z"), int(0)),
            gt(
                PureExpr::BinOp(
                    Arc::new(var("x")),
                    trust_wp_core::formula::BinOp::Add,
                    Arc::new(var("y")),
                ),
                var("z"),
            ),
        );
        let level_z = forall("z", innermost_body);
        let level_y = exists("y", level_z);
        let level_x = forall("x", level_y);

        let result = encoder.encode_pure(&level_x);
        assert!(
            result.is_ok(),
            "three-level nested quantifier should encode: {result:?}"
        );
    }

    /// Quantifier with multiple bound variables at the same level via
    /// nested single-variable quantifiers: forall<x> forall<y> (x > y ==> x > 0).
    /// This is how multi-variable quantifiers are represented in PureExpr.
    #[test]
    #[timeout(30000)]
    fn multi_var_forall_via_nesting() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let body = implies(gt(var("x"), var("y")), gt(var("x"), int(0)));
        let inner = forall("y", body);
        let outer = forall("x", inner);

        let result = encoder.encode_pure(&outer);
        assert!(
            result.is_ok(),
            "multi-variable forall should encode: {result:?}"
        );
    }

    /// Quantifier with explicit trigger annotations: forall<x> (x > 0 ==> f(x) > 0)
    /// with trigger pattern [[f(x)]]. The trigger should be passed through
    /// to the ay quantifier.
    #[test]
    #[timeout(30000)]
    fn forall_with_explicit_trigger_encodes_successfully() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // Register logic function f so the trigger term can be encoded.
        let f_def = trust_wp_core::logic::LogicFnDef::new(
            "f".to_string(),
            "crate::test::f".to_string(),
            vec!["x".to_string()],
            var("x"),
        );
        encoder.register_logic_fn(&f_def).expect("register f");

        let body = implies(
            gt(var("x"), int(0)),
            gt(logic_fn_call("f", vec![var("x")]), int(0)),
        );
        let trigger_pattern = vec![vec![logic_fn_call("f", vec![var("x")])]];
        let outer = forall_with_triggers("x", body, trigger_pattern);

        let result = encoder.encode_pure(&outer);
        assert!(
            result.is_ok(),
            "forall with explicit trigger should encode: {result:?}"
        );
    }

    /// Exists with explicit trigger annotations: exists<x> f(x) == 42
    /// with trigger pattern [[f(x)]].
    #[test]
    #[timeout(30000)]
    fn exists_with_explicit_trigger_encodes_successfully() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let f_def = trust_wp_core::logic::LogicFnDef::new(
            "f".to_string(),
            "crate::test::f".to_string(),
            vec!["x".to_string()],
            var("x"),
        );
        encoder.register_logic_fn(&f_def).expect("register f");

        let body = eq(logic_fn_call("f", vec![var("x")]), int(42));
        let trigger_pattern = vec![vec![logic_fn_call("f", vec![var("x")])]];
        let outer = exists_with_triggers("x", body, trigger_pattern);

        let result = encoder.encode_pure(&outer);
        assert!(
            result.is_ok(),
            "exists with explicit trigger should encode: {result:?}"
        );
    }

    /// Conjunction of two quantifiers at the same level:
    /// (forall<x> x > 0 ==> x > -1) && (exists<y> y == 42).
    /// Verifies that independent quantifiers in a conjunction both encode.
    #[test]
    #[timeout(30000)]
    fn conjunction_of_independent_quantifiers() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let q1 = forall("x", implies(gt(var("x"), int(0)), gt(var("x"), int(-1))));
        let q2 = exists("y", eq(var("y"), int(42)));
        let conj = and(q1, q2);

        let result = encoder.encode_pure(&conj);
        assert!(
            result.is_ok(),
            "conjunction of quantifiers should encode: {result:?}"
        );
    }

    /// Disjunction of quantifiers: (forall<x> x > 0) || (exists<y> y < 0).
    #[test]
    #[timeout(30000)]
    fn disjunction_of_quantifiers() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let q1 = forall("x", gt(var("x"), int(0)));
        let q2 = exists("y", lt(var("y"), int(0)));
        let disj = or(q1, q2);

        let result = encoder.encode_pure(&disj);
        assert!(
            result.is_ok(),
            "disjunction of quantifiers should encode: {result:?}"
        );
    }
}

/// Tests for ground sub-expression registration from quantifier bodies (#2696).
#[cfg(test)]
mod ground_subexpr_registration_tests {
    use ntest::timeout;

    use crate::{
        encoder::AYEncoder,
        tests::helpers::{
            and, bool_expr, forall, ge, gt, implies, int, logic_fn_call, lt, method_call, var,
        },
    };

    /// When a quantifier body contains a LogicFnCall that is completely ground
    /// (doesn't reference the bound variable), it should be registered in the
    /// ground pool after encoding.
    #[test]
    #[timeout(30000)]
    fn ground_logic_fn_in_forall_body_registered_in_pool() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // Register logic function g so it gets proper SMT encoding.
        let g_def = trust_wp_core::logic::LogicFnDef::new(
            "g".to_string(),
            "crate::test::g".to_string(),
            vec!["a".to_string()],
            var("a"),
        );
        encoder.register_logic_fn(&g_def).expect("register g");

        // Register logic function f.
        let f_def = trust_wp_core::logic::LogicFnDef::new(
            "f".to_string(),
            "crate::test::f".to_string(),
            vec!["x".to_string()],
            var("x"),
        );
        encoder.register_logic_fn(&f_def).expect("register f");

        // Declare 'a' as a ground variable so g(a) can be encoded.
        encoder
            .get_or_declare_var("a", ay_dpll::api::Sort::Int)
            .expect("declare a");

        let pool_before = encoder.ground_pool.ground_term_count();

        // forall x. f(x) > 0 ==> g(a) > 0
        // g(a) is ground w.r.t. bound var x.
        let body = implies(
            gt(logic_fn_call("f", vec![var("x")]), int(0)),
            gt(logic_fn_call("g", vec![var("a")]), int(0)),
        );
        let quantifier = forall("x", body);

        let result = encoder.encode_pure(&quantifier);
        assert!(
            result.is_ok(),
            "forall with ground sub-expression should encode: {result:?}"
        );

        let pool_after = encoder.ground_pool.ground_term_count();
        // g(a) should be registered in the ground pool.
        assert!(
            pool_after > pool_before,
            "ground pool should have more entries after encoding quantifier with ground g(a): \
             before={pool_before}, after={pool_after}"
        );

        // The SMT name for logic function "g" is "logic_g" (per logic_fn_smt_name).
        let g_entries = encoder
            .ground_pool
            .entries_for("logic_g")
            .map(|e| e.len())
            .unwrap_or(0);
        assert!(
            g_entries > 0,
            "ground pool should have entries for g (logic_g): got {g_entries}"
        );
    }

    /// When a quantifier body contains a MethodCall (e.g., v.len()) that is
    /// completely ground, it should be accessible for ground pool E-matching.
    #[test]
    #[timeout(30000)]
    fn ground_method_call_in_forall_body_encoded_without_error() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // forall i. i >= 0 && i < v.len() ==> true
        // v.len() is ground w.r.t. bound var i.
        let body = implies(
            and(
                ge(var("i"), int(0)),
                lt(var("i"), method_call(var("v"), "len", vec![])),
            ),
            bool_expr(true),
        );
        let quantifier = forall("i", body);

        // This should encode without error — the ground sub-expression
        // extraction should not interfere with normal quantifier encoding.
        let result = encoder.encode_pure(&quantifier);
        assert!(
            result.is_ok(),
            "forall with ground v.len() should encode: {result:?}"
        );
    }

    /// When ALL sub-expressions reference the bound variable, no ground terms
    /// should be extracted (and encoding should still work).
    #[test]
    #[timeout(30000)]
    fn no_ground_subexprs_encodes_normally() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let f_def = trust_wp_core::logic::LogicFnDef::new(
            "f".to_string(),
            "crate::test::f".to_string(),
            vec!["x".to_string()],
            var("x"),
        );
        encoder.register_logic_fn(&f_def).expect("register f");

        let pool_before = encoder.ground_pool.ground_term_count();

        // forall x. f(x) > 0 — no ground sub-expressions.
        let body = gt(logic_fn_call("f", vec![var("x")]), int(0));
        let quantifier = forall("x", body);

        let result = encoder.encode_pure(&quantifier);
        assert!(
            result.is_ok(),
            "forall without ground subexprs should encode: {result:?}"
        );

        // The ground pool should NOT have new entries from f(x) since x is bound.
        let pool_after = encoder.ground_pool.ground_term_count();
        assert_eq!(
            pool_before, pool_after,
            "no ground sub-expressions should be registered when all calls mention bound vars"
        );
    }
}
