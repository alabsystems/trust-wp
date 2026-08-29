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

    use ntest::timeout;
    use trust_wp_core::formula::{BinOp, PureExpr};
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

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

    /// exists<k, v> x == Pair(k, v) should eliminate to is_pair(x).
    #[test]
    #[timeout(30000)]
    fn exists_two_var_pair_eliminates_to_tester() {
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

        let tester = encoder
            .solver
            .try_datatype_tester("Pair", x_term)
            .expect("tester should exist");
        assert_eq!(result.unwrap(), tester, "should eliminate to is_pair(x)");
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

    /// exists<a, b, c> x == Triple(a, b, c) should eliminate to is_triple(x).
    #[test]
    #[timeout(30000)]
    fn exists_three_var_triple_eliminates_to_tester() {
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

        let tester = encoder
            .solver
            .try_datatype_tester("Triple", x_term)
            .expect("tester");
        assert_eq!(result.unwrap(), tester, "should eliminate to is_triple(x)");
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

    use ntest::timeout;
    use trust_wp_core::formula::{ExprSort, PureExpr};
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

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

    use ntest::timeout;
    use trust_wp_core::{formula::Formula, logic::LogicFnDef};
    use ay_dpll::api::Sort;

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

    use ntest::timeout;
    use trust_wp_core::formula::ExprSort;
    use ay_dpll::api::Sort;

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
    use ntest::timeout;
    use ay_dpll::api::{Logic, SolveResult, Solver, SolverError, Sort};

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
        assert!(
            matches!(solver.check_sat().into_inner(), SolveResult::Unsat(_)),
            "NOT(exists x. true) should be Unsat after triggerless fallback"
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
