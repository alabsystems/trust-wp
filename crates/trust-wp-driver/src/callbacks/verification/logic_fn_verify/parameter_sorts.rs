// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Carry the current function's declared parameter types into its own VCs.
//! Its defining axiom is deliberately absent from that environment, so its
//! signature cannot be relied on to reintroduce otherwise missing types.

use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::{
    formula::{ExprSort, MatchArm, PureExpr},
    logic::LogicFnDef,
};

pub(super) fn annotate(def: &LogicFnDef) -> Result<LogicFnDef, String> {
    if def.params().iter().collect::<HashSet<_>>().len() != def.params().len() {
        return Err("parameter names are not unique".to_string());
    }
    if !def.param_sorts().is_empty() && def.params().len() != def.param_sorts().len() {
        return Err("parameter type metadata does not match the parameter list".to_string());
    }
    let sorts: HashMap<&str, &ExprSort> = def
        .params()
        .iter()
        .zip(def.param_sorts())
        .filter_map(|(name, sort)| sort.as_ref().map(|sort| (name.as_str(), sort)))
        .collect();
    let apply = |expr: &PureExpr| {
        let mut conflict = None;
        expr.for_each_free_var(|name, annotation| {
            if let (Some(expected), Some(actual)) = (sorts.get(name), annotation) {
                if *expected != actual {
                    conflict = Some(format!(
                        "parameter `{name}` has conflicting declared and expression types"
                    ));
                }
            }
        });
        if let Some(conflict) = conflict {
            return Err(conflict);
        }
        let unsupported = Cell::new(false);
        let typed = annotate_expr(expr, &sorts, &unsupported);
        if unsupported.get() {
            return Err("unsupported expression while preserving parameter types".to_string());
        }
        Ok(typed)
    };
    let mut typed = def.clone();
    typed.set_body(apply(def.body())?);
    typed.set_requires(def.requires().iter().map(apply).collect::<Result<_, _>>()?);
    typed.set_ensures(def.ensures().iter().map(apply).collect::<Result<_, _>>()?);
    Ok(typed)
}

fn annotate_expr(
    expr: &PureExpr,
    sorts: &HashMap<&str, &ExprSort>,
    unsupported: &Cell<bool>,
) -> PureExpr {
    if sorts.is_empty() {
        return expr.clone();
    }
    let hiding = |names: &[&str]| {
        let mut visible = sorts.clone();
        for name in names {
            visible.remove(*name);
        }
        visible
    };
    // Prune binders before the generic structure-preserving walk and recurse
    // their scopes explicitly. Substitution is inappropriate here: it can
    // reduce tuples or reinterpret a zero-argument call as a variable.
    expr.rewrite_bottom_up_prune(
        |node| match node {
            PureExpr::Forall { .. }
            | PureExpr::Exists { .. }
            | PureExpr::Match { .. }
            | PureExpr::Let { .. }
            | PureExpr::Closure { .. } => false,
            PureExpr::Bool(_)
            | PureExpr::Int(_)
            | PureExpr::Float(_)
            | PureExpr::Var(..)
            | PureExpr::BinOp(..)
            | PureExpr::UnOp(..)
            | PureExpr::Ite(..)
            | PureExpr::Old(_)
            | PureExpr::Deref(_)
            | PureExpr::Final(_)
            | PureExpr::View(_)
            | PureExpr::MethodCall { .. }
            | PureExpr::LogicFnCall { .. }
            | PureExpr::LetAssume { .. }
            | PureExpr::LetObligation { .. } => true,
            _ => {
                unsupported.set(true);
                false
            }
        },
        |node| match node {
            PureExpr::Var(name, annotation) => {
                let annotation =
                    annotation.or_else(|| sorts.get(name.as_str()).map(|s| (*s).clone()));
                PureExpr::Var(name, annotation)
            }
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let visible = hiding(&[var.as_str()]);
                PureExpr::Forall {
                    var,
                    var_sort,
                    body: Arc::new(annotate_expr(&body, &visible, unsupported)),
                    triggers: triggers
                        .iter()
                        .map(|group| {
                            group
                                .iter()
                                .map(|trigger| annotate_expr(trigger, &visible, unsupported))
                                .collect()
                        })
                        .collect(),
                }
            }
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let visible = hiding(&[var.as_str()]);
                PureExpr::Exists {
                    var,
                    var_sort,
                    body: Arc::new(annotate_expr(&body, &visible, unsupported)),
                    triggers: triggers
                        .iter()
                        .map(|group| {
                            group
                                .iter()
                                .map(|trigger| annotate_expr(trigger, &visible, unsupported))
                                .collect()
                        })
                        .collect(),
                }
            }
            PureExpr::Let { var, value, body } => {
                let visible = hiding(&[var.as_str()]);
                PureExpr::Let {
                    var,
                    value: Arc::new(annotate_expr(&value, sorts, unsupported)),
                    body: Arc::new(annotate_expr(&body, &visible, unsupported)),
                }
            }
            PureExpr::Closure { params, body } => {
                let names = params
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect::<Vec<_>>();
                let visible = hiding(&names);
                PureExpr::Closure {
                    params,
                    body: Arc::new(annotate_expr(&body, &visible, unsupported)),
                }
            }
            PureExpr::Match { scrutinee, arms } => PureExpr::Match {
                scrutinee: Arc::new(annotate_expr(&scrutinee, sorts, unsupported)),
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        let names = arm.pattern.bound_names();
                        let visible = hiding(&names);
                        MatchArm {
                            pattern: arm.pattern,
                            body: annotate_expr(&arm.body, &visible, unsupported),
                        }
                    })
                    .collect(),
            },
            other => other,
        },
    )
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{BinOp, FloatWidth};

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn definition(body: PureExpr) -> LogicFnDef {
        LogicFnDef::new("f".into(), "test::f".into(), vec!["n".into()], body)
            .with_param_sorts(vec![Some(ExprSort::Float(FloatWidth::F64))])
    }

    #[test]
    fn declared_float_sort_is_retained_in_all_own_clauses() {
        let mut def = definition(var("n"));
        def.set_requires(vec![var("n")]);
        def.set_ensures(vec![var("n")]);
        let typed = annotate(&def).unwrap();
        let expected = PureExpr::Var("n".into(), Some(ExprSort::Float(FloatWidth::F64)));
        assert_eq!(typed.body(), &expected);
        assert_eq!(typed.requires(), [expected.clone()]);
        assert_eq!(typed.ensures(), [expected]);
    }

    #[test]
    fn local_binders_keep_their_types_and_let_initializers_read_the_parameter() {
        let quantified = PureExpr::Forall {
            var: "n".into(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(var("n")),
            triggers: vec![],
        };
        let expr = PureExpr::Let {
            var: "n".into(),
            value: Arc::new(var("n")),
            body: Arc::new(quantified.clone()),
        };
        let typed = annotate(&definition(expr)).unwrap();
        let PureExpr::Let { value, body, .. } = typed.body() else {
            panic!("let must survive");
        };
        assert_eq!(
            value.as_ref(),
            &PureExpr::Var("n".into(), Some(ExprSort::Float(FloatWidth::F64)))
        );
        assert_eq!(body.as_ref(), &quantified);
    }

    #[test]
    fn conflicting_free_parameter_annotation_refuses() {
        let def = definition(PureExpr::Var("n".into(), Some(ExprSort::Int)));
        assert!(annotate(&def).is_err());
    }

    #[test]
    fn missing_type_metadata_still_uses_the_existing_arithmetic_inference() {
        let expr = PureExpr::BinOp(Arc::new(var("n")), BinOp::Add, Arc::new(PureExpr::Int(1)));
        let def = LogicFnDef::new("f".into(), "test::f".into(), vec!["n".into()], expr.clone());
        assert_eq!(annotate(&def).unwrap().body(), &expr);
    }

    #[test]
    fn annotation_preserves_obligations_in_discarded_tuple_fields() {
        use trust_wp_core::formula::internal::tuple_lowering::{
            tuple_field_logic_fn_name, tuple_logic_fn_name,
        };
        let assertion = PureExpr::LogicFnCall {
            name: "proof_assert".into(),
            args: vec![PureExpr::Bool(false)],
        };
        let body = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(2),
                args: vec![PureExpr::Int(0), assertion],
            }],
        };
        let typed = annotate(&definition(body.clone())).unwrap();
        assert_eq!(typed.body(), &body);
        assert!(matches!(
            super::super::assertions::assertion_goal(typed.body()),
            super::super::assertions::AssertionGoal::Refused(_)
        ));
    }

    #[test]
    fn parameter_annotation_does_not_replace_a_same_named_nullary_call() {
        let body = PureExpr::LogicFnCall {
            name: "n".into(),
            args: vec![],
        };
        assert_eq!(annotate(&definition(body.clone())).unwrap().body(), &body);
    }
}
