// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use trust_wp_core::formula::PureExpr;

use super::*;

fn make_logic_fn_with_adt_param(name: &str, param_name: &str) -> trust_wp_core::logic::LogicFnDef {
    use trust_wp_core::formula::{MatchArm, Pattern};

    trust_wp_core::logic::LogicFnDef::new(
        name.to_string(),
        format!("crate::{name}"),
        vec![param_name.to_string()],
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var(param_name.to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Cons".to_string(),
                        inner: Some(Box::new(Pattern::Tuple(vec![
                            Pattern::Binding("a".to_string()),
                            Pattern::Binding("l".to_string()),
                        ]))),
                    },
                    body: PureExpr::Int(1),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Nil".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Int(0),
                },
            ],
        },
    )
}

#[cfg(test)]
mod adt_decls;
#[cfg(test)]
mod any_expr_matches;
#[cfg(test)]
mod call_site_dt_vars;
#[cfg(test)]
mod custom_sorts_detection;
#[cfg(test)]
mod datatype_scrutinee_tests;
#[cfg(test)]
mod detect_logic_requirements;
#[cfg(test)]
mod detect_logic_requirements_array_theory;
#[cfg(test)]
mod filter_logic_functions;
#[cfg(test)]
mod filter_type_invariants_retain_all;
#[cfg(test)]
mod filter_type_invariants_unqualified;
#[cfg(test)]
mod predeclare_collected_vars;
#[cfg(test)]
mod quantifier_detection;
