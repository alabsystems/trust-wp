// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression analysis utilities.
//!
//! This module provides helper functions for analyzing `PureExpr` trees,
//! used by the encoder and verification modules.
//!
//! # Submodules
//!
//! - [`logic_fn_names`]: Logic function name collection
//! - [`solver_features`]: Solver feature detection predicates
//! - [`uf_detection`]: Uninterpreted function detection
//! - [`var_analysis`]: Variable mention and pattern binding analysis

mod logic_fn_names;
mod solver_features;
mod standard_forall_grounding;
mod uf_detection;
mod var_analysis;

pub(crate) use self::{
    logic_fn_names::collect_logic_fn_names,
    solver_features::{
        expr_has_bitwise_ops, expr_has_closure_spec_method, expr_has_datatype_spec_method,
        expr_has_match_constructor_pattern, expr_has_tuple_fn, expr_needs_quantifiers,
    },
    standard_forall_grounding::{
        instantiate_standard_precondition_foralls, instantiate_standard_precondition_foralls_from,
        is_grounding_exempt_standard_forall, is_standard_data_structure_precondition_forall,
    },
    uf_detection::{expr_has_mut_ref_carrier, expr_has_uf_method_call},
    var_analysis::expr_mentions_var,
};

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, sync::Arc};

    use ntest::timeout;
    use trust_wp_core::formula::PureExpr;

    use super::{collect_logic_fn_names, expr_has_datatype_spec_method};

    #[test]
    #[timeout(30000)]
    fn collect_logic_fn_names_includes_method_style_logic_calls() {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
            method: "sub_pre".to_string(),
            args: vec![PureExpr::Var("rhs".to_string(), None)],
        };

        let mut names = HashSet::new();
        collect_logic_fn_names(&expr, &mut names);

        assert!(
            names.contains("sub_pre"),
            "method call names should be collected for logic function filtering"
        );
    }

    #[test]
    fn datatype_spec_detection_includes_unwrap_or_default() {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("opt".to_string(), None)),
            method: "unwrap_or_default".to_string(),
            args: vec![],
        };

        assert!(
            expr_has_datatype_spec_method(&expr),
            "unwrap_or_default requires Option/Result axiom demand"
        );
    }

    #[test]
    fn collect_logic_fn_names_includes_closure_spec_receivers() {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("T::deref_mut".to_string(), None)),
            method: "postcondition".to_string(),
            args: vec![
                PureExpr::Var("x".to_string(), None),
                PureExpr::Var("result".to_string(), None),
            ],
        };

        let mut names = HashSet::new();
        collect_logic_fn_names(&expr, &mut names);

        assert!(
            names.contains("T::deref_mut"),
            "closure-spec receivers should be retained for goal filtering"
        );
        assert!(
            names.contains("postcondition"),
            "closure-spec dispatcher method should still be collected"
        );
    }
}
