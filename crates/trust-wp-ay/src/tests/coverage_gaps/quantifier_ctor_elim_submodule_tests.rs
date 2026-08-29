// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for the decomposed `encoder/quantifier_ctor_elim/` submodules
//! (#1988 structural decomposition, Part of #1296).
//!
//! Coverage targets:
//! - `detection.rs`: `detect_constructor_eq` edge cases — Forall+Implies guard,
//!   reversed equality, duplicate qvars, non-Var args, nested constructors,
//!   nullary constructors (bare Var and LogicFnCall forms)
//! - `detection_forall_tests.rs`: Forall/Implies and rejection boundary cases
//! - `detection_exists_tests.rs`: Exists-side constructor equality cases
//! - `detection_nullary_tests.rs`: nullary constructor detection helpers
//! - `detection_rejection_tests.rs`: constructor-equality rejection cases
//! - `detection_empty_qvars_tests.rs`: empty-qvars detection boundary cases
//! - `detection_argument_rejection_tests.rs`: constructor-argument rejection cases
//! - `sort_inference.rs`: `infer_constructor_arg_sort` through various expression
//!   forms (BinOp, Ite, MethodCall, Let, LetAssume, Closure, Match)
//! - `sort_inference_binding_let_tests.rs`: Let shadowing and shadow-value checks
//! - `sort_inference_binding_tests.rs`: binding shadowing and scope-handling
//! - `sort_inference_binding_quantifier_tests.rs`: nested quantifier shadowing
//! - `sort_inference_binding_closure_tests.rs`: closure shadowing cases
//! - `sort_inference_wrapper_tests.rs`: wrapper/context propagation cases
//! - `sort_inference_propagation_tests.rs`: wrapper/context propagation cases
//! - `sort_inference_method_call_tests.rs`: MethodCall receiver/args cases
//! - `sort_inference_control_flow_tests.rs`: BinOp/Ite/Let value cases
//! - `sort_inference_direct_tests.rs`: direct expression-tree inference cases
//! - `batch_inference_direct_tests.rs`: direct batch traversal/branch cases
//! - `batch_inference_branch_propagation_tests.rs`: batch propagation through
//!   BinOp/Ite/LetAssume
//! - `batch_inference_tests.rs`: `infer_constructor_arg_sorts_batch` shadowing
//!   and early-exit
//! - `batch_consistency_tests.rs`: batch/single inference agreement on a
//!   combined tree
//! - `arg_is_any_qvar_reference_tests.rs`: nested wrapper qvar detection
//! - `fixtures.rs`: shared datatype builders used by all child modules
//! - `elimination.rs`: tested indirectly via encoder round-trip assertions

use std::sync::Arc;

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use ntest::timeout;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::*;
use crate::encoder::{
    quantifier::QuantifierKind,
    quantifier_ctor_elim::{
        detect_constructor_eq, infer_constructor_arg_sort, infer_constructor_arg_sorts_batch,
        infer_method_call_usage_sort, infer_method_call_usage_sorts_batch,
    },
};

mod detection;

#[path = "quantifier_ctor_elim_submodule_tests/detection_forall_tests.rs"]
mod detection_forall_tests;

#[path = "quantifier_ctor_elim_submodule_tests/detection_exists_tests.rs"]
mod detection_exists_tests;

#[path = "quantifier_ctor_elim_submodule_tests/detection_nullary_tests.rs"]
mod detection_nullary_tests;

#[path = "quantifier_ctor_elim_submodule_tests/detection_rejection_tests.rs"]
mod detection_rejection_tests;

#[path = "quantifier_ctor_elim_submodule_tests/detection_empty_qvars_tests.rs"]
mod detection_empty_qvars_tests;

#[path = "quantifier_ctor_elim_submodule_tests/detection_argument_rejection_tests.rs"]
mod detection_argument_rejection_tests;

#[path = "quantifier_ctor_elim_submodule_tests/batch_inference_tests.rs"]
mod batch_inference_tests;

#[path = "quantifier_ctor_elim_submodule_tests/batch_inference_direct_tests.rs"]
mod batch_inference_direct_tests;

#[path = "quantifier_ctor_elim_submodule_tests/batch_inference_branch_propagation_tests.rs"]
mod batch_inference_branch_propagation_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_tests.rs"]
mod sort_inference_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_binding_tests.rs"]
mod sort_inference_binding_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_binding_let_tests.rs"]
mod sort_inference_binding_let_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_binding_closure_tests.rs"]
mod sort_inference_binding_closure_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_binding_quantifier_tests.rs"]
mod sort_inference_binding_quantifier_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_wrapper_tests.rs"]
mod sort_inference_wrapper_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_propagation_tests.rs"]
mod sort_inference_propagation_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_method_call_tests.rs"]
mod sort_inference_method_call_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_control_flow_tests.rs"]
mod sort_inference_control_flow_tests;

#[path = "quantifier_ctor_elim_submodule_tests/sort_inference_direct_tests.rs"]
mod sort_inference_direct_tests;

#[path = "quantifier_ctor_elim_submodule_tests/batch_consistency_tests.rs"]
mod batch_consistency_tests;

#[path = "quantifier_ctor_elim_submodule_tests/round_trip_integration_tests.rs"]
mod round_trip_integration_tests;

#[path = "quantifier_ctor_elim_submodule_tests/arg_is_any_qvar_reference_tests.rs"]
mod arg_is_any_qvar_reference_tests;

#[path = "quantifier_ctor_elim_submodule_tests/fixtures.rs"]
mod fixtures;

pub(crate) use fixtures::*;
