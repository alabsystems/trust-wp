// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for callbacks module - thread-local caches, parameter normalization,
//! call assumption analysis, final variable extraction, and logic function
//! mode scoping.

use std::{
    fs,
    sync::{atomic::Ordering, Arc},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
        BinOp, ExprSort, MatchArm, Pattern, PureExpr, UnOp,
    },
    logic::LogicMode,
};

use super::{
    closure_enrichment::{
        final_receiver_state_expr, strip_deref_wrappers, strip_receiver_state_wrappers,
    },
    helpers::{
        analyze_call_assumptions, expr_contains_old, extract_final_vars, parent_module,
        scope_logic_fn_modes, synthesize_identity_final_values,
    },
    parsing::build_param_normalization,
    proof_assert_extract::{
        apply_projected_writes_to_substitutions, apply_type_and_field_rewrites,
        collapse_idempotent_views, is_deref_precondition, normalize_scalar_proof_assert_boundary,
        normalize_view_fn_calls,
    },
    should_preload_builtin_extern_specs,
    thread_locals::{clear_caches, CacheGuard, EXTERN_SPECS, MIR_BODIES},
};
use crate::mir_analysis::{
    clear_qualified_assoc_const_definitions,
    extract::{record_qualified_assoc_const_definition, UNEVAL_CONST_EXPANSION_DEPTH},
    take_qualified_assoc_const_definitions,
};

mod shared;

mod caches;
mod identity_final_values;
mod params_analysis;
mod scalar_rewrites;
mod scope;
mod view_normalization;
mod wrappers;

#[test]
fn test_should_preload_builtin_extern_specs_skips_trust_wp_std() {
    assert!(!should_preload_builtin_extern_specs("trust_wp_std"));
    assert!(should_preload_builtin_extern_specs("trust-wp"));
    assert!(should_preload_builtin_extern_specs("closure_project"));
}
