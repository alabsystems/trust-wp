// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use trust_wp_core::formula::PureExpr;
use trust_wp_driver::StdSpec;

use crate::contracts::{FunctionContract, TraitMethodContract};

pub(in crate::callbacks) fn build_user_spec_table(
    contracts: &[FunctionContract],
) -> HashMap<DefId, StdSpec> {
    let mut specs = HashMap::new();
    for contract in contracts {
        if contract.requires.is_empty() && contract.ensures.is_empty() {
            continue;
        }
        specs.insert(
            contract.def_id,
            StdSpec {
                requires: contract.requires.clone(),
                ensures: contract.ensures.clone(),
                param_names: None,
            },
        );
    }
    specs
}

pub(in crate::callbacks) fn build_trait_spec_table(
    trait_contracts: &[TraitMethodContract],
) -> HashMap<DefId, StdSpec> {
    let mut specs = HashMap::new();
    for contract in trait_contracts {
        if contract.requires.is_empty() && contract.ensures.is_empty() {
            continue;
        }
        specs.insert(
            contract.method_def_id,
            StdSpec {
                requires: contract.requires.clone(),
                ensures: contract.ensures.clone(),
                param_names: None,
            },
        );
    }
    specs
}

/// Build a parameter-name substitution map for trait refinement checks.
///
/// When a trait declares `fn foo(&self, x: i32)` and an impl uses
/// `fn foo(&self, y: i32)`, the refinement check needs to normalize
/// `y` → `x` in the impl's contracts so the SMT variables align.
pub(in crate::callbacks) fn build_param_normalization(
    trait_names: &[String],
    impl_names: &[String],
) -> Option<HashMap<String, PureExpr>> {
    if trait_names.len() != impl_names.len() {
        return None;
    }

    let mut substitutions = HashMap::new();
    for (trait_name, impl_name) in trait_names.iter().zip(impl_names.iter()) {
        if trait_name != impl_name {
            substitutions.insert(impl_name.clone(), PureExpr::Var(trait_name.clone(), None));
        }
    }
    Some(substitutions)
}
