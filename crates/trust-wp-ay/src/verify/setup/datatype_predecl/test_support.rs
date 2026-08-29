// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::DatatypeSort;
#[cfg(test)]
use ay_dpll::api::{DatatypeConstructor, DatatypeField, Sort};
#[cfg(test)]
use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtDecls};
use trust_wp_core::{formula::PureExpr, logic::LogicFnDef};

use super::collect_bootstrap_datatype_var_sorts;
#[cfg(test)]
use crate::encoder::{sort_context::expr_sort_to_ay_sort, AYEncoder};

#[cfg(test)]
/// Convert a driver-provided `AdtDecl` into a ay `DatatypeSort` for solver
/// declaration. Maps each constructor and field from the Rust-level metadata
/// to ay's native datatype representation. (#1982 Slice 3)
pub(in crate::verify) fn adt_decl_to_datatype_sort(decl: &AdtDecl) -> DatatypeSort {
    let constructors = decl
        .constructors
        .iter()
        .map(adt_constructor_to_ay)
        .collect();
    DatatypeSort::new(&decl.adt_name, constructors)
}

#[cfg(test)]
fn adt_constructor_to_ay(ctor: &AdtConstructorDecl) -> DatatypeConstructor {
    let fields = ctor
        .fields
        .iter()
        .map(|f| DatatypeField::new(&f.name, expr_sort_to_ay_sort(&f.sort)))
        .collect();
    DatatypeConstructor::new(&ctor.smt_name, fields)
}

/// Pre-declare datatypes and variables with Datatype sorts.
///
/// Test-only wrapper retained for targeted setup regression coverage. Production
/// bootstrap now collects these sorts into `SortPlan` and applies them once.
#[cfg(test)]
pub(in crate::verify) fn predeclare_datatype_vars(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    context_exprs: &[&PureExpr],
    logic_fns: Option<&[LogicFnDef]>,
    adt_decls: Option<&AdtDecls>,
) {
    // Pass 0: Register driver-provided ADT declarations before any heuristic
    // scanning. This makes registered datatypes available for match-arm lookups
    // in Pass 1 and call-site propagation in Pass 2. (#1982 Slice 3)
    if let Some(decls) = adt_decls {
        for decl in decls.values() {
            let dt = adt_decl_to_datatype_sort(decl);
            encoder.ensure_datatype_declared(&dt);
        }
    }

    let mut input_exprs: Vec<&PureExpr> = requires.iter().collect();
    input_exprs.extend(ensures.iter());
    input_exprs.extend(context_exprs.iter().copied());
    let postcondition_exprs = if ensures.is_empty() {
        None
    } else {
        Some(ensures)
    };
    let dt_vars = collect_bootstrap_datatype_var_sorts(
        &input_exprs,
        postcondition_exprs,
        logic_fns,
        &encoder
            .decls()
            .datatypes_iter()
            .cloned()
            .collect::<Vec<_>>(),
    );

    for (var_name, dt) in &dt_vars {
        encoder.ensure_datatype_declared(dt);
        let _ = encoder.get_or_declare_var(var_name, Sort::Datatype(dt.clone()));
    }
}
