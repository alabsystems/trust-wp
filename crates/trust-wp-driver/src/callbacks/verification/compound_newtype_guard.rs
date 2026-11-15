// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fail-closed guard: aggregate construction of a compound single-field struct.
//!
//! `build_newtype_param_set` keeps the field projection `tuple_get_0(p)` for a
//! single-field struct that keeps its native Datatype sort and whose field is
//! compound (`W(Vec<u64>)`, `Tp((u64, u64))`, `Ar([u64; 2])`): collapsing it
//! identified the struct with its field (cell/02_fib encoder panic). The MIR
//! aggregate lowering, however, still collapses `W(v)` to `v`, so a value
//! built by an aggregate is a field-sorted term standing for a struct-sorted
//! one. Returned, wrapped (`Some(W(v))`, `(W(v), 1)`) or passed to a callee,
//! that mismatch let false contracts verify. Until the aggregate lowers to a
//! constructor term whose projection is the field, refuse such bodies.

use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{AggregateKind, Body, Rvalue, StatementKind},
    ty::TyCtxt,
};

use crate::{
    callbacks::{
        try_get_body_with_context, type_invariants::is_compound_native_single_field_struct,
    },
    mir_analysis::get_mir_body,
};

/// Return the path of the first compound native single-field struct built by
/// an aggregate in the body of `local_def_id`, if any.
pub(super) fn compound_newtype_aggregate_in_body(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
) -> Option<String> {
    let body_with_facts = try_get_body_with_context(tcx, local_def_id)?;
    first_compound_newtype_aggregate(tcx, get_mir_body(&body_with_facts))
}

fn first_compound_newtype_aggregate<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Option<String> {
    for bb_data in body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            let StatementKind::Assign((
                _,
                Rvalue::Aggregate(AggregateKind::Adt(def_id, _, args, ..), _),
            )) = &stmt.kind
            else {
                continue;
            };
            let adt_def = tcx.adt_def(*def_id);
            if is_compound_native_single_field_struct(tcx, adt_def, *args) {
                return Some(tcx.def_path_str(*def_id));
            }
        }
    }
    None
}

/// Report and count the compound-newtype refusal for `def_path`, if the body
/// builds one. Returns `false` when the contract was refused; the caller must
/// stop.
///
/// The detection and the refusal live together on purpose: a guard whose
/// report sits in another file is a guard that a later edit can drop without
/// the detection noticing.
pub(super) fn refuse_compound_newtype_aggregate(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
    def_path: &str,
    errors: &mut usize,
) -> bool {
    let Some(ty_name) = compound_newtype_aggregate_in_body(tcx, local_def_id) else {
        return true;
    };
    eprintln!(
        "trust-wp: {def_path} error: unsupported aggregate construction of compound \
         single-field struct `{ty_name}` (the body lowering of `{ty_name}(..)` does not \
         align with the field projection kept by contracts; refusing instead of \
         risking an unsound proof)"
    );
    *errors += 1;
    false
}
