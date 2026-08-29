// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR place analysis utilities for mutable borrow extraction.
//!
//! Stateless helpers for inspecting MIR places, projections, and rvalues.

use std::collections::HashMap;

use rustc_middle::{
    mir::{Body, Local, Place},
    ty::{Ty, TyKind},
};

use super::data::DerefTarget;

/// Resolve a local to its originating `&mut` parameter.
///
/// Returns `Some(local)` if `base_local` is itself a `&mut` param, or
/// `Some(origin)` if it transitively reborrows one via `reborrow_map`.
/// Returns `None` if the local is unrelated to any tracked `&mut` param.
pub(super) fn resolve_reborrow_param_local(
    base_local: Local,
    mut_borrow_params: &[Local],
    reborrow_map: &HashMap<Local, Local>,
) -> Option<Local> {
    if mut_borrow_params.contains(&base_local) {
        return Some(base_local);
    }
    reborrow_map.get(&base_local).copied()
}

/// Determine the deref target of a write through a mutable borrow.
///
/// Inspects MIR place projections to classify writes:
/// - `*v = expr` → `Whole(v)` (simple deref)
/// - `(*_1).N = expr` → `Field(_1, N)` (closure capture field)
/// - `*((*_1).N) = expr` → `Field(_1, N)` (FnMut capture by &mut)
/// - `*(v.0) = expr` → `Whole(v)` (newtype wrapping &mut)
/// - `(v).N.deref = expr` → `Field(v, N)` (tuple with inner &mut)
pub(super) fn get_deref_target(
    place: &Place<'_>,
    body: &Body<'_>,
    mut_borrow_params: &[Local],
    reborrow_map: &HashMap<Local, Local>,
) -> Option<DerefTarget> {
    use rustc_middle::mir::ProjectionElem;

    let projections: Vec<_> = place.projection.iter().collect();

    // Check for patterns that write through a tracked closure-capture field.
    //
    // We keep the target at the owning capture field even if the write passes
    // through wrapper projections such as `Box<&mut T>` or
    // `Box<Box<&mut T>>`. Those shapes can appear either as:
    // - `(*_1).N` for an `&mut` closure env
    // - `(_1).N` for a by-value closure env
    // followed by one or more trailing derefs that eventually reach the
    // mutable reference being written through.
    //
    // Matching from the outside inward lets us ignore any number of leading
    // wrapper derefs before the first field projection, while still requiring
    // that the tail after that field is only derefs.
    if let Some((base_local, field_idx)) =
        tracked_capture_field_target(&projections, place.local, mut_borrow_params, reborrow_map)
    {
        return Some(DerefTarget::Field(base_local, field_idx));
    }

    // Check for pattern: (*_N).field where _N is a mutable borrow param
    // This is a FnMut closure capture field write: (*_1).0 = expr
    // Check for pattern: (v).field.deref — writing through inner `&mut` inside a newtype.
    // For `HasMutRef<'_, u32>(pub &'a mut u32)`, MIR for `*x.0 = 5` is:
    //   Place { local: _1, projection: [Field(0, &mut u32), Deref] }
    // This writes through the inner mutable reference, logically updating
    // the value tracked by deref_exprs[_1].
    if projections.len() == 2 {
        if let (ProjectionElem::Field(field, field_ty), ProjectionElem::Deref) =
            (projections[0], projections[1])
        {
            let base_local = place.local;
            // Resolve base_local: either a direct &mut param or a reborrow of one (#1682)
            let resolved = if mut_borrow_params.contains(&base_local) {
                Some(base_local)
            } else {
                reborrow_map.get(&base_local).copied()
            };
            if let Some(param_local) = resolved {
                // For single-field structs (newtypes) where field 0 is `&mut T`,
                // treat as a whole-deref write (the newtype is just a wrapper).
                // Use the resolved param's type for the newtype check.
                let param_ty = body.local_decls[param_local].ty;
                let is_newtype = matches!(param_ty.kind(), TyKind::Adt(adt_def, _)
                    if adt_def.is_struct()
                        && adt_def.variants().iter().next().is_some_and(|v| v.fields.len() == 1));
                if is_newtype && field.as_u32() == 0 {
                    // Newtype wrapping &mut: *(x.0) = expr => Whole write
                    return Some(DerefTarget::Whole(param_local));
                }
                // For tuples or multi-field structs, this is a field-level
                // deref write. Check that the field type is actually &mut.
                if matches!(
                    field_ty.kind(),
                    TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                ) {
                    return Some(DerefTarget::Field(param_local, field.as_u32()));
                }
            }
        }
    }

    // Check for pattern: *_N where _N is a mutable borrow param
    // or *_M where _M is a reborrow of a mutable borrow param
    if projections.len() == 1 {
        if let ProjectionElem::Deref = projections[0] {
            let base_local = place.local;
            // Direct deref of mutable borrow param
            if mut_borrow_params.contains(&base_local) {
                return Some(DerefTarget::Whole(base_local));
            }

            // Check if base_local is a reborrow of a &mut param (#1682)
            if let Some(&origin) = reborrow_map.get(&base_local) {
                return Some(DerefTarget::Whole(origin));
            }
        }
    }
    None
}

fn tracked_capture_field_target(
    projections: &[rustc_middle::mir::ProjectionElem<Local, Ty<'_>>],
    base_local: Local,
    mut_borrow_params: &[Local],
    reborrow_map: &HashMap<Local, Local>,
) -> Option<(Local, u32)> {
    use rustc_middle::mir::ProjectionElem;

    let resolved_local = resolve_reborrow_param_local(base_local, mut_borrow_params, reborrow_map)?;

    let mut idx = 0;
    while idx < projections.len() && matches!(projections[idx], ProjectionElem::Deref) {
        idx += 1;
    }

    let ProjectionElem::Field(field, _) = projections.get(idx).copied()? else {
        return None;
    };

    if projections[idx + 1..]
        .iter()
        .all(|projection| matches!(*projection, ProjectionElem::Deref))
    {
        Some((resolved_local, field.as_u32()))
    } else {
        None
    }
}
