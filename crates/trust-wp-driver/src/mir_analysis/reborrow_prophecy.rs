// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recognizer for the "recursive `&mut self` match-reborrow, divergent other
//! arms" shape (the rusthorn `take_some` benchmarks).
//!
//! Such a function matches `*self` into a single non-diverging enum variant,
//! reborrows the variant's fields, and returns one field's reborrow (or the
//! result of recursing on a field) selected by data-independent branches. The
//! post-borrowck MIR carries the exact structure:
//!
//! ```text
//! _R_i = &mut (((*_1) as Variant).i)     // one field reborrow per used field
//! _C   = Self::method(move recv)         // recv reborrows field j (recursion)
//! ```
//!
//! This module extracts, for such a body, which enum field each recursion
//! touches (via its receiver) so that [`per_contract`] can synthesize the
//! sound prophecy-pinning premise
//! `^self == Variant(f0, .., fn)` — see the module docs there. The analysis
//! is deliberately fail-closed: any deviation from the recognized mutation-free
//! shape returns `None`, so no premise is emitted.
//!
//! [`per_contract`]: crate::callbacks::verification::per_contract

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};

use super::call_resolve::extract_call_def_id;

/// Recognized reborrow-prophecy structure for a `&mut self` method.
#[derive(Debug, Clone)]
pub(crate) struct ReborrowProphecyInfo {
    /// Number of fields in the matched (single non-diverging) enum variant.
    pub(crate) field_count: usize,
    /// Map from a recursive self-call's destination local index to the enum
    /// field index that recursion touches (via its `&mut` receiver).
    pub(crate) call_local_to_field: HashMap<u32, usize>,
}

/// Recognize the recursive `&mut self` match-reborrow shape and return the
/// per-recursion field mapping, or `None` if the body is not the exact
/// mutation-free shape the sound premise requires.
pub(crate) fn analyze_reborrow_prophecy<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_def_id: DefId,
    body: &Body<'tcx>,
    arg_names: &[String],
) -> Option<ReborrowProphecyInfo> {
    // Gate: a single `&mut self` parameter over an enum referent.
    if arg_names.len() != 1 || arg_names[0] != "self" {
        return None;
    }
    let self_local = Local::from_u32(1);
    let self_ty = body.local_decls.get(self_local)?.ty;
    let TyKind::Ref(_, referent, rustc_ast::Mutability::Mut) = self_ty.kind() else {
        return None;
    };
    let TyKind::Adt(adt_def, _) = referent.kind() else {
        return None;
    };
    if !adt_def.is_enum() {
        return None;
    }
    let _ = tcx;

    // Gate: the body performs NO writes through a reference, and never
    // reassigns `self` itself. A field reborrow's final value equals its
    // current value UNLESS that field is returned or recursed upon — which the
    // touched-condition premise accounts for exactly. A deref-write, or a
    // rebinding of `self`, could silently change a field, so either is fatal.
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            if let StatementKind::Assign(boxed) = &stmt.kind {
                let (place, _rv) = &**boxed;
                if place.local == self_local {
                    return None;
                }
                if place
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Deref))
                {
                    return None;
                }
            }
        }
        if let Some(term) = &bb.terminator {
            if let TerminatorKind::Call { destination, .. } = &term.kind {
                if destination
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Deref))
                {
                    return None;
                }
            }
        }
    }

    // Collect field reborrows `_R = &mut (((*_1) as Variant).i)` and plain
    // reborrow / move chains `_L = &mut (*X ..)` / `_L = move X`.
    let mut field_reborrows: HashMap<Local, (u32, usize)> = HashMap::new();
    let mut reborrow_src: HashMap<Local, Local> = HashMap::new();
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let StatementKind::Assign(boxed) = &stmt.kind else {
                continue;
            };
            let (dest, rv) = &**boxed;
            if !dest.projection.is_empty() {
                continue;
            }
            match rv {
                // Only MUTABLE reborrows can carry a mutation capability to a
                // field. A shared reborrow (`&(*x)`) cannot mutate, so it must
                // not connect a downstream arg back to a field reborrow (that
                // would spuriously bail on ghost lemma calls like
                // `snapshot! { ml.lemma() }`).
                Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Mut { .. }, src_place) => {
                    let projs: Vec<_> = src_place.projection.iter().collect();
                    if src_place.local == self_local {
                        if let [ProjectionElem::Deref, ProjectionElem::Downcast(_, vidx), ProjectionElem::Field(fidx, _)] =
                            projs.as_slice()
                        {
                            field_reborrows.insert(dest.local, (vidx.as_u32(), fidx.as_usize()));
                            continue;
                        }
                    }
                    reborrow_src.insert(dest.local, src_place.local);
                }
                Rvalue::Use(Operand::Move(src_place) | Operand::Copy(src_place), _)
                | Rvalue::CopyForDeref(src_place) => {
                    reborrow_src.insert(dest.local, src_place.local);
                }
                _ => {}
            }
        }
    }
    if field_reborrows.is_empty() {
        return None;
    }

    // The matched variant must be consistent across all field reborrows.
    let mut variant_index: Option<u32> = None;
    for (_l, (v, _f)) in &field_reborrows {
        match variant_index {
            None => variant_index = Some(*v),
            Some(existing) if existing != *v => return None,
            _ => {}
        }
    }
    let variant_index = variant_index?;
    let variant = adt_def
        .variants()
        .iter()
        .find(|v| adt_def.variant_index_with_id(v.def_id).as_u32() == variant_index)?;
    let field_count = variant.fields.len();

    // Trace a local back to the enum field it (transitively) reborrows.
    let trace_field = |start: Local| -> Option<usize> {
        let mut local = start;
        for _ in 0..64 {
            if let Some((_v, f)) = field_reborrows.get(&local) {
                return Some(*f);
            }
            match reborrow_src.get(&local) {
                Some(src) => local = *src,
                None => return None,
            }
        }
        None
    };

    // Map each recursive self-call's destination to the field it touches.
    let mut call_local_to_field: HashMap<u32, usize> = HashMap::new();
    for bb in body.basic_blocks.iter() {
        let Some(term) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            continue;
        };
        // Which fields do this call's args reborrow?
        let mut arg_fields: Vec<usize> = Vec::new();
        for arg in args.iter() {
            let place = match &arg.node {
                Operand::Move(p) | Operand::Copy(p) => p,
                _ => continue,
            };
            if let Some(fidx) = trace_field(place.local) {
                arg_fields.push(fidx);
            }
        }
        let is_recursion = extract_call_def_id(func) == Some(self_def_id);
        // A field reborrow may only flow into a self-recursion (whose mutation
        // effect is the receiver field, accounted for by the touched premise).
        // Passing one to any other call, or to a recursion alongside a second
        // field reborrow, could mutate a field off the accounted branch.
        if !arg_fields.is_empty() && (!is_recursion || arg_fields.len() != 1) {
            return None;
        }
        if is_recursion && arg_fields.len() == 1 && destination.projection.is_empty() {
            call_local_to_field.insert(destination.local.as_u32(), arg_fields[0]);
        }
    }

    Some(ReborrowProphecyInfo {
        field_count,
        call_local_to_field,
    })
}
