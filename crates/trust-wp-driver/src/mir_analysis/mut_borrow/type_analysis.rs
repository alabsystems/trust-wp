// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type-level mutable reference analysis.
//!
//! Pure type-inspection functions that determine whether types contain `&mut`
//! references and extract projection paths to those references.

use rustc_middle::{
    mir::{Body, Local},
    ty::{TyCtxt, TyKind, CAPTURE_STRUCT_LOCAL},
};
use trust_wp_core::formula::ExprSort;

use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

/// Declared closure-capture field metadata used to seed mut-borrow tracking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ClosureFieldSeed {
    pub(super) field_idx: u32,
    pub(super) sort: Option<ExprSort>,
}

/// Check if a type contains a trackable `&mut` reference.
///
/// Returns `true` for:
/// - `&mut T` (direct mutable reference)
/// - `(&mut T, U)`, `(T, &mut U)`, etc. (tuple containing `&mut`)
/// - `&mut (T, &mut U)` (mutable ref to tuple with inner `&mut`)
/// - `HasMutRef<'a, T>` where `HasMutRef(pub &'a mut T)` (newtype wrapping `&mut`)
///
/// Returns `false` for currently unsupported nested by-value paths where every
/// mutable reference appears deeper than one field projection (for example
/// `((i32, &mut i32), i32)` yields path `[0, 1]` only).
///
/// Requires `TyCtxt` for ADT field type resolution. Use the non-tcx
/// overload for contexts where `TyCtxt` is unavailable.
pub(crate) fn type_contains_mut_ref_with_tcx<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    collect_mut_ref_paths_with_tcx(tcx, ty)
        .iter()
        .any(|path| path.is_empty() || path.len() == 1)
}

/// One step of a [`MutRefPinPath`].
///
/// `Field` covers tuple elements and struct fields (both are reached with the
/// positional getter downstream); `Variant` covers an enum payload and carries
/// the constructor name because the pin it addresses MUST be guarded by that
/// constructor's tester. (#prophecy-slots M5)
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MutRefPinStep {
    /// Tuple element / struct field index.
    Field(u32),
    /// Enum variant payload: `variant_idx` for MIR `Downcast` matching, `ctor`
    /// for the encoder-side tester, `field` for the payload position.
    Variant {
        variant_idx: u32,
        ctor: String,
        field: u32,
    },
}

/// A projection path from a type down to an embedded `&mut`.
pub(crate) type MutRefPinPath = Vec<MutRefPinStep>;

/// Depth cap for [`collect_mut_ref_pin_paths_with_tcx`].
///
/// `Option<(&mut T, &mut U)>` — the canonical `split_first_mut` shape and the
/// reason this collector exists — needs depth 2 (`Variant{Some,0}` then
/// `Field(i)`). The cap is 4 so a newtype or one extra wrapper layer still
/// resolves, while recursive enum types (`List<&mut T>`) terminate.
const MUT_REF_PIN_PATH_MAX_DEPTH: usize = 4;

/// Hard node budget for the pin-path walk.
///
/// Unlike the legacy collector (tuples + newtypes only), this one enters every
/// field of every struct and every field of every enum variant, so a wide type
/// could otherwise cost `fields^depth`. The budget makes the walk O(1) in the
/// worst case; it is far above anything the corpus's types reach, and the cut
/// is deterministic (fixed DFS order), so it can only ever drop deep paths —
/// never change the length-0/1 answers the legacy view is built from.
const MUT_REF_PIN_PATH_NODE_BUDGET: usize = 20_000;

/// Collect mutable-reference projection paths within a type, INCLUDING paths
/// that pass through enum variants. (#prophecy-slots M5)
///
/// This is the enum-aware superset of [`collect_mut_ref_paths_with_tcx`]. The
/// legacy collector was structurally unable to see the primary Fix-B shape:
/// it recursed into exactly `TyKind::Tuple` and SINGLE-FIELD STRUCTS, so
/// `Option<&mut T>` produced the empty path set and a `&mut` inside a returned
/// enum payload was invisible to every downstream consumer. Enums are entered
/// here, each variant contributing a [`MutRefPinStep::Variant`] step so the
/// projection stays inseparable from the tester that makes it meaningful.
///
/// Examples (variant steps abbreviated `V{ctor,field}`):
/// - `&mut T` -> `[[]]`
/// - `(&mut T, &mut U)` -> `[[Field 0], [Field 1]]`
/// - `Option<&mut T>` -> `[[V{Some,0}]]`
/// - `Option<(&mut T, &mut U)>` -> `[[V{Some,0}, Field 0], [V{Some,0}, Field 1]]`
/// - `HasMutRef<'a, T>(pub &'a mut T)` -> `[[Field 0]]`
///
/// Multi-field structs are entered field-wise (the legacy collector only
/// unwrapped newtypes); that is a strict superset and only ever ADDS paths,
/// which is why the legacy view below filters rather than re-derives.
pub(crate) fn collect_mut_ref_pin_paths_with_tcx<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Vec<MutRefPinPath> {
    fn rec<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: rustc_middle::ty::Ty<'tcx>,
        path: &mut MutRefPinPath,
        out: &mut Vec<MutRefPinPath>,
        depth: usize,
        budget: &mut usize,
    ) {
        if depth > MUT_REF_PIN_PATH_MAX_DEPTH || *budget == 0 {
            return;
        }
        *budget -= 1;
        match ty.kind() {
            TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Mut) => {
                out.push(path.clone());
                rec(tcx, *inner, path, out, depth + 1, budget);
            }
            TyKind::Tuple(fields) => {
                for (idx, field_ty) in fields.iter().enumerate() {
                    let Ok(field_idx) = u32::try_from(idx) else {
                        continue;
                    };
                    path.push(MutRefPinStep::Field(field_idx));
                    rec(tcx, field_ty, path, out, depth + 1, budget);
                    path.pop();
                }
            }
            // `Box<T, A>` and friends are compiler-known indirections whose
            // internal fields are not a stable way to recover `T`; the pin lane
            // has no business projecting through them, so they are left out
            // (fail-closed: no path means no pin).
            TyKind::Adt(adt_def, _) if adt_def.is_box() => {}
            TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
                for (idx, field) in adt_def.non_enum_variant().fields.iter().enumerate() {
                    let Ok(field_idx) = u32::try_from(idx) else {
                        continue;
                    };
                    let field_ty = field.ty(tcx, substs).skip_norm_wip();
                    path.push(MutRefPinStep::Field(field_idx));
                    rec(tcx, field_ty, path, out, depth + 1, budget);
                    path.pop();
                }
            }
            // ★THE M5 ARM. Every variant is entered separately, and the step
            // records the constructor: a pin reached through this step is only
            // meaningful under `is-<ctor>(receiver)`.
            TyKind::Adt(adt_def, substs) if adt_def.is_enum() => {
                for (variant_idx, variant) in adt_def.variants().iter_enumerated() {
                    let Ok(variant_u32) = u32::try_from(variant_idx.as_usize()) else {
                        continue;
                    };
                    for (field_pos, field) in variant.fields.iter().enumerate() {
                        let Ok(field_idx) = u32::try_from(field_pos) else {
                            continue;
                        };
                        let field_ty = field.ty(tcx, substs).skip_norm_wip();
                        path.push(MutRefPinStep::Variant {
                            variant_idx: variant_u32,
                            ctor: variant.name.to_string(),
                            field: field_idx,
                        });
                        rec(tcx, field_ty, path, out, depth + 1, budget);
                        path.pop();
                    }
                }
            }
            _ => {}
        }
    }

    let mut out = Vec::new();
    let mut budget = MUT_REF_PIN_PATH_NODE_BUDGET;
    rec(tcx, ty, &mut Vec::new(), &mut out, 0, &mut budget);
    out
}

/// Collect mutable-reference projection paths within a type.
///
/// Path segments correspond to tuple/newtype field indices. An empty path (`[]`)
/// means the type itself is a mutable reference.
///
/// Examples:
/// - `&mut T` -> `[[]]`
/// - `(&mut T, &mut U)` -> `[[0], [1]]`
/// - `&mut (i32, &mut i32)` -> `[[], [1]]`
/// - `HasMutRef<'a, T>(pub &'a mut T)` -> `[[0]]`
///
/// ## Why this is a FILTERED VIEW of the enum-aware collector (#prophecy-slots M5)
///
/// This function feeds `type_contains_mut_ref_with_tcx`, which decides
/// `find_mut_borrow_params` — i.e. which parameters enter RustHorn tracking at
/// all. Widening it is a corpus-wide behaviour change with no bearing on the
/// pin lane, so M5 deliberately keeps it BYTE-EQUIVALENT: variant-bearing paths
/// are dropped, and multi-field structs (which the legacy recursion never
/// entered) are dropped by requiring the struct to be a newtype. One recursion,
/// one source of truth, and the equivalence is pinned by unit tests.
pub(crate) fn collect_mut_ref_paths_with_tcx<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Vec<Vec<u32>> {
    collect_mut_ref_pin_paths_with_tcx(tcx, ty)
        .into_iter()
        .filter_map(|path| legacy_field_path(tcx, ty, &path))
        .collect()
}

/// Project a pin path onto the legacy `Vec<u32>` field-index view, or `None`
/// when the legacy recursion would never have produced it (a variant step, or a
/// field of a struct with more than one field).
fn legacy_field_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    root_ty: rustc_middle::ty::Ty<'tcx>,
    path: &MutRefPinPath,
) -> Option<Vec<u32>> {
    let mut current = root_ty;
    let mut out = Vec::with_capacity(path.len());
    for step in path {
        // Peel any `&mut` layers the legacy recursion peeled implicitly.
        while let TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Mut) = current.kind() {
            current = *inner;
        }
        let MutRefPinStep::Field(field_idx) = step else {
            return None; // variant step: not reachable in the legacy lane
        };
        match current.kind() {
            TyKind::Tuple(fields) => {
                current = fields.get(*field_idx as usize).copied()?;
            }
            TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
                let variant = adt_def.variants().iter().next()?;
                if variant.fields.len() != 1 {
                    return None; // legacy unwrapped NEWTYPES only
                }
                let field = variant.fields.iter().next()?;
                current = field.ty(tcx, substs).skip_norm_wip();
            }
            _ => return None,
        }
        out.push(*field_idx);
    }
    Some(out)
}

/// Derive directly trackable closure fields from rustc's declared capture order.
///
/// This is the source of truth for mut-borrow closure-field seeding. The old
/// MIR-projection-count heuristic only reflected what the current body happened
/// to project, while closure metadata preserves the declared environment shape.
pub(super) fn direct_closure_field_seeds<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    env_local: Local,
) -> Vec<ClosureFieldSeed> {
    closure_capture_fields_with_eventual_mut_ref(tcx, body, env_local)
        .into_iter()
        .map(|(field_idx, upvar_ty)| ClosureFieldSeed {
            field_idx,
            sort: ty_to_expr_sort_enriched(tcx, upvar_ty),
        })
        .collect()
}

/// Return the top-level closure capture fields whose types eventually contain `&mut`.
///
/// This is the closure-env-specific Slice 1 admission rule for #2318. We keep
/// the mut-borrow tracking boundary at the owning capture field (`self.N`) even
/// when the nested mutable reference sits behind wrapper chains such as
/// `Box<&mut T>` or `Box<Box<&mut T>>`.
fn closure_capture_fields_with_eventual_mut_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    env_local: Local,
) -> Vec<(u32, rustc_middle::ty::Ty<'tcx>)> {
    if env_local != CAPTURE_STRUCT_LOCAL {
        return Vec::new();
    }

    let env_ty = body.local_decls[env_local].ty;
    let (closure_def_id, substs) = match env_ty.kind() {
        TyKind::Closure(def_id, substs) => (*def_id, substs),
        TyKind::Ref(_, inner, _) => match inner.kind() {
            TyKind::Closure(def_id, substs) => (*def_id, substs),
            _ => return Vec::new(),
        },
        _ => return Vec::new(),
    };
    let Some(local_def_id) = closure_def_id.as_local() else {
        return Vec::new();
    };

    tcx.closure_captures(local_def_id)
        .iter()
        .zip(substs.as_closure().upvar_tys())
        .enumerate()
        .filter_map(|(idx, (_capture, upvar_ty))| {
            if !type_eventually_contains_mut_ref(tcx, upvar_ty) {
                return None;
            }

            Some((u32::try_from(idx).ok()?, upvar_ty))
        })
        .collect()
}

/// Check if a type eventually contains a `&mut T` reference at any depth.
///
/// Unlike `type_contains_mut_ref_with_tcx` (which restricts to depth 0 or 1)
/// and `collect_mut_ref_paths_with_tcx` (which only recurses into single-field
/// ADTs), this walks through ALL fields of ALL ADT variants to arbitrary depth.
///
/// This is necessary because `Box<T, A>` has two fields (pointer + allocator),
/// so `collect_mut_ref_paths_with_tcx` skips it. But the pointer field
/// (`Unique<T>` -> `NonNull<T>` -> `*const T`) does eventually contain `&mut T`
/// when `T` is `&mut U`. We also walk through raw pointer types (`*const T`,
/// `*mut T`) since Box's internal representation uses them.
///
/// Used for closure-env-specific admission where the top-level capture field
/// must be tracked even when the inner `&mut` is behind multiple wrappers.
///
/// Examples:
/// - `&mut T` -> true
/// - `Box<&mut T>` -> true (through Unique -> NonNull -> *const -> &mut)
/// - `Box<Box<&mut T>>` -> true
/// - `i32` -> false
/// - `Box<i32>` -> false
pub(crate) fn type_eventually_contains_mut_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    // First try the fast path: single-field ADT chain.
    if !collect_mut_ref_paths_with_tcx(tcx, ty).is_empty() {
        return true;
    }
    // Slow path: walk through all ADT fields and raw pointers.
    deep_contains_mut_ref(tcx, ty, 0)
}

/// Recursive deep search for `&mut T` through all ADT fields and pointer types.
///
/// The `depth` parameter prevents infinite recursion on recursive types.
const MAX_MUT_REF_SEARCH_DEPTH: usize = 8;

fn deep_contains_mut_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    depth: usize,
) -> bool {
    if depth > MAX_MUT_REF_SEARCH_DEPTH {
        return false;
    }
    match ty.kind() {
        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut) => true,
        TyKind::Ref(_, inner, _) => deep_contains_mut_ref(tcx, *inner, depth + 1),
        TyKind::RawPtr(inner, _) => deep_contains_mut_ref(tcx, *inner, depth + 1),
        TyKind::Tuple(fields) => fields
            .iter()
            .any(|field_ty| deep_contains_mut_ref(tcx, field_ty, depth + 1)),
        // `Box<T, A>` is a compiler-known owning indirection. Its internal ADT
        // fields are intentionally not a stable way to recover `T` (and are no
        // longer exposed as an ordinary struct payload by Trust 1.99), so walk
        // the semantic pointee argument directly. This also avoids coupling
        // capture admission to allocator/layout implementation details.
        TyKind::Adt(adt_def, substs) if adt_def.is_box() => {
            deep_contains_mut_ref(tcx, substs.type_at(0), depth + 1)
        }
        TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
            if let Some(variant) = adt_def.variants().iter().next() {
                variant.fields.iter().any(|field| {
                    let field_ty = field.ty(tcx, substs).skip_norm_wip();
                    deep_contains_mut_ref(tcx, field_ty, depth + 1)
                })
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check if a type is a single-field ADT (newtype) wrapping `&mut T`.
///
/// Returns true for patterns like `struct HasMutRef<'a, T>(pub &'a mut T)`.
/// These need special handling in final_values: the deref value must be
/// wrapped in a tuple constructor so postconditions like `^x.0` can decompose
/// it via tuple axioms.
pub(super) fn is_newtype_wrapping_mut<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    match ty.kind() {
        TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
            if let Some(variant) = adt_def.variants().iter().next() {
                let mut fields = variant.fields.iter();
                if let (Some(only_field), 1) = (fields.next(), variant.fields.len()) {
                    let field_ty = only_field.ty(tcx, substs).skip_norm_wip();
                    return matches!(
                        field_ty.kind(),
                        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                    );
                }
            }
            false
        }
        _ => false,
    }
}

/// Get the field count of a multi-field struct behind `&mut T`.
///
/// Peels one layer of `&mut` to examine the referent type. Returns `Some(n)`
/// when the referent is a struct with `n >= 2` fields that is NOT a newtype
/// wrapping `&mut`. Returns `None` for primitives, enums, tuples, newtypes,
/// and non-struct ADTs.
///
/// Used to reconstruct whole-struct final values from per-field final values
/// when field-level writes occur (e.g., `x.a = 34` on `&mut S { a, b }`).
pub(super) fn struct_field_count_behind_mut<'tcx>(
    _tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<usize> {
    // Peel &mut
    let inner_ty = match ty.kind() {
        TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Mut) => *inner,
        _ => return None,
    };
    match inner_ty.kind() {
        TyKind::Adt(adt_def, _) if adt_def.is_struct() => {
            let variant = adt_def.variants().iter().next()?;
            let count = variant.fields.len();
            if count >= 2 {
                // Exclude newtypes (handled separately)
                Some(count)
            } else {
                None
            }
        }
        TyKind::Tuple(fields) if fields.len() >= 2 => Some(fields.len()),
        _ => None,
    }
}

/// Find locals that are mutable borrow parameters.
///
/// Detects:
/// - Direct `&mut T` parameters
/// - Tuple parameters containing `&mut` references (e.g., `(&mut u32, &mut u32)`)
/// - Single-field ADTs (newtypes) wrapping `&mut T`
/// - Closure env parameters (`self`) where any upvar eventually contains `&mut T`,
///   even behind wrapper chains like `Box<&mut T>` or `Box<Box<&mut T>>`. (#2318)
///
/// These are tracked in `extract_mut_borrow_body` for RustHorn-style verification
/// where mutable borrows are modeled as prophecy variables.
pub(super) fn find_mut_borrow_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
) -> Vec<Local> {
    let mut result = Vec::new();
    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let local_decl = &body.local_decls[local];

        if type_contains_mut_ref_with_tcx(tcx, local_decl.ty) {
            result.push(local);
        } else if name == "self"
            && !closure_capture_fields_with_eventual_mut_ref(tcx, body, local).is_empty()
        {
            // FnOnce closure envs are passed by value (not &mut Self), so
            // type_contains_mut_ref_with_tcx may not detect mut-refs nested
            // behind wrapper types like Box<&mut T>. Use closure capture
            // metadata to check upvar types at arbitrary depth. (#2318)
            result.push(local);
        }
    }
    result
}
