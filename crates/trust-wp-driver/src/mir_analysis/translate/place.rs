// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Place translation: MIR Place → PureExpr with projection support.

use std::sync::Arc;

use rustc_middle::{
    mir::{Local, Place},
    ty::{Ty, TyCtxt, TyKind},
};
use trust_wp_core::formula::{
    internal::tuple_lowering::{
        tuple_field_logic_fn_index, tuple_field_logic_fn_name, tuple_logic_fn_arity,
        NAMED_FIELD_LOGIC_FN_PREFIX,
    },
    ExprSort, PureExpr,
};

use super::{record_translation_gap, ExprLookup, TranslationDiagContext};

/// Translate a MIR Place to a PureExpr (compatibility shim).
pub(crate) fn translate_place(place: &Place<'_>, locals: &impl ExprLookup) -> Option<PureExpr> {
    translate_place_detailed(place, locals, None)
}

/// Translate a typed ADT/tuple field place using rustc field metadata.
///
/// The untyped projection path intentionally avoids treating every datatype as
/// a tuple. This fallback is for callers that have `TyCtxt` and need a stable
/// expression for source field projections such as `(*self).buckets`.
pub(crate) fn translate_typed_field_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    place: &Place<'tcx>,
    locals: &impl ExprLookup,
) -> Option<PureExpr> {
    use rustc_middle::mir::ProjectionElem;

    let mut current = locals.get_expr(&place.local)?.clone();
    let mut current_ty = body.local_decls[place.local].ty;

    for proj in place.projection {
        match proj {
            ProjectionElem::Deref => {
                let box_inner = box_inner_ty(current_ty);
                if let TyKind::Ref(_, inner, _) = current_ty.kind() {
                    current_ty = *inner;
                } else if let Some(inner) = box_inner {
                    current_ty = inner;
                } else {
                    current_ty = current_ty.peel_refs();
                }
                if box_inner.is_some() {
                    if !matches!(current, PureExpr::Deref(_)) {
                        current = PureExpr::Deref(Arc::new(current));
                    }
                } else if expr_is_ref_like(&current) {
                    current = PureExpr::Deref(Arc::new(current));
                }
            }
            ProjectionElem::Field(field, _) => {
                let field_idx = usize::try_from(field.as_u32()).ok()?;
                let (projected, field_ty) =
                    typed_field_projection(tcx, current, current_ty, field_idx)?;
                current = projected;
                current_ty = field_ty;
            }
            _ => return None,
        }
    }

    Some(current)
}

/// Translate a MIR Place to a PureExpr, recording diagnostics for failures.
///
/// Supports deref-aware resolution via the `ExprLookup` trait's optional
/// `get_deref_expr` and `get_field_deref_expr` methods. When an `ExprLookup`
/// implementation provides deref tracking (e.g., for mutable borrow analysis),
/// specific projection patterns are resolved against the deref maps before
/// falling back to the normal projection walk. (#895)
pub(crate) fn translate_place_detailed(
    place: &Place<'_>,
    locals: &impl ExprLookup,
    diag: Option<&TranslationDiagContext<'_>>,
) -> Option<PureExpr> {
    use rustc_middle::mir::ProjectionElem;

    // For simple locals, just look up the expression.
    if place.projection.is_empty() {
        let result = locals.get_expr(&place.local).cloned();
        if result.is_none() {
            record_translation_gap(
                diag,
                format!("missing local expression for {:?}", place.local),
            );
        }
        return result;
    }

    // Deref-aware fast paths: resolve mutable borrow projection patterns
    // via the ExprLookup trait before the general projection walk.
    // These patterns come from MIR lowering of `&mut` parameter accesses.
    if let Some(result) = resolve_deref_projection(place, locals) {
        return Some(result);
    }

    let Some(base) = locals.get_expr(&place.local) else {
        record_translation_gap(
            diag,
            format!(
                "missing local expression for {:?} (with projections)",
                place.local
            ),
        );
        return None;
    };
    let mut current = base.clone();
    let mut downcast_active = false;

    // Walk projection chains (`(*_1).0`, tuple fields, etc.).
    for proj in place.projection {
        match proj {
            ProjectionElem::Field(field, _) => {
                let field_idx = usize::try_from(field.as_u32()).ok()?;
                current =
                    translate_field_projection(current, field_idx, &mut downcast_active, locals)?;
            }
            ProjectionElem::Deref => {
                downcast_active = false;
                // Check for tracked deref expression before treating as alias.
                if let Some(expr) = locals.get_deref_expr(&place.local) {
                    current = expr.clone();
                } else if expr_is_ref_like(&current) {
                    // Keep deref semantics when the current expression is a
                    // reference-typed value. This matters for closures like
                    // `|b: &bool| *b` where the pointee is the current value.
                    current = PureExpr::Deref(Arc::new(current));
                }
            }
            ProjectionElem::Downcast(_, _) => {
                downcast_active = true;
                // Downcast projection (e.g., `(_2 as Some)`) — selects a variant
                // for subsequent field access. Since ADT aggregates already store
                // the inner value directly, this is a no-op in the expression model.
            }
            ProjectionElem::Index(index_local) => {
                downcast_active = false;
                current = translate_index_projection(current, locals, index_local)?;
            }
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                downcast_active = false;
                current =
                    translate_constant_index_projection(current, offset, min_length, from_end)?;
            }
            _ => {
                record_translation_gap(diag, format!("unsupported place projection: {proj:?}"));
                return None;
            }
        }
    }

    // Final normalization: simplify patterns like `tuple_get_N(tuple_K(a, b, ...))`
    // to the N-th element. This can arise when a field projection extracts a
    // tuple_get_N call, e.g., field 0 of `tuple2(tuple_get_1(x), tuple_get_0(x))`
    // gives `tuple_get_1(x)` which should further simplify if x is a constructor.
    if let Some(simplified) = simplify_tuple_get_from_constructor(&current) {
        return Some(simplified);
    }

    Some(current)
}

/// Translate a `ProjectionElem::Index(local)` into a `PureExpr`.
fn translate_index_projection(
    current: PureExpr,
    locals: &impl ExprLookup,
    index_local: Local,
) -> Option<PureExpr> {
    let index_expr = locals.get_expr(&index_local)?.clone();
    if let Some(index) = const_index_from_expr(&index_expr) {
        if let Some(projected) = project_const_index(&current, index) {
            return Some(projected);
        }
    }
    Some(PureExpr::MethodCall {
        receiver: Arc::new(current),
        method: "index_logic".to_string(),
        args: vec![index_expr],
    })
}

/// Translate a `ProjectionElem::ConstantIndex` into a `PureExpr`.
fn translate_constant_index_projection(
    current: PureExpr,
    offset: u64,
    min_length: u64,
    from_end: bool,
) -> Option<PureExpr> {
    let offset = usize::try_from(offset).ok()?;
    let min_length = usize::try_from(min_length).ok()?;
    let index = if from_end {
        min_length.checked_sub(offset.checked_add(1)?)?
    } else {
        offset
    };
    if let Some(projected) = project_const_index(&current, index) {
        return Some(projected);
    }
    Some(PureExpr::MethodCall {
        receiver: Arc::new(current),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(i64::try_from(index).ok()?)],
    })
}

fn translate_field_projection(
    mut current: PureExpr,
    field_idx: usize,
    downcast_active: &mut bool,
    locals: &impl ExprLookup,
) -> Option<PureExpr> {
    if *downcast_active {
        *downcast_active = false;
        // Enum payload projection after downcast, e.g.:
        // `(_1 as Some).0` where `_1` translated to
        // `LogicFnCall { name: "Some", args: [...] }`.
        if let PureExpr::LogicFnCall { args, .. } = &current {
            if let Some(payload) = args.get(field_idx) {
                return Some(payload.clone());
            }
        }
    }
    if locals.rich_field_projections() {
        if let Some(normalized) = simplify_tuple_get_from_constructor(&current) {
            current = normalized;
        }
        if let Some(projected) = project_tuple_field(&current, field_idx) {
            return Some(projected);
        }
        if !matches!(current, PureExpr::Var(_, Some(ExprSort::Datatype(_)))) {
            if let Some(projected) = project_closure_capture_field(&current, field_idx) {
                return Some(projected);
            }
        }
        if let Some(projected) = project_nested_tuple_get_field(&current, field_idx) {
            return Some(projected);
        }
    }
    // Fallback: checked-op temporaries (CheckedAdd, etc.) flow as scalar values
    // even when MIR projects `.0`. Only allow this for non-compound expressions.
    if field_idx == 0 && allows_field0_identity_fallback(&current) {
        return Some(current);
    }
    if locals.rich_field_projections() && matches!(current, PureExpr::Var(_, _)) {
        return Some(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(field_idx),
            args: vec![current],
        });
    }
    if !matches!(current, PureExpr::Var(_, Some(ExprSort::Datatype(_)))) {
        if let Some(projected) = project_closure_capture_field(&current, field_idx) {
            return Some(projected);
        }
    }
    None
}

fn typed_field_projection<'tcx>(
    tcx: TyCtxt<'tcx>,
    current: PureExpr,
    current_ty: Ty<'tcx>,
    field_idx: usize,
) -> Option<(PureExpr, Ty<'tcx>)> {
    match current_ty.peel_refs().kind() {
        TyKind::Tuple(fields) => {
            let field_ty = *fields.get(field_idx)?;
            if field_idx == 0 && allows_field0_identity_fallback(&current) {
                return Some((current, field_ty));
            }
            let projected = PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(field_idx),
                args: vec![current],
            };
            Some((projected, field_ty))
        }
        TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
            let variant = adt_def.variants().iter().next()?;
            let field = variant
                .fields
                .get(rustc_abi::FieldIdx::from_usize(field_idx))?;
            let field_ty = field.ty(tcx, substs).skip_norm_wip();
            let field_name = field.name.as_str();
            let accessor = if field_name.bytes().all(|b| b.is_ascii_digit()) {
                tuple_field_logic_fn_name(field_idx)
            } else {
                format!("{NAMED_FIELD_LOGIC_FN_PREFIX}{field_name}")
            };
            Some((
                PureExpr::LogicFnCall {
                    name: accessor,
                    args: vec![current],
                },
                field_ty,
            ))
        }
        _ => None,
    }
}

fn box_inner_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.peel_refs().kind() {
        TyKind::Adt(adt_def, substs) if adt_def.is_box() => substs.types().next(),
        _ => None,
    }
}

/// Translate a `Rvalue::Ref(_, _, place)` rvalue using body type info.
///
/// Reborrow semantics: `&[mut] *e` is logically `e` (both refer to the same
/// memory). When the source MIR place ends in a `Deref` projection, the
/// surrounding `Ref` rvalue cancels it, so the corresponding `Deref` layer
/// should NOT appear in the resulting `PureExpr`.
///
/// Box transparency: `Box<T>` shares its `ExprSort` with `T`. A MIR
/// `Deref` projection through a Box is a value-preserving unwrap in our
/// model — it must not add a `Deref` to the `PureExpr` (otherwise we'd
/// over-deref the underlying value).
///
/// This translator handles **pure-Deref** projection chains (no `Field`,
/// `Index`, `Downcast`, etc.). Mixed projection chains (e.g.,
/// `&(*x).field`) are left to the existing projected-ref path. Returns
/// `None` if the place is not a pure-Deref chain or the local expression
/// is missing; callers should fall back to the regular place translator.
///
/// Together these rules give the right encoding for reborrow chains like
/// `&mut **x` where `x: Box<&mut i32>`: the Box deref is transparent, and
/// the trailing `*` is cancelled by the surrounding `&mut`, so the result
/// is just `Var("x", MutRef(Int))` — the same mutref the caller passed in.
/// (#7 box_borrow_resolve)
pub(crate) fn translate_ref_rvalue_place<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    place: &Place<'tcx>,
    locals: &impl ExprLookup,
) -> Option<PureExpr> {
    use rustc_middle::mir::ProjectionElem;

    let projections: &[_] = place.projection.as_ref();

    // Only apply this translator for pure-Deref chains. Mixed chains
    // (Deref+Field, etc.) are handled by the existing projected-ref
    // path; return None so the caller falls back.
    if projections.is_empty()
        || !projections
            .iter()
            .all(|p| matches!(p, ProjectionElem::Deref))
    {
        return None;
    }

    // The trailing Deref is cancelled by the outer `&[mut]`. Walk the
    // remaining Deref projections, treating Box derefs as no-ops in the
    // PureExpr model (Box shares ExprSort with its inner type).
    let mut current = locals.get_expr(&place.local)?.clone();
    let mut current_ty = body.local_decls[place.local].ty;
    let walk_count = projections.len().saturating_sub(1);
    for _ in 0..walk_count {
        if let Some(inner) = box_inner_ty(current_ty) {
            // Box deref is transparent: advance the type but keep the
            // PureExpr unchanged.
            current_ty = inner;
        } else if let TyKind::Ref(_, inner, _) = current_ty.kind() {
            current_ty = *inner;
            if expr_is_ref_like(&current) {
                current = PureExpr::Deref(Arc::new(current));
            }
        } else {
            // Unknown deref shape — fall back to the general translator
            // so we don't silently drop a real deref layer.
            return None;
        }
    }
    Some(current)
}

/// Resolve deref-aware projection patterns for mutable borrow tracking.
///
/// Returns `Some(expr)` if the place matches a known deref pattern and the
/// `ExprLookup` implementation provides a tracked expression for it.
/// Returns `None` to fall through to the general projection walk.
fn resolve_deref_projection(place: &Place<'_>, locals: &impl ExprLookup) -> Option<PureExpr> {
    use rustc_middle::mir::ProjectionElem;

    let projections: &[_] = place.projection.as_ref();

    match projections {
        // *((*_1).N) — FnMut closure &mut capture read
        [ProjectionElem::Deref, ProjectionElem::Field(field, _), ProjectionElem::Deref] => locals
            .get_field_deref_expr(&place.local, field.as_u32())
            .cloned(),
        // (*v).N — closure capture field read
        [ProjectionElem::Deref, ProjectionElem::Field(field, _)] => locals
            .get_field_deref_expr(&place.local, field.as_u32())
            .cloned()
            .or_else(|| {
                let base = locals.get_expr(&place.local)?;
                project_closure_capture_field(base, usize::try_from(field.as_u32()).ok()?)
            }),
        // *(v.N) — newtype inner &mut read
        [ProjectionElem::Field(field, _), ProjectionElem::Deref] => {
            // For newtypes (field 0), try whole-deref first
            if field.as_u32() == 0 {
                if let Some(expr) = locals.get_deref_expr(&place.local) {
                    return Some(expr.clone());
                }
            }
            // For multi-field structs, check field-level tracking
            locals
                .get_field_deref_expr(&place.local, field.as_u32())
                .cloned()
        }
        // *v — plain deref
        [ProjectionElem::Deref] => locals.get_deref_expr(&place.local).cloned(),
        // **v, ***v, ... — multi-level deref through Box wrappers (#2318)
        //
        // When a local has a tracked deref expression (e.g., from a
        // field_reborrow_map entry for Box<&mut T>), multi-level deref
        // projections collapse to a single logical deref because Box is
        // transparent in the logical model. For `bx: Box<&mut i32>`,
        // MIR generates `**bx` = [Deref, Deref], but the deref_exprs
        // entry already stores `Deref(Var("self.0"))` which accounts
        // for both the Box unwrap and the &mut follow.
        _ if projections.len() >= 2
            && projections
                .iter()
                .all(|p| matches!(p, ProjectionElem::Deref)) =>
        {
            locals.get_deref_expr(&place.local).cloned()
        }
        _ => None,
    }
}

pub(super) fn project_tuple_field(base: &PureExpr, field_idx: usize) -> Option<PureExpr> {
    if let PureExpr::LogicFnCall { name, args } = base {
        let arity = tuple_logic_fn_arity(name)?;
        if args.len() != arity {
            return None;
        }
        return args.get(field_idx).cloned();
    }
    None
}

pub(super) fn project_closure_capture_field(base: &PureExpr, field_idx: usize) -> Option<PureExpr> {
    match base {
        PureExpr::Var(name, _) if name == "self" || name.starts_with("self.") => {
            Some(PureExpr::Var(format!("{name}.{field_idx}"), None))
        }
        _ => None,
    }
}

pub(super) fn project_nested_tuple_get_field(
    base: &PureExpr,
    field_idx: usize,
) -> Option<PureExpr> {
    if let PureExpr::LogicFnCall { name, .. } = base {
        if tuple_field_logic_fn_index(name).is_some() {
            return Some(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(field_idx),
                args: vec![base.clone()],
            });
        }
    }
    None
}

pub(super) fn simplify_tuple_get_from_constructor(base: &PureExpr) -> Option<PureExpr> {
    if let PureExpr::LogicFnCall { name, args } = base {
        let field_idx = tuple_field_logic_fn_index(name)?;
        if args.len() != 1 {
            return None;
        }
        return project_tuple_field(&args[0], field_idx);
    }
    None
}

fn const_index_from_expr(expr: &PureExpr) -> Option<usize> {
    let PureExpr::Int(idx) = expr else {
        return None;
    };
    usize::try_from(*idx).ok()
}

pub(super) fn project_const_index(base: &PureExpr, idx: usize) -> Option<PureExpr> {
    if let Some(projected) = project_tuple_field(base, idx) {
        return Some(projected);
    }

    // array_repeat(elem, len)[k] == elem for any in-bounds constant k.
    if let PureExpr::LogicFnCall { name, args } = base {
        if name == "array_repeat" && args.len() == 2 {
            let len = const_index_from_expr(&args[1])?;
            if idx < len {
                return Some(args[0].clone());
            }
        }
    }

    None
}

pub(crate) fn allows_field0_identity_fallback(base: &PureExpr) -> bool {
    // Field(0) identity fallback is only valid for scalar checked-op temporaries.
    // Keep this narrowly scoped to expression shapes produced by checked-op
    // lowering. Opaque values (e.g., Var, MethodCall, LogicFnCall) may be
    // compound tuples/structs, and collapsing `.0` to identity is unsound.
    matches!(
        base,
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::BinOp(_, _, _) | PureExpr::UnOp(_, _)
    )
}

fn expr_is_ref_like(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, Some(ExprSort::Ref(_) | ExprSort::MutRef(_))) => true,
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => expr_is_ref_like(inner),
        _ => false,
    }
}
