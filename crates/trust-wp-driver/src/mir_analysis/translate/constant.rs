// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constant translation: MIR constants → PureExpr.

use std::sync::Arc;

use rustc_middle::ty::TyKind;
use trust_wp_core::formula::{internal::tuple_lowering::tuple_logic_fn_name, BinOp, PureExpr};

use super::{
    discriminant::translate_ty_const_to_usize, float::translate_float_scalar_bits,
    ty_sort::ty_to_expr_sort,
};

/// Translate a MIR constant operand to a `PureExpr`.
///
/// Handles scalar constants (Int, Bool) directly via `try_to_scalar_int()`.
/// For compound types (tuples, arrays), decomposes `ValTree::Branch` nodes.
///
/// Note: `Const::Unevaluated` constants (named constants like `const FOO`)
/// require evaluation via `translate_constant_with_tcx` which has access
/// to `TyCtxt`. Without evaluation, unevaluated constants return `None`.
pub(crate) fn translate_constant(
    constant: &rustc_middle::mir::ConstOperand<'_>,
) -> Option<PureExpr> {
    translate_constant_inner(&constant.const_, constant.ty())
}

/// Translate a promoted constant's inner value when the promoted is a reference
/// type (e.g., `&NonCopy(1i32)` from `snapshot!(NonCopy(1i32))`).
///
/// The CTFE result for a reference-typed promoted constant is a `ConstValue`
/// pointing to an allocation. This function dereferences the pointer and reads
/// the scalar value from the allocation for simple inner types (Int, Uint, Bool)
/// and single-field ADTs (newtypes). (#1572)
fn translate_promoted_ref_value<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    value: rustc_middle::mir::ConstValue,
    inner_ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<PureExpr> {
    use rustc_middle::mir::ConstValue;

    // The ConstValue for a reference is a Scalar pointer to an allocation.
    let ConstValue::Scalar(scalar) = value else {
        return None;
    };
    let ptr = scalar.to_pointer(&tcx).discard_err()?;
    let (Some(prov), offset) = ptr.into_raw_parts() else {
        return None;
    };
    let alloc_id = prov.alloc_id();
    let alloc = tcx.global_alloc(alloc_id).unwrap_memory();

    read_scalar_from_alloc(tcx, alloc, offset, inner_ty)
}

/// Read a scalar value from a const allocation at a given offset.
///
/// Handles Int, Uint, Bool directly and recurses through single-field ADTs
/// (newtypes like `NonCopy(i32)`) to extract the inner scalar. (#1572)
fn read_scalar_from_alloc<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    alloc: rustc_middle::mir::interpret::ConstAllocation<'tcx>,
    offset: rustc_abi::Size,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<PureExpr> {
    use rustc_middle::mir::interpret::AllocRange;
    let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
    // Erase regions before querying layout_of: promoted constants from macro
    // expansions (e.g., `print!`, `format_args!`) can carry inference region
    // variables like `'?27` in their types. The query system panics when
    // hashing region variables. Regions do not affect layout, so erasing
    // them is safe. (#printing crash)
    let erased_ty = tcx.erase_and_anonymize_regions(ty);
    let layout = tcx.layout_of(typing_env.as_query_input(erased_ty)).ok()?;
    let size = layout.layout.size();
    let range = AllocRange {
        start: offset,
        size,
    };

    match ty.kind() {
        TyKind::Int(_) => {
            let scalar = alloc.inner().read_scalar(&tcx, range, false).ok()?;
            let scalar_int = scalar.try_to_scalar_int().ok()?;
            let signed = scalar_int.to_int(size);
            i64::try_from(signed).ok().map(PureExpr::Int)
        }
        TyKind::Uint(_) => {
            let scalar = alloc.inner().read_scalar(&tcx, range, false).ok()?;
            let scalar_int = scalar.try_to_scalar_int().ok()?;
            let unsigned = scalar_int.to_uint(size);
            i64::try_from(unsigned).ok().map(PureExpr::Int)
        }
        TyKind::Bool => {
            let scalar = alloc.inner().read_scalar(&tcx, range, false).ok()?;
            let scalar_int = scalar.try_to_scalar_int().ok()?;
            Some(PureExpr::Bool(scalar_int.to_uint(size) != 0))
        }
        // For single-field ADTs (newtypes like `NonCopy(i32)`), recurse into
        // the sole field's type at the same allocation offset.
        TyKind::Adt(adt_def, substs) => {
            if !adt_def.is_struct() || adt_def.variants().len() != 1 {
                return None;
            }
            let variant = adt_def.variant(rustc_abi::FIRST_VARIANT);
            if variant.fields.len() != 1 {
                return None;
            }
            let field_ty = variant.fields[rustc_abi::FieldIdx::ZERO]
                .ty(tcx, substs)
                .skip_norm_wip();
            read_scalar_from_alloc(tcx, alloc, offset, field_ty)
        }
        _ => None,
    }
}

/// Translate a MIR constant with `TyCtxt` for evaluating `Unevaluated`
/// constants (named constants, inline const blocks, associated constants).
///
/// When `tcx` is provided, `Const::Unevaluated` constants are resolved
/// via `tcx.const_eval_resolve_for_typeck` to obtain a `ValTree`, which
/// enables decomposition of compound types (tuples, arrays). This handles
/// patterns like `const TUP: (i32, i32) = (42, 24)` and
/// `const ARR: [i32; 5] = [1; 5]` which MIR keeps as unevaluated references.
pub(crate) fn translate_constant_with_tcx<'tcx>(
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> Option<PureExpr> {
    use rustc_hir::def::DefKind;
    use rustc_middle::{mir::Const as MirConst, ty::TypingEnv};

    let mir_const = match constant.const_ {
        MirConst::Unevaluated(ref uneval, ty) => {
            // Promoted constants (e.g., `const fn::promoted[0]` for `&NonCopy(1i32)`)
            // have the DefKind of their enclosing function, not `Const`.
            // Evaluate them directly via CTFE. (#1572)
            if uneval.promoted.is_some() {
                let typing_env = TypingEnv::fully_monomorphized();
                match tcx.const_eval_resolve(typing_env, *uneval, constant.span) {
                    Ok(val) => {
                        // For reference types, look through to the inner type and
                        // try to translate the pointed-to value from the allocation.
                        if let TyKind::Ref(_, inner_ty, _) = ty.kind() {
                            return translate_promoted_ref_value(tcx, val, *inner_ty);
                        }
                        return translate_constant_inner(&MirConst::Val(val, ty), ty);
                    }
                    Err(_) => return None,
                }
            }
            // CTFE only supports true const items here. Calling const-eval on
            // non-const DefKinds (e.g., Fn) can panic in rustc internals.
            let def_kind = tcx.def_kind(uneval.def);
            let is_const_item = matches!(
                def_kind,
                DefKind::Const { .. }
                    | DefKind::AssocConst { .. }
                    | DefKind::AnonConst
                    | DefKind::InlineConst
            );
            if !is_const_item {
                return None;
            }
            // Generic unevaluated constants require symbolic handling in the
            // MIR extractor fallback; CTFE needs monomorphic arguments.
            let has_params = uneval.args.iter().any(|arg| {
                arg.as_type()
                    .is_some_and(|t| matches!(t.kind(), TyKind::Param(_)))
                    || arg
                        .as_const()
                        .is_some_and(|c| matches!(c.kind(), rustc_middle::ty::ConstKind::Param(_)))
            });
            if has_params {
                return None;
            }
            // Type-level evaluation now consumes the alias-constant view. We
            // handled promoted constants above, so shrinking cannot discard a
            // promotion index here.
            let alias_const = (*uneval).shrink(tcx);
            let typing_env = TypingEnv::fully_monomorphized();
            match tcx.const_eval_resolve_for_typeck(typing_env, alias_const, constant.span) {
                Ok(Ok(val)) => {
                    // Wrap the evaluated Value into a Const::Ty for ValTree-based
                    // decomposition of compound types (tuples, arrays).
                    let ty_const = rustc_middle::ty::Const::new_value(tcx, val, ty);
                    MirConst::Ty(ty, ty_const)
                }
                _ => {
                    // Fall back to runtime evaluation for constants that can't
                    // be expressed as ValTrees (e.g., function pointers).
                    match tcx.const_eval_resolve(typing_env, *uneval, constant.span) {
                        Ok(val) => MirConst::Val(val, ty),
                        Err(_) => return None,
                    }
                }
            }
        }
        ref other => *other,
    };
    if let TyKind::Adt(adt_def, _) = constant.ty().kind() {
        if adt_def.is_enum() {
            if let Some(discr) = mir_const.try_to_scalar_int() {
                let discr_val = discr.to_uint(discr.size());
                if let Some((variant_idx, _)) = adt_def
                    .discriminants(tcx)
                    .find(|(idx, d)| adt_def.variant(*idx).fields.is_empty() && d.val == discr_val)
                {
                    let variant = adt_def.variant(variant_idx);
                    let adt_name = tcx.item_name(adt_def.did());
                    return Some(PureExpr::LogicFnCall {
                        name: format!("{}::{}", adt_name, variant.name),
                        args: vec![],
                    });
                }
            }
        }
    }

    // For array constants with compound element types (enums, structs, refs),
    // use the tcx-aware translator that can decompose ADT ValTree nodes.
    // This enables constant-index recovery for arrays like
    // `const PEANOS: [Peano; 2] = [Peano::Z, Peano::S(&Peano::Z)]`. (#2572)
    if let TyKind::Array(elem_ty, len_const) = constant.ty().kind() {
        if let Some(result) = translate_const_array_with_tcx(tcx, &mir_const, *elem_ty, *len_const)
        {
            return Some(result);
        }
    }

    translate_constant_inner(&mir_const, constant.ty())
}

/// Resolve a `DefKind::Const` item to its concrete `PureExpr` value via CTFE.
///
/// Given the `DefId` of a `const` item (e.g., `const TUP: (i32, i32) = (42, 24)`),
/// evaluates it at compile time and translates the result into a `PureExpr`.
/// Returns `None` if the item is not a const, has generic parameters, or
/// CTFE evaluation fails. (#1588)
pub(crate) fn resolve_const_item_value<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
) -> Option<PureExpr> {
    use rustc_hir::def::DefKind;
    use rustc_middle::{mir::Const as MirConst, ty::TypingEnv};

    let def_kind = tcx.def_kind(def_id);
    if !matches!(def_kind, DefKind::Const { .. } | DefKind::AssocConst { .. }) {
        return None;
    }
    // Only monomorphic constants can be evaluated via CTFE.
    let generics = tcx.generics_of(def_id);
    if generics.count() > 0 {
        return None;
    }
    let ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
    let typing_env = TypingEnv::fully_monomorphized();
    let args = rustc_middle::ty::GenericArgs::empty();
    let alias_const = rustc_middle::ty::AliasConst::new(
        tcx,
        rustc_middle::ty::AliasConstKind::new_from_def_id(tcx, def_id),
        args,
    );
    // Try type-level evaluation first (produces ValTree for compound types).
    if let Ok(Ok(val)) =
        tcx.const_eval_resolve_for_typeck(typing_env, alias_const, rustc_span::DUMMY_SP)
    {
        let ty_const = rustc_middle::ty::Const::new_value(tcx, val, ty);
        let mir_const = MirConst::Ty(ty, ty_const);
        translate_constant_inner(&mir_const, ty)
    } else {
        // Fall back to runtime CTFE.
        let mir_uneval = rustc_middle::mir::UnevaluatedConst {
            def: def_id,
            args,
            promoted: None,
        };
        match tcx.const_eval_resolve(typing_env, mir_uneval, rustc_span::DUMMY_SP) {
            Ok(val) => translate_constant_inner(&MirConst::Val(val, ty), ty),
            Err(_) => None,
        }
    }
}

/// Core translation logic shared by both `translate_constant` and
/// `translate_constant_with_tcx`.
fn translate_constant_inner<'tcx>(
    mir_const: &rustc_middle::mir::Const<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<PureExpr> {
    // Try to evaluate as a constant value
    match ty.kind() {
        TyKind::Tuple(fields) if fields.is_empty() => Some(PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(0),
            args: vec![],
        }),
        TyKind::Int(_) => {
            if let Some(val) = mir_const.try_to_scalar_int() {
                let signed = val.to_int(val.size());
                Some(large_signed_to_expr(signed))
            } else {
                translate_symbolic_param_const(mir_const, ty)
            }
        }
        TyKind::Uint(_) => {
            if let Some(val) = mir_const.try_to_scalar_int() {
                let unsigned = val.to_uint(val.size());
                Some(large_unsigned_to_expr(unsigned))
            } else {
                translate_symbolic_param_const(mir_const, ty)
            }
        }
        TyKind::Float(float_ty) => mir_const
            .try_to_scalar_int()
            .and_then(|val| translate_float_scalar_bits(*float_ty, val.to_uint(val.size()))),
        TyKind::Bool => mir_const
            .try_to_scalar_int()
            .map(|val| PureExpr::Bool(val.to_uint(val.size()) != 0))
            .or_else(|| translate_symbolic_param_const(mir_const, ty)),

        // Non-empty tuple constants: decompose ValTree branches into
        // __trust_wp_tupleN(field0, field1, ...) constructor calls. (#1588)
        TyKind::Tuple(field_tys) => translate_const_tuple(mir_const, field_tys),

        // Array constants: decompose ValTree branches into
        // array_repeat(elem, len) when all elements are identical,
        // otherwise return None (mixed-element arrays not yet supported). (#1588)
        TyKind::Array(elem_ty, len_const) => translate_const_array(mir_const, *elem_ty, *len_const),

        _ => None,
    }
}

/// Construct a PureExpr for a `u128` value, decomposing values > `i64::MAX`
/// into `high * 2^32 + low` using recursive binary decomposition.
///
/// Without this, constants like `u64::MAX` silently return `None` from
/// `i64::try_from`, causing unsubstituted parameter variables and vacuous
/// proofs in duration/instant tests. (#976)
pub(crate) fn large_unsigned_to_expr(value: u128) -> PureExpr {
    if let Ok(small) = i64::try_from(value) {
        return PureExpr::Int(small);
    }
    let high = value >> 32;
    let low = (value & 0xFFFF_FFFF) as i64;
    let high_expr = large_unsigned_to_expr(high);
    let shift = PureExpr::BinOp(
        Arc::new(high_expr),
        BinOp::Mul,
        Arc::new(PureExpr::Int(1 << 32)),
    );
    if low == 0 {
        shift
    } else {
        PureExpr::BinOp(Arc::new(shift), BinOp::Add, Arc::new(PureExpr::Int(low)))
    }
}

/// Construct a PureExpr for a large `i128` value that doesn't fit in `i64`.
/// Negative values use `0 - large_unsigned_to_expr(abs)`.
pub(crate) fn large_signed_to_expr(value: i128) -> PureExpr {
    if let Ok(small) = i64::try_from(value) {
        return PureExpr::Int(small);
    }
    if value >= 0 {
        large_unsigned_to_expr(value.cast_unsigned())
    } else {
        PureExpr::BinOp(
            Arc::new(PureExpr::Int(0)),
            BinOp::Sub,
            Arc::new(large_unsigned_to_expr(value.unsigned_abs())),
        )
    }
}

/// Translate generic const parameters (`const N: usize`) into symbolic variables.
///
/// This is intentionally narrow: only `ConstKind::Param` is translated here.
/// Other unresolved constants (associated consts, anon consts) require `TyCtxt`
/// and are handled in `extract.rs` fallback paths.
fn translate_symbolic_param_const<'tcx>(
    mir_const: &rustc_middle::mir::Const<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<PureExpr> {
    use rustc_middle::{mir::Const as MirConst, ty::ConstKind};

    let MirConst::Ty(_, ty_const) = mir_const else {
        return None;
    };
    let ConstKind::Param(param) = ty_const.kind() else {
        return None;
    };
    Some(PureExpr::Var(
        param.name.as_str().to_string(),
        ty_to_expr_sort(ty),
    ))
}

/// Translate a scalar `ValTree` leaf to a `PureExpr` based on its type.
fn translate_scalar_valtree(
    scalar: rustc_middle::ty::ScalarInt,
    ty_kind: &TyKind<'_>,
) -> Option<PureExpr> {
    match ty_kind {
        TyKind::Int(_) => {
            let signed = scalar.to_int(scalar.size());
            Some(large_signed_to_expr(signed))
        }
        TyKind::Uint(_) => {
            let unsigned = scalar.to_uint(scalar.size());
            Some(large_unsigned_to_expr(unsigned))
        }
        TyKind::Float(float_ty) => {
            translate_float_scalar_bits(*float_ty, scalar.to_uint(scalar.size()))
        }
        TyKind::Bool => Some(PureExpr::Bool(scalar.to_uint(scalar.size()) != 0)),
        _ => None,
    }
}

/// Decompose a const tuple into `__trust_wp_tupleN(field0, field1, ...)`.
///
/// Works by matching `Const::Ty(_, ty_const)` where the `ty_const` has
/// `ConstKind::Value` with a `ValTree::Branch` containing the field values.
fn translate_const_tuple(
    mir_const: &rustc_middle::mir::Const<'_>,
    field_tys: &rustc_middle::ty::List<rustc_middle::ty::Ty<'_>>,
) -> Option<PureExpr> {
    use rustc_middle::mir::Const as MirConst;

    // Only Const::Ty carries a ValTree; Const::Val tuples are pre-lowered
    // by the MIR pipeline into Rvalue::Aggregate which translate_rvalue handles.
    let MirConst::Ty(_, ty_const) = mir_const else {
        return None;
    };
    let value = ty_const.try_to_value()?;
    // Trust: ValTreeKind::Branch now holds &[ty::Const], not &[ValTree];
    // ty::Value::try_to_branch yields the &[ty::Const] slice directly.
    let fields = value.try_to_branch()?;
    if fields.len() != field_tys.len() {
        return None;
    }

    let mut translated = Vec::with_capacity(fields.len());
    for (field, field_ty) in fields.iter().zip(field_tys.iter()) {
        let expr = translate_valtree_to_expr(branch_const_to_valtree(*field)?, field_ty)?;
        translated.push(expr);
    }

    match translated.as_slice() {
        [single] => Some(single.clone()),
        _ => Some(PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(translated.len()),
            args: translated,
        }),
    }
}

/// Decompose a const array into a PureExpr.
///
/// For arrays where all elements are identical (common for `[val; N]`),
/// produces `array_repeat(val, N)`. For mixed-element arrays, lowers to a
/// tuple constructor so constant-index projections can recover concrete values.
fn translate_const_array<'tcx>(
    mir_const: &rustc_middle::mir::Const<'tcx>,
    elem_ty: rustc_middle::ty::Ty<'tcx>,
    len_const: rustc_middle::ty::Const<'tcx>,
) -> Option<PureExpr> {
    use rustc_middle::mir::Const as MirConst;

    let MirConst::Ty(_, ty_const) = mir_const else {
        return None;
    };
    let value = ty_const.try_to_value()?;
    // Trust: ValTreeKind::Branch now holds &[ty::Const]; project to the slice.
    let elements = value.try_to_branch()?;

    let len = translate_ty_const_to_usize(len_const)?;
    if elements.is_empty() {
        return None;
    }

    // Translate the first element to check if all are identical
    let first_expr = translate_valtree_to_expr(branch_const_to_valtree(elements[0])?, elem_ty)?;

    // Check if all elements are identical (common for [val; N] patterns)
    let all_same = elements.iter().skip(1).all(|elem| {
        branch_const_to_valtree(*elem)
            .and_then(|vt| translate_valtree_to_expr(vt, elem_ty))
            .is_some_and(|e| e == first_expr)
    });

    if all_same {
        Some(PureExpr::LogicFnCall {
            name: "array_repeat".to_string(),
            args: vec![first_expr, PureExpr::Int(len)],
        })
    } else {
        let mut translated = Vec::with_capacity(elements.len());
        for element in elements {
            translated.push(translate_valtree_to_expr(
                branch_const_to_valtree(*element)?,
                elem_ty,
            )?);
        }
        match translated.as_slice() {
            [single] => Some(single.clone()),
            _ => Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(translated.len()),
                args: translated,
            }),
        }
    }
}

/// Extract the inner `ValTree` from a branch element `ty::Const`.
///
/// Trust: `ValTreeKind::Branch` now stores `&[ty::Const]` rather than nested
/// `ValTree`s, so branch children must be re-projected to their valtree before
/// the recursive lowering helpers (which still operate on `ValTree`) can run.
fn branch_const_to_valtree(
    c: rustc_middle::ty::Const<'_>,
) -> Option<rustc_middle::ty::ValTree<'_>> {
    c.try_to_value().map(|value| value.valtree)
}

/// Translate a `ValTree` node into a `PureExpr` given its expected type.
///
/// `ValTree::Leaf` produces scalar literals; `ValTree::Branch` decomposes
/// tuples recursively. Used by both `translate_const_tuple` and
/// `translate_const_array` to lower individual fields/elements.
fn translate_valtree_to_expr(
    valtree: rustc_middle::ty::ValTree<'_>,
    expected_ty: rustc_middle::ty::Ty<'_>,
) -> Option<PureExpr> {
    use rustc_middle::ty::ValTreeKind;

    match (*valtree, expected_ty.kind()) {
        (ValTreeKind::Leaf(ref scalar), kind) => translate_scalar_valtree(*scalar, kind),
        (ValTreeKind::Branch(fields), TyKind::Tuple(field_tys)) if !field_tys.is_empty() => {
            // Nested tuple: recursively decompose
            if fields.len() != field_tys.len() {
                return None;
            }
            let mut translated = Vec::with_capacity(fields.len());
            // Trust: branch children are now &[ty::Const]; project each to its valtree.
            for (field, field_ty) in fields.iter().zip(field_tys.iter()) {
                translated.push(translate_valtree_to_expr(
                    branch_const_to_valtree(field)?,
                    field_ty,
                )?);
            }
            match translated.as_slice() {
                [single] => Some(single.clone()),
                _ => Some(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(translated.len()),
                    args: translated,
                }),
            }
        }
        (ValTreeKind::Branch(_), TyKind::Tuple(field_tys)) if field_tys.is_empty() => {
            Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(0),
                args: vec![],
            })
        }
        _ => None,
    }
}

/// `TyCtxt`-aware variant of [`translate_valtree_to_expr`] that additionally
/// handles `TyKind::Adt` (enum/struct constants) and `TyKind::Ref` (transparent
/// deref through const references).
///
/// For enums, the ValTree layout is `Branch([Leaf(variant_idx), field0, ...])`.
/// The variant index is the first branch element as a u32 leaf, followed by
/// the variant's fields. This mirrors rustc's `destructure_const` decomposition.
/// (#2572)
fn translate_valtree_to_expr_with_tcx<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    valtree: rustc_middle::ty::ValTree<'tcx>,
    expected_ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<PureExpr> {
    use rustc_middle::ty::ValTreeKind;

    match (*valtree, expected_ty.kind()) {
        (ValTreeKind::Leaf(ref scalar), kind) => translate_scalar_valtree(*scalar, kind),
        (ValTreeKind::Branch(fields), TyKind::Tuple(field_tys)) if !field_tys.is_empty() => {
            if fields.len() != field_tys.len() {
                return None;
            }
            let mut translated = Vec::with_capacity(fields.len());
            // Trust: branch children are now &[ty::Const]; project each to its valtree.
            for (field, field_ty) in fields.iter().zip(field_tys.iter()) {
                translated.push(translate_valtree_to_expr_with_tcx(
                    tcx,
                    branch_const_to_valtree(field)?,
                    field_ty,
                )?);
            }
            match translated.as_slice() {
                [single] => Some(single.clone()),
                _ => Some(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(translated.len()),
                    args: translated,
                }),
            }
        }
        (ValTreeKind::Branch(_), TyKind::Tuple(field_tys)) if field_tys.is_empty() => {
            Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(0),
                args: vec![],
            })
        }
        // Enum ADT: Branch([Leaf(variant_idx), field0, field1, ...])
        // The first element encodes the variant index as a u32 leaf.
        // Remaining elements are the variant's field ValTrees. (#2572)
        (ValTreeKind::Branch(branches), TyKind::Adt(adt_def, substs)) if adt_def.is_enum() => {
            let (head, field_branches) = branches.split_first()?;
            // Trust: branch children are now ty::Const; the variant index leaf is
            // recovered via the head const's value/leaf rather than ValTree::unwrap_leaf.
            let variant_leaf = head.try_to_value()?.try_to_leaf()?;
            let variant_idx = rustc_abi::VariantIdx::from_u32(variant_leaf.to_u32());
            let variant = adt_def.variant(variant_idx);
            let adt_name = tcx.item_name(adt_def.did());
            let name = format!("{}::{}", adt_name, variant.name);
            if field_branches.len() != variant.fields.len() {
                return None;
            }
            let mut args = Vec::with_capacity(field_branches.len());
            for (field_vt, field_def) in field_branches.iter().zip(variant.fields.iter()) {
                let field_ty = field_def.ty(tcx, substs).skip_norm_wip();
                args.push(translate_valtree_to_expr_with_tcx(
                    tcx,
                    branch_const_to_valtree(*field_vt)?,
                    field_ty,
                )?);
            }
            Some(PureExpr::LogicFnCall { name, args })
        }
        // Reference types: transparent deref — the ValTree stores the
        // pointee's ValTree directly (not a pointer). (#2572)
        (_, TyKind::Ref(_, inner_ty, _)) => {
            translate_valtree_to_expr_with_tcx(tcx, valtree, *inner_ty)
        }
        _ => None,
    }
}

/// `TyCtxt`-aware variant of [`translate_const_array`] that uses
/// [`translate_valtree_to_expr_with_tcx`] to handle ADT element types.
/// (#2572)
fn translate_const_array_with_tcx<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    mir_const: &rustc_middle::mir::Const<'tcx>,
    elem_ty: rustc_middle::ty::Ty<'tcx>,
    len_const: rustc_middle::ty::Const<'tcx>,
) -> Option<PureExpr> {
    use rustc_middle::mir::Const as MirConst;

    let MirConst::Ty(_, ty_const) = mir_const else {
        return None;
    };
    let value = ty_const.try_to_value()?;
    // Trust: ValTreeKind::Branch now holds &[ty::Const]; project to the slice.
    let elements = value.try_to_branch()?;

    let len = translate_ty_const_to_usize(len_const)?;
    if elements.is_empty() {
        return None;
    }

    let first_expr =
        translate_valtree_to_expr_with_tcx(tcx, branch_const_to_valtree(elements[0])?, elem_ty)?;

    let all_same = elements.iter().skip(1).all(|elem| {
        branch_const_to_valtree(*elem)
            .and_then(|vt| translate_valtree_to_expr_with_tcx(tcx, vt, elem_ty))
            .is_some_and(|e| e == first_expr)
    });

    if all_same {
        Some(PureExpr::LogicFnCall {
            name: "array_repeat".to_string(),
            args: vec![first_expr, PureExpr::Int(len)],
        })
    } else {
        let mut translated = Vec::with_capacity(elements.len());
        for element in elements {
            translated.push(translate_valtree_to_expr_with_tcx(
                tcx,
                branch_const_to_valtree(*element)?,
                elem_ty,
            )?);
        }
        match translated.as_slice() {
            [single] => Some(single.clone()),
            _ => Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(translated.len()),
                args: translated,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: evaluate a PureExpr decomposition tree back to i128.
    fn eval_expr(expr: &PureExpr) -> i128 {
        match expr {
            PureExpr::Int(v) => *v as i128,
            PureExpr::BinOp(lhs, BinOp::Mul, rhs) => eval_expr(lhs) * eval_expr(rhs),
            PureExpr::BinOp(lhs, BinOp::Add, rhs) => eval_expr(lhs) + eval_expr(rhs),
            PureExpr::BinOp(lhs, BinOp::Sub, rhs) => eval_expr(lhs) - eval_expr(rhs),
            _ => panic!("unexpected expr in decomposition: {expr:?}"),
        }
    }

    #[test]
    fn test_large_unsigned_small_value_is_int() {
        let expr = large_unsigned_to_expr(42);
        assert_eq!(expr, PureExpr::Int(42));
    }

    #[test]
    fn test_large_unsigned_i64_max_is_int() {
        let expr = large_unsigned_to_expr(i64::MAX as u128);
        assert_eq!(expr, PureExpr::Int(i64::MAX));
    }

    #[test]
    fn test_large_unsigned_u64_max_decomposes() {
        let expr = large_unsigned_to_expr(u64::MAX as u128);
        assert!(matches!(expr, PureExpr::BinOp(..)));
        assert_eq!(eval_expr(&expr), u64::MAX as i128);
    }

    #[test]
    fn test_large_unsigned_u128_max_decomposes() {
        // u128::MAX exceeds i128 range so we can't round-trip evaluate,
        // but the decomposition must produce a valid BinOp tree.
        let expr = large_unsigned_to_expr(u128::MAX);
        assert!(matches!(expr, PureExpr::BinOp(..)));
    }

    #[test]
    fn test_large_signed_small_positive() {
        assert_eq!(large_signed_to_expr(100), PureExpr::Int(100));
    }

    #[test]
    fn test_large_signed_small_negative() {
        assert_eq!(large_signed_to_expr(-42), PureExpr::Int(-42));
    }

    #[test]
    fn test_large_signed_i128_max_decomposes() {
        let expr = large_signed_to_expr(i128::MAX);
        assert!(matches!(expr, PureExpr::BinOp(..)));
        assert_eq!(eval_expr(&expr), i128::MAX);
    }

    #[test]
    fn test_large_signed_i128_min_decomposes() {
        // i128::MIN's absolute value (2^127) exceeds i128::MAX, so the test
        // evaluator overflows. Just check the decomposition is a valid tree.
        let expr = large_signed_to_expr(i128::MIN);
        assert!(matches!(expr, PureExpr::BinOp(..)));
    }

    #[test]
    fn test_large_unsigned_power_of_2_32() {
        // Exactly 2^32 — just above i64 threshold but clean power.
        let val: u128 = 1 << 32;
        let expr = large_unsigned_to_expr(val);
        assert_eq!(eval_expr(&expr), val.cast_signed());
    }
}
