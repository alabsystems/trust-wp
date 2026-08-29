// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR Rvalue translation (hub module importing from all siblings).

use std::sync::Arc;

use rustc_middle::{
    mir::{AggregateKind, Body, CastKind, Operand, Rvalue, UnOp as MirUnOp, WithRetag},
    ty::{adjustment::PointerCoercion, TyCtxt, TyKind},
};
use trust_wp_core::formula::{internal::tuple_lowering::tuple_logic_fn_name, BinOp, PureExpr};

use super::{
    binop::{int_ty_bits, lower_float_to_int, translate_binop, translate_unop, uint_ty_bits},
    constant::translate_constant_with_tcx,
    discriminant::{operand_int_ty, translate_ty_const_to_expr},
    float::{fold_concrete_float_binop, fold_concrete_float_unop},
    operand::{
        operand_array_len_expr, operand_is_bool, operand_is_machine_int, operand_is_signed_int,
        operand_is_slice_ptr_metadata, translate_operand_detailed,
    },
    place::{translate_place_detailed, translate_ref_rvalue_place, translate_typed_field_place},
    record_translation_gap, ExprLookup, TranslationDiagContext,
};

/// True iff a shift-amount expression is syntactically guaranteed to lie in
/// `[0, bits)`, discharging the shift-amount range obligation without a
/// marker and keeping the shape byte-identical to its historical translation:
///
/// - an integer literal already inside `[0, bits)` (`x << 3`), or
/// - a bitwise AND with a non-negative literal mask `m < bits`
///   (`x << (n & 7)` — the canonical `amt & (BITS - 1)` masking idiom):
///   for a non-negative mask `m`, `e & m` is in `[0, m]` for EVERY `e`
///   (each result bit is at most the corresponding mask bit), so the range
///   holds regardless of `e`.
pub(super) fn shift_amount_syntactically_in_range(expr: &PureExpr, bits: u32) -> bool {
    match expr {
        PureExpr::Int(value) => *value >= 0 && *value < i64::from(bits),
        PureExpr::BinOp(left, BinOp::BitAnd, right) => {
            let mask_in_range = |side: &PureExpr| matches!(side, PureExpr::Int(mask) if *mask >= 0 && *mask < i64::from(bits));
            mask_in_range(left) || mask_in_range(right)
        }
        _ => false,
    }
}

/// Wrap the shift-amount operand of a machine-int `<<`/`>>` in the internal
/// `__trust_wp_shift_amount_in_range_{bits}` marker.
///
/// Rust machine-int shifts are only defined for `0 <= amount < BITS` of the
/// SHIFTED operand's type; an over-wide (or negative) amount is an overflow
/// panic. The marker is the identity on its argument value-wise; the ay
/// encoder intercepts it and collects the path-guarded proof obligation
/// `0 <= amount && amount < bits` alongside the division obligations —
/// exactly the `divisor != 0` side-obligation pattern (`assert_nonzero_divisor`).
/// The corresponding MIR overflow assert is deliberately NOT assumed as a
/// fact (see `assert_fact_from_condition`), so the obligation is genuinely
/// checked rather than vacuously entailed by its own assumption.
///
/// Logical `Int` shifts (parsed contracts) never reach MIR lowering and the
/// no-body path cannot name a machine width, so both keep the plain,
/// unbounded translation. Syntactically in-range amounts (in-range literals
/// and `amt & (BITS - 1)`-style masks) skip the marker — see
/// [`shift_amount_syntactically_in_range`]. (ledger int-shift-full)
///
/// A shift whose SHIFTED operand's machine-int width cannot be determined
/// (non-machine-int shapes: overloaded `Shl`/`Shr` lowerings, projections
/// `place_int_ty` does not model) keeps its historical unmarked translation
/// — but the skip is RECORDED as a translation gap so an unmarked machine
/// shift is auditable rather than a silent hole in the obligation coverage.
fn wrap_shift_amount_in_range_marker<'tcx>(
    bin_op: BinOp,
    left: &Operand<'tcx>,
    right_expr: PureExpr,
    body: Option<&Body<'tcx>>,
    diag: Option<&TranslationDiagContext<'_>>,
) -> PureExpr {
    if !matches!(bin_op, BinOp::Shl | BinOp::Shr) {
        return right_expr;
    }
    let Some(body) = body else {
        // No MIR body (unit-test shims): no machine width is nameable —
        // documented plain translation, not a gap.
        return right_expr;
    };
    let Some(left_ty) = operand_int_ty(left, body) else {
        record_translation_gap(
            diag,
            format!(
                "shift-amount range marker skipped: cannot determine the shifted \
                 operand's machine-int width for {bin_op:?} (operand: {left:?})"
            ),
        );
        return right_expr;
    };
    if shift_amount_syntactically_in_range(&right_expr, left_ty.bits) {
        return right_expr;
    }
    PureExpr::LogicFnCall {
        name: format!("__trust_wp_shift_amount_in_range_{}", left_ty.bits),
        args: vec![right_expr],
    }
}

/// Translate a MIR Rvalue to a PureExpr (compatibility shim).
///
/// Calls `translate_rvalue_detailed` without a diagnostic context.
pub(crate) fn translate_rvalue<'tcx>(
    rvalue: &Rvalue<'tcx>,
    locals: &impl ExprLookup,
    body: Option<&Body<'tcx>>,
) -> Option<PureExpr> {
    translate_rvalue_detailed(rvalue, locals, body, None)
}

/// Translate a MIR Rvalue with `TyCtxt`-aware fallbacks.
///
/// The ordinary translator is intentionally syntax-driven. Loop extraction has
/// access to `TyCtxt`, so it can recover field projections, unevaluated
/// constants, and native struct aggregate constructors without weakening the
/// default path.
pub(crate) fn translate_rvalue_typed<'tcx>(
    tcx: TyCtxt<'tcx>,
    rvalue: &Rvalue<'tcx>,
    locals: &impl ExprLookup,
    body: Option<&Body<'tcx>>,
) -> Option<PureExpr> {
    if let Rvalue::Aggregate(box AggregateKind::Adt(def_id, variant_idx, ..), operands) = rvalue {
        let adt_def = tcx.adt_def(*def_id);
        if adt_def.is_struct() && operands.len() >= 2 {
            let mut args = Vec::with_capacity(operands.len());
            for operand in operands {
                args.push(translate_operand_detailed(operand, locals, None)?);
            }
            return Some(PureExpr::LogicFnCall {
                name: tcx.item_name(adt_def.did()).to_string(),
                args,
            });
        }
        // Enum aggregate (e.g., `Option::None`, `Option::Some(v)`): preserve
        // the variant constructor so sort information flows through. Without
        // this, a 0-field variant like `None` falls through to the generic
        // ADT path in `translate_rvalue_detailed`, which lowers to
        // `__trust_wp_tuple0()` (Unit sort). For a `*b = None` write where
        // `b: &mut Option<T>`, the resulting deref-effect would equate
        // `b_prime_current` (Option sort) to a Unit term, producing a
        // sort-mismatch axiom that drives the SAT solver into a degenerate
        // model and breaks the loop preservation check for while-let. (#994)
        if adt_def.is_enum() {
            let mut args = Vec::with_capacity(operands.len());
            for operand in operands {
                args.push(translate_operand_detailed(operand, locals, None)?);
            }
            let variant = adt_def.variant(*variant_idx);
            let adt_path = tcx.def_path_str(adt_def.did());
            // Match `translate_rvalue_with_enum_variants`'s naming for std
            // Option/Result so the encoder's variant axioms (`logic_Some`,
            // `logic_None`, ...) line up with the body extractor's output.
            let name = if matches!(
                adt_path.as_str(),
                "Option"
                    | "std::option::Option"
                    | "core::option::Option"
                    | "Result"
                    | "std::result::Result"
                    | "core::result::Result"
            ) {
                variant.name.as_str().to_string()
            } else {
                format!(
                    "{}::{}",
                    tcx.item_name(adt_def.did()).as_str(),
                    variant.name
                )
            };
            return Some(PureExpr::LogicFnCall { name, args });
        }
    }

    match rvalue {
        // Reborrow rvalue: try the body-aware reborrow translator first so
        // pure-Deref chains (e.g., `&mut **x` for `x: Box<&mut i32>`) collapse
        // to the underlying mutref instead of dropping into the typed-field
        // path which would add a spurious `Deref` layer per projection.
        // (#7 box_borrow_resolve)
        Rvalue::Ref(_, _, place) => body
            .and_then(|body| translate_ref_rvalue_place(body, place, locals))
            .or_else(|| body.and_then(|body| translate_typed_field_place(tcx, body, place, locals)))
            .or_else(|| translate_rvalue_detailed(rvalue, locals, body, None)),
        Rvalue::Use(operand, with_retag) => {
            translate_use_operand_typed(tcx, operand, *with_retag, locals, body)
        }
        Rvalue::CopyForDeref(place) => body
            .and_then(|body| translate_typed_field_place(tcx, body, place, locals))
            .or_else(|| translate_rvalue_detailed(rvalue, locals, body, None)),
        _ => translate_rvalue_detailed(rvalue, locals, body, None),
    }
}

fn int_to_int_cast_needs_unsoundness_tracking<'tcx>(
    operand: &Operand<'tcx>,
    cast_ty: &rustc_middle::ty::Ty<'tcx>,
    body: Option<&Body<'tcx>>,
) -> bool {
    let Some(body) = body else {
        return true;
    };

    // Bool → any integer is always value-preserving (0 or 1 fits in every
    // integer type). Treat bool as an unsigned 1-bit integer so widening
    // to u8/i8/u16/... is recognized as safe. (#2675)
    if operand_is_bool(operand, body) {
        return false;
    }

    let Some(source_ty) = super::operand_int_ty(operand, body) else {
        return true;
    };
    let Some((target_signed, target_bits)) = int_ty_kind_signed_bits(cast_ty.kind()) else {
        return true;
    };

    // Same sign + widening → always safe.
    if source_ty.signed == target_signed && source_ty.bits <= target_bits {
        return false;
    }

    // Non-negative signed constant → unsigned with enough bits is safe.
    // Rust shift operations generate `i32 → u32` casts for the shift
    // amount, where the constant is typically a small non-negative
    // literal. The SMT identity model is correct for these. (#2675)
    if source_ty.signed && !target_signed {
        if let Some(val) = operand_const_signed_value(operand) {
            if val >= 0 && source_ty.bits <= target_bits {
                return false;
            }
        }
    }

    true
}

/// Extract the signed integer value from a constant operand, if possible.
///
/// Returns `Some(value)` for `Operand::Constant` with an integer scalar;
/// `None` for non-constant operands or non-integer types.
fn operand_const_signed_value(operand: &Operand<'_>) -> Option<i128> {
    let Operand::Constant(constant) = operand else {
        return None;
    };
    let scalar_int = constant.const_.try_to_scalar_int()?;
    Some(scalar_int.to_int(scalar_int.size()))
}

fn int_ty_kind_signed_bits(kind: &TyKind<'_>) -> Option<(bool, u32)> {
    match kind {
        TyKind::Int(int_ty) => Some((true, int_ty_bits(*int_ty))),
        TyKind::Uint(uint_ty) => Some((false, uint_ty_bits(*uint_ty))),
        _ => None,
    }
}

/// Translate the value carried by `Rvalue::Use`.
///
/// `WithRetag` controls whether rustc performs a provenance retag, but the
/// operand's extensional Rust value is unchanged. Trust-WP's admitted
/// functional fragment cannot observe pointer provenance (unsafe/provenance-
/// sensitive operations are rejected elsewhere), and its logical borrow IDs,
/// finality, and writeback facts are derived from explicit `Rvalue::Ref`
/// creation plus borrow-checker facts—not from runtime provenance tags. Thus
/// `Yes` and `No` deliberately share this value translation. This also
/// preserves the pre-1.99 policy, where standalone retag statements carried no
/// functional expression in Trust-WP.
#[inline]
fn erase_use_retag(_with_retag: WithRetag) {}

fn translate_use_operand(
    operand: &Operand<'_>,
    with_retag: WithRetag,
    locals: &impl ExprLookup,
    diag: Option<&TranslationDiagContext<'_>>,
) -> Option<PureExpr> {
    erase_use_retag(with_retag);
    translate_operand_detailed(operand, locals, diag)
}

/// TyCtxt-aware `Use` translation with the same explicit retag-erasure policy
/// as `translate_use_operand`.
fn translate_use_operand_typed<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
    with_retag: WithRetag,
    locals: &impl ExprLookup,
    body: Option<&Body<'tcx>>,
) -> Option<PureExpr> {
    erase_use_retag(with_retag);
    match operand {
        Operand::Copy(place) | Operand::Move(place) => body
            .and_then(|body| translate_typed_field_place(tcx, body, place, locals))
            .or_else(|| translate_use_operand(operand, with_retag, locals, None)),
        Operand::Constant(constant) => translate_constant_with_tcx(constant, tcx)
            .or_else(|| translate_use_operand(operand, with_retag, locals, None)),
        Operand::RuntimeChecks(_) => translate_use_operand(operand, with_retag, locals, None),
    }
}

/// Translate the compiler's generic user-ADT reborrow operation.
///
/// Although rustc implements the operation as a bitwise copy, an exclusive
/// `Reborrow` also disables and later writes back through the source carrier;
/// a shared `CoerceShared` may additionally change the ADT type. Trust-WP's
/// mutable-borrow/finality lanes currently model those semantics only for
/// built-in references. Treating either generic operation as a plain identity
/// would lose alias/writeback facts, so both forms fail closed until the custom
/// carrier semantics are modeled end to end.
pub(super) fn translate_generic_reborrow(
    mutability: rustc_middle::ty::Mutability,
    diag: Option<&TranslationDiagContext<'_>>,
) -> Option<PureExpr> {
    record_translation_gap(
        diag,
        format!(
            "{mutability:?} generic reborrow requires custom-carrier alias/writeback semantics"
        ),
    );
    None
}

/// Translate a MIR Rvalue to a PureExpr, recording diagnostics for failures.
///
/// `body` is used for type-aware translation of BitAnd/BitOr (#490):
/// boolean operands map to logical And/Or, integer operands return None.
/// When `body` is `None` (e.g., in unit tests), BitAnd/BitOr default to
/// logical interpretation (preserves backward compatibility).
///
/// When `diag` is provided, failure sites record a `FeatureGap` diagnostic
/// with the specific MIR construct that could not be translated.
#[allow(clippy::too_many_lines)] // Match dispatch over all Rvalue variants
pub(crate) fn translate_rvalue_detailed<'tcx>(
    rvalue: &Rvalue<'tcx>,
    locals: &impl ExprLookup,
    body: Option<&Body<'tcx>>,
    diag: Option<&TranslationDiagContext<'_>>,
) -> Option<PureExpr> {
    match rvalue {
        Rvalue::Use(operand, with_retag) => {
            translate_use_operand(operand, *with_retag, locals, diag)
        }

        Rvalue::BinaryOp(op, box (left, right)) => {
            let left_expr = translate_operand_detailed(left, locals, diag)?;
            let right_expr = translate_operand_detailed(right, locals, diag)?;
            let bool_ops = body.is_none_or(|b| operand_is_bool(left, b));
            let Some(bin_op) = translate_binop(*op, bool_ops) else {
                record_translation_gap(diag, format!("unsupported binary operator: {op:?}"));
                return None;
            };
            // Rust's `/` on machine integers TRUNCATES toward zero
            // (`-7 / 2 == -3`), matching Creusot's `Int` `/` model
            // `int.ComputerDivision.div`. Lower it to `BinOp::DivTrunc` for ANY
            // machine int (signed or unsigned) so the body division uses the
            // SAME term as the parsed contract `l@ / r@` (also `DivTrunc`),
            // letting `result@ == l@ / r@` discharge reflexively. Unsigned
            // operands truncate identically to Euclidean (non-negative), so the
            // value is unchanged.
            //
            // Rust's signed `%` likewise truncates (`-1 % 5 == -1`), lowered to
            // `BinOp::RemTrunc`. Unsigned `%` stays Euclidean `BinOp::Mod`,
            // matching the contract `%` which also stays Euclidean (wrapping
            // arithmetic specs depend on the non-negative remainder).
            //
            // Floats and the no-body / projected-place path keep exact/Euclidean
            // `Div`/`Mod`. Mathematical `Int` never reaches MIR lowering (it
            // comes from parsed contracts). See trust-wp-divmod-semantics.
            let bin_op = match bin_op {
                BinOp::Div if body.is_some_and(|b| operand_is_machine_int(left, b)) => {
                    BinOp::DivTrunc
                }
                BinOp::Mod if body.is_some_and(|b| operand_is_signed_int(left, b)) => {
                    BinOp::RemTrunc
                }
                other => other,
            };
            if let Some(folded) = fold_concrete_float_binop(&left_expr, bin_op, &right_expr) {
                return Some(folded);
            }
            // Machine-int shifts carry the shift-amount-in-range side
            // obligation via the internal marker; every other operator keeps
            // the amount/right operand untouched. (ledger int-shift-full)
            let right_expr =
                wrap_shift_amount_in_range_marker(bin_op, left, right_expr, body, diag);
            Some(PureExpr::BinOp(
                Arc::new(left_expr),
                bin_op,
                Arc::new(right_expr),
            ))
        }

        Rvalue::UnaryOp(op, operand) => {
            // PtrMetadata replaces the old Rvalue::Len in modern rustc.
            // `slice.len()` compiles to `PtrMetadata(copy slice_ref)`.
            // Model as a `.len()` method call so the ay encoder dispatches
            // to seq_len for Seq-sorted receivers or an uninterpreted
            // function otherwise. (#947)
            //
            // Guard: only produce `.len()` when the operand is a slice/array
            // reference. PtrMetadata on `&dyn Trait` extracts the vtable
            // pointer, not a length — modeling that as `.len()` would be
            // unsound. The translator therefore requires MIR type data and
            // fails closed when `body` is unavailable. (#952, #2049)
            if matches!(op, MirUnOp::PtrMetadata) {
                let Some(b) = body else {
                    record_translation_gap(diag, "PtrMetadata without MIR body");
                    return None;
                };
                if !operand_is_slice_ptr_metadata(operand, b) {
                    record_translation_gap(diag, "PtrMetadata on non-slice/non-array type");
                    return None;
                }
                // Fixed-size arrays have type-level lengths. Folding these
                // lengths at MIR translation time avoids introducing
                // uninterpreted `len()` calls for `[T; N]` values.
                if let Some(array_len) = operand_array_len_expr(operand, b) {
                    return Some(array_len);
                }
                let operand_expr = translate_operand_detailed(operand, locals, diag)?;
                // Wrap the receiver in View() to model `slice.len()` as
                // `(slice@).len()` — the length of the logical Seq view.
                // Without View, the bare Var receiver falls to the FSet
                // dispatch path in the ay encoder because is_seq_receiver
                // only promotes bare Var receivers when a separate View
                // evidence exists in the scanned expressions. With View,
                // the sort hint prescan directly classifies the receiver
                // as Seq, ensuring dispatch to seq_len. This connects
                // the PtrMetadata result to the same `seq_len(var_view)`
                // term used by postconditions like `result@ == self@.len()`.
                // (#2675)
                return Some(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(operand_expr))),
                    method: "len".to_string(),
                    args: vec![],
                });
            }
            let operand_expr = translate_operand_detailed(operand, locals, diag)?;
            let bool_op = body.is_none_or(|b| operand_is_bool(operand, b));
            let Some(unary_op) = translate_unop(*op, bool_op) else {
                record_translation_gap(diag, format!("unsupported unary operator: {op:?}"));
                return None;
            };
            if let Some(folded) = fold_concrete_float_unop(unary_op, &operand_expr) {
                return Some(folded);
            }
            Some(PureExpr::UnOp(unary_op, Arc::new(operand_expr)))
        }

        // Cast operations — type-aware dispatch following Creusot's cast handling.
        // Integer-to-integer: BV truncation for narrowing casts, identity otherwise.
        // Pointer coercions: identity for safe variants, None for unsupported.
        Rvalue::Cast(kind, operand, cast_ty) => match kind {
            // Integer casts: same-signed widening is value-preserving (identity).
            // Narrowing and sign-changing casts use BV truncation when bitwise
            // proof mode is enabled (#2666, #938). The encoder's
            // `encode_int_truncation_bv` converts Int → BV(width) → extract →
            // Int, giving exact modular truncation semantics.
            CastKind::IntToInt => {
                let operand_expr = translate_operand_detailed(operand, locals, diag);
                if !int_to_int_cast_needs_unsoundness_tracking(operand, cast_ty, body) {
                    // Safe cast (widening, same-sign): identity.
                    return operand_expr;
                }
                // Narrowing or sign-changing cast: emit a BV truncation call
                // that the encoder intercepts. The name encodes the target
                // bit width and signedness so the encoder can call
                // `encode_int_truncation_bv(value, bits, signed)`.
                //
                // Falls back to identity + unsoundness tracking when we cannot
                // determine the target type parameters. (#938)
                let Some((target_signed, target_bits)) = int_ty_kind_signed_bits(cast_ty.kind())
                else {
                    trust_wp_ay::unsoundness::increment(
                        trust_wp_ay::UnsoundnessCategory::IntegerCastIdentity,
                    );
                    return operand_expr;
                };
                let operand_expr = operand_expr?;
                if let Some(body) = body {
                    if let Some(source_ty) = super::operand_int_ty(operand, body) {
                        if !source_ty.signed && target_signed && source_ty.bits == target_bits {
                            return Some(PureExpr::LogicFnCall {
                                name: format!(
                                    "__trust_wp_int_cast_u{}_to_s{}",
                                    source_ty.bits, target_bits
                                ),
                                args: vec![operand_expr],
                            });
                        }
                    }
                }

                let sign_tag = if target_signed { "s" } else { "u" };
                Some(PureExpr::LogicFnCall {
                    name: format!("__trust_wp_int_truncate_{sign_tag}{target_bits}"),
                    args: vec![operand_expr],
                })
            }

            // Int→Float: identity. Every integer is exactly representable as a
            // Real in the SMT model. Sort coercion (Int→Real) is handled by the
            // encoding layer. (#1802)
            CastKind::IntToFloat => translate_operand_detailed(operand, locals, diag),

            // Float→Float (e.g., f32→f64): identity. trust-wp models all floats as
            // unbounded Reals, so precision changes are invisible at the logical
            // level. (#1802)
            CastKind::FloatToFloat => translate_operand_detailed(operand, locals, diag),

            // Pointer-to-pointer reinterpretation: identity at the logical level.
            CastKind::PtrToPtr => translate_operand_detailed(operand, locals, diag),

            // Subtype coercion (e.g., lifetime variance): value-preserving.
            CastKind::Subtype => translate_operand_detailed(operand, locals, diag),

            // Unsize coercion: &[T; N] → &[T] is value-preserving identity.
            // For dyn coercions the logical value is also preserved (vtable is
            // invisible at the specification level).
            CastKind::PointerCoercion(PointerCoercion::Unsize, _) => {
                translate_operand_detailed(operand, locals, diag)
            }

            // &mut T → &T (or *mut T → *const T): mutability is erased
            // in the logical model.
            CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _) => {
                translate_operand_detailed(operand, locals, diag)
            }

            // Closure/fn-item to fn-pointer: identity at the logical level
            // (closure captures are modeled via tuple sorts, not fn pointers).
            CastKind::PointerCoercion(
                // Trust: ReifyFnPointer is now a tuple variant.
                PointerCoercion::ClosureFnPointer(_) | PointerCoercion::ReifyFnPointer(_),
                _,
            ) => translate_operand_detailed(operand, locals, diag),

            // Float→Int: truncate toward zero + clamp to target range.
            // Rust: `x as i32` rounds toward zero, saturates on overflow.
            // Lowering: let t = trunc_zero(x) in clamp(t, bounds...) (#1802)
            CastKind::FloatToInt => {
                let arg = translate_operand_detailed(operand, locals, diag)?;
                lower_float_to_int(arg, cast_ty.kind())
            }

            // Unsupported cast kinds — return None so the caller can handle
            // the untranslatable expression (fail-closed).
            CastKind::FnPtrToPtr
            | CastKind::PointerExposeProvenance
            | CastKind::PointerWithExposedProvenance
            | CastKind::Transmute
            | CastKind::PointerCoercion(
                PointerCoercion::UnsafeFnPointer | PointerCoercion::ArrayToPointer,
                _,
            ) => {
                record_translation_gap(diag, format!("unsupported cast kind: {kind:?}"));
                None
            }
        },

        // Reborrow / borrow rvalues (`_tmp = &[mut] place`). For pure-Deref
        // chains, this is a reborrow: `&*e == e`. The body-aware translator
        // also recognises Box derefs as transparent (Box<T> shares its sort
        // with T). Mixed projection chains and projection-less places fall
        // back to the existing place translator. (#7 box_borrow_resolve)
        Rvalue::Ref(_, _, place) => body
            .and_then(|b| translate_ref_rvalue_place(b, place, locals))
            .or_else(|| translate_place_detailed(place, locals, diag)),

        Rvalue::Reborrow(_, mutability, _) => translate_generic_reborrow(*mutability, diag),

        // Tuple construction (for Fn/FnMut call lowering and checked-op helpers).
        // `()` lowers to `__trust_wp_tuple0()` so zero-arg closure call specs keep
        // their unit argument, `(x,)` is modeled as `x`, and wider tuples lower
        // to synthetic tuple constructor calls.
        Rvalue::Aggregate(box rustc_middle::mir::AggregateKind::Tuple, operands) => {
            let mut translated: Vec<PureExpr> = Vec::with_capacity(operands.len());
            for operand in operands {
                translated.push(translate_operand_detailed(operand, locals, diag)?);
            }
            match translated.as_slice() {
                [] => Some(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(0),
                    args: vec![],
                }),
                [single] => Some(single.clone()),
                _ => Some(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(translated.len()),
                    args: translated,
                }),
            }
        }

        // Closure environment construction.
        //
        // Unlike tuple/newtype lowering, preserve arity-1 environments as
        // `tuple1(capture)` (do not collapse to the inner value). This keeps
        // capture-field projections (`self.0`, `self.1`, ...) representable at
        // call sites and proof_assert extraction.
        Rvalue::Aggregate(box rustc_middle::mir::AggregateKind::Closure(..), operands) => {
            let mut translated: Vec<PureExpr> = Vec::with_capacity(operands.len());
            for operand in operands {
                translated.push(translate_operand_detailed(operand, locals, diag)?);
            }
            if translated.is_empty() {
                // A non-capturing closure captures nothing, so its environment
                // IS the unit value. Lower it to `tuple0()`, mirroring the
                // empty-tuple aggregate case above (rvalue.rs:435), so downstream
                // loop/obligation analysis proceeds instead of failing extraction.
                Some(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(0),
                    args: vec![],
                })
            } else {
                Some(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(translated.len()),
                    args: translated,
                })
            }
        }

        // ADT (struct/enum variant) construction — handle newtypes and
        // multi-field structs so their body expressions flow through
        // verification. Single-field structs pass through as their inner
        // value (identity, like single-element tuples). Multi-field structs
        // lower to synthetic tuple constructors, matching the field-projection
        // logic in `project_tuple_field`. (#359)
        Rvalue::Aggregate(box rustc_middle::mir::AggregateKind::Adt(..), operands) => {
            let mut translated: Vec<PureExpr> = Vec::with_capacity(operands.len());
            for operand in operands {
                translated.push(translate_operand_detailed(operand, locals, diag)?);
            }
            match translated.as_slice() {
                [] => Some(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(0),
                    args: vec![],
                }),
                [single] => Some(single.clone()),
                _ => Some(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(translated.len()),
                    args: translated,
                }),
            }
        }

        // Discriminant read: `_N = discriminant(_M)` in MIR, generated by
        // match/if-let on enums. We model this as a `.discriminant()` method
        // call on the base expression, which the ay encoder will dispatch to
        // an uninterpreted Int function. This populates local_exprs so that
        // downstream SwitchInt can branch on it instead of falling back to
        // exploring all arms blindly. (#947)
        Rvalue::Discriminant(place) => {
            let base = translate_place_detailed(place, locals, diag)?;
            Some(PureExpr::MethodCall {
                receiver: Arc::new(base),
                method: "discriminant".to_string(),
                args: vec![],
            })
        }

        // CopyForDeref: `_N = CopyForDeref(_M)` — identity copy before
        // a dereference. Semantically equivalent to Use(Copy(place)). (#947)
        Rvalue::CopyForDeref(place) => translate_place_detailed(place, locals, diag),

        // Repeat: `[expr; N]` array literal initialization.
        // MIR generates `Rvalue::Repeat(operand, count)` for this pattern.
        // Model as `array_repeat(operand, count)` so the ay encoder can
        // dispatch to a suitable axiomatization (e.g., a constant-valued
        // sequence of length N). (#948)
        Rvalue::Repeat(operand, count) => {
            let operand_expr = translate_operand_detailed(operand, locals, diag)?;
            let count_expr = translate_ty_const_to_expr(*count)?;
            Some(PureExpr::LogicFnCall {
                name: "array_repeat".to_string(),
                args: vec![operand_expr, count_expr],
            })
        }

        // Other aggregate forms (e.g., closures, coroutines) are unsupported.
        _ => {
            record_translation_gap(diag, format!("unsupported rvalue kind: {rvalue:?}"));
            None
        }
    }
}
