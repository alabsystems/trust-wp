// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Enum-aware rvalue translation and unevaluated-const symbolic expansion.

use std::collections::HashMap;

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE},
    ConstItemRhs, ImplItemKind, Node, TraitItemKind,
};
use rustc_middle::{
    mir::{AggregateKind, Body, Local, Location, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::{contract_parser::parse_contract_body, formula::PureExpr};
use trust_wp_driver::StdSpec;

use super::super::{
    super::translate::{
        translate_constant_with_tcx, translate_operand, translate_rvalue_detailed,
        translate_rvalue_typed, ty_to_expr_sort_enriched, ExprLookup, TranslationDiagContext,
    },
    record_qualified_assoc_const_definition, MAX_UNEVAL_CONST_EXPANSION_DEPTH,
    UNEVAL_CONST_EXPANSION_DEPTH,
};
use crate::mir_analysis::diagnostics::{
    record_extraction_diag, ExtractionDiagKind, ExtractionDiagnosticSink,
};

/// RAII guard for `UNEVAL_CONST_EXPANSION_DEPTH`.
///
/// Increments the depth counter on construction and restores the previous
/// value on drop, ensuring the counter is restored even on unwind (#1712).
struct UnevalConstDepthGuard<'a> {
    cell: &'a std::cell::Cell<usize>,
    previous: usize,
}

impl<'a> UnevalConstDepthGuard<'a> {
    fn new(cell: &'a std::cell::Cell<usize>, previous: usize) -> Self {
        cell.set(previous + 1);
        Self { cell, previous }
    }
}

impl Drop for UnevalConstDepthGuard<'_> {
    fn drop(&mut self) {
        self.cell.set(self.previous);
    }
}

/// Translate enum ADT constructors to `LogicFnCall` terms.
///
/// `translate_rvalue` intentionally collapses single-field ADTs to the inner
/// value (newtype behavior). That is useful for structs/newtypes, but unsound
/// for enum variants (for example `Some(v)` must retain variant identity).
///
/// Also preserve nullary enum constants (`Option::None`, etc.) assigned via
/// `Rvalue::Use(Operand::Constant(...))` so match-based postconditions can
/// resolve the correct branch in proof_assert substitution extraction.
///
/// For enum aggregates, preserve the constructor name and translated operands:
/// - `Option::None` => `LogicFnCall { name: "Option::None", args: [] }`
/// - `OwnResult::Ok(v)` => `LogicFnCall { name: "OwnResult::Ok", args: [v] }`
///
/// This keeps variant information available to match-based std specs (such as
/// `Option::ok_or`) in proof_assert extraction. (#1264, #1277)
pub(in super::super) fn translate_rvalue_with_enum_variants<'tcx>(
    tcx: TyCtxt<'tcx>,
    rvalue: &Rvalue<'tcx>,
    locals: &impl ExprLookup,
    body: Option<&Body<'tcx>>,
    diagnostics: Option<&ExtractionDiagnosticSink>,
    location: Option<Location>,
) -> Option<PureExpr> {
    if let Rvalue::Use(Operand::Constant(box constant), _) = rvalue {
        if let rustc_middle::ty::TyKind::Adt(adt_def, _) = constant.ty().kind() {
            if adt_def.is_enum() {
                if let Some(discr) = constant.const_.try_to_scalar_int() {
                    let discr_val = discr.to_uint(discr.size());
                    if let Some((variant_idx, _)) = adt_def.discriminants(tcx).find(|(idx, d)| {
                        adt_def.variant(*idx).fields.is_empty() && d.val == discr_val
                    }) {
                        let variant = adt_def.variant(variant_idx);
                        let name =
                            enum_variant_logic_name(tcx, adt_def.did(), variant.name.as_str());
                        return Some(PureExpr::LogicFnCall { name, args: vec![] });
                    }
                }
            }
        }
    }

    if let Rvalue::Aggregate(box AggregateKind::Adt(def_id, variant_idx, ..), operands) = rvalue {
        let adt_def = tcx.adt_def(*def_id);
        if adt_def.is_enum() {
            let mut args = Vec::with_capacity(operands.len());
            for operand in operands {
                args.push(translate_operand(operand, locals)?);
            }
            let variant = adt_def.variant(*variant_idx);
            let name = enum_variant_logic_name(tcx, adt_def.did(), variant.name.as_str());
            return Some(PureExpr::LogicFnCall { name, args });
        }
    }
    if let Some(expr) = translate_rvalue_typed(tcx, rvalue, locals, body) {
        return Some(expr);
    }

    // Then try the standard translation with diagnostic context.
    let diag_ctx = diagnostics.map(|sink| TranslationDiagContext {
        sink: Some(sink),
        module: "translate/mod.rs",
        location,
    });
    if let Some(expr) = translate_rvalue_detailed(rvalue, locals, body, diag_ctx.as_ref()) {
        return Some(expr);
    }

    if let Rvalue::Cast(
        rustc_middle::mir::CastKind::IntToInt,
        Operand::Constant(box constant),
        cast_ty,
    ) = rvalue
    {
        if let Some(expr) = translate_int_to_int_constant_cast(tcx, constant, *cast_ty, diagnostics)
        {
            return Some(expr);
        }
    }

    // Fallback: named constants (`const FOO: usize = 42`), const blocks
    // (`const { N + 1 }`), and associated constants (`T::VALUE`) appear as
    // `Const::Unevaluated` in MIR. `translate_rvalue` → `translate_constant`
    // cannot resolve these without TyCtxt.
    //
    // First try CTFE-backed constant translation, then fall back to symbolic/
    // MIR-body expansion for generic constants and associated constants that
    // CTFE cannot monomorphize. (#1588)
    if let Rvalue::Use(Operand::Constant(box constant), _) = rvalue {
        if let rustc_middle::mir::Const::Unevaluated(ref uneval, _) = constant.const_ {
            let def_kind = tcx.def_kind(uneval.def);
            let is_const_item = matches!(
                def_kind,
                DefKind::Const { .. }
                    | DefKind::AssocConst { .. }
                    | DefKind::AnonConst
                    | DefKind::InlineConst
            );
            let has_params = uneval.args.iter().any(|arg| {
                arg.as_type()
                    .is_some_and(|ty| matches!(ty.kind(), rustc_middle::ty::TyKind::Param(_)))
                    || arg
                        .as_const()
                        .is_some_and(|c| matches!(c.kind(), rustc_middle::ty::ConstKind::Param(_)))
            });

            // CTFE path: monomorphic const items and promoted constants.
            // Promoted constants (e.g., `const fn::promoted[0]` for `&NonCopy(1i32)`)
            // have DefKind::Fn (their enclosing function), not DefKind::Const,
            // so we check `promoted.is_some()` separately. (#1572)
            let is_promoted = uneval.promoted.is_some();
            if (is_const_item && !has_params) || is_promoted {
                if let Some(expr) = translate_constant_with_tcx(constant, tcx) {
                    return Some(expr);
                }
            }

            // Symbolic/MIR-body path (supports generic const params and assoc consts).
            if is_const_item {
                if let Some(expr) = translate_unevaluated_const_symbolic(tcx, constant, diagnostics)
                {
                    return Some(expr);
                }
            }
        }
    }

    None
}

fn translate_int_to_int_constant_cast<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
    cast_ty: rustc_middle::ty::Ty<'tcx>,
    diagnostics: Option<&ExtractionDiagnosticSink>,
) -> Option<PureExpr> {
    let value = translate_constant_with_tcx(constant, tcx)
        .or_else(|| translate_unevaluated_const_symbolic(tcx, constant, diagnostics))?;

    let source = int_ty_signed_bits(constant.ty().kind())?;
    let target = int_ty_signed_bits(cast_ty.kind())?;
    if int_cast_is_value_preserving(&value, source, target) {
        return Some(value);
    }

    let sign_tag = if target.signed { "s" } else { "u" };
    Some(PureExpr::LogicFnCall {
        name: format!("__trust_wp_int_truncate_{sign_tag}{}", target.bits),
        args: vec![value],
    })
}

#[derive(Clone, Copy)]
struct IntCastTy {
    signed: bool,
    bits: u32,
}

fn int_ty_signed_bits(kind: &rustc_middle::ty::TyKind<'_>) -> Option<IntCastTy> {
    use rustc_middle::ty::{IntTy, UintTy};

    let (signed, bits) = match kind {
        rustc_middle::ty::TyKind::Int(int_ty) => (
            true,
            match int_ty {
                IntTy::Isize => (std::mem::size_of::<isize>() * 8) as u32,
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
                IntTy::I128 => 128,
            },
        ),
        rustc_middle::ty::TyKind::Uint(uint_ty) => (
            false,
            match uint_ty {
                UintTy::Usize => (std::mem::size_of::<usize>() * 8) as u32,
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 => 64,
                UintTy::U128 => 128,
            },
        ),
        _ => return None,
    };
    Some(IntCastTy { signed, bits })
}

fn int_cast_is_value_preserving(value: &PureExpr, source: IntCastTy, target: IntCastTy) -> bool {
    if source.signed == target.signed && source.bits <= target.bits {
        return true;
    }
    if let PureExpr::Int(value) = value {
        return int_literal_fits_target(*value, target);
    }
    false
}

fn int_literal_fits_target(value: i64, target: IntCastTy) -> bool {
    let value = i128::from(value);
    if target.signed {
        let max = signed_max(target.bits);
        let min = -max - 1;
        value >= min && value <= max
    } else {
        value >= 0 && u128::try_from(value).is_ok_and(|v| v <= unsigned_max(target.bits))
    }
}

fn signed_max(bits: u32) -> i128 {
    if bits >= 128 {
        i128::MAX
    } else {
        (1_i128 << (bits - 1)) - 1
    }
}

fn unsigned_max(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1_u128 << bits) - 1
    }
}

fn enum_variant_logic_name(tcx: TyCtxt<'_>, adt_def_id: DefId, variant_name: &str) -> String {
    // For standard library Option and Result, use unqualified variant names
    // ("Some", "None", "Ok", "Err") so they match the UF constructors used
    // by the Option/Result axiom system in trust-wp-ay's adt_axioms module.
    // The axioms are keyed on `logic_Some`, `logic_None`, etc. — using
    // qualified names like `logic_Option_P__P_Some` breaks the connection
    // between the MIR extraction output and the reconstruction axioms
    // (e.g., `is_some(x) => Some(unwrap(x)) == x`). (#2675)
    let adt_path = tcx.def_path_str(adt_def_id);
    if is_std_option_or_result(&adt_path) {
        return variant_name.to_string();
    }
    format!("{}::{variant_name}", tcx.item_name(adt_def_id).as_str())
}

/// Check if the ADT path corresponds to std `Option` or `Result`.
fn is_std_option_or_result(path: &str) -> bool {
    matches!(
        path,
        "Option"
            | "std::option::Option"
            | "core::option::Option"
            | "Result"
            | "std::result::Result"
            | "core::result::Result"
    )
}

pub(super) fn translate_unevaluated_const_symbolic<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
    diagnostics: Option<&ExtractionDiagnosticSink>,
) -> Option<PureExpr> {
    use rustc_middle::mir::Const as MirConst;

    let MirConst::Unevaluated(ref uneval, _) = constant.const_ else {
        return None;
    };
    let def_id = uneval.def;
    let def_kind = tcx.def_kind(def_id);
    if !matches!(
        def_kind,
        DefKind::Const { .. }
            | DefKind::AssocConst { .. }
            | DefKind::AnonConst
            | DefKind::InlineConst
    ) {
        return None;
    }

    UNEVAL_CONST_EXPANSION_DEPTH.with(|depth| {
        let current = depth.get();
        if current >= MAX_UNEVAL_CONST_EXPANSION_DEPTH {
            record_extraction_diag(
                diagnostics,
                "extract/helpers/unevaluated_const.rs",
                ExtractionDiagKind::UnevaluatedConstRecursionLimit,
                format!(
                    "stopped symbolic MIR expansion for `{}` at depth {}",
                    tcx.def_path_str(def_id),
                    current
                ),
                None,
            );
            return None;
        }
        let _guard = UnevalConstDepthGuard::new(depth, current);
        translate_unevaluated_const_symbolic_impl(tcx, constant, def_id, diagnostics)
    })
}

/// Detect the primary extractor's `on_assign_local` placeholder for the
/// return place when its rvalue could not be translated.
///
/// In `primary.rs::on_assign_local`, an untranslatable RHS leaves the local
/// bound as `PureExpr::Var("_<n>", sort)` so downstream reads do not crash.
/// When that local is the return place (`_0`), `extract_return_expr_impl`
/// returns that placeholder as the body's value. For a `DefKind::Const`
/// body (e.g., `const STR: &'static str = "Hello"`), surfacing the
/// placeholder would shadow the const's symbolic name and disconnect the
/// extracted body from the postcondition. (lang/const `str()` — Phase 3.)
fn is_trivial_return_place_var(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == "_0")
}

pub(super) fn translate_unevaluated_const_symbolic_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
    def_id: DefId,
    diagnostics: Option<&ExtractionDiagnosticSink>,
) -> Option<PureExpr> {
    // Prefer the const item's MIR body when available: this preserves symbolic
    // generic expressions such as `N + 1`, `<T as Nat>::VALUE`, and nested const
    // wrappers (`const { foo::<T>() }`) without requiring CTFE monomorphization.
    // The Trust toolchain's `mir_for_ctfe` carries a `debug_assert!(!is_trivial_const)`
    // (rustc_mir_transform/src/lib.rs) — trivial consts (e.g. a `const STR: &str = "…"`
    // whose value is a reference to a static, requiring no CTFE computation) have no
    // CTFE MIR and panic if queried. `is_mir_available` still returns true for them, so
    // it is no longer a sufficient guard. Skip the CTFE-MIR body for trivial consts and
    // fall through to the symbolic-name path below (`Var(item_name)`), which is the
    // correct representation for such opaque consts anyway. Non-trivial arithmetic consts
    // (e.g. `const FOO: usize = 42`, which has a real CTFE body) are unaffected and keep
    // their value-bearing extraction. (lang/const `str()` — new-toolchain panic fix.)
    if tcx.is_mir_available(def_id) && !tcx.is_trivial_const(def_id) {
        let body = tcx.mir_for_ctfe(def_id);
        let empty_specs: HashMap<DefId, StdSpec> = HashMap::new();
        let empty_extern: HashMap<String, StdSpec> = HashMap::new();
        let config = super::super::ExtractionConfig {
            scope_call_context: false,
            cutoff_span: None,
            cutoff_location: None,
            diagnostics,
        };
        if let (Some(expr), _effects) = super::super::extract_return_expr_impl(
            tcx,
            body,
            &[],
            &empty_specs,
            &empty_specs,
            &empty_extern,
            config,
        ) {
            // Reject the trivial `Var("_0")` fallback from the primary
            // extractor's `on_assign_local`. When the const body assigns an
            // unrecognized rvalue (e.g., `const STR: &'static str = "Hello"`
            // assigning a `ConstValue::Slice` whose `&str` type is not in any
            // `translate_constant_inner` arm), the primary extractor keeps
            // the destination bound as `Var("_0")` so downstream reads do
            // not crash. Returning that here would propagate the placeholder
            // back into the caller's `local_exprs[_0]`, disconnecting the
            // body from the postcondition's `Var("STR")`. Fall through to
            // the symbolic-name path which produces `Var("STR")` directly.
            // (Phase 3 — `lang/const.rs` `str()` postcondition.)
            if !is_trivial_return_place_var(&expr) {
                for name in qualified_assoc_const_names(tcx, constant, def_id) {
                    record_qualified_assoc_const_definition(name, expr.clone());
                }
                return Some(expr);
            }
        }
        if let Some(expr) = translate_const_body_return_rvalue(tcx, body, diagnostics) {
            for name in qualified_assoc_const_names(tcx, constant, def_id) {
                record_qualified_assoc_const_definition(name, expr.clone());
            }
            return Some(expr);
        }
        record_extraction_diag(
            diagnostics,
            "extract/helpers/unevaluated_const.rs",
            ExtractionDiagKind::FeatureGap,
            format!(
                "const MIR extraction returned no expression for `{}`",
                tcx.def_path_str(def_id)
            ),
            None,
        );
    }

    match tcx.def_kind(def_id) {
        DefKind::Const { .. } => Some(PureExpr::Var(
            tcx.item_name(def_id).as_str().to_string(),
            ty_to_expr_sort_enriched(tcx, constant.ty()),
        )),
        DefKind::AnonConst | DefKind::InlineConst => symbolic_anon_const_name(constant)
            .map(|name| PureExpr::Var(name, ty_to_expr_sort_enriched(tcx, constant.ty()))),
        DefKind::AssocConst { .. } => {
            symbolic_assoc_const_name(tcx, constant, def_id).map(|name| {
                let sort = ty_to_expr_sort_enriched(tcx, constant.ty());
                let var = PureExpr::Var(name.clone(), sort.clone());
                // Register bare aliases so the contract parser's short forms (`S::C`)
                // unify with the body extractor's generic-spelled name (`S<T>::C`).
                // Without this, the postcondition's `Var("S::C", None)` is treated as
                // a nullary logic placeholder by the encoder while the body uses the
                // declared SMT variable `S<T>::C`, leaving the two disconnected. (#2054)
                let assoc_name = tcx.item_name(def_id).as_str().to_string();
                for alias in bare_assoc_const_aliases(&name, &assoc_name) {
                    record_qualified_assoc_const_definition(alias, var.clone());
                }
                var
            })
        }
        _ => None,
    }
}

/// Short user-facing aliases that the contract parser may produce for an
/// associated constant. These are bare paths such as `S::C` (matching the
/// way users typically write the constant inside a contract) and the
/// generic-spelled `S<T>::C` form produced by `symbolic_assoc_const_name`.
fn bare_assoc_const_aliases(canonical_name: &str, assoc_name: &str) -> Vec<String> {
    let mut aliases = vec![canonical_name.to_string()];
    // Bare form: strip the angle-bracket generic args from the leading type
    // segment so `S<T>::C` collapses to `S::C`. The contract parser produces
    // this short form when the user writes `S::C`.
    if let (Some(open), Some(close)) = (canonical_name.find('<'), canonical_name.find('>')) {
        // The remainder after `>` must be `::<assoc_name>` for this to be the
        // canonical `T<...>::C` shape (defensively skip QualifiedSelf forms
        // like `<S as F>::C`).
        let after = &canonical_name[close + 1..];
        if after == format!("::{assoc_name}") {
            let bare = format!("{}::{}", &canonical_name[..open], assoc_name);
            if bare != canonical_name {
                aliases.push(bare);
            }
        }
    }
    aliases
}

pub(super) fn symbolic_anon_const_name<'tcx>(
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
) -> Option<String> {
    use rustc_middle::mir::Const as MirConst;

    let MirConst::Unevaluated(ref uneval, _) = constant.const_ else {
        return None;
    };
    let const_params: Vec<String> = uneval
        .args
        .iter()
        .filter_map(|arg| {
            arg.as_const().and_then(|c| {
                if let rustc_middle::ty::ConstKind::Param(param) = c.kind() {
                    Some(param.name.as_str().to_string())
                } else {
                    None
                }
            })
        })
        .collect();

    if const_params.len() == 1 {
        return const_params.into_iter().next();
    }
    None
}

pub(super) fn symbolic_assoc_const_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
    def_id: DefId,
) -> Option<String> {
    use rustc_middle::mir::Const as MirConst;

    let MirConst::Unevaluated(ref uneval, _) = constant.const_ else {
        return None;
    };
    let assoc_name = tcx.item_name(def_id).as_str().to_string();

    let self_ty = uneval.args.iter().find_map(|arg| arg.as_type())?;
    let self_name = match self_ty.kind() {
        rustc_middle::ty::TyKind::Param(param) => param.name.as_str().to_string(),
        _ => self_ty.to_string(),
    };

    // Keep compatibility with parsed contract syntax for `is_zst`.
    if assoc_name == "IS_ZST" {
        let parent = tcx.opt_parent(def_id)?;
        if tcx.def_path_str(parent).contains("SizedTypeProperties") {
            return Some(format!(
                "<{self_name} as ::std::mem::SizedTypeProperties>::IS_ZST"
            ));
        }
    }

    // Common `Nat::VALUE` patterns in lang/const.rs:
    // - `<I<'a, T, N, U> as Nat>::VALUE` simplifies to `N`
    // - `<I2<T> as Nat>::VALUE` simplifies to `T::VALUE`
    if assoc_name == "VALUE" {
        if let rustc_middle::ty::TyKind::Adt(_, adt_args) = self_ty.kind() {
            if let Some(const_param) = adt_args.iter().find_map(|arg| {
                arg.as_const().and_then(|c| {
                    if let rustc_middle::ty::ConstKind::Param(param) = c.kind() {
                        Some(param.name.as_str().to_string())
                    } else {
                        None
                    }
                })
            }) {
                return Some(const_param);
            }
            if let Some(type_param) = adt_args.iter().find_map(|arg| {
                arg.as_type().and_then(|ty| {
                    if let rustc_middle::ty::TyKind::Param(param) = ty.kind() {
                        Some(param.name.as_str().to_string())
                    } else {
                        None
                    }
                })
            }) {
                return Some(format!("{type_param}::VALUE"));
            }
        }
    }

    Some(format!("{self_name}::{assoc_name}"))
}

fn qualified_assoc_const_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
    def_id: DefId,
) -> Vec<String> {
    use rustc_middle::ty::TyKind;

    let rustc_middle::mir::Const::Unevaluated(ref uneval, _) = constant.const_ else {
        return Vec::new();
    };
    let Some(assoc_item) = tcx.opt_associated_item(def_id) else {
        return Vec::new();
    };
    let Some(trait_item_def_id) = assoc_item.trait_item_def_id() else {
        return Vec::new();
    };
    let assoc_name = tcx.item_name(def_id).as_str().to_string();
    let Some(self_ty) = uneval.args.iter().find_map(|arg| arg.as_type()) else {
        return Vec::new();
    };
    let self_name = match self_ty.kind() {
        TyKind::Param(param) => param.name.as_str().to_string(),
        _ => self_ty.to_string(),
    };

    if assoc_name == "IS_ZST" {
        let trait_def_id = tcx.parent(trait_item_def_id);
        if tcx
            .def_path_str(trait_def_id)
            .contains("SizedTypeProperties")
        {
            return vec![format!(
                "<{self_name} as ::std::mem::SizedTypeProperties>::IS_ZST"
            )];
        }
    }

    qualified_assoc_const_aliases(tcx, &self_name, tcx.parent(trait_item_def_id), &assoc_name)
}

/// Collect generic associated constant definitions for contract substitution.
///
/// Iterates over all local trait-impl `AssocConst` items with generics and
/// translates each as an identity-instantiated unevaluated const. This reuses
/// the symbolic const fallback path so const-block bodies like
/// `const { T::VALUE + T::VALUE }` lower to the same `PureExpr` shape used by
/// MIR extraction. The keys match contract-parser qualified paths such as
/// `<I3<T> as Nat>::VALUE`. (#2550, #1474)
pub(crate) fn collect_generic_assoc_const_definitions<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> HashMap<String, PureExpr> {
    let mut map = HashMap::new();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::AssocConst { .. }) {
            continue;
        }
        // Skip monomorphic constants — already handled by resolve_const_item_value.
        let generics = tcx.generics_of(def_id);
        if generics.count() == 0 {
            continue;
        }

        // Must be in a trait impl (not a bare impl or trait definition).
        let Some(parent) = tcx.opt_parent(def_id) else {
            continue;
        };
        if !matches!(tcx.def_kind(parent), DefKind::Impl { of_trait: true }) {
            continue;
        }
        let impl_trait_ref = tcx.impl_trait_ref(parent);
        let trait_ref = impl_trait_ref.skip_binder();

        // Construct the qualified name: <SelfType as Trait>::CONST
        let const_name = tcx.item_name(def_id).as_str().to_string();
        let self_ty = trait_ref.self_ty();
        let self_name = format!("{self_ty}");

        let body_expr = source_assoc_const_body_expr(tcx, local_def_id).or_else(|| {
            tcx.iter_local_def_id()
                .filter_map(|child_local_def_id| {
                    let child_def_id = child_local_def_id.to_def_id();
                    (tcx.opt_parent(child_def_id) == Some(def_id)
                        && matches!(
                            tcx.def_kind(child_def_id),
                            DefKind::AnonConst | DefKind::InlineConst
                        ))
                    .then_some(child_def_id)
                })
                .find_map(|child_def_id| {
                    let const_operand = identity_const_operand(tcx, child_def_id);
                    translate_unevaluated_const_symbolic_impl(
                        tcx,
                        &const_operand,
                        child_def_id,
                        None,
                    )
                })
                .or_else(|| {
                    let const_operand = identity_const_operand(tcx, def_id);
                    translate_unevaluated_const_symbolic_impl(tcx, &const_operand, def_id, None)
                })
        });

        if let Some(body_expr) = body_expr {
            for qualified_name in
                qualified_assoc_const_aliases(tcx, &self_name, trait_ref.def_id, &const_name)
            {
                map.insert(qualified_name, body_expr.clone());
            }
        }
    }

    map
}

fn qualified_assoc_const_aliases<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_name: &str,
    trait_def_id: DefId,
    assoc_name: &str,
) -> Vec<String> {
    let mut aliases = Vec::new();
    let bare_trait_name = tcx.item_name(trait_def_id).as_str().to_string();
    let trait_path = tcx.def_path_str(trait_def_id);

    push_qualified_assoc_const_alias(&mut aliases, self_name, &bare_trait_name, assoc_name);
    push_qualified_assoc_const_alias(&mut aliases, self_name, &trait_path, assoc_name);

    if trait_def_id.krate == LOCAL_CRATE
        && trait_path.contains("::")
        && !trait_path.starts_with("crate::")
    {
        push_qualified_assoc_const_alias(
            &mut aliases,
            self_name,
            &format!("crate::{trait_path}"),
            assoc_name,
        );
    }

    if trait_path.contains("::") && !trait_path.starts_with("::") {
        let crate_name = tcx.crate_name(trait_def_id.krate);
        push_qualified_assoc_const_alias(
            &mut aliases,
            self_name,
            &format!("::{crate_name}::{trait_path}"),
            assoc_name,
        );
    }

    aliases
}

fn push_qualified_assoc_const_alias(
    aliases: &mut Vec<String>,
    self_name: &str,
    trait_path: &str,
    assoc_name: &str,
) {
    let alias = format!("<{self_name} as {trait_path}>::{assoc_name}");
    if !aliases.contains(&alias) {
        aliases.push(alias);
    }
}

fn identity_const_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> rustc_middle::mir::ConstOperand<'tcx> {
    use rustc_middle::mir::{Const as MirConst, ConstOperand, UnevaluatedConst};

    ConstOperand {
        span: rustc_span::DUMMY_SP,
        user_ty: None,
        const_: MirConst::Unevaluated(
            UnevaluatedConst {
                def: def_id,
                args: rustc_middle::ty::GenericArgs::identity_for_item(tcx, def_id),
                promoted: None,
            },
            tcx.type_of(def_id).instantiate_identity().skip_norm_wip(),
        ),
    }
}

fn source_assoc_const_body_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_def_id: rustc_hir::def_id::LocalDefId,
) -> Option<PureExpr> {
    let body_id = match tcx.hir_node_by_def_id(local_def_id) {
        Node::ImplItem(item) => match item.kind {
            ImplItemKind::Const(_, ConstItemRhs::Body(body_id)) => body_id,
            _ => return None,
        },
        Node::TraitItem(item) => match item.kind {
            TraitItemKind::Const(_, Some(ConstItemRhs::Body(body_id))) => body_id,
            _ => return None,
        },
        _ => return None,
    };
    let body = tcx.hir_body(body_id);
    let snippet = tcx
        .sess
        .source_map()
        .span_to_snippet(body.value.span)
        .ok()?;
    let expr_source = strip_const_block_wrapper(&snippet).unwrap_or(snippet.trim());
    parse_contract_body(expr_source).ok()
}

fn strip_const_block_wrapper(snippet: &str) -> Option<&str> {
    let trimmed = snippet.trim();
    let after_const = trimmed.strip_prefix("const")?.trim_start();
    let after_open = after_const.strip_prefix('{')?.trim_start();
    let inner = after_open.strip_suffix('}')?.trim_end();
    Some(inner.trim())
}

fn translate_const_body_return_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    diagnostics: Option<&ExtractionDiagnosticSink>,
) -> Option<PureExpr> {
    let empty_locals: HashMap<Local, PureExpr> = HashMap::new();
    body.basic_blocks
        .iter()
        .find(|bb_data| matches!(bb_data.terminator().kind, TerminatorKind::Return))
        .and_then(|bb_data| {
            bb_data.statements.iter().rev().find_map(|stmt| {
                let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                    return None;
                };
                (place.local == rustc_middle::mir::RETURN_PLACE).then_some(rvalue)
            })
        })
        .and_then(|rvalue| {
            translate_rvalue_with_enum_variants(
                tcx,
                rvalue,
                &empty_locals,
                Some(body),
                diagnostics,
                None,
            )
        })
}

#[cfg(test)]
mod tests {
    use super::bare_assoc_const_aliases;

    #[test]
    fn bare_assoc_const_aliases_keeps_canonical_only_when_no_generics() {
        // Concrete impls produce `S::C` — no `<...>` to strip.
        let aliases = bare_assoc_const_aliases("S::C", "C");
        assert_eq!(aliases, vec!["S::C".to_string()]);
    }

    #[test]
    fn bare_assoc_const_aliases_strips_generic_args_for_short_form() {
        // Body extractor's canonical form is `S<T>::C` for generic impls;
        // contracts typically write `S::C`. Both aliases must be present.
        let aliases = bare_assoc_const_aliases("S<T>::C", "C");
        assert_eq!(aliases, vec!["S<T>::C".to_string(), "S::C".to_string()]);
    }

    #[test]
    fn bare_assoc_const_aliases_skips_qualified_self_forms() {
        // `<S<T> as F>::C` is not in `T<...>::C` shape, so only the canonical
        // form should be returned.
        let aliases = bare_assoc_const_aliases("<S<T> as F>::C", "C");
        assert_eq!(aliases, vec!["<S<T> as F>::C".to_string()]);
    }

    #[test]
    fn bare_assoc_const_aliases_handles_multi_arg_generics() {
        let aliases = bare_assoc_const_aliases("Pair<T, U>::C", "C");
        assert_eq!(
            aliases,
            vec!["Pair<T, U>::C".to_string(), "Pair::C".to_string()]
        );
    }
}
