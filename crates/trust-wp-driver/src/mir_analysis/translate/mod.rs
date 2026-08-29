// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR-to-PureExpr translation helpers.
//!
//! Translates MIR rvalues, operands, places, and constants into
//! `PureExpr` representations for verification condition generation.

use std::collections::HashMap;

use rustc_middle::mir::{Local, Location};
use trust_wp_core::formula::PureExpr;

use super::{
    diagnostics::{record_extraction_diag, ExtractionDiagKind, ExtractionDiagnosticSink},
    spanned::SpannedBodyExpr,
};

mod binop;
mod constant;
mod discriminant;
mod float;
mod operand;
mod place;
mod rvalue;
mod ty_sort;

#[cfg(test)]
pub(crate) use binop::{translate_binop, translate_unop};
#[cfg(test)]
pub(crate) use constant::translate_constant;
pub(crate) use constant::{resolve_const_item_value, translate_constant_with_tcx};
pub(crate) use discriminant::{
    operand_int_ty, switch_value_to_expr, switch_value_to_i64, DiscrIntTy,
};
pub(crate) use operand::{
    operand_is_bool, translate_operand, translate_operand_detailed, translate_operand_with_tcx,
};
#[cfg(test)]
pub(crate) use place::allows_field0_identity_fallback;
pub(crate) use place::{translate_place, translate_typed_field_place};
#[cfg(test)]
use rvalue::translate_generic_reborrow;
pub(crate) use rvalue::{translate_rvalue, translate_rvalue_detailed, translate_rvalue_typed};
pub(crate) use ty_sort::{ty_to_expr_sort, ty_to_expr_sort_enriched};

/// Lightweight context for recording translation-layer diagnostics.
///
/// Passed through the detailed translation helpers so that each None-return
/// site can explain *why* it failed, rather than requiring the caller to guess.
pub(crate) struct TranslationDiagContext<'a> {
    pub(crate) sink: Option<&'a ExtractionDiagnosticSink>,
    pub(crate) module: &'static str,
    pub(crate) location: Option<Location>,
}

pub(super) fn record_translation_gap(
    diag: Option<&TranslationDiagContext<'_>>,
    detail: impl Into<String>,
) {
    if let Some(ctx) = diag {
        record_extraction_diag(
            ctx.sink,
            ctx.module,
            ExtractionDiagKind::FeatureGap,
            detail,
            ctx.location,
        );
    }
}

// =============================================================================
// Expression Lookup Trait (L9 fix: avoid O(S*L) expr_map cloning)
// =============================================================================

/// Trait for looking up `PureExpr` values by `Local` key.
///
/// Both `HashMap<Local, PureExpr>` and `HashMap<Local, SpannedBodyExpr>` implement
/// this trait, so `translate_rvalue`/`translate_operand`/`translate_place` can work
/// with either map type without allocating a full converted copy.
///
/// The optional `get_deref_expr` and `get_field_deref_expr` methods support
/// deref-aware translation for mutable borrow analysis. Default implementations
/// return `None`, preserving existing behavior for non-deref callers.
#[allow(clippy::trivially_copy_pass_by_ref)] // &Local matches HashMap::get() signature
pub(crate) trait ExprLookup {
    fn get_expr(&self, local: &Local) -> Option<&PureExpr>;

    /// Look up a tracked whole-deref expression for `*local`.
    fn get_deref_expr(&self, _local: &Local) -> Option<&PureExpr> {
        None
    }

    /// Look up a tracked field-deref expression for `(*local).field`.
    fn get_field_deref_expr(&self, _local: &Local, _field: u32) -> Option<&PureExpr> {
        None
    }

    /// Whether `translate_place` should apply rich field projection logic
    /// (tuple constructors, closure captures, Var-base struct accessors).
    ///
    /// Returns `true` by default (VC extraction needs full projection).
    /// Deref-aware lookups (mutable borrow analysis) return `false` to match
    /// the simpler field-0-identity-only fallback behavior.
    fn rich_field_projections(&self) -> bool {
        true
    }
}

impl ExprLookup for HashMap<Local, PureExpr> {
    fn get_expr(&self, local: &Local) -> Option<&PureExpr> {
        self.get(local)
    }
}

impl ExprLookup for HashMap<Local, SpannedBodyExpr> {
    fn get_expr(&self, local: &Local) -> Option<&PureExpr> {
        self.get(local).map(|s| &s.expr)
    }
}

#[cfg(test)]
#[allow(unused_imports)] // Re-exports for test convenience via `use super::*;`
mod test_reexports {
    pub(super) use rustc_middle::{
        mir::{BinOp as MirBinOp, Body, Operand, Place, ProjectionElem, Rvalue, UnOp as MirUnOp},
        ty::{IntTy, TyKind, UintTy},
    };
    pub(super) use trust_wp_core::formula::{
        intern_sort_name,
        internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
        BinOp, ExprSort, UnOp,
    };

    pub(super) use super::{
        binop::{int_ty_bits, uint_ty_bits},
        float::concrete_float_expr_f64,
        place::{
            project_closure_capture_field, project_const_index, project_nested_tuple_get_field,
            project_tuple_field, simplify_tuple_get_from_constructor,
        },
    };
}
#[cfg(test)]
#[allow(unused_imports)]
use test_reexports::*;

#[cfg(test)]
mod tests;
