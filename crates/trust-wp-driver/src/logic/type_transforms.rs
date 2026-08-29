// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type-directed post-processing for logic function definitions.
//!
//! This module handles:
//! - **Newtype view simplification**: Collapsing `View(tuple_get_0(self))` to
//!   `Var(self)` for newtype types where field access is identity (#359).
//! - **Unit field constraints**: Generating `field(param) == tuple0()` equality
//!   constraints for `()` fields (#1271).
//! - **Type invariant extraction**: Identifying `impl Invariant for T` methods
//!   and converting them to [`TypeInvariantDef`] (#359, #645).

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{TyCtxt, TyKind};
use trust_wp_core::{
    formula::{PureExpr, PureExprChildRole},
    logic::TypeInvariantDef,
};

use super::discovery::{find_logic_functions, LogicFunction};
use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

// ---------------------------------------------------------------------------
// Newtype view simplification
// ---------------------------------------------------------------------------

/// Return logic-function parameter names whose concrete Rust types are
/// newtype-invariant ADTs.
pub(super) fn newtype_param_names_for_logic_fn(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    param_names: &[String],
    newtype_type_names: &HashSet<String>,
) -> HashSet<String> {
    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();

    // `tcx.def_path_str()` returns local paths (e.g., "NonZeroU32") without
    // the crate prefix. `newtype_type_names` may contain crate-qualified
    // names (e.g., "creusot_test::NonZeroU32") from `extract_invariant_type_name`.
    // Check both forms so the lookup succeeds regardless of qualification (#2341).
    let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);

    let mut newtype_params = HashSet::new();
    for (idx, ty) in inputs.iter().enumerate() {
        if idx >= param_names.len() {
            break;
        }

        let inner_ty = match ty.kind() {
            TyKind::Ref(_, inner, _) => *inner,
            _ => *ty,
        };
        if let TyKind::Adt(adt_def, _) = inner_ty.kind() {
            let type_name = tcx.def_path_str(adt_def.did());
            let qualified_type_name = format!("{crate_name}::{type_name}");
            if newtype_type_names.contains(&type_name)
                || newtype_type_names.contains(&qualified_type_name)
            {
                newtype_params.insert(param_names[idx].clone());
            }
        }
    }

    newtype_params
}

pub(super) fn simplify_newtype_view_in_expr_for_params(
    mut expr: PureExpr,
    newtype_params: &HashSet<String>,
) -> PureExpr {
    let mut params: Vec<&str> = newtype_params.iter().map(String::as_str).collect();
    params.sort_unstable();
    for param in params {
        expr = simplify_newtype_view_in_body(expr, param);
    }
    expr
}

/// Check if an expression tree contains any tuple field access with index > 0.
///
/// Used in test-only legacy invariant extraction to distinguish single-field
/// newtypes from multi-field tuple structs. (#359)
#[cfg(test)]
fn has_higher_tuple_field_access(expr: &PureExpr) -> bool {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_index;

    expr.any_recursive(|node| {
        matches!(node, PureExpr::LogicFnCall { name, .. }
            if tuple_field_logic_fn_index(name).map_or(false, |i| i > 0))
    })
}

/// Simplify `View(tuple_get_0(Var(self_param)))` → `Var(self_param)` in an expression tree.
///
/// For newtype invariants (e.g., `NonZeroU32(u32)` with `self.0@ > 0`), the `.0` field
/// access is identity (single-field struct) and `@` on integers is identity, so the
/// combined `self.0@` expression can be collapsed to just `self`.
///
/// This simplification also collapses bare `tuple_get_0(self)` without View, since
/// for newtypes the field extraction is always identity regardless of View. (#359)
#[allow(clippy::needless_pass_by_value)] // PureExpr by-value is idiomatic for rewrite chains
fn simplify_newtype_view_in_body(expr: PureExpr, self_param: &str) -> PureExpr {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_index;

    fn is_newtype_field_zero_view(expr: &PureExpr, self_param: &str) -> bool {
        match expr {
            PureExpr::View(inner) => matches!(
                inner.as_ref(),
                PureExpr::LogicFnCall { name, args }
                    if tuple_field_logic_fn_index(name) == Some(0)
                        && args.len() == 1
                        && matches!(&args[0], PureExpr::Var(v, _) if v == self_param)
            ),
            _ => false,
        }
    }

    expr.rewrite_bottom_up_with_context(
        false,
        |_, role, _| role == PureExprChildRole::MethodReceiver,
        |node, is_method_receiver| {
            if !*is_method_receiver && is_newtype_field_zero_view(&node, self_param) {
                PureExpr::Var(self_param.to_string(), None)
            } else {
                node
            }
        },
    )
}

/// Return the single-field newtype field sort if it is Int-viewable
/// (Int or Bool), so the type invariant axiom and the `self` quantifier
/// can be declared with a scalar sort consistent with the body rewrite
/// performed by `simplify_newtype_view_in_body`.
///
/// Returns `None` for non-newtype types, types whose field sort cannot be
/// resolved, or types whose field is itself a Datatype/MutRef/etc — those
/// must keep the original `param_sort` so the encoder retains the carrier
/// sort. (#5, spans::quux)
fn newtype_field_int_viewable_sort<'tcx>(
    tcx: TyCtxt<'tcx>,
    inner_ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<trust_wp_core::formula::ExprSort> {
    use trust_wp_core::formula::ExprSort;

    let TyKind::Adt(adt_def, substs) = inner_ty.kind() else {
        return None;
    };
    if !adt_def.is_struct() {
        return None;
    }
    let variant = adt_def.non_enum_variant();
    if variant.fields.len() != 1 {
        return None;
    }
    let field = variant.fields.iter().next()?;
    let field_ty = field.ty(tcx, substs).skip_norm_wip();
    let field_sort = ty_to_expr_sort_enriched(tcx, field_ty)?;
    // Only override when the field sort is itself Int-viewable. For
    // Datatype/MutRef/Ref/Seq/Tuple fields, retain the user-provided
    // param_sort so the encoder keeps the carrier sort.
    match field_sort {
        ExprSort::Int | ExprSort::Bool => Some(field_sort),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Unit field constraints
// ---------------------------------------------------------------------------

/// Generate unit field equality constraints for logic function parameters.
///
/// When a logic function parameter has an ADT type with unit-typed (`()`) fields,
/// the SMT encoding needs explicit constraints because named field accessors
/// (`__trust_wp_field_X`) are uninterpreted functions returning `Int`. Without
/// constraints, the solver cannot prove `field(param) == tuple0()` even though
/// the Rust type system guarantees it.
///
/// For each parameter `p` of type `S` where `S` has a field `f: ()`, this
/// generates `__trust_wp_field_f(p) == __trust_wp_tuple0()` as a precondition.
///
/// Reference: Issue #1271.
pub(super) fn unit_field_constraints_for_logic_fn(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    param_names: &[String],
) -> Vec<PureExpr> {
    use trust_wp_core::formula::{
        internal::tuple_lowering::{tuple_logic_fn_name, NAMED_FIELD_LOGIC_FN_PREFIX},
        BinOp,
    };

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();

    let mut constraints = Vec::new();
    for (idx, ty) in inputs.iter().enumerate() {
        if idx >= param_names.len() {
            break;
        }

        // Peel through references to get the underlying type
        let inner_ty = match ty.kind() {
            TyKind::Ref(_, inner, _) => *inner,
            _ => *ty,
        };

        // Only process ADT types (structs, enums)
        let TyKind::Adt(adt_def, substs) = inner_ty.kind() else {
            continue;
        };

        // Only process structs with a single variant (not enums)
        if !adt_def.is_struct() {
            continue;
        }

        let variant = adt_def.non_enum_variant();
        for field in &variant.fields {
            let field_ty = field.ty(tcx, substs).skip_norm_wip();
            // Check if the field type is unit `()`
            if !field_ty.is_unit() {
                continue;
            }

            let field_name = field.name.to_string();
            let param_name = &param_names[idx];

            // Build: __trust_wp_field_<name>(param) == __trust_wp_tuple0()
            let param_sort = ty_to_expr_sort_enriched(tcx, *ty);
            let field_access = PureExpr::LogicFnCall {
                name: format!("{NAMED_FIELD_LOGIC_FN_PREFIX}{field_name}"),
                args: vec![PureExpr::Var(param_name.clone(), param_sort)],
            };
            let tuple0 = PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(0),
                args: vec![],
            };
            let eq = PureExpr::BinOp(Arc::new(field_access), BinOp::Eq, Arc::new(tuple0));
            constraints.push(eq);
        }
    }

    constraints
}

// ---------------------------------------------------------------------------
// Type invariant extraction
// ---------------------------------------------------------------------------

/// Check if a logic function is an `impl Invariant for T` invariant method.
///
/// Matches full paths like `<Sum10 as creusot_std::Invariant>::invariant` or
/// `<NonZeroU32 as trust_wp_std::Invariant>::invariant`.
fn is_invariant_impl(logic_fn: &LogicFunction) -> bool {
    logic_fn.name == "invariant" && logic_fn.full_path.contains("Invariant>::invariant")
}

/// Convert a logic function from an `impl Invariant for T` block into a
/// [`TypeInvariantDef`] for SMT axiom registration (#359, #645).
///
/// The logic function's body becomes the invariant body, and its first
/// parameter (self) determines the SMT sort of the universally quantified
/// variable in the defining axiom.
fn parse_type_invariant_def_parts(
    logic_fn: &LogicFunction,
) -> Option<(
    String,
    String,
    Option<trust_wp_core::formula::ExprSort>,
    PureExpr,
)> {
    use trust_wp_core::contract_parser::parse_contract;

    let body_text = logic_fn.body_text.as_ref()?;
    let body = match parse_contract(body_text) {
        Ok(body) => body,
        Err(e) => {
            crate::result_protocol_state::record_parse_error();
            eprintln!(
                "trust-wp: error: failed to parse type invariant body for {}: {}",
                logic_fn.full_path, e
            );
            return None;
        }
    };

    let self_param = logic_fn
        .params
        .first()
        .cloned()
        .unwrap_or_else(|| "self".to_string());

    let param_sort = logic_fn.param_sort_hints.first().cloned().flatten();

    let type_name = extract_invariant_type_name(&logic_fn.full_path);

    Some((type_name, self_param, param_sort, body))
}

#[cfg(test)]
fn to_type_invariant_def(logic_fn: &LogicFunction) -> Option<TypeInvariantDef> {
    let (type_name, self_param, param_sort, body) = parse_type_invariant_def_parts(logic_fn)?;

    // Simplify newtype field access patterns in the invariant body for
    // single-field structs. The MIR-level single-field ADT aggregate collapse
    // (rvalue.rs: `Self(n)` → `n`) produces scalar return expressions, so the
    // invariant must also operate on scalars to avoid a sort mismatch between
    // the Datatype postcondition and the Int result_expr. (#2669)
    //
    // For this legacy path we keep the old heuristic so the existing unit
    // tests continue to document the body rewrite behavior in isolation.
    let is_newtype = !has_higher_tuple_field_access(&body);
    let body = if is_newtype {
        simplify_newtype_view_in_body(body, &self_param)
    } else {
        body
    };

    Some(trust_wp_core::type_invariant_def! {
        type_name: type_name,
        self_param: self_param,
        param_sort: param_sort,
        body: body,
        is_newtype: is_newtype,
        element_invariant_method: None,
    })
}

fn to_type_invariant_def_with_self_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_ty: rustc_middle::ty::Ty<'tcx>,
    logic_fn: &LogicFunction,
) -> Option<TypeInvariantDef> {
    let (type_name, self_param, param_sort, body) = parse_type_invariant_def_parts(logic_fn)?;

    let inner_ty = match self_ty.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => self_ty,
    };
    let is_single_field_adt = matches!(
        inner_ty.kind(),
        TyKind::Adt(adt_def, _) if adt_def.is_struct() && adt_def.non_enum_variant().fields.len() == 1
    );

    if is_single_field_adt {
        let body = simplify_newtype_view_in_body(body, &self_param);
        // For newtypes whose single field is Int-viewable (Int/Bool), the body
        // has been simplified so the self parameter refers to the underlying
        // scalar — not the Datatype carrier. The param_sort hint from the
        // user's `invariant(self)` method signature still carries
        // `Datatype(NonNeg)`, which would cause the encoder to declare the
        // quantifier `self` (and any downstream view variable bridged to it)
        // with `Sort::Uninterpreted("Tuple1")` / `Sort::Datatype(NonNeg)`
        // instead of `Sort::Int`. Override with the field's Int-viewable
        // sort so #[variant]/mut-borrow obligations using `i.0@` get a
        // proper Int decrease comparison rather than an opaque
        // uninterpreted relation. (#5, spans::quux, result/own::as_mut)
        let newtype_param_sort = newtype_field_int_viewable_sort(tcx, inner_ty)
            .map(Some)
            .unwrap_or(param_sort);
        return Some(trust_wp_core::type_invariant_def! {
            type_name: type_name,
            self_param: self_param,
            param_sort: newtype_param_sort,
            body: body,
            is_newtype: true,
            element_invariant_method: None,
        });
    }

    let enriched_sort = ty_to_expr_sort_enriched(tcx, inner_ty);
    let inferred_sort = enriched_sort.clone().unwrap_or_else(|| {
        trust_wp_core::formula::ExprSort::Datatype(trust_wp_core::formula::intern_sort_name(
            &type_name,
        ))
    });

    // Multi-field struct tuple-lowering alignment (partially_opaque #1):
    // Multi-field structs that are NOT carried by a native ADT datatype are
    // lowered to `Tuple<N>` at the call site, so the invariant `self` must use
    // the matching `Tuple<N>` sort. But when the struct DOES have a native
    // `Datatype` carrier (the common case — `ty_to_expr_sort_enriched` returns
    // `Datatype(..)`), the call-site final-value carrier is that datatype (e.g.
    // `S(34, 0)`), and overriding `self` to `Tuple<N>` desyncs the invariant
    // axiom's `self` sort from the carrier. That break leaves the invariant
    // UF/inline applied to a fresh `Tuple<N>` value disconnected from the field
    // writes tracked on the `S`-sorted carrier — a spurious `&mut` postcondition
    // failure. Only apply the Tuple override when there is NO native datatype
    // carrier; otherwise keep the native `Datatype` sort so `self` connects to
    // the carrier and `tuple_get_i(self)` resolves to the native field selector. (#2683)
    let has_native_datatype_carrier = matches!(
        enriched_sort,
        Some(trust_wp_core::formula::ExprSort::Datatype(_))
    );
    let tuple_param_sort = if has_native_datatype_carrier {
        None
    } else {
        match inner_ty.kind() {
            TyKind::Adt(adt_def, _)
                if adt_def.is_struct() && adt_def.non_enum_variant().fields.len() > 1 =>
            {
                u8::try_from(adt_def.non_enum_variant().fields.len())
                    .ok()
                    .map(trust_wp_core::formula::ExprSort::Tuple)
            }
            _ => None,
        }
    };

    Some(trust_wp_core::type_invariant_def! {
        type_name: type_name,
        self_param: self_param,
        param_sort: tuple_param_sort.or(param_sort).or(Some(inferred_sort)),
        body: body,
        is_newtype: false,
        element_invariant_method: None,
    })
}

/// Extract the type path from a `<T as Trait>::method` path.
///
/// Given `<Counter as Invariant>::invariant`, returns `"Counter"`.
/// Given `<my_crate::Counter as creusot_std::Invariant>::invariant`,
/// returns `"my_crate::Counter"`.
/// Given `<Bounded<i32> as Invariant>::invariant`, returns `"Bounded"`.
/// Given `creusot_test::<SumTo10 as creusot_std::Invariant>::invariant`,
/// returns `"creusot_test::SumTo10"` (#1370).
///
/// Generic parameters are stripped because `tcx.def_path_str()` on the
/// lookup side omits them — keeping them would cause a name mismatch (#686).
/// Falls back to the full path segment if parsing fails.
fn extract_invariant_type_name(full_path: &str) -> String {
    // Pattern: [crate_prefix::]<TypePath as TraitPath>::method
    // The `<` may appear at position 0 or after a crate prefix like `creusot_test::`.
    if let Some(lt_pos) = full_path.find('<') {
        let after_lt = &full_path[lt_pos + 1..];
        if let Some(type_path) = after_lt.split(" as ").next() {
            // Strip generic parameters to match def_path_str output (#686).
            // "Bounded<i32>" → "Bounded", "my_crate::Pair<A, B>" → "my_crate::Pair"
            let base = strip_generic_params(type_path);
            // If there's a crate prefix before `<` (e.g., "creusot_test::"), and the type
            // inside `<>` is unqualified (no `::` separator), combine them to get the
            // fully-qualified type path that matches `tcx.def_path_str()` output (#1370).
            let prefix = &full_path[..lt_pos];
            let result = if !prefix.is_empty() && !base.contains("::") {
                format!("{prefix}{base}")
            } else {
                base.to_string()
            };
            return result;
        }
    }
    // Fallback: use the full path
    full_path.to_string()
}

/// Strip generic type parameters from a type path.
///
/// Handles nested generics by tracking angle bracket depth.
/// `"Bounded<i32>"` → `"Bounded"`, `"A<B<C>>"` → `"A"`,
/// `"my_crate::Pair<A, B>"` → `"my_crate::Pair"`.
fn strip_generic_params(type_path: &str) -> &str {
    match type_path.find('<') {
        Some(pos) => &type_path[..pos],
        None => type_path,
    }
}

/// Extract type invariant definitions from logic functions in the crate (#359).
///
/// Identifies `impl Invariant for T` methods among the `#[logic]` functions
/// and converts them to [`TypeInvariantDef`] for the encoder's body axiom
/// registration.
pub(crate) fn extract_type_invariant_defs(tcx: TyCtxt<'_>) -> Vec<TypeInvariantDef> {
    let mut def_ids_by_path: HashMap<String, DefId> = HashMap::new();
    let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if matches!(
            tcx.def_kind(def_id),
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
        ) {
            let local_path = tcx.def_path_str(def_id);
            def_ids_by_path.insert(format!("{crate_name}::{local_path}"), def_id);
        }
    }

    find_logic_functions(tcx)
        .iter()
        .filter(|f| is_invariant_impl(f))
        .filter_map(|logic_fn| {
            let def_id = def_ids_by_path.get(&logic_fn.full_path).copied()?;
            let sig = tcx.fn_sig(def_id).instantiate_identity();
            let sig = sig.skip_binder();
            let self_ty = sig.inputs().first().copied()?;
            to_type_invariant_def_with_self_ty(tcx, self_ty, logic_fn)
        })
        .collect()
}

#[cfg(test)]
#[path = "type_transforms_tests.rs"]
mod tests;
