// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    Node, TraitFn, TraitItemKind,
};
use rustc_middle::{
    mir::{Body, Local, VarDebugInfoContents},
    ty::TyCtxt,
};
use trust_wp_core::formula::PureExpr;

use crate::mir_analysis::{name_unnamed_params, type_contains_mut_ref_with_tcx};

pub(super) fn collect_mut_ref_arg_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
) -> HashSet<String> {
    let mut names = HashSet::new();
    for (idx, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(idx + 1);
        if let Some(local_decl) = body.local_decls.get(local) {
            if type_contains_mut_ref_with_tcx(tcx, local_decl.ty) {
                names.insert(name.clone());
            }
        }
    }
    names
}

/// Build argument names for MIR extraction.
///
/// Closures have an implicit environment argument in MIR local `_1` that is
/// not present in HIR parameter lists. We model it as `self` so closure body
/// extraction aligns with projection symbols like `self.0` (captured fields).
pub(super) fn get_arg_names_for_mir_extraction(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    local_def_id: LocalDefId,
) -> Vec<String> {
    let mut names = get_arg_names_from_hir(tcx, local_def_id);
    if tcx.def_kind(def_id) == DefKind::Closure {
        names.insert(0, "self".to_string());
    }
    names
}

/// Result of building closure capture substitutions.
///
/// For Rust 2021 minimal captures, a closure may capture individual fields
/// (e.g., `p.1`) instead of whole variables. When that happens, the bare
/// `Var("p")` substitution is wrong because `self.N` already IS `p.1`, and
/// applying `__trust_wp_tuple_get_1(self.N)` yields a double field access.
///
/// This struct separates whole-variable substitutions from projected captures
/// so the caller can apply a collapse pass for the projected case. (#2554)
pub(super) struct CaptureSubstitutionResult {
    /// Standard `Var(name) → Var("self.N")` substitutions for whole-variable captures.
    pub substitutions: HashMap<String, PureExpr>,
    /// Projected field captures: `(source_var, field_idx, "self.N")`.
    /// These need a collapse pass on `LogicFnCall("__trust_wp_tuple_get_N", [Var(source)])`
    /// instead of a bare variable substitution.
    pub projected_captures: Vec<(String, usize, String)>,
}

/// Build substitutions for closure captures.
///
/// Captured variables are lowered in MIR as fields on the closure environment
/// (e.g., `(*_1).0`). We substitute capture names in contracts to synthetic
/// field vars (`self.<idx>`) so contracts and extracted body expressions share
/// the same symbols.
///
/// For projected captures (Rust 2021 minimal capture of `p.N`), the bare
/// variable substitution is skipped and the caller must run
/// `collapse_projected_field_captures` after the regular substitution. (#2554)
pub(super) fn closure_capture_substitutions(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
) -> CaptureSubstitutionResult {
    if tcx.def_kind(local_def_id.to_def_id()) != DefKind::Closure {
        return CaptureSubstitutionResult {
            substitutions: HashMap::new(),
            projected_captures: Vec::new(),
        };
    }

    let mut substitutions = HashMap::new();
    let mut projected_captures = Vec::new();
    // Track source variables that have projected captures so we don't
    // add a conflicting bare substitution from saved debug names.
    let mut projected_source_vars = HashSet::new();

    for (idx, capture) in tcx.closure_captures(local_def_id).iter().enumerate() {
        let capture_var = format!("self.{idx}");
        let field_var = PureExpr::Var(capture_var.clone(), None);
        let source_var = capture.var_ident.as_str().to_string();
        let symbol_name = capture.to_symbol().to_string();

        // Detect projected captures: to_symbol() includes the field suffix
        // with double underscores (e.g., "_ref__p__1" for &mut capture of p.1),
        // while var_ident is the bare name ("p"). If the symbol matches
        // the `{var}__{N}` pattern, this is a projected field capture.
        if let Some(field_idx) = detect_field_projection(&source_var, &symbol_name) {
            projected_captures.push((source_var.clone(), field_idx, capture_var));
            projected_source_vars.insert(source_var);
        } else {
            // The body names the capture as the parent's binding is named
            // (D-237); a clause names it by its source name.
            let debug_name = crate::mir_analysis::binding_identity::hir_binding_debug_name(
                tcx,
                &source_var,
                capture.get_root_variable(),
            );
            if debug_name != source_var {
                substitutions.insert(debug_name, field_var.clone());
            }
            // The name the closure's clauses read this capture by once
            // discovery renamed it (D-238): any capture of a name the
            // function binds more than once, a parameter's too (D-239).
            if crate::mir_analysis::binding_identity::capture_read_apart(
                tcx,
                &source_var,
                capture.get_root_variable(),
            ) {
                substitutions.insert(
                    crate::mir_analysis::binding_identity::capture_clause_name(
                        &source_var,
                        capture.get_root_variable(),
                    ),
                    field_var.clone(),
                );
            }
            substitutions.insert(source_var, field_var.clone());
            if symbol_name != capture.var_ident.as_str() {
                substitutions.insert(symbol_name, field_var);
            }
        }
    }

    // Also include saved debug names used by rustc for captured fields,
    // but skip names for variables that have projected captures.
    for (idx, symbol) in tcx
        .closure_saved_names_of_captured_variables(local_def_id.to_def_id())
        .iter()
        .enumerate()
    {
        let name = symbol.as_str().to_string();
        if !projected_source_vars.contains(&name) {
            substitutions
                .entry(name)
                .or_insert_with(|| PureExpr::Var(format!("self.{idx}"), None));
        }
    }

    CaptureSubstitutionResult {
        substitutions,
        projected_captures,
    }
}

/// Each whole-variable capture of the closure `local_def_id` under every name
/// its contracts read it by, as `(capture index, name)`: the table
/// [`closure_capture_substitutions`] rewrites the closure's own clauses with,
/// so a call that binds a capture by these names owes the clause the
/// closure's body is verified under. A projected capture (`p.1`) is not in it.
pub(crate) fn closure_capture_index_names(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
) -> Vec<(usize, String)> {
    // A capture of a binding the function binds more than once is read by
    // the closure's clauses under its own name only (D-238, D-239). At a call
    // its source name is the CALLER's: a parameter that keeps it (of the
    // function, or of a calling closure), which an argument may name, and
    // which must not be read as the capture.
    let renamed_sources: HashSet<String> =
        if tcx.def_kind(local_def_id.to_def_id()) == DefKind::Closure {
            tcx.closure_captures(local_def_id)
                .iter()
                .filter(|capture| {
                    crate::mir_analysis::binding_identity::capture_read_apart(
                        tcx,
                        capture.var_ident.as_str(),
                        capture.get_root_variable(),
                    )
                })
                .map(|capture| capture.var_ident.as_str().to_string())
                .collect()
        } else {
            HashSet::new()
        };
    let mut bindings: Vec<(usize, String)> = closure_capture_substitutions(tcx, local_def_id)
        .substitutions
        .into_iter()
        .filter(|(name, _)| !renamed_sources.contains(name))
        .filter_map(|(name, field)| match field {
            PureExpr::Var(field_name, _) => field_name
                .strip_prefix("self.")
                .and_then(|idx| idx.parse::<usize>().ok())
                .map(|idx| (idx, name)),
            _ => None,
        })
        .collect();
    bindings.sort();
    bindings
}

/// Detect if a capture is a projected field capture by comparing the source
/// variable name against the symbol name.
///
/// For `p.1` captured by `&mut`, rustc produces:
/// - `var_ident = "p"`, `to_symbol() = "_ref__p__1"` (double underscore, `_ref__` prefix)
/// - saved debug name: `"p__1"`
///
/// Returns `Some(field_index)` if the symbol represents a projected field access.
fn detect_field_projection(source_var: &str, symbol_name: &str) -> Option<usize> {
    // Strip the _ref__ prefix that rustc adds for &mut captures
    let stripped = symbol_name.strip_prefix("_ref__").unwrap_or(symbol_name);
    // Match pattern: {source_var}__{field_index} (double underscore separator)
    let field_suffix = stripped.strip_prefix(source_var)?.strip_prefix("__")?;
    field_suffix.parse::<usize>().ok()
}

/// Collapse `LogicFnCall("__trust_wp_tuple_get_N", [Var(source)])` to
/// `Var("self.M")` for projected closure captures (Rust 2021 minimal capture).
///
/// When a closure captures `p.1`, the capture `self.0` IS `p.1`. The contract
/// text `p.1` is parsed as `LogicFnCall("__trust_wp_tuple_get_1", [Var("p")])`.
/// Since `Var("p")` isn't substituted for projected captures, this function
/// matches the pattern and replaces it with `Var("self.0")`. (#2554)
pub(super) fn collapse_projected_field_captures(
    expr: &PureExpr,
    projections: &[(String, usize, String)],
) -> PureExpr {
    collapse_projected_impl(expr, projections)
}

fn collapse_projected_impl(expr: &PureExpr, projections: &[(String, usize, String)]) -> PureExpr {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            // Check for __trust_wp_tuple_get_N(Var(source)) pattern
            if let Some(field_idx) =
                trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_index(name)
            {
                if args.len() == 1 {
                    if let PureExpr::Var(source_var, _) = &args[0] {
                        for (src, idx, capture_var) in projections {
                            if src == source_var && *idx == field_idx {
                                return PureExpr::Var(capture_var.clone(), None);
                            }
                        }
                    }
                }
            }
            // Recurse into args
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|a| collapse_projected_impl(a, projections))
                .collect();
            PureExpr::LogicFnCall {
                name: name.clone(),
                args: new_args,
            }
        }
        PureExpr::BinOp(l, op, r) => {
            let new_l = collapse_projected_impl(l, projections);
            let new_r = collapse_projected_impl(r, projections);
            PureExpr::BinOp(std::sync::Arc::new(new_l), *op, std::sync::Arc::new(new_r))
        }
        PureExpr::UnOp(op, inner) => {
            let new_inner = collapse_projected_impl(inner, projections);
            PureExpr::UnOp(*op, std::sync::Arc::new(new_inner))
        }
        PureExpr::View(inner) => {
            let new_inner = collapse_projected_impl(inner, projections);
            PureExpr::View(std::sync::Arc::new(new_inner))
        }
        PureExpr::Deref(inner) => {
            let new_inner = collapse_projected_impl(inner, projections);
            PureExpr::Deref(std::sync::Arc::new(new_inner))
        }
        PureExpr::Final(inner) => {
            let new_inner = collapse_projected_impl(inner, projections);
            PureExpr::Final(std::sync::Arc::new(new_inner))
        }
        PureExpr::Old(inner) => {
            let new_inner = collapse_projected_impl(inner, projections);
            PureExpr::Old(std::sync::Arc::new(new_inner))
        }
        PureExpr::Ite(c, t, e) => {
            let new_c = collapse_projected_impl(c, projections);
            let new_t = collapse_projected_impl(t, projections);
            let new_e = collapse_projected_impl(e, projections);
            PureExpr::Ite(
                std::sync::Arc::new(new_c),
                std::sync::Arc::new(new_t),
                std::sync::Arc::new(new_e),
            )
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver = collapse_projected_impl(receiver, projections);
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|a| collapse_projected_impl(a, projections))
                .collect();
            PureExpr::MethodCall {
                receiver: std::sync::Arc::new(new_receiver),
                method: method.clone(),
                args: new_args,
            }
        }
        // Leaf nodes — no recursion needed
        PureExpr::Var(..) | PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => {
            expr.clone()
        }
        // Other composite nodes — delegate to the generic rewriter in
        // trust-wp-core's traversal module. For now, just clone since the
        // patterns we need to collapse (tuple_get on Var) don't appear
        // inside quantifiers, match, let, or closure bodies in practice.
        _ => expr.clone(),
    }
}

/// Get argument names from HIR or MIR for a DefId.
///
/// For local functions, extracts names from HIR (source code). For cross-crate
/// functions (e.g., trust-wp-std methods), falls back to MIR `var_debug_info` to
/// recover parameter names from compiled metadata. Without this fallback,
/// spec contracts for cross-crate methods (FSet, FMap, etc.) cannot bind
/// `self`/`arg1` to actual call-site arguments, making their ensures clauses
/// vacuous. (#2215)
pub(in crate::callbacks) fn get_arg_names_from_def_id(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> Option<Vec<String>> {
    // Local functions: use HIR (source-level parameter names).
    if let Some(local_def_id) = def_id.as_local() {
        let names = get_arg_names_from_hir(tcx, local_def_id);
        if !names.is_empty() {
            return Some(names);
        }

        // Trait method declarations often have no body (`TraitFn::Required`),
        // so body-based extraction returns no names. Pull names from the trait
        // signature in that case.
        if let Node::TraitItem(trait_item) = tcx.hir_node_by_def_id(local_def_id) {
            if let TraitItemKind::Fn(_, TraitFn::Required(param_names)) = trait_item.kind {
                let names = param_names
                    .iter()
                    .map(|ident| {
                        ident
                            .map(|ident| ident.as_str().to_string())
                            .filter(|name| !name.is_empty() && name != "_")
                    })
                    .collect();
                return Some(name_unnamed_params(names));
            }
        }

        // Zero-argument functions are valid; represent as empty arg list rather
        // than "name extraction failed".
        return Some(Vec::new());
    }

    // Cross-crate functions: extract parameter names from MIR debug info.
    // This enables spec contract binding for trust-wp-std methods (FSet, FMap,
    // Vec, etc.) that are compiled in a different crate. (#2215)
    get_arg_names_from_cross_crate_mir(tcx, def_id)
}

/// Get argument names from HIR (source code).
///
/// This extracts parameter names from the function's HIR signature without
/// needing to access MIR. A parameter with no source name gets its positional
/// name (`name_unnamed_params`).
fn get_arg_names_from_hir(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Vec<String> {
    let Some(hir_body_id) = tcx.hir_node_by_def_id(def_id).body_id() else {
        return Vec::new();
    };
    let names = tcx
        .hir_body(hir_body_id)
        .params
        .iter()
        .map(|param| match param.pat.kind {
            rustc_hir::PatKind::Binding(_, _, ident, _) => Some(ident.as_str().to_string()),
            _ => None,
        })
        .collect();
    name_unnamed_params(names)
}

/// Extract parameter names from cross-crate MIR `var_debug_info`.
///
/// MIR locals `_1` through `_N` (where N = `arg_count`) are the function's
/// parameters. The `var_debug_info` entries map locals to their source-level
/// names. For methods, `_1` is `self`.
fn get_arg_names_from_cross_crate_mir(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Vec<String>> {
    // Guard: only attempt MIR extraction for functions with available MIR.
    if !tcx.is_mir_available(def_id) {
        return None;
    }

    // Catch panics from MIR access — some cross-crate items may have
    // unavailable or malformed MIR despite is_mir_available returning true.
    let body = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tcx.optimized_mir(def_id)))
        .ok()?;

    let arg_count = body.arg_count;
    if arg_count == 0 {
        return Some(Vec::new());
    }

    // Build a map from MIR local index → debug name.
    // Arguments are locals 1..=arg_count (local 0 is the return place).
    let mut arg_names: Vec<Option<String>> = vec![None; arg_count];
    for debug_info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &debug_info.value {
            let local_idx = place.local.as_usize();
            // Arguments are locals 1..=arg_count
            if (1..=arg_count).contains(&local_idx) {
                arg_names[local_idx - 1] = Some(debug_info.name.as_str().to_string());
            }
        }
    }

    // Convert to final names, using positional fallback for any missing entries.
    Some(name_unnamed_params(arg_names))
}
