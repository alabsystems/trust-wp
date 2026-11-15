// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract attribute extraction and loop contract collection.
//!
//! Handles legacy tool attribute parsing, loop-level invariant/variant
//! collection from function bodies via HIR visitor, and source-level
//! fallback extraction for attributes not preserved in HIR.

use rustc_ast::attr::AttributeExt;
use rustc_attr_ir::Attribute;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
    Expr, ExprKind,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};

use super::super::super::attr_utils::{
    get_contract_attrs_from_doc, get_contract_attrs_from_proc_macro,
};

/// Get the values of all attributes matching a path.
///
/// For example, `#[trust_wp::spec::requires = "x > 0"]` with path
/// `["trust-wp", "spec", "requires"]` returns `vec!["x > 0"]`.
pub(super) fn get_contract_attrs(attrs: &[Attribute], path: &[&str]) -> Vec<String> {
    let mut values = Vec::new();

    for attr in attrs {
        // Skip doc comments
        if attr.is_doc_comment().is_some() {
            continue;
        }

        // Check if this is an unparsed (custom) attribute
        let (Attribute::Tool(item) | Attribute::DeriveHelper(item)) = attr else {
            continue;
        };

        // Check path matches
        if item.path.segments.len() != path.len() {
            continue;
        }

        let matches = item
            .path
            .segments
            .iter()
            .zip(path)
            // Trust: AttrPath.segments is now Box<[Symbol]>; seg is a &Symbol directly.
            .all(|(seg, s)| seg.as_str() == *s);

        if matches {
            // Extract the value string
            if let Some(value) = crate::attr_utils::doc_marker_str(attr) {
                values.push(value.to_string());
            }
        }
    }

    values
}

/// (
///   flat_invariants,
///   flat_variants,
///   per_loop_invariants,
///   per_loop_variants,
///   all_loop_spans,
/// )
pub(in crate::callbacks) type LoopContractAttrs = (
    Vec<String>,
    Vec<String>,
    Vec<(u32, u32, Vec<String>)>,
    Vec<(u32, u32, Vec<String>)>,
    Vec<(u32, u32)>,
);

/// Collect loop-level invariant/variant attributes from a function body.
///
/// Returns
/// (flat_invariants, flat_variants, per_loop_invariants, per_loop_variants, all_loop_spans).
/// `per_loop_invariants` maps each loop's source span (start, end) to its invariants.
/// `per_loop_variants` maps each loop's source span (start, end) to its variants.
/// `all_loop_spans` contains spans of ALL loops (including those without invariants).
pub(in crate::callbacks) fn collect_loop_contract_attrs(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
) -> LoopContractAttrs {
    let Some(body_id) = tcx.hir_node_by_def_id(local_def_id).body_id() else {
        return (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    };
    let body = tcx.hir_body(body_id);
    let mut collector = LoopContractAttrCollector {
        tcx,
        invariants: Vec::new(),
        variants: Vec::new(),
        per_loop_invariants: Vec::new(),
        per_loop_variants: Vec::new(),
        all_loop_spans: Vec::new(),
    };
    collector.visit_body(body);
    (
        collector.invariants,
        collector.variants,
        collector.per_loop_invariants,
        collector.per_loop_variants,
        collector.all_loop_spans,
    )
}

/// Visitor that finds `#[invariant]`/`#[variant]` attrs on loop expressions.
struct LoopContractAttrCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    invariants: Vec<String>,
    variants: Vec<String>,
    /// Per-loop invariants with source span (start, end) of the loop expression.
    /// Matching uses span containment: a MIR loop header matches if its position
    /// falls within [start, end) and this is the tightest such span.
    per_loop_invariants: Vec<(u32, u32, Vec<String>)>,
    /// Per-loop variants with source span (start, end) of the loop expression.
    per_loop_variants: Vec<(u32, u32, Vec<String>)>,
    /// Source spans (start, end) of ALL loop expressions in the function body,
    /// including those without invariants. Used to detect when a MIR loop header
    /// falls inside a nested loop that has no invariant (preventing false inheritance
    /// from an outer loop's invariant).
    all_loop_spans: Vec<(u32, u32)>,
}

impl<'tcx> Visitor<'tcx> for LoopContractAttrCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let attrs = self.tcx.hir_attrs(expr.hir_id);
        let loop_invs = collect_contract_attrs_any_style(attrs, "invariant");
        let loop_vars = collect_contract_attrs_any_style(attrs, "variant");

        // Record ALL loop expression spans (with or without invariants).
        // This is needed to detect when a MIR loop header falls inside a
        // nested loop without an invariant.
        if matches!(expr.kind, ExprKind::Loop(..)) {
            let start = expr.span.lo().0;
            let end = expr.span.hi().0;
            self.all_loop_spans.push((start, end));
        }

        // Record per-loop invariants with the loop expression's full span.
        if !loop_invs.is_empty() {
            let start = expr.span.lo().0;
            let end = expr.span.hi().0;
            self.per_loop_invariants
                .push((start, end, loop_invs.clone()));
        }
        if !loop_vars.is_empty() {
            let start = expr.span.lo().0;
            let end = expr.span.hi().0;
            self.per_loop_variants.push((start, end, loop_vars.clone()));
        }

        extend_unique(&mut self.invariants, loop_invs);
        extend_unique(&mut self.variants, loop_vars);

        // Invariants/variants on loops inside closures belong to the closure's body.
        // Avoid attributing them to the containing function.
        if matches!(expr.kind, ExprKind::Closure(_)) {
            return;
        }

        intravisit::walk_expr(self, expr);
    }
}

fn collect_contract_attrs_any_style(attrs: &[Attribute], name: &str) -> Vec<String> {
    let mut values = get_contract_attrs_from_doc(attrs, name);

    if values.is_empty() {
        values = get_contract_attrs(attrs, &["trust-wp", "spec", name]);
    }

    if values.is_empty() {
        values = get_contract_attrs_from_proc_macro(attrs, name);
    }

    values
}

pub(super) fn extend_unique(dst: &mut Vec<String>, src: Vec<String>) {
    for value in src {
        if !dst.iter().any(|existing| existing == &value) {
            dst.push(value);
        }
    }
}

/// Fallback extraction for loop attrs that don't survive to HIR attributes.
///
/// Some Creusot-style statement attributes (`#[invariant]`, `#[variant]`) can
/// be missing from the post-expansion HIR attribute list even though they are
/// present in the source snippet. Scan the function source as a fallback.
pub(in crate::callbacks) fn collect_loop_contract_attrs_from_source(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> (Vec<String>, Vec<String>) {
    // Skip closures: their def_span from macro expansion can encompass
    // invariant/variant attributes that belong to the enclosing function
    // (e.g., proof_assert! probe closures inside ghost blocks with loops).
    // The HIR-based collector handles closures that genuinely contain loops.
    if tcx.def_kind(def_id) == DefKind::Closure {
        return (Vec::new(), Vec::new());
    }

    let span = tcx.def_span(def_id);
    let Ok(snippet) = tcx.sess.source_map().span_to_snippet(span) else {
        return (Vec::new(), Vec::new());
    };

    let invariants = extract_attr_args_from_source(&snippet, "invariant");
    let variants = extract_attr_args_from_source(&snippet, "variant");
    (invariants, variants)
}

pub(super) fn extract_attr_args_from_source(source: &str, attr_name: &str) -> Vec<String> {
    let bytes = source.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;

    while i + 2 < bytes.len() {
        if bytes[i] != b'#' || bytes[i + 1] != b'[' {
            i += 1;
            continue;
        }
        i += 2;
        i = skip_ws(bytes, i);

        let name_start = i;
        while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
            i += 1;
        }
        if &source[name_start..i] != attr_name {
            continue;
        }

        i = skip_ws(bytes, i);
        if i >= bytes.len() || bytes[i] != b'(' {
            continue;
        }
        i += 1;
        let args_start = i;
        let mut depth = 1usize;

        while i < bytes.len() {
            match bytes[i] {
                b'"' => {
                    // Skip string literal contents (handle \" escapes)
                    i += 1;
                    while i < bytes.len() && bytes[i] != b'"' {
                        if bytes[i] == b'\\' {
                            i += 1; // skip escaped char
                        }
                        i += 1;
                    }
                    // i now points at closing '"' (or past end)
                }
                b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'*' => {
                    // Skip block comment
                    i += 2;
                    while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                        i += 1;
                    }
                    if i + 1 < bytes.len() {
                        i += 1; // skip past '*/', i will point at '/'
                    }
                }
                b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'/' => {
                    // Skip line comment
                    i += 2;
                    while i < bytes.len() && bytes[i] != b'\n' {
                        i += 1;
                    }
                    // i now points at '\n' (or past end)
                }
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            i += 1;
        }

        if i >= bytes.len() || depth != 0 {
            break;
        }

        let args = source[args_start..i].trim();
        i += 1;
        i = skip_ws(bytes, i);
        if i < bytes.len() && bytes[i] == b']' && !args.is_empty() {
            out.push(args.to_string());
            i += 1;
        }
    }

    out
}

fn skip_ws(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    i
}
