// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Creusot frontend refusals that have no solver-side equivalent.
//!
//! Every check here only ADDS rejections, each mirroring a specific Creusot
//! frontend diagnostic, and each is deliberately a subset of what Creusot
//! rejects (when in doubt, a construct is left for the verifier):
//!
//! - ghost purity for external program functions called inside `ghost!`
//!   (creusot `validate/purity.rs`: `called non-ghost function .. in ghost context`),
//! - the `creusot::contractless_external_function` lint when it is denied
//!   (creusot `translation/function/terminator.rs`),
//! - `#[variant(x)]` whose type does not implement `WellFounded`
//!   (creusot-std `__stubs::variant_check<R: WellFounded>`, error E0277),
//! - `dyn Trait` types in specifications other than the logically
//!   dyn-compatible traits (creusot `backend/clone_map/elaborator.rs`).
//!
//! One check is trust-wp's own fail-closed guard rather than a Creusot
//! diagnostic: a source identifier in a namespace the verifier synthesizes
//! names in (see [`validate_reserved_binding_names`]).

use std::collections::HashMap;

use rustc_ast::attr::AttributeExt;
use rustc_attr_ir::Attribute;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    intravisit::{walk_expr, walk_pat, Visitor},
    Expr, ExprKind, HirId, Pat, PatKind,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{Ty, TyCtxt, TyKind, TypeckResults},
};
use rustc_span::{Span, Symbol};
use trust_wp_driver::StdSpec;

use crate::ghost::GhostBlock;

#[derive(Debug)]
pub(super) struct FrontendCheckError {
    pub(super) span: Span,
    pub(super) message: String,
}

const SPEC_LIBRARY_CRATES: &[&str] = &[
    "trust_wp_std",
    "trust-wp",
    "trust_wp",
    "creusot_std",
    "creusot_contracts",
    "trust_wp_lib",
];

fn local_crate_is_spec_library(tcx: TyCtxt<'_>) -> bool {
    let name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    SPEC_LIBRARY_CRATES.contains(&name.as_str())
}

fn def_is_from_spec_library(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let name = tcx.crate_name(def_id.krate).to_string();
    SPEC_LIBRARY_CRATES.contains(&name.as_str())
}

/// True when trust-wp knows ANY contract (built-in std spec, trust-wp-std
/// extern spec, or local `extern_spec!`) for the external function `def_id`.
fn external_fn_has_contract(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    extern_specs: &HashMap<String, StdSpec>,
) -> bool {
    let path = tcx.def_path_str(def_id);
    let mut candidates = vec![path.clone()];
    for (from, to) in [
        ("std::", "core::"),
        ("std::", "alloc::"),
        ("core::", "std::"),
    ] {
        if let Some(rest) = path.strip_prefix(from) {
            candidates.push(format!("{to}{rest}"));
        }
    }
    candidates
        .iter()
        .any(|p| crate::provenance::spec_exists_for_def(tcx, def_id, Some(extern_specs), p))
}

/// An external FREE function (not a trait/inherent method, not from a spec
/// library) for which trust-wp has no contract. Creusot gives such a function
/// no `#[check(ghost)]` and an impossible precondition.
fn is_contractless_external_free_fn(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    extern_specs: &HashMap<String, StdSpec>,
) -> bool {
    !def_id.is_local()
        && tcx.def_kind(def_id) == DefKind::Fn
        && !def_is_from_spec_library(tcx, def_id)
        && !external_fn_has_contract(tcx, def_id, extern_specs)
}

fn call_callee_def_id(typeck: &TypeckResults<'_>, expr: &Expr<'_>) -> Option<DefId> {
    let ExprKind::Call(callee, _) = expr.kind else {
        return None;
    };
    match typeck.expr_ty_opt(callee)?.kind() {
        TyKind::FnDef(def_id, _) => Some(*def_id),
        _ => None,
    }
}

// ── ghost purity: external program functions inside ghost! ────────────────

/// Creusot: inside `ghost!` only ghost (or logic-free ghost-intrinsic)
/// functions may be called; an external function is ghost only when its
/// extern spec says `#[check(ghost)]`. A contractless external function is
/// therefore never ghost (`should_fail/alloc_max_size`: `size_of_val`).
pub(super) fn validate_ghost_block_external_calls(
    tcx: TyCtxt<'_>,
    ghost_blocks: &[GhostBlock],
    extern_specs: &HashMap<String, StdSpec>,
) -> Vec<FrontendCheckError> {
    if local_crate_is_spec_library(tcx) {
        return Vec::new();
    }
    let mut errors = Vec::new();
    for block in ghost_blocks {
        let expr = tcx.hir_node(block.hir_id).expect_expr();
        let body = tcx.hir_body_owned_by(block.containing_fn);
        let typeck = tcx.typeck_body(body.id());
        let mut visitor = ContractlessCallVisitor {
            tcx,
            typeck,
            extern_specs,
            hits: Vec::new(),
        };
        visitor.visit_expr(expr);
        for (span, def_id) in visitor.hits {
            errors.push(FrontendCheckError {
                span,
                message: format!(
                    "called non-ghost function `{}` in ghost context",
                    tcx.def_path_str(def_id)
                ),
            });
        }
    }
    errors
}

struct ContractlessCallVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    extern_specs: &'a HashMap<String, StdSpec>,
    hits: Vec<(Span, DefId)>,
}

impl<'tcx> Visitor<'tcx> for ContractlessCallVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if crate::callbacks::spec_typecheck::is_spec_tc_closure_expr(self.tcx, expr) {
            return;
        }
        // Only calls written by the user: macro-generated calls (desugarings,
        // spec-macro plumbing) are left alone.
        if !expr.span.from_expansion() {
            if let Some(def_id) = call_callee_def_id(self.typeck, expr) {
                if is_contractless_external_free_fn(self.tcx, def_id, self.extern_specs) {
                    self.hits.push((expr.span, def_id));
                }
            }
        }
        walk_expr(self, expr);
    }
}

// ── lint: creusot::contractless_external_function ─────────────────────────

const CONTRACTLESS_LINT: &str = "creusot::contractless_external_function";

/// Lint level of `creusot::contractless_external_function` set by one
/// attribute: `Some(true)` for deny/forbid, `Some(false)` for allow/warn/expect.
fn contractless_lint_level(tcx: TyCtxt<'_>, attr: &Attribute) -> Option<bool> {
    if attr.is_doc_comment().is_some() {
        return None;
    }
    // `Attribute::span()` panics on most parsed attributes, so an unparsed
    // attribute is read from its source text and a parsed one (rustc may parse
    // lint-level attributes itself) from its structured Debug rendering.
    let text = match attr {
        Attribute::Tool(item) | Attribute::DeriveHelper(item) => {
            tcx.sess.source_map().span_to_snippet(item.span).ok()?
        }
        Attribute::Parsed(_) => format!("{attr:?}"),
    };
    let compact: String = text
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect::<String>();
    if !compact.contains(CONTRACTLESS_LINT) && !compact.contains("contractless_external_function") {
        return None;
    }
    if !compact.contains("creusot") {
        return None;
    }
    let lower = compact.to_ascii_lowercase();
    let head = lower.trim_start_matches("#[");
    if head.starts_with("deny") || head.starts_with("forbid") {
        return Some(true);
    }
    if head.starts_with("allow") || head.starts_with("warn") || head.starts_with("expect") {
        return Some(false);
    }
    // Parsed rendering: the level is named somewhere in the structure.
    if lower.contains("deny") || lower.contains("forbid") {
        Some(true)
    } else if lower.contains("allow") || lower.contains("warn") || lower.contains("expect") {
        Some(false)
    } else {
        None
    }
}

fn contractless_lint_denied(tcx: TyCtxt<'_>, hir_id: HirId) -> bool {
    let chain = std::iter::once(hir_id).chain(tcx.hir_parent_iter(hir_id).map(|(id, _)| id));
    for id in chain {
        // Innermost lint attribute wins, as in rustc's lint-level resolution.
        if let Some(level) = tcx
            .hir_attrs(id)
            .iter()
            .filter_map(|attr| contractless_lint_level(tcx, attr))
            .last()
        {
            return level;
        }
    }
    false
}

/// Creusot gives an external function without a contract `#[requires(false)]`
/// and reports each call through the `contractless_external_function` lint
/// (Warn by default). Only a DENIED lint is an error, so only that is refused.
pub(super) fn validate_contractless_external_calls(
    tcx: TyCtxt<'_>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Vec<FrontendCheckError> {
    if local_crate_is_spec_library(tcx) {
        return Vec::new();
    }
    let mut errors = Vec::new();
    for owner in tcx.hir_body_owners() {
        if tcx.def_kind(owner) == DefKind::Closure {
            // Closure bodies are visited through their parent body.
            continue;
        }
        if !contractless_lint_denied(tcx, tcx.local_def_id_to_hir_id(owner)) {
            continue;
        }
        let body = tcx.hir_body_owned_by(owner);
        let typeck = tcx.typeck_body(body.id());
        let mut visitor = ContractlessCallVisitor {
            tcx,
            typeck,
            extern_specs,
            hits: Vec::new(),
        };
        visitor.visit_body(body);
        for (span, def_id) in visitor.hits {
            errors.push(FrontendCheckError {
                span,
                message: format!(
                    "calling external function `{}` with no contract will yield an impossible precondition",
                    tcx.item_name(def_id)
                ),
            });
        }
    }
    errors
}

// ── #[variant] type must implement WellFounded ────────────────────────────

pub(super) const VARIANT_NOT_WELL_FOUNDED: &str =
    "the variant type does not implement `WellFounded`";

fn is_plain_ident(text: &str) -> bool {
    let mut chars = text.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Self types of local `impl WellFounded for _` blocks.
fn local_well_founded_self_tys(tcx: TyCtxt<'_>) -> Vec<Ty<'_>> {
    tcx.iter_local_def_id()
        .filter(|local| {
            matches!(
                tcx.def_kind(local.to_def_id()),
                DefKind::Impl { of_trait: true }
            )
        })
        .filter_map(|local| {
            let iref = tcx.impl_trait_ref(local.to_def_id()).skip_binder();
            (tcx.item_name(iref.def_id).as_str() == "WellFounded").then(|| iref.self_ty())
        })
        .collect()
}

/// Definitely not `WellFounded`: a LOCAL struct/enum/union with no local
/// `WellFounded` impl (no other crate can implement a foreign trait for it
/// except through a blanket impl, and trust-wp-std/creusot-std have none).
/// Every other type is left to the verifier.
fn definitely_not_well_founded<'tcx>(ty: Ty<'tcx>, wf_self_tys: &[Ty<'tcx>]) -> bool {
    let TyKind::Adt(adt, _) = ty.peel_refs().kind() else {
        return false;
    };
    if !adt.did().is_local() {
        return false;
    }
    !wf_self_tys
        .iter()
        .any(|self_ty| match self_ty.peel_refs().kind() {
            TyKind::Adt(other, _) => other.did() == adt.did(),
            // Blanket/parametric impls: cannot rule them out structurally.
            _ => true,
        })
}

pub(super) fn validate_variant_types(tcx: TyCtxt<'_>) -> Vec<FrontendCheckError> {
    if local_crate_is_spec_library(tcx) {
        return Vec::new();
    }
    let wf_self_tys = local_well_founded_self_tys(tcx);
    let mut errors = Vec::new();
    for owner in tcx.hir_body_owners() {
        // Specification type-check closures are neither program code nor
        // specifications the verifier reads (see `spec_typecheck`).
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, owner) {
            continue;
        }
        let body = tcx.hir_body_owned_by(owner);
        let typeck = tcx.typeck_body(body.id());

        let mut collector = VariantSiteCollector {
            tcx,
            bindings: Vec::new(),
            loop_variants: Vec::new(),
        };
        collector.visit_body(body);

        let mut sites: Vec<(Span, String, Option<u32>)> = Vec::new();
        let owner_attrs = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
        for text in crate::attr_utils::get_contract_attrs_from_doc(owner_attrs, "variant") {
            sites.push((tcx.def_span(owner.to_def_id()), text, None));
        }
        for (span, text) in collector.loop_variants {
            sites.push((span, text, Some(span.lo().0)));
        }

        let param_ids: Vec<HirId> = body.params.iter().map(|p| p.pat.hir_id).collect();
        for (span, text, before) in sites {
            let name = text.trim();
            if !is_plain_ident(name) {
                continue;
            }
            let binding = collector
                .bindings
                .iter()
                .filter(|(sym, _, bspan, pat_id)| {
                    sym.as_str() == name
                        && match before {
                            Some(pos) => bspan.hi().0 <= pos,
                            None => param_ids.contains(pat_id),
                        }
                })
                .max_by_key(|(_, _, bspan, _)| bspan.lo().0);
            let Some((_, hir_id, _, _)) = binding else {
                continue;
            };
            let Some(ty) = typeck.node_type_opt(*hir_id) else {
                continue;
            };
            if definitely_not_well_founded(ty, &wf_self_tys) {
                errors.push(FrontendCheckError {
                    span,
                    message: format!(
                        "the trait bound `{ty}: WellFounded` is not satisfied: {VARIANT_NOT_WELL_FOUNDED} (`#[variant({name})]`)"
                    ),
                });
            }
        }
    }
    errors
}

struct VariantSiteCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// (name, binding hir id, binding span, top-level pattern hir id)
    bindings: Vec<(Symbol, HirId, Span, HirId)>,
    loop_variants: Vec<(Span, String)>,
}

impl<'tcx> Visitor<'tcx> for VariantSiteCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_param(&mut self, param: &'tcx rustc_hir::Param<'tcx>) {
        let top = param.pat.hir_id;
        collect_bindings(param.pat, top, &mut self.bindings);
        rustc_hir::intravisit::walk_param(self, param);
    }

    fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
        collect_bindings(local.pat, local.pat.hir_id, &mut self.bindings);
        rustc_hir::intravisit::walk_local(self, local);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if crate::callbacks::spec_typecheck::is_spec_tc_closure_expr(self.tcx, expr) {
            return;
        }
        if matches!(expr.kind, ExprKind::Loop(..)) {
            let attrs = self.tcx.hir_attrs(expr.hir_id);
            for text in crate::attr_utils::get_contract_attrs_from_doc(attrs, "variant") {
                self.loop_variants.push((expr.span, text));
            }
        }
        if matches!(expr.kind, ExprKind::Closure(_)) {
            // A closure is its own body owner; its variants are checked there.
            return;
        }
        walk_expr(self, expr);
    }
}

fn collect_bindings(pat: &Pat<'_>, top: HirId, out: &mut Vec<(Symbol, HirId, Span, HirId)>) {
    struct Bindings<'o> {
        top: HirId,
        out: &'o mut Vec<(Symbol, HirId, Span, HirId)>,
    }
    impl<'v> Visitor<'v> for Bindings<'_> {
        fn visit_pat(&mut self, pat: &'v Pat<'v>) {
            if let PatKind::Binding(_, hir_id, ident, _) = pat.kind {
                self.out.push((ident.name, hir_id, pat.span, self.top));
            }
            walk_pat(self, pat);
        }
    }
    Bindings { top, out }.visit_pat(pat);
}

// ── source identifiers in a synthesized-name namespace ───────────────────

/// Why `name` may not be a source identifier, if it lies in a namespace the
/// verifier synthesizes names in AND that namespace is still spelled as a
/// Rust identifier.
///
/// Synthesized VARIABLE names that could alias a source name (call results,
/// call-argument placeholders, anonymous parameters, havoc symbols, skolems,
/// borrow carriers) carry `$` (`trust_wp_core::formula::synthesized_names`),
/// which no source identifier can contain, so they need no refusal here.
///
/// What remains in the identifier namespace is the `__trust_wp_` / `__twp`
/// family: the contract parser's accessor functions (`__trust_wp_field_x`,
/// `__trust_wp_tuple_get_0`), encoder constants and functions
/// (`__trust_wp_unit`, `__trust_wp_int_truncate_*`, ...), and marker names.
/// A clause resolves a path to its LAST segment (`S::C`, `dep::C` → `C`), so a
/// const, static, fn, associated item, variant, field, `use` alias or binding
/// with such a name could stand for a synthesized symbol. None of these
/// spellings occurs in the Creusot corpus.
fn reserved_identifier_reason(name: &str) -> Option<&'static str> {
    if name.starts_with("__trust_wp") || name.starts_with("__twp") {
        return Some(
            "the `__trust_wp` / `__twp` prefixes name synthesized functions and constants",
        );
    }
    None
}

/// Bindings the trust-wp macros themselves introduce (`ghost!`, `snapshot!`).
/// Exempt only when the binding's innermost expansion is a macro DEFINED in
/// the `trust_wp_macros` proc-macro crate: a user `macro_rules!` (or any other
/// crate's macro) emitting `let __trust_wp_ghost_value = ..` is refused like a
/// hand-written binding.
const MACRO_EMITTED_BINDINGS: &[&str] = &["__trust_wp_ghost_value", "__trust_wp_snap_ref"];
const MACRO_EMITTING_CRATE: &str = "trust_wp_macros";

fn is_macro_emitted(tcx: TyCtxt<'_>, name: &str, span: Span) -> bool {
    if !MACRO_EMITTED_BINDINGS.contains(&name) || !span.from_expansion() {
        return false;
    }
    span.ctxt()
        .outer_expn_data()
        .macro_def_id
        .is_some_and(|def_id| tcx.crate_name(def_id.krate).as_str() == MACRO_EMITTING_CRATE)
}

/// Identifier tokens (maximal `[A-Za-z0-9_]` runs not starting with a digit)
/// of specification text.
fn spec_text_identifiers(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|tok| tok.chars().next().is_some_and(|c| !c.is_ascii_digit()))
}

/// Refuse every source identifier in a synthesized-name namespace: item names
/// of every kind (const, static, fn, type, trait, associated items, foreign
/// items, variants, fields, generic parameters, `use` aliases), bindings
/// (parameters, `let`, closure parameters, match bindings), the last segment
/// of every path a body names (items imported from other crates), and every
/// identifier of specification text.
///
/// Only ADDS rejections; the run stops with exit 2 and grants no credit.
pub(super) fn validate_reserved_binding_names(tcx: TyCtxt<'_>) -> Vec<FrontendCheckError> {
    struct Names<'o, 't> {
        tcx: TyCtxt<'t>,
        seen: &'o mut std::collections::HashSet<(Span, String)>,
        errors: &'o mut Vec<FrontendCheckError>,
    }
    impl Names<'_, '_> {
        fn check(&mut self, what: &str, name: &str, span: Span) {
            let Some(reason) = reserved_identifier_reason(name) else {
                return;
            };
            if is_macro_emitted(self.tcx, name, span) {
                return;
            }
            if self.seen.insert((span, name.to_string())) {
                self.errors.push(FrontendCheckError {
                    span,
                    message: format!(
                        "trust-wp: {what} `{name}` lies in a namespace the verifier \
                         synthesizes names in ({reason}); rename it"
                    ),
                });
            }
        }
    }
    impl<'v> Visitor<'v> for Names<'_, '_> {
        fn visit_pat(&mut self, pat: &'v Pat<'v>) {
            if let PatKind::Binding(_, _, ident, _) = pat.kind {
                // The identifier's span, not the pattern's: who wrote the
                // name decides the exemption, and `mut`/`ref`/`@` tokens of
                // another expansion say nothing about it (D-239).
                self.check("binding", ident.name.as_str(), ident.span);
            }
            walk_pat(self, pat);
        }
        fn visit_path(&mut self, path: &rustc_hir::Path<'v>, _id: HirId) {
            if let Some(last) = path.segments.last() {
                self.check("path", last.ident.name.as_str(), path.span);
            }
            rustc_hir::intravisit::walk_path(self, path);
        }
    }

    if local_crate_is_spec_library(tcx) {
        return Vec::new();
    }
    let mut seen = std::collections::HashSet::new();
    let mut errors = Vec::new();
    {
        let mut names = Names {
            tcx,
            seen: &mut seen,
            errors: &mut errors,
        };
        for def_id in tcx.hir_crate_items(()).definitions() {
            let Some(name) = tcx.opt_item_name(def_id.to_def_id()) else {
                continue;
            };
            // The sibling helper trust-wp-macros emits for a contract on a
            // bodyless trait method (`__trust_wp_spec_tc_<m>_<n>`) is not a
            // source identifier. It is exempt only when it passes the full
            // provenance check (macro-emitted marker, trait default body,
            // `Self: Sized`); a user item with that prefix is refused here
            // and by `spec_typecheck::forged_spec_tc_markers`.
            if crate::callbacks::spec_typecheck::is_spec_tc_trait_helper(tcx, def_id) {
                continue;
            }
            let span = tcx.def_span(def_id.to_def_id());
            names.check("item", name.as_str(), span);
        }
    }
    for owner in tcx.hir_body_owners() {
        let body = tcx.hir_body_owned_by(owner);
        let mut visitor = Names {
            tcx,
            seen: &mut seen,
            errors: &mut errors,
        };
        for param in body.params {
            visitor.visit_pat(param.pat);
        }
        rustc_hir::intravisit::walk_expr(&mut visitor, body.value);

        for clause in spec_clauses_of_body_owner(tcx, owner) {
            for ident in spec_text_identifiers(&clause.text) {
                let mut names = Names {
                    tcx,
                    seen: &mut seen,
                    errors: &mut errors,
                };
                names.check("specification identifier", ident, clause.span);
            }
        }
    }
    errors
}

// ── source value names that alias an encoder-derived name ────────────────

/// Suffix derivations the encoder and the verification pipeline build from a
/// variable name `x` into ANOTHER solver variable: `x_current` / `x_final` /
/// `x_id` (the `&mut` components, `trust-wp-ay` `MutRefVarNames`), `x_view`
/// (`x@`), `x_prime` (loop next state), `x_final_old` (loop prophecy entry
/// value), `x_ssa_K` (intermediate `^` chain values).
const DERIVED_NAME_SUFFIXES: &[&str] = &["_view", "_current", "_final", "_prime", "_id", "_old"];
/// Prefix derivations: `old_x` (pre-state) and `final_x`.
const DERIVED_NAME_PREFIXES: &[&str] = &["old_", "final_"];

/// Every base name that `name` could be derived from by peeling one or more
/// derivation layers, over EVERY split: at each layer every applicable
/// `_ssa_K`, suffix and prefix peel is explored, not just the first match.
/// `old_a_id_current` yields `old_a_id`, `a_id_current`, `old_a`, `a_id`,
/// `a_current`, `a`, ...; a first-match peel stopped at `old_a` / `a` and never
/// reached `a_id`, so `fn g(a_id: &mut u32, old_a_id_current: u32)` aliased
/// the encoder's `old(*a_id)` (measured exit-0 false accept). Each peel
/// strictly shortens the name, so the search terminates; results are
/// de-duplicated in discovery order.
fn derived_name_bases(name: &str) -> Vec<&str> {
    let mut bases: Vec<&str> = Vec::new();
    let mut seen: std::collections::HashSet<&str> = std::collections::HashSet::new();
    let mut work = vec![name];
    let mut index = 0;
    while index < work.len() {
        let current = work[index];
        index += 1;
        let mut peeled: Vec<&str> = Vec::new();
        if let Some((head, digits)) = current.rsplit_once("_ssa_") {
            if !head.is_empty() && !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
            {
                peeled.push(head);
            }
        }
        peeled.extend(
            DERIVED_NAME_SUFFIXES
                .iter()
                .filter_map(|suffix| current.strip_suffix(suffix).filter(|base| !base.is_empty())),
        );
        peeled.extend(
            DERIVED_NAME_PREFIXES
                .iter()
                .filter_map(|prefix| current.strip_prefix(prefix).filter(|base| !base.is_empty())),
        );
        for base in peeled {
            if seen.insert(base) {
                bases.push(base);
                work.push(base);
            }
        }
    }
    bases
}

/// Whether one occurrence of an identifier token in (token-printed)
/// specification text is in ITEM position: a field or method name (`p . f`,
/// `v . len ()`), a call head (`f (..)`), or a path prefix (`m :: x`). A value
/// binder is never declared in such a position (`forall < x : T >`, `| x |`,
/// `Some (x)`), so a name some occurrence of which is not in item position may
/// be a value.
fn spec_ident_in_item_position(text: &str, start: usize, end: usize) -> bool {
    let before = text[..start].trim_end();
    if let Some(rest) = before.strip_suffix('.') {
        if !rest.ends_with('.') {
            return true;
        }
    }
    let after = text[end..].trim_start();
    after.starts_with('(') || (after.starts_with("::") && !after.starts_with(":::"))
}

/// Identifier tokens of specification text with their item-position flag
/// (see [`spec_ident_in_item_position`]).
fn spec_text_identifier_occurrences(text: &str) -> Vec<(&str, bool)> {
    let mut out = Vec::new();
    let mut offset = 0;
    for tok in text.split(|c: char| !(c.is_alphanumeric() || c == '_')) {
        let start = offset;
        let end = start + tok.len();
        // Each separator is one char; advance past it.
        offset = end + text[end..].chars().next().map_or(0, char::len_utf8);
        if tok.chars().next().is_some_and(|c| !c.is_ascii_digit()) {
            out.push((tok, spec_ident_in_item_position(text, start, end)));
        }
    }
    out
}

/// Refuse a source VALUE name that is spelled as an encoder-derived name of
/// another source value name of the crate.
///
/// The encoder names the solver variables it derives from a variable `x` by
/// appending or prepending to the source spelling (`*x` → `x_current`, `^x` →
/// `x_final`, the loop next state → `x_prime`, ...). A parameter literally named
/// `x_current` next to `x: &mut u32` is then the same solver constant as `*x`,
/// so `#[ensures(result == x_current)] fn g(x: &mut u32, x_current: u32) -> u32
/// { *x }` verified (measured exit-0 false accept). The derived spellings are
/// shared by encoder-internal consumers (sort inference, view resolution), so
/// the colliding SOURCE name is refused instead.
///
/// Value names are bindings, `const` / `static` / associated-const / const
/// generic parameter names, and identifiers of specification text (a clause
/// resolves `dep::C` to `C`) that are not the name of a local non-value item
/// (a function, type, trait, module, field or variant never becomes a solver
/// variable). Bases are value names plus `result` and `self`. Only ADDS
/// rejections.
pub(super) fn validate_derived_name_aliases(tcx: TyCtxt<'_>) -> Vec<FrontendCheckError> {
    struct Bindings<'o> {
        out: &'o mut Vec<(String, Span)>,
    }
    impl<'v> Visitor<'v> for Bindings<'_> {
        fn visit_pat(&mut self, pat: &'v Pat<'v>) {
            if let PatKind::Binding(_, _, ident, _) = pat.kind {
                self.out.push((ident.name.to_string(), pat.span));
            }
            walk_pat(self, pat);
        }
        // A body path to a value item of ANY crate (`dep::x_current`) reaches
        // the solver as its last segment, like a local const does.
        fn visit_path(&mut self, path: &rustc_hir::Path<'v>, _id: HirId) {
            if let rustc_hir::def::Res::Def(
                DefKind::Const { .. }
                | DefKind::Static { .. }
                | DefKind::AssocConst { .. }
                | DefKind::ConstParam,
                _,
            ) = path.res
            {
                if let Some(last) = path.segments.last() {
                    self.out.push((last.ident.name.to_string(), path.span));
                }
            }
            rustc_hir::intravisit::walk_path(self, path);
        }
    }

    if local_crate_is_spec_library(tcx) {
        return Vec::new();
    }
    // (name, span) of every value-name occurrence, and the set of local
    // non-value item names.
    let mut values: Vec<(String, Span)> = Vec::new();
    let mut spec_idents: Vec<(String, Span)> = Vec::new();
    // Spec-text identifiers with at least one occurrence NOT in item position
    // (a possible value: a quantifier / closure / pattern binder, a variable).
    let mut spec_value_position: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut non_value_items: std::collections::HashSet<String> = std::collections::HashSet::new();
    for def_id in tcx.hir_crate_items(()).definitions() {
        let Some(name) = tcx.opt_item_name(def_id.to_def_id()) else {
            continue;
        };
        match tcx.def_kind(def_id) {
            DefKind::Const { .. }
            | DefKind::Static { .. }
            | DefKind::AssocConst { .. }
            | DefKind::ConstParam => {
                values.push((name.to_string(), tcx.def_span(def_id.to_def_id())));
            }
            DefKind::Fn | DefKind::AssocFn => {
                non_value_items.insert(name.to_string());
                // Parameters of a function without a body (a required trait
                // method) are named by its contract but visited by no body walk.
                if tcx.hir_maybe_body_owned_by(def_id).is_none() {
                    for ident in tcx.fn_arg_idents(def_id.to_def_id()).iter().flatten() {
                        values.push((ident.name.to_string(), ident.span));
                    }
                }
            }
            _ => {
                non_value_items.insert(name.to_string());
            }
        }
    }
    for owner in tcx.hir_body_owners() {
        let body = tcx.hir_body_owned_by(owner);
        let mut visitor = Bindings { out: &mut values };
        for param in body.params {
            visitor.visit_pat(param.pat);
        }
        rustc_hir::intravisit::walk_expr(&mut visitor, body.value);
        for clause in spec_clauses_of_body_owner(tcx, owner) {
            for (ident, item_position) in spec_text_identifier_occurrences(&clause.text) {
                if !item_position {
                    spec_value_position.insert(ident.to_string());
                }
                spec_idents.push((ident.to_string(), clause.span));
            }
        }
    }

    // A spec identifier is exempt as a local non-value item only when EVERY
    // occurrence of it is in item position: a quantifier binder
    // `forall<x_current: u32>` is a VALUE even when `fn x_current()` exists.
    let spec_values: Vec<&(String, Span)> = spec_idents
        .iter()
        .filter(|(name, _)| spec_value_position.contains(name) || !non_value_items.contains(name))
        .collect();
    let mut bases: std::collections::HashSet<&str> =
        values.iter().map(|(name, _)| name.as_str()).collect();
    // A spec-text binder (`forall<a: &mut u32> *a == ..`) is a base too: its
    // `*a` is named `a_current` like a parameter's.
    bases.extend(
        spec_values
            .iter()
            .filter(|(name, _)| spec_value_position.contains(name))
            .map(|(name, _)| name.as_str()),
    );
    bases.insert("result");
    bases.insert("self");
    let mut seen = std::collections::HashSet::new();
    let mut errors = Vec::new();
    let candidates = values.iter().chain(spec_values.iter().copied());
    for (name, span) in candidates {
        let Some(base) = derived_name_bases(name)
            .into_iter()
            .find(|base| bases.contains(base))
        else {
            continue;
        };
        if seen.insert((*span, name.clone())) {
            errors.push(FrontendCheckError {
                span: *span,
                message: format!(
                    "trust-wp: `{name}` is spelled as a name the verifier derives from \
                     `{base}` (`_current`, `_final`, `_view`, `_prime`, `old_`, ... denote \
                     components of `{base}`); rename it"
                ),
            });
        }
    }
    errors
}

// ── forbidden dyn types in specifications ─────────────────────────────────

/// The `extern_spec` marker kind, whose payload is `requires=`/`ensures=`
/// prefixed rather than the clause text itself.
const EXTERN_SPEC_MARKER_KIND: &str = "extern_spec";

const SPEC_MARKER_KINDS: &[&str] = &[
    "proof_assert",
    "trusted_proof_assert",
    "requires",
    "ensures",
    "invariant",
    "variant",
    "logic_body",
];

/// One specification clause the driver reads (a `trust-wp:<kind>:<text>` doc
/// marker whose kind is in `SPEC_MARKER_KINDS`, or a source-parsed loop
/// clause): its text and the span a refusal is reported at.
struct SpecClause {
    text: String,
    span: Span,
}

/// Every specification clause the driver reads for the body owner `owner`,
/// from EVERY site that can carry one:
///
/// * the owner's own attributes — `#[requires]`/`#[ensures]`/`#[variant]` on
///   a fn, a closure's contract (a closure's owner node IS the closure
///   expression), the fn-level `#[invariant]` spelling;
/// * the markers on every HIR node INSIDE the body — a loop clause
///   `#[invariant]`/`#[variant]` sits on the loop expression
///   (`discovery::collect_loop_contract_attrs`), a `proof_assert!` /
///   trusted-proof-assert marker on the closure the macro emits
///   (`proof_assert::get_proof_assert_expr_text`);
/// * the loop clauses discovery re-reads from the fn's SOURCE snippet
///   (`collect_loop_contract_attrs_from_source`);
/// * the `requires=`/`ensures=` payload of an `extern_spec!` stub's
///   `trust-wp:extern_spec:` markers — an extern spec's ensures is assumed at
///   every call of its target, so its text takes credit like any other.
///
/// A guard over specification text must run over all of them, because each
/// is a lane that takes credit from the text: a reserved-name scan that reads
/// the owner's attributes only refuses a loop invariant spelled
/// `__trust_wp_tuple_get_0((i, 0)) == i` nowhere, and it earns
/// `loop invariant ... verified` (`tests/adversarial/cases/s71_reserved_name_loop_*`),
/// while `spec_tc::encode` leaves such calls untyped on the premise that the
/// driver refuses every one of them.
fn spec_clauses_of_body_owner(tcx: TyCtxt<'_>, owner: LocalDefId) -> Vec<SpecClause> {
    struct Markers<'t> {
        tcx: TyCtxt<'t>,
        out: Vec<SpecClause>,
    }
    impl<'v> Visitor<'v> for Markers<'_> {
        fn visit_id(&mut self, hir_id: HirId) {
            push_marker_clauses(
                self.tcx.hir_attrs(hir_id),
                self.tcx.hir_span(hir_id),
                &mut self.out,
            );
        }
    }

    let mut out = Vec::new();
    let owner_span = tcx.def_span(owner.to_def_id());
    push_marker_clauses(
        tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)),
        owner_span,
        &mut out,
    );

    let mut markers = Markers { tcx, out };
    markers.visit_body(tcx.hir_body_owned_by(owner));
    let mut out = markers.out;

    let (invariants, variants) =
        crate::callbacks::discovery::source_parsing::collect_loop_contract_attrs_from_source(
            tcx,
            owner.to_def_id(),
        );
    out.extend(
        invariants
            .into_iter()
            .chain(variants)
            .map(|text| SpecClause {
                text,
                span: owner_span,
            }),
    );
    out
}

/// The `trust-wp:<kind>:<text>` doc markers of `attrs` whose kind is a
/// specification clause kind, as clauses at `span`.
fn push_marker_clauses(attrs: &[Attribute], span: Span, out: &mut Vec<SpecClause>) {
    for attr in attrs {
        let Some(value) = crate::attr_utils::doc_marker_str(attr) else {
            continue;
        };
        let value = value.as_str();
        let Some(rest) = value.strip_prefix("trust-wp:") else {
            continue;
        };
        let Some((kind, text)) = rest.split_once(':') else {
            continue;
        };
        if kind == EXTERN_SPEC_MARKER_KIND {
            // `trust-wp:extern_spec:requires=<text>` / `ensures=<text>`, the
            // clauses `extern_specs::parse_extern_spec_docs` reads — one
            // marker carries several clauses separated by `;`, and it reads
            // them the same way.
            for prefix in ["requires=", "ensures="] {
                let Some(joined) = text.strip_prefix(prefix) else {
                    continue;
                };
                out.extend(
                    joined
                        .split(';')
                        .map(str::trim)
                        .filter(|c| !c.is_empty())
                        .map(|clause| SpecClause {
                            text: clause.to_string(),
                            span,
                        }),
                );
            }
            continue;
        }
        if !SPEC_MARKER_KINDS.contains(&kind) {
            continue;
        }
        out.push(SpecClause {
            text: text.to_string(),
            span,
        });
    }
}

/// Traits Creusot accepts under `dyn` (`is_logically_dyn_compatible_trait`).
const LOGICALLY_DYN_COMPATIBLE: &[&str] = &["Debug", "Write"];

/// Find `dyn <TraitPath>` in specification text whose trait is not logically
/// dyn-compatible. Returns the trait path as written.
pub(super) fn find_forbidden_dyn_trait(text: &str) -> Option<String> {
    let bytes = text.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut i = 0;
    while let Some(off) = text[i..].find("dyn") {
        let start = i + off;
        let end = start + 3;
        i = end;
        if (start > 0 && is_ident(bytes[start - 1])) || (end < bytes.len() && is_ident(bytes[end]))
        {
            continue;
        }
        // Parse `Seg ( :: Seg )*`, tolerating the spaces token printing inserts.
        let rest = &text[end..];
        let mut segments: Vec<&str> = Vec::new();
        let mut cursor = rest.trim_start();
        loop {
            let len = cursor.bytes().take_while(|b| is_ident(*b)).count();
            if len == 0 {
                break;
            }
            segments.push(&cursor[..len]);
            let after = cursor[len..].trim_start();
            match after.strip_prefix("::") {
                Some(next) => cursor = next.trim_start(),
                None => break,
            }
        }
        let Some(last) = segments.last() else {
            continue;
        };
        if !LOGICALLY_DYN_COMPATIBLE.contains(last) {
            return Some(segments.join("::"));
        }
    }
    None
}

pub(super) fn validate_forbidden_dyn_in_specs(tcx: TyCtxt<'_>) -> Vec<FrontendCheckError> {
    if local_crate_is_spec_library(tcx) {
        return Vec::new();
    }
    let mut errors = Vec::new();
    // A closure's contract is seen twice (as the closure owner's own
    // attributes and as a node of the enclosing body): report it once.
    let mut seen: std::collections::HashSet<(Span, String)> = std::collections::HashSet::new();
    for owner in tcx.hir_body_owners() {
        // Specification type-check closures are neither program code nor
        // specifications the verifier reads (see `spec_typecheck`).
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, owner) {
            continue;
        }
        for clause in spec_clauses_of_body_owner(tcx, owner) {
            if let Some(trait_path) = find_forbidden_dyn_trait(&clause.text) {
                if !seen.insert((clause.span, trait_path.clone())) {
                    continue;
                }
                errors.push(FrontendCheckError {
                    span: clause.span,
                    message: format!(
                        "forbidden dyn type: dyn {trait_path} (dyn support is currently minimal, please open an issue to improve this feature)"
                    ),
                });
            }
        }
    }
    errors
}

#[cfg(test)]
mod tests {
    use super::{
        derived_name_bases, find_forbidden_dyn_trait, is_plain_ident,
        spec_text_identifier_occurrences,
    };

    #[test]
    fn derived_name_peeling() {
        assert_eq!(derived_name_bases("x_current"), vec!["x"]);
        let bases = derived_name_bases("old_x_current_view");
        for base in ["old_x_current", "old_x", "x_current", "x"] {
            assert!(bases.contains(&base), "{base} missing from {bases:?}");
        }
        assert_eq!(derived_name_bases("v_ssa_2"), vec!["v"]);
        assert_eq!(derived_name_bases("x_final_old"), vec!["x_final", "x"]);
        assert!(derived_name_bases("counter").is_empty());
        assert!(derived_name_bases("_view").is_empty());
        // Review probes d1 / d2 / d5: a first-match peel never reached these.
        assert!(derived_name_bases("old_a_id_current").contains(&"a_id"));
        assert!(derived_name_bases("old_view_current").contains(&"view"));
        assert!(derived_name_bases("final_current_view").contains(&"current"));
    }

    /// Every derived-name constructor the encoder uses, as a composition of
    /// unit derivations. Producers (grep `format!("{..}_current")` etc. over
    /// crates/*/src): trust-wp-core `smt/encoding/var_collect.rs`
    /// (`{n}_current`, `{n}_final`, `{n}_view`, `{n}_current_view`,
    /// `{n}_final_view`, `old_{n}`, `old_{n}_current`, `old_{n}_final`,
    /// `old_{n}_view`, `old_{n}_current_view`, `old_{n}_final_view`, `{v}_id`),
    /// `sort_inference.rs` (`old_{n}`, `{n}_view`); trust-wp-ay
    /// `sort_context/derived_names.rs` (`DerivedKind::format_name` /
    /// `format_chain`: `_view`, `_current`, `_final`, `_prime`, `old_`,
    /// `final_`), `sort_context/mod.rs` (`{b}_id`), `verify/mut_borrow`
    /// (`{f}_current`, `{f}_final`, `{b}_id`, `final_{b}_view`),
    /// `verify/pipeline.rs` (`{b}_final` repeated), `seq/coercion.rs` and
    /// `closure_axioms/fn_laws.rs` (`{n}_view`, `old_{cap}`); trust-wp-driver
    /// `loop_verify` (`{s}_prime`, `{p}_final_old`),
    /// `proof_assert_extract/view_normalization.rs` (`{n}_current`,
    /// `{n}_final`), `verification/contract_transform.rs` (`{n}_ssa_{k}`).
    const UNIT_DERIVATIONS: &[fn(&str) -> String] = &[
        |b| format!("{b}_view"),
        |b| format!("{b}_current"),
        |b| format!("{b}_final"),
        |b| format!("{b}_prime"),
        |b| format!("{b}_id"),
        |b| format!("{b}_old"),
        |b| format!("{b}_ssa_0"),
        |b| format!("{b}_ssa_17"),
        |b| format!("old_{b}"),
        |b| format!("final_{b}"),
    ];

    /// Base spellings that are themselves spelled like derivation tokens,
    /// the shapes a first-match peel mishandled.
    const TRICKY_BASES: &[&str] = &[
        "x",
        "a_id",
        "view",
        "old",
        "final",
        "current",
        "prime",
        "id",
        "ssa",
        "x_current",
        "old_a",
        "final_x",
        "a_ssa_1",
        "old_view",
        "x_final_old",
        "_",
        "_x",
        "x_",
        "result",
        "self",
        "ssa_3",
        "_ssa_2",
        "old_old",
        "view_view",
    ];

    /// No source VALUE name can equal an encoder-derived name of another
    /// value name without being refused: for every base and every chain of up
    /// to three unit derivations, peeling the derived spelling reaches the
    /// base, so `validate_derived_name_aliases` finds it in `bases`.
    #[test]
    fn every_encoder_derived_spelling_peels_back_to_its_base() {
        fn check(base: &str, spelled: &str) {
            assert!(
                derived_name_bases(spelled).contains(&base),
                "`{spelled}` (derived from `{base}`) does not peel back to it: {:?}",
                derived_name_bases(spelled)
            );
        }
        for base in TRICKY_BASES {
            for d1 in UNIT_DERIVATIONS {
                let n1 = d1(base);
                check(base, &n1);
                for d2 in UNIT_DERIVATIONS {
                    let n2 = d2(&n1);
                    check(base, &n2);
                    for d3 in UNIT_DERIVATIONS {
                        check(base, &d3(&n2));
                    }
                }
            }
            // Explicit compound producers.
            for spelled in [
                format!("old_{base}_current_view"),
                format!("old_{base}_final_view"),
                format!("final_{base}_view"),
                format!("{base}_final_final_final_final"),
                format!("{base}_final_old"),
                format!("old_{base}_ssa_4_current"),
            ] {
                check(base, &spelled);
            }
        }
    }

    #[test]
    fn spec_identifier_item_positions() {
        let occ = spec_text_identifier_occurrences(
            "forall < x_current : u32 > x_current == v . len () && f (a) && m :: C && 0 .. n",
        );
        let flags: Vec<(&str, bool)> = occ;
        assert_eq!(
            flags,
            vec![
                ("forall", false),
                ("x_current", false),
                ("u32", false),
                ("x_current", false),
                ("v", false),
                ("len", true),
                ("f", true),
                ("a", false),
                ("m", true),
                ("C", false),
                ("n", false),
            ]
        );
        assert_eq!(
            spec_text_identifier_occurrences("x_current()"),
            vec![("x_current", true)]
        );
    }

    #[test]
    fn forbidden_dyn_detection() {
        assert_eq!(
            find_forbidden_dyn_trait("forall < x : dyn False > x . falso () == ()"),
            Some("False".to_string())
        );
        assert_eq!(
            find_forbidden_dyn_trait("forall<x: &dyn my::Tr> true"),
            Some("my::Tr".to_string())
        );
        assert_eq!(
            find_forbidden_dyn_trait("x : dyn core :: fmt :: Debug"),
            None
        );
        assert_eq!(find_forbidden_dyn_trait("dynamic == dyn_x"), None);
        assert_eq!(find_forbidden_dyn_trait("x@ == 1"), None);
    }

    #[test]
    fn plain_ident() {
        assert!(is_plain_ident("x"));
        assert!(is_plain_ident("_len2"));
        assert!(!is_plain_ident("x@"));
        assert!(!is_plain_ident("j-i"));
        assert!(!is_plain_ident("0"));
    }
}
