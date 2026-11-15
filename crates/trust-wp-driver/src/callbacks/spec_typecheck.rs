// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Erase specification type-check closures from MIR.
//!
//! `trust-wp-macros` places every contract clause, lowered to Rust, inside a
//! closure marked `#[doc = "__trust_wp_spec_tc"]` so that rustc TYPE-CHECKS
//! the clause exactly as Creusot's attribute expansion makes it type-check
//! (`trust-wp-macros/src/spec_tc`). The verifier never reads these closures:
//! the clause text still comes from the `trust-wp:` doc markers.
//!
//! Pearlite is not subject to Rust ownership, so the closures must not be
//! borrow-checked, and they must not change the MIR the verifier analyses.
//! This mirrors Creusot's `cleanup_spec_closures` (a `mir_built` override):
//!
//! * the body of a marked closure — and of every closure nested inside one
//!   (quantifier binders, logical mappings) — is replaced by a bare `return`;
//! * in every other body, each statement that constructs a marked closure is
//!   turned into a `Nop`, as are the statements that only feed or mention
//!   that closure value (its capture temporaries, `StorageLive/Dead`,
//!   `PlaceMention`, `FakeRead`). User variables are never touched, so a
//!   variable captured by value is not moved. Statements become `Nop` rather
//!   than being removed, so every other statement keeps its `Location`.
//!
//! The result is MIR identical to the pre-vehicle MIR up to `Nop`s and unused
//! local declarations. This only ever removes code the macros inserted for
//! type checking; it can neither add an assumption nor discharge an
//! obligation.

use std::collections::HashSet;

use rustc_ast::{attr::AttributeExt, token::DocFragmentKind};
use rustc_attr_ir::{Attribute, AttributeKind, LangItem};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    HirId,
};
use rustc_middle::{
    mir::{AggregateKind, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{self, TyCtxt},
};
use rustc_span::{symbol::kw, ExpnKind, Span};

/// Doc marker emitted by `trust-wp-macros::spec_tc::SPEC_TC_MARKER`.
pub(crate) const SPEC_TC_MARKER: &str = "__trust_wp_spec_tc";

/// Name prefix of the sibling helper `trust-wp-macros` emits for a contract
/// on a bodyless trait method. Reserved: a user item may not use it.
pub(crate) const SPEC_TC_HELPER_PREFIX: &str = "__trust_wp_spec_tc_";

/// Crate name of the proc-macro crate that emits the marker.
const MACROS_CRATE: &str = "trust_wp_macros";

/// The marker value a logic body's type-check closure carries in place of
/// `SPEC_TC_MARKER` (`trust-wp-macros::spec_tc::SPEC_TC_LOGIC_BODY_MARKER`).
/// It is honoured, and refused when forged, exactly as `SPEC_TC_MARKER` is.
const SPEC_TC_LOGIC_BODY_MARKER: &str = "__trust_wp_spec_tc:logic_body";

/// Prefix of the doc attribute `trust-wp-macros` puts on a clause's
/// type-check body beside the marker (`spec_tc::clause_tag_attr`):
/// `<prefix><kind>:<text>`, the clause's `trust-wp:<kind>:` marker kind and
/// exactly the text that marker carries.
const SPEC_TC_CLAUSE_TAG: &str = "__trust_wp_spec_tc_clause:";

fn is_marker_attr(attr: &Attribute) -> bool {
    crate::attr_utils::doc_marker_str(attr)
        .is_some_and(|v| v.as_str() == SPEC_TC_MARKER || v.as_str() == SPEC_TC_LOGIC_BODY_MARKER)
}

/// The clause an honoured type-check body type-checks, as (marker kind,
/// marker text); `None` for a body that is not honoured or carries no tag (a
/// logic body's closure). Only read on an honoured body, which the macros
/// build whole, so the tag is theirs.
pub(crate) fn clause_tag(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<(String, String)> {
    if !is_spec_tc_body(tcx, def_id) || !has_spec_tc_marker(tcx, def_id) {
        return None;
    }
    let mut tags = tcx
        .hir_attrs(tcx.local_def_id_to_hir_id(def_id))
        .iter()
        .filter_map(crate::attr_utils::doc_marker_str)
        .filter_map(|value| {
            let (kind, text) = value
                .as_str()
                .strip_prefix(SPEC_TC_CLAUSE_TAG)?
                .split_once(':')?;
            Some((kind.to_string(), text.to_string()))
        });
    let tag = tags.next()?;
    tags.next().is_none().then_some(tag)
}

/// The fn-level `requires` and `ensures` clauses `owner` carries, as (kind,
/// text): every `trust-wp:<kind>:` doc marker and every contract attribute
/// left unexpanded, as the contract discovery reads them.
pub(crate) fn clause_markers(tcx: TyCtxt<'_>, owner: DefId) -> Vec<(String, String)> {
    let Some(local) = owner.as_local() else {
        return Vec::new();
    };
    let attrs = tcx.hir_attrs(tcx.local_def_id_to_hir_id(local));
    ["requires", "ensures"]
        .into_iter()
        .flat_map(|kind| {
            crate::attr_utils::get_contract_attrs_from_doc(attrs, kind)
                .into_iter()
                .chain(crate::attr_utils::get_contract_attrs_from_proc_macro(
                    attrs, kind,
                ))
                .map(move |text| (kind.to_string(), text))
        })
        .collect()
}

/// The type-check closure `trust-wp-macros` emits for the body of the logic
/// function `def_id` (`spec_tc::logic_body_statement`): the one closure among
/// the function body's own statements that carries the logic-body marker,
/// every marker on it macro-emitted. `None` when there is not exactly one.
pub(crate) fn logic_body_tc_closure<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<&'tcx rustc_hir::Closure<'tcx>> {
    let body = tcx.hir_maybe_body_owned_by(def_id)?;
    let rustc_hir::ExprKind::Block(block, _) = body.value.kind else {
        return None;
    };
    let mut closures = block.stmts.iter().filter_map(|stmt| {
        let rustc_hir::StmtKind::Let(local) = stmt.kind else {
            return None;
        };
        let rustc_hir::ExprKind::Closure(closure) = local.init?.kind else {
            return None;
        };
        let marks_a_body = tcx
            .hir_attrs(tcx.local_def_id_to_hir_id(closure.def_id))
            .iter()
            .filter_map(crate::attr_utils::doc_marker_str)
            .any(|value| value.as_str() == SPEC_TC_LOGIC_BODY_MARKER);
        (marks_a_body && has_spec_tc_marker(tcx, closure.def_id)).then_some(closure)
    });
    let closure = closures.next()?;
    closures.next().is_none().then_some(closure)
}

/// Every honoured specification type-check body of the crate that type-checks
/// something other than a logic body: a marked closure (a contract clause, a
/// `proof_assert!`, a loop invariant) not nested in another, or a
/// trait-signature helper. A logic body's closure is read against the parsed
/// body instead (`logic::call_resolution::settle_spelled_calls`).
pub(crate) fn clause_tc_bodies(tcx: TyCtxt<'_>) -> Vec<LocalDefId> {
    // Every local definition, closures among them (`hir_crate_items`'
    // `definitions` holds only the item owners).
    tcx.iter_local_def_id()
        .filter(|&local| match tcx.def_kind(local) {
            DefKind::Closure => {
                has_spec_tc_marker(tcx, local)
                    && !is_spec_tc_body(tcx, tcx.local_parent(local))
                    && !tcx
                        .hir_attrs(tcx.local_def_id_to_hir_id(local))
                        .iter()
                        .filter_map(crate::attr_utils::doc_marker_str)
                        .any(|value| value.as_str() == SPEC_TC_LOGIC_BODY_MARKER)
            }
            DefKind::AssocFn => is_spec_tc_trait_helper(tcx, local),
            _ => false,
        })
        .collect()
}

/// `span` was produced by a macro defined in `trust-wp-macros`: the
/// innermost expansion that created its tokens is a (non-local) proc macro
/// of that crate. A user-written token keeps its source span (no
/// expansion), and a token produced by a user `macro_rules!` or another
/// proc-macro crate names that macro instead.
pub(crate) fn span_is_from_trust_wp_macros(tcx: TyCtxt<'_>, span: Span) -> bool {
    if !span.from_expansion() {
        return false;
    }
    let data = span.ctxt().outer_expn_data();
    matches!(data.kind, ExpnKind::Macro(..))
        && data.macro_def_id.is_some_and(|did| {
            !did.is_local() && tcx.crate_name(did.krate).as_str() == MACROS_CRATE
        })
}

/// The marker attribute was emitted by `trust-wp-macros` (which builds it
/// entirely at `Span::call_site()`): both the attribute's span and, when
/// recorded, the span of its string value come from that crate's
/// expansion. A `#[doc = "__trust_wp_spec_tc"]` written in user source —
/// or pasted through a user macro — is not.
pub(crate) fn marker_is_from_trust_wp_macros(tcx: TyCtxt<'_>, attr: &Attribute) -> bool {
    let (attr_span, value_span) = match attr {
        Attribute::Parsed(AttributeKind::DocComment {
            kind: DocFragmentKind::Raw(value_span),
            span,
            ..
        }) => (*span, Some(*value_span)),
        Attribute::Parsed(AttributeKind::DocComment { .. }) => {
            // A `///` doc comment: never what the macros emit.
            return false;
        }
        Attribute::Tool(item) | Attribute::DeriveHelper(item) => (item.span, attr.value_span()),
        Attribute::Parsed(_) => return false,
    };
    span_is_from_trust_wp_macros(tcx, attr_span)
        && value_span.is_none_or(|sp| span_is_from_trust_wp_macros(tcx, sp))
}

/// Every marker on `def_id` is macro-emitted, and there is at least one.
/// A single forged marker disqualifies the carrier.
fn has_spec_tc_marker(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let hir_id = tcx.local_def_id_to_hir_id(def_id);
    let mut markers = tcx
        .hir_attrs(hir_id)
        .iter()
        .filter(|a| is_marker_attr(a))
        .peekable();
    markers.peek().is_some() && markers.all(|attr| marker_is_from_trust_wp_macros(tcx, attr))
}

/// The sibling helper `trust-wp-macros` emits for a contract on a bodyless
/// trait method (`spec_tc::trait_signature_helper`), recognised by ALL of:
/// an associated fn of a trait (not of an impl) with a default body, named
/// `__trust_wp_spec_tc_*`, with a `Self: Sized` where-clause, carrying only
/// macro-emitted markers. Anything short of that is user code.
pub(crate) fn is_spec_tc_trait_helper(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    if tcx.def_kind(def_id) != DefKind::AssocFn
        || tcx.def_kind(tcx.local_parent(def_id)) != DefKind::Trait
    {
        return false;
    }
    if !tcx
        .opt_item_name(def_id.to_def_id())
        .is_some_and(|name| name.as_str().starts_with(SPEC_TC_HELPER_PREFIX))
    {
        return false;
    }
    let rustc_hir::Node::TraitItem(item) = tcx.hir_node_by_def_id(def_id) else {
        return false;
    };
    if !matches!(
        item.kind,
        rustc_hir::TraitItemKind::Fn(_, rustc_hir::TraitFn::Provided(_))
    ) {
        return false;
    }
    let self_sized = tcx
        .clauses_of(def_id)
        .clauses
        .iter()
        .any(|(clause, _)| {
            clause.as_trait_clause().is_some_and(|tc| {
                let tc = tc.skip_binder();
                tcx.is_lang_item(tc.def_id(), LangItem::Sized)
                    && matches!(tc.self_ty().kind(), ty::Param(p) if p.index == 0 && p.name == kw::SelfUpper)
            })
        });
    self_sized && has_spec_tc_marker(tcx, def_id)
}

/// A macro-emitted marked closure, a macro-emitted trait-signature helper
/// method, or a closure (transitively) nested inside either.
pub(crate) fn is_spec_tc_body(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let mut cur = def_id;
    loop {
        match tcx.def_kind(cur) {
            DefKind::Closure => {
                if has_spec_tc_marker(tcx, cur) {
                    return true;
                }
                cur = tcx.local_parent(cur);
            }
            DefKind::AssocFn => return is_spec_tc_trait_helper(tcx, cur),
            _ => return false,
        }
    }
}

/// Frontend refusal: every `__trust_wp_spec_tc` marker in the crate that
/// the driver would NOT honour (written in user source, or on anything but
/// a marked closure / trait-signature helper), and every user item using
/// the reserved `__trust_wp_spec_tc_` name prefix. Honouring a forged
/// marker would erase the carrier's MIR and skip its verification, so a
/// forged marker is a hard error rather than an inert doc string.
pub(crate) fn forged_spec_tc_markers(tcx: TyCtxt<'_>) -> Vec<(Span, String)> {
    let mut errors = Vec::new();
    let crate_items = tcx.hir_crate_items(());
    for owner in crate_items.owners() {
        let attr_map = tcx.hir_attr_map(owner);
        for (local_id, attrs) in attr_map.map.iter() {
            let Some(attr) = attrs.iter().find(|a| is_marker_attr(a)) else {
                continue;
            };
            let hir_id = HirId {
                owner,
                local_id: *local_id,
            };
            let honoured = match tcx.hir_node(hir_id) {
                rustc_hir::Node::Expr(rustc_hir::Expr {
                    kind: rustc_hir::ExprKind::Closure(c),
                    ..
                }) => has_spec_tc_marker(tcx, c.def_id),
                rustc_hir::Node::TraitItem(item) => {
                    is_spec_tc_trait_helper(tcx, item.owner_id.def_id)
                }
                _ => false,
            };
            if !honoured {
                errors.push((
                    crate::attr_utils::attr_span(attr).unwrap_or_else(|| tcx.hir_span(hir_id)),
                    format!(
                        "trust-wp: `#[doc = \"{SPEC_TC_MARKER}\"]` is reserved for \
                         specification type-check code generated by trust-wp's contract \
                         macros; it may not be written in user code"
                    ),
                ));
            }
        }
    }
    for local_def_id in crate_items.definitions() {
        let Some(name) = tcx.opt_item_name(local_def_id.to_def_id()) else {
            continue;
        };
        if name.as_str().starts_with(SPEC_TC_HELPER_PREFIX)
            && !is_spec_tc_trait_helper(tcx, local_def_id)
        {
            errors.push((
                tcx.def_span(local_def_id),
                format!(
                    "trust-wp: the name prefix `{SPEC_TC_HELPER_PREFIX}` is reserved for \
                     specification type-check helpers generated by trust-wp's contract \
                     macros (`{name}`)"
                ),
            ));
        }
    }
    errors
}

/// HIR guard for driver frontend walkers: a type-check closure is not user
/// program code and not a specification the verifier reads, so no frontend
/// diagnostic may be derived from (or suppressed by) its contents.
pub(crate) fn is_spec_tc_closure_expr(tcx: TyCtxt<'_>, expr: &rustc_hir::Expr<'_>) -> bool {
    matches!(expr.kind, rustc_hir::ExprKind::Closure(c) if has_spec_tc_marker(tcx, c.def_id))
}

/// The block `trust-wp-macros` wraps around a loop or closure that carries a
/// type-checked clause: `{ let _ = <marked closure>; ..; <tail> }`, every
/// statement a type-check `let`. Returns the tail — the user's own loop or
/// closure expression — with nested wrappers stripped; `expr` itself when it
/// is not such a wrapper. A block with any other statement, or without a
/// tail, is user code and is returned unchanged.
pub(crate) fn strip_spec_tc_wrapper<'hir>(
    tcx: TyCtxt<'_>,
    expr: &'hir rustc_hir::Expr<'hir>,
) -> &'hir rustc_hir::Expr<'hir> {
    let mut cur = expr;
    loop {
        let rustc_hir::ExprKind::Block(block, None) = cur.kind else {
            return cur;
        };
        let Some(tail) = block.expr else {
            return cur;
        };
        if block.stmts.is_empty()
            || !block.stmts.iter().all(|stmt| match stmt.kind {
                rustc_hir::StmtKind::Let(local) => local
                    .init
                    .is_some_and(|init| is_spec_tc_closure_expr(tcx, init)),
                _ => false,
            })
        {
            return cur;
        }
        cur = tail;
    }
}

fn is_spec_tc_closure(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    def_id.as_local().is_some_and(|local| {
        matches!(tcx.def_kind(local), DefKind::Closure) && has_spec_tc_marker(tcx, local)
    })
}

/// Test harnesses that compile fixtures with `--cfg trust_wp` must erase the
/// type-check closures exactly as `TrustWpCallbacks::config` does, or those
/// closures reach borrowck (E0507/E0596 on specification code the production
/// driver never borrow-checks). Call inside `config.override_queries`.
#[cfg(test)]
pub(crate) fn install_spec_tc_mir_built_erasure(providers: &mut rustc_middle::util::Providers) {
    providers.queries.mir_built = |tcx, def_id| {
        let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.mir_built)(tcx, def_id);
        let mut mir = mir.steal();
        cleanup_spec_tc_closures(tcx, def_id, &mut mir);
        crate::mir_analysis::binding_identity::rename_shadowed_bindings(tcx, def_id, &mut mir);
        tcx.alloc_steal_mir(mir)
    };
}

/// Apply the cleanup to a freshly built body.
pub(crate) fn cleanup_spec_tc_closures<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &mut Body<'tcx>,
) {
    if is_spec_tc_body(tcx, def_id) {
        // Keep the entry block (and its source info), drop everything else.
        let blocks = body.basic_blocks_mut();
        blocks.raw.truncate(1);
        if let Some(entry) = blocks.raw.first_mut() {
            entry.statements.clear();
            entry.terminator_mut().kind = TerminatorKind::Return;
        }
        return;
    }

    // Locals holding a marked closure value, and capture temporaries moved
    // into its construction.
    let mut erased: HashSet<Local> = HashSet::new();
    let mut found = false;
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            if let StatementKind::Assign((
                place,
                Rvalue::Aggregate(AggregateKind::Closure(cdef, _), ops),
            )) = &stmt.kind
            {
                if is_spec_tc_closure(tcx, *cdef) {
                    found = true;
                    if let Some(local) = place.as_local() {
                        erased.insert(local);
                    }
                    for op in ops {
                        if let Operand::Move(p) = op {
                            if let Some(local) = p.as_local() {
                                erased.insert(local);
                            }
                        }
                    }
                }
            }
        }
    }
    if !found {
        return;
    }
    // Never erase a user variable (or the return place / arguments).
    erased.retain(|local| {
        local.as_usize() > body.arg_count && !body.local_decls[*local].is_user_variable()
    });
    for data in body.basic_blocks_mut().iter_mut() {
        for stmt in &mut data.statements {
            let erase = match &stmt.kind {
                StatementKind::Assign((place, rvalue)) => {
                    matches!(rvalue, Rvalue::Aggregate(AggregateKind::Closure(cdef, _), _) if is_spec_tc_closure(tcx, *cdef))
                        || erased.contains(&place.local)
                }
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                    erased.contains(local)
                }
                StatementKind::PlaceMention(place) => erased.contains(&place.local),
                StatementKind::FakeRead((_, place)) => erased.contains(&place.local),
                _ => false,
            };
            if erase {
                stmt.make_nop(true);
            }
        }
    }
}
