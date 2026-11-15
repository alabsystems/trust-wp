// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! One name per binding (D-237).
//!
//! The verifier states facts and reads assertions over SOURCE NAMES: a MIR
//! local is translated to `Var(<its debug name>)`, a program-point
//! substitution is keyed by that name, and the assertion's text names it
//! again. When a body binds one name to more than one local (a shadowing
//! `let`, a block-local, a branch- or loop-body `let`), the name stops saying
//! which binding a term means: a clone fact about the first `r` was read as a
//! fact about the second (`let r2 = r.clone(); let r = Rc::new(2);
//! proof_assert!(r == r2)`), and a ghost write `*g = *h` read the visible `h`
//! instead of the one it copied.
//!
//! So every body is renamed before anything reads it. In `mir_built`, each
//! debug binding of a name its function binds more than once (by any binding
//! pattern of the function or of a closure in it, or by two places of the
//! body) is given its own name, `{name}$shadow{N}` with `N` its HIR binding
//! pattern's local id (`{name}$shadow_l{local}` where no pattern accounts for
//! it). A closure's capture of a binding takes that binding's name, so a value
//! the closure's body reads is the parent's binding it captured. A parameter
//! keeps its name: a contract names its parameters, and no body binding can
//! rename them. A renamed name contains the synthesized sigil, so no source
//! text can spell it: a term that reaches one has come from that binding and
//! from nowhere else.
//!
//! Text that names a binding (a `proof_assert!`, a loop invariant, a ghost
//! write recovered from HIR) is resolved where it stands
//! ([`visible_binding`]): the binding the name denotes at that MIR source
//! scope is the innermost one whose visibility scope encloses it and whose
//! identifier has the text's hygiene, exactly as Rust resolves it. Hygiene is
//! part of the name (D-238): a `let x` a `macro_rules!` expansion introduces is
//! not the `x` its caller writes after the macro call, though its scope
//! encloses that text. A name whose binding cannot be told apart is refused,
//! never guessed.
//!
//! A closure's contract is text written at the closure, and every call site
//! reads it in the caller's body, where a parameter keeps its source name. So
//! a closure clause that names a shadowed binding is rewritten at discovery to
//! name the capture by a name only the capture substitution knows, or refused
//! ([`closure_clause_name`]).

use std::collections::{HashMap, HashSet};

use rustc_hir::{
    self as hir,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
    HirId,
};
use rustc_middle::{
    hir::nested_filter,
    mir::{Body, Local, SourceScope, VarDebugInfoContents},
    ty::TyCtxt,
};
use rustc_span::{hygiene::SyntaxContext, Span, Symbol};
use trust_wp_core::formula::{rename_free_var, CaptureAvoidingSubstOptions, PureExpr};

/// The infix of a renamed shadowed binding's debug name.
pub(crate) const SHADOWED_BINDING_INFIX: &str = "$shadow";

/// The source name a debug name was renamed from (the name itself when it
/// was not renamed).
pub(crate) fn source_name_of(debug_name: &str) -> &str {
    match debug_name.rfind(SHADOWED_BINDING_INFIX) {
        Some(at) => {
            let suffix = &debug_name[at + SHADOWED_BINDING_INFIX.len()..];
            let digits = suffix.strip_prefix("_l").unwrap_or(suffix);
            if !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()) {
                &debug_name[..at]
            } else {
                debug_name
            }
        }
        None => debug_name,
    }
}

/// Whether `debug_name` is a renamed shadowed binding.
pub(crate) fn is_renamed_binding(debug_name: &str) -> bool {
    source_name_of(debug_name).len() != debug_name.len()
}

/// Whether `name` is an identifier a source binding has: a Rust-style
/// identifier, or the name a shadowed one was renamed to.
pub(crate) fn is_binding_ident(name: &str) -> bool {
    let mut chars = source_name_of(name).chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

/// The name of the binding `hir_id` of `name`: one per HIR binding, so a
/// closure's capture of it and the parent's local share it.
fn hir_binding_name(name: &str, hir_id: HirId) -> String {
    format!("{name}{SHADOWED_BINDING_INFIX}{}", hir_id.local_id.as_u32())
}

/// The name of a debug binding no HIR binding pattern accounts for: its own,
/// which nothing else (no capture, no text) can name.
fn local_binding_name(name: &str, local: Local) -> String {
    format!("{name}{SHADOWED_BINDING_INFIX}_l{}", local.as_u32())
}

/// The binding patterns of one typeck root: the function and every closure
/// in it, which share its HIR owner (and so its `HirId` local ids).
struct OwnerBindings {
    /// Names bound by more than one binding pattern of the owner.
    shadowed: HashSet<Symbol>,
    /// Every name a binding pattern of the owner binds.
    bound: HashSet<Symbol>,
    /// Binding patterns that are a parameter of the function or of a closure.
    params: HashSet<HirId>,
    /// Binding pattern span (whole pattern, and its identifier) -> binding.
    by_span: HashMap<Span, Vec<HirId>>,
    /// Binding -> the hygiene of its IDENTIFIER (D-239). Rust resolves a
    /// local by its identifier's span; a binding pattern's own span (`mut x`,
    /// `ref x`, `x @ ..`) takes the context of tokens the identifier does not
    /// have (a macro's `mut`), so it says nothing about the name's hygiene.
    ident_hygiene: HashMap<HirId, SyntaxContext>,
}

struct BindingCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    count: HashMap<Symbol, usize>,
    params: HashSet<HirId>,
    by_span: HashMap<Span, Vec<HirId>>,
    ident_hygiene: HashMap<HirId, SyntaxContext>,
}

impl<'tcx> Visitor<'tcx> for BindingCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_body(&mut self, body: &hir::Body<'tcx>) {
        for param in body.params {
            param.pat.each_binding(|_, hir_id, _, _| {
                self.params.insert(hir_id);
            });
        }
        intravisit::walk_body(self, body);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        // A specification type-check closure is erased before borrowck and
        // read by no lane: its bindings (`|result| ..`) shadow nothing.
        if crate::callbacks::spec_typecheck::is_spec_tc_closure_expr(self.tcx, expr) {
            return;
        }
        intravisit::walk_expr(self, expr);
    }

    fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
        if let hir::PatKind::Binding(_, hir_id, ident, _) = pat.kind {
            *self.count.entry(ident.name).or_default() += 1;
            self.ident_hygiene.insert(hir_id, name_hygiene(ident.span));
            self.by_span.entry(pat.span).or_default().push(hir_id);
            if ident.span != pat.span {
                self.by_span.entry(ident.span).or_default().push(hir_id);
            }
        }
        intravisit::walk_pat(self, pat);
    }
}

fn owner_bindings(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<OwnerBindings> {
    let root = tcx.typeck_root_def_id(def_id.to_def_id()).as_local()?;
    let body_id = tcx.hir_node_by_def_id(root).body_id()?;
    let mut collector = BindingCollector {
        tcx,
        count: HashMap::new(),
        params: HashSet::new(),
        by_span: HashMap::new(),
        ident_hygiene: HashMap::new(),
    };
    collector.visit_body(tcx.hir_body(body_id));
    Some(OwnerBindings {
        bound: collector.count.keys().copied().collect(),
        shadowed: collector
            .count
            .into_iter()
            .filter(|(_, count)| *count > 1)
            .map(|(name, _)| name)
            .collect(),
        params: collector.params,
        by_span: collector.by_span,
        ident_hygiene: collector.ident_hygiene,
    })
}

impl OwnerBindings {
    /// The one binding whose pattern has `span`.
    fn binding_at(&self, span: Span) -> Option<HirId> {
        match self.by_span.get(&span).map(Vec::as_slice) {
            Some([hir_id]) => Some(*hir_id),
            _ => None,
        }
    }

    /// The hygiene of the identifier of the binding a debug entry at `span`
    /// declares (D-239): a local's or a parameter's entry has its binding
    /// pattern's span, a capture's its root variable's identifier span; both
    /// are keys of `by_span`. `None` when no binding pattern has that span, or
    /// when the bindings that do have identifiers of different hygiene: the
    /// caller then cannot tell which name the entry binds.
    fn hygiene_at(&self, span: Span) -> Option<SyntaxContext> {
        let mut hygiene = None;
        for hir_id in self.by_span.get(&span)? {
            let ctxt = *self.ident_hygiene.get(hir_id)?;
            match hygiene {
                None => hygiene = Some(ctxt),
                Some(seen) if seen == ctxt => {}
                Some(_) => return None,
            }
        }
        hygiene
    }
}

/// The hygiene of each debug entry's binding identifier, in `var_debug_info`
/// order (D-239). It is read from the HIR binding the entry declares, never
/// from the entry's own span, which is the binding PATTERN's: `let mut $n`
/// in a `macro_rules!` expansion has the macro's hygiene on `mut`, and the
/// caller's on `$n`, the name. `None` is an entry whose identifier cannot be
/// found: [`visible_binding`] refuses a name with such a binding rather
/// than guess its hygiene.
fn debug_hygienes(body: &Body<'_>) -> Vec<Option<SyntaxContext>> {
    let owner = body.source.def_id().as_local().and_then(|def_id| {
        rustc_middle::ty::tls::with_opt(|tcx| tcx.and_then(|tcx| owner_bindings(tcx, def_id)))
    });
    body.var_debug_info
        .iter()
        .map(|debug| {
            owner
                .as_ref()
                .and_then(|owner| owner.hygiene_at(debug.source_info.span))
        })
        .collect()
}

/// The debug name every body gives the binding `hir_id`, named `name`:
/// `name` itself unless the owner binds `name` more than once and the
/// binding is not a parameter (a contract names its parameters).
fn binding_debug_name(owner: &OwnerBindings, name: Symbol, hir_id: HirId) -> String {
    if owner.shadowed.contains(&name) && !owner.params.contains(&hir_id) {
        hir_binding_name(name.as_str(), hir_id)
    } else {
        name.to_string()
    }
}

/// Give every binding of a name its function binds more than once a name of
/// its own (see the module docs). Run on every body in `mir_built`, before
/// any analysis reads it. A binding is named after its HIR binding pattern,
/// so a closure's capture of it is named as the parent's local is.
pub(crate) fn rename_shadowed_bindings<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &mut Body<'tcx>,
) {
    let owner = owner_bindings(tcx, def_id);
    let captures: Vec<(Symbol, HirId)> = if tcx.is_closure_like(def_id.to_def_id()) {
        tcx.closure_captures(def_id)
            .iter()
            .map(|capture| (capture.var_ident.name, capture.get_root_variable()))
            .collect()
    } else {
        Vec::new()
    };
    // Names this body binds to more than one place: renamed even where the
    // HIR does not say why (two locals one pattern accounts for keep sharing
    // it, as they did).
    let mut keys: HashMap<Symbol, HashSet<String>> = HashMap::new();
    for debug in &body.var_debug_info {
        let key = match (&debug.value, owner.as_ref()) {
            (VarDebugInfoContents::Place(place), Some(owner)) if place.projection.is_empty() => {
                owner
                    .binding_at(debug.source_info.span)
                    .map_or_else(|| format!("{place:?}"), |hir_id| format!("{hir_id:?}"))
            }
            (VarDebugInfoContents::Place(place), _) => format!("{place:?}"),
            (VarDebugInfoContents::Const(constant), _) => format!("const {constant:?}"),
        };
        keys.entry(debug.name).or_default().insert(key);
    }
    for debug in &mut body.var_debug_info {
        let name = debug.name;
        if name.as_str() == "_" || is_renamed_binding(name.as_str()) {
            continue;
        }
        let shadowed_in_owner = owner
            .as_ref()
            .is_some_and(|owner| owner.shadowed.contains(&name));
        let shadowed_here = keys.get(&name).is_some_and(|keys| keys.len() > 1);
        if !shadowed_in_owner && !shadowed_here {
            continue;
        }
        if debug.argument_index.is_some() {
            continue;
        }
        let VarDebugInfoContents::Place(place) = &debug.value else {
            continue;
        };
        let renamed = if place.projection.is_empty() {
            match owner.as_ref().and_then(|owner| {
                owner
                    .binding_at(debug.source_info.span)
                    .map(|id| (owner, id))
            }) {
                Some((owner, hir_id)) if owner.params.contains(&hir_id) => continue,
                Some((owner, hir_id)) => binding_debug_name(owner, name, hir_id),
                None => local_binding_name(name.as_str(), place.local),
            }
        } else {
            // A capture: named as the binding it captures is named.
            let mut roots = captures
                .iter()
                .filter(|(capture_name, _)| *capture_name == name)
                .map(|(_, root)| *root);
            match (roots.next(), roots.next(), owner.as_ref()) {
                (Some(root), None, Some(owner)) => binding_debug_name(owner, name, root),
                _ => local_binding_name(name.as_str(), place.local),
            }
        };
        debug.name = Symbol::intern(&renamed);
    }
}

/// The debug name every body gives the HIR binding `root` named `name` (see
/// [`rename_shadowed_bindings`]): the parent's local and a closure's capture
/// of it alike.
pub(crate) fn hir_binding_debug_name(tcx: TyCtxt<'_>, name: &str, root: HirId) -> String {
    match owner_bindings(tcx, root.owner.def_id) {
        Some(owner) => binding_debug_name(&owner, Symbol::intern(name), root),
        None => name.to_string(),
    }
}

/// The name a closure clause reads its capture of the binding `root`, named
/// `name`, by once that capture's binding is renamed (D-238): an identifier
/// the clause parser reads as written, in the `__twp` namespace no source
/// binding may use (`creusot_frontend_checks::reserved_identifier_reason`),
/// so the only term it can come from is the closure's clause, and only the
/// capture substitution gives it a value.
pub(crate) fn capture_clause_name(name: &str, root: HirId) -> String {
    format!("__twp_cap{}_{name}", root.local_id.as_u32())
}

/// Whether a closure's clauses read its capture of the binding `root`, named
/// `name`, by [`capture_clause_name`] (D-238, D-239): exactly when the
/// function binds `name` more than once. A captured parameter keeps its name
/// in every body, but a clause is read in each CALLING body, where the name
/// may be bound otherwise (a calling closure's parameter): only the capture
/// name says it is this capture.
pub(crate) fn capture_read_apart(tcx: TyCtxt<'_>, name: &str, root: HirId) -> bool {
    owner_bindings(tcx, root.owner.def_id)
        .is_some_and(|owner| owner.shadowed.contains(&Symbol::intern(name)))
}

/// How a closure's clause reads one source name it mentions (D-238).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ClosureClauseName {
    /// Read as written: a parameter of the closure, or a name the function
    /// binds once, which every lane reads alike.
    AsWritten,
    /// A capture of a binding the bodies rename because the function binds
    /// its name more than once: read by [`capture_clause_name`].
    Capture(String),
    /// Read by no lane faithfully: the clause is refused, with this reason.
    Refused(String),
}

/// How the clauses of the closure `closure` read the source name `name`.
///
/// A closure's clause is written at the closure, but every call site reads
/// it in the caller's body, where a parameter keeps its source name (D-237):
/// a name the function binds more than once, read there as written, is the
/// parameter. A capture of such a binding is therefore named for the
/// capture alone; a name the closure does not capture, while the function
/// binds it more than once, or binds it under another hygiene than the
/// closure's, is refused.
pub(crate) fn closure_clause_name(
    tcx: TyCtxt<'_>,
    closure: LocalDefId,
    name: &str,
) -> ClosureClauseName {
    if !tcx.is_closure_like(closure.to_def_id()) {
        return ClosureClauseName::AsWritten;
    }
    let Some(owner) = owner_bindings(tcx, closure) else {
        return ClosureClauseName::AsWritten;
    };
    let symbol = Symbol::intern(name);
    if !owner.bound.contains(&symbol) {
        return ClosureClauseName::AsWritten;
    }
    let mut is_param = false;
    if let Some(body) = tcx.hir_maybe_body_owned_by(closure) {
        for param in body.params {
            param.pat.each_binding(|_, _, _, ident| {
                is_param |= ident.name == symbol;
            });
        }
    }
    if is_param {
        return ClosureClauseName::AsWritten;
    }
    let site = name_hygiene(tcx.def_span(closure));
    let shadowed = owner.shadowed.contains(&symbol);
    let captures: Vec<(HirId, bool)> = tcx
        .closure_captures(closure)
        .iter()
        .filter(|capture| capture.var_ident.name == symbol)
        .map(|capture| {
            (
                capture.get_root_variable(),
                !capture.place.projections.is_empty(),
            )
        })
        .collect();
    let hygienic: Vec<(HirId, bool)> = captures
        .iter()
        .copied()
        .filter(|(root, _)| owner.ident_hygiene.get(root) == Some(&site))
        .collect();
    match hygienic.as_slice() {
        [] if !shadowed && captures.is_empty() => ClosureClauseName::AsWritten,
        [] if captures.is_empty() => ClosureClauseName::Refused(format!(
            "it names `{name}`, which the closure does not capture, while the function binds \
             `{name}` more than once, so no call site can tell which binding it means"
        )),
        [] => ClosureClauseName::Refused(format!(
            "the closure captures `{name}` only from a binding of another hygiene (a macro's)"
        )),
        [(_, _)] if captures.len() > 1 => {
            ClosureClauseName::Refused(format!("the closure captures two bindings named `{name}`"))
        }
        // A capture of a binding whose name the function binds more than
        // once (D-237): read as written, the name is some other binding of
        // it. That holds for a captured PARAMETER too (D-239): the clause is
        // read in every calling body, and in a calling closure the name may be
        // that closure's own parameter, or a binding of its own.
        [(root, projected)] if shadowed => {
            if *projected {
                ClosureClauseName::Refused(format!(
                    "it names `{name}`, a binding the function binds more than once, of which \
                     the closure captures a place, not the whole binding"
                ))
            } else {
                ClosureClauseName::Capture(capture_clause_name(name, *root))
            }
        }
        [_] => ClosureClauseName::AsWritten,
        _ => {
            ClosureClauseName::Refused(format!("the closure captures two bindings named `{name}`"))
        }
    }
}

/// What a source name denotes at a point of a body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Visible {
    /// The body renamed no binding of this name: it means what it says.
    Unshadowed,
    /// The debug name of the one binding the name denotes there.
    Binding(String),
    /// The body shadows the name and the binding meant there cannot be
    /// told: no binding of it encloses the point, or two do at once.
    Unresolvable,
}

/// The hygiene a name written at `span` is resolved with. Rust compares a
/// local variable's identifier with its use modulo the marks a desugaring or
/// a proc macro's call-site span adds (`normalize_to_macro_rules`), so the
/// marks that remain are the `macro_rules!` expansions that wrote it: a `let x`
/// such an expansion introduces is no binding of the `x` its caller writes.
pub(crate) fn name_hygiene(span: Span) -> SyntaxContext {
    span.ctxt().normalize_to_macro_rules()
}

/// The binding the source name `name`, written with the hygiene `site`,
/// denotes at the MIR source scope `scope` of `body`.
///
/// Text written directly in the source (`site` is the root) names only the
/// bindings whose identifier the source wrote: exactly Rust's resolution of
/// a local. Text written inside a macro expansion may hold tokens of another
/// hygiene (a `$e` fragment), which the text no longer records, so there the
/// name is resolved only when every binding of it has the text's own hygiene.
pub(crate) fn visible_binding(
    body: &Body<'_>,
    name: &str,
    scope: SourceScope,
    site: SyntaxContext,
) -> Visible {
    let hygienes = debug_hygienes(body);
    let candidates: Vec<(&str, SourceScope, Option<Local>, Option<SyntaxContext>)> = body
        .var_debug_info
        .iter()
        .zip(hygienes)
        .filter(|(debug, _)| source_name_of(debug.name.as_str()) == name)
        .map(|(debug, hygiene)| {
            let local = match &debug.value {
                VarDebugInfoContents::Place(place) => Some(place.local),
                VarDebugInfoContents::Const(_) => None,
            };
            (debug.name.as_str(), debug.source_info.scope, local, hygiene)
        })
        .collect();
    // A binding whose identifier's hygiene is unknown may be the one the
    // text names, or not: refused, never discarded as foreign.
    if candidates.iter().any(|(_, _, _, ctxt)| ctxt.is_none()) {
        return Visible::Unresolvable;
    }
    let foreign = candidates.iter().any(|(_, _, _, ctxt)| *ctxt != Some(site));
    if !foreign
        && !candidates
            .iter()
            .any(|(debug_name, _, _, _)| is_renamed_binding(debug_name))
    {
        return Visible::Unshadowed;
    }
    if foreign && !site.is_root() {
        return Visible::Unresolvable;
    }
    let candidates: Vec<(&str, SourceScope, Option<Local>)> = candidates
        .into_iter()
        .filter(|(_, _, _, ctxt)| *ctxt == Some(site))
        .map(|(debug_name, binding_scope, local, _)| (debug_name, binding_scope, local))
        .collect();
    let mut current = Some(scope);
    while let Some(at) = current {
        let here: Vec<&(&str, SourceScope, Option<Local>)> = candidates
            .iter()
            .filter(|(_, binding_scope, _)| *binding_scope == at)
            .collect();
        if let Some(first) = here.first() {
            if here
                .iter()
                .any(|(debug_name, _, local)| *debug_name != first.0 || *local != first.2)
            {
                return Visible::Unresolvable;
            }
            return Visible::Binding(first.0.to_string());
        }
        current = body
            .source_scopes
            .get(at)
            .and_then(|data| data.parent_scope);
    }
    Visible::Unresolvable
}

/// Rewrite every free source name of `expr` that `body` shadows, or binds
/// with a hygiene other than `site`'s, to the binding it denotes at `scope`.
/// `Err` names the first one that cannot be resolved: the caller refuses the
/// term rather than read it as some other binding of that name.
pub(crate) fn resolve_names_at_scope(
    body: &Body<'_>,
    expr: &PureExpr,
    scope: SourceScope,
    site: SyntaxContext,
) -> Result<PureExpr, String> {
    let mut names: Vec<String> = expr.free_vars().into_iter().collect();
    names.sort();
    let mut resolved = expr.clone();
    for name in names {
        match visible_binding(body, &name, scope, site) {
            Visible::Unshadowed => {}
            Visible::Binding(debug_name) => {
                if debug_name != name {
                    resolved = rename_free_var(
                        &resolved,
                        &name,
                        &debug_name,
                        &CaptureAvoidingSubstOptions::default(),
                    );
                }
            }
            Visible::Unresolvable => return Err(name),
        }
    }
    Ok(resolved)
}

/// The clauses `exprs` written at the loop whose header is `header` (a loop
/// invariant or variant names the bindings visible at its loop, with the
/// loop's hygiene), each name the body shadows rewritten to the binding it
/// denotes there. A name no binding of that hygiene encloses there is
/// renamed to one of its own, `{name}$unresolved_{header}`,
/// which nothing else names: the clause can then neither be proved from, nor
/// prove, a fact about some other binding of the name.
pub(crate) fn resolve_loop_clauses(
    body: &Body<'_>,
    header: rustc_middle::mir::BasicBlock,
    exprs: Vec<PureExpr>,
) -> Vec<PureExpr> {
    let Some(data) = body.basic_blocks.get(header) else {
        return exprs;
    };
    let source_info = data.terminator().source_info;
    let site = name_hygiene(source_info.span);
    if shadowed_source_names(body).is_empty() && !binds_with_other_hygiene(body, site) {
        return exprs;
    }
    let scope = source_info.scope;
    exprs
        .into_iter()
        .map(|expr| {
            let mut current = expr;
            loop {
                match resolve_names_at_scope(body, &current, scope, site) {
                    Ok(resolved) => return resolved,
                    Err(name) => {
                        let isolated = format!("{name}$unresolved_{}", header.as_u32());
                        current = rename_free_var(
                            &current,
                            &name,
                            &isolated,
                            &CaptureAvoidingSubstOptions::default(),
                        );
                    }
                }
            }
        })
        .collect()
}

/// The assertion with each name the body binds more than once, or binds with
/// a hygiene other than the assertion's, rewritten to the binding visible at
/// the assertion's source scope (D-237, D-238), or the name whose binding
/// there cannot be told.
pub(crate) fn resolve_proof_assert_bindings(
    tcx: TyCtxt<'_>,
    pa: &crate::proof_assert::ProofAssert,
    assertion: &PureExpr,
) -> Result<PureExpr, String> {
    let Some(body_with_facts) = crate::callbacks::try_get_body_with_context(tcx, pa.containing_fn)
    else {
        return Ok(assertion.clone());
    };
    let body = crate::mir_analysis::get_mir_body(&body_with_facts);
    // `pa.span` is the marker closure's, a call-site span of the
    // `proof_assert!` expansion: its hygiene is the invocation's.
    let site = name_hygiene(pa.span);
    let shadowed = shadowed_source_names(body);
    let other_hygiene = binds_with_other_hygiene(body, site);
    let free = assertion.free_vars();
    if !free
        .iter()
        .any(|name| shadowed.contains(name) || (other_hygiene && binds_name(body, name)))
    {
        return Ok(assertion.clone());
    }
    let first_needing = || {
        let mut names: Vec<&String> = free
            .iter()
            .filter(|name| shadowed.contains(*name) || binds_name(body, name))
            .collect();
        names.sort();
        names
            .first()
            .map(|name| (*name).clone())
            .unwrap_or_default()
    };
    let Some(scope) = pa.source_scope else {
        return Err(first_needing());
    };
    // Inside a macro expansion the assertion's tokens may carry another
    // hygiene than its invocation; only the type-check vehicle, which rustc
    // resolves where the assertion stands, says that every name it reads is
    // bound at the invocation's own (`visible_binding` then refuses a binding
    // of any other).
    if !site.is_root() && !proof_assert_has_vehicle(tcx, pa) {
        return Err(first_needing());
    }
    resolve_names_at_scope(body, assertion, scope, site)
}

/// Whether `body` binds `name` at all.
fn binds_name(body: &Body<'_>, name: &str) -> bool {
    body.var_debug_info
        .iter()
        .any(|debug| source_name_of(debug.name.as_str()) == name)
}

/// Whether some binding of `body` has a hygiene other than `site`.
fn binds_with_other_hygiene(body: &Body<'_>, site: SyntaxContext) -> bool {
    debug_hygienes(body)
        .into_iter()
        .any(|hygiene| hygiene != Some(site))
}

/// Whether `trust-wp-macros` placed a type-check vehicle beside the
/// assertion `pa` (`spec_tc::proof_assert_statement`, emitted as
/// `{ <vehicle> <marker block> }`): a closure of the assertion's tag in one
/// of the blocks that enclose its marker closure, before any enclosing
/// closure or item. With one, rustc resolved every name of the assertion
/// where it stands, and compiled it.
fn proof_assert_has_vehicle(tcx: TyCtxt<'_>, pa: &crate::proof_assert::ProofAssert) -> bool {
    let (Some(marker), Some(text)) = (
        pa.closure_def_id
            .and_then(rustc_hir::def_id::DefId::as_local),
        pa.expr_text.as_deref(),
    ) else {
        return false;
    };
    let kind = if pa.trusted {
        "trusted_proof_assert"
    } else {
        "proof_assert"
    };
    let mut blocks = 0;
    for (_, node) in tcx.hir_parent_iter(tcx.local_def_id_to_hir_id(marker)) {
        match node {
            hir::Node::Block(block) => {
                let found = block.stmts.iter().any(|stmt| {
                    let hir::StmtKind::Let(local) = stmt.kind else {
                        return false;
                    };
                    let Some(init) = local.init else {
                        return false;
                    };
                    let hir::ExprKind::Closure(closure) = init.kind else {
                        return false;
                    };
                    crate::callbacks::spec_typecheck::clause_tag(tcx, closure.def_id)
                        .is_some_and(|(tag_kind, tag_text)| tag_kind == kind && tag_text == text)
                });
                if found {
                    return true;
                }
                blocks += 1;
                if blocks > 3 {
                    return false;
                }
            }
            hir::Node::Expr(hir::Expr {
                kind: hir::ExprKind::Closure(_),
                ..
            })
            | hir::Node::Item(_)
            | hir::Node::ImplItem(_)
            | hir::Node::TraitItem(_) => return false,
            _ => {}
        }
    }
    false
}

/// Source names `body` renamed at least one binding of.
pub(crate) fn shadowed_source_names(body: &Body<'_>) -> HashSet<String> {
    body.var_debug_info
        .iter()
        .map(|debug| debug.name.as_str())
        .filter(|name| is_renamed_binding(name))
        .map(|name| source_name_of(name).to_string())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_name_strips_only_the_rename() {
        assert_eq!(source_name_of("r$shadow4"), "r");
        assert_eq!(source_name_of("r"), "r");
        assert_eq!(source_name_of("r$shadow"), "r$shadow");
        assert_eq!(source_name_of("r$shadow4x"), "r$shadow4x");
        assert_eq!(source_name_of("r$shadow_l4"), "r");
        assert_eq!(source_name_of("r$shadow_l"), "r$shadow_l");
        assert!(is_renamed_binding("h$shadow12"));
        assert!(!is_renamed_binding("h"));
        assert!(!is_renamed_binding("$call_3"));
    }

    #[test]
    fn a_renamed_name_is_no_source_name() {
        let name = local_binding_name("x", Local::from_u32(7));
        assert_eq!(name, "x$shadow_l7");
        assert_eq!(source_name_of(&name), "x");
        assert!(trust_wp_core::formula::is_synthesized_name(&name));
    }
}
