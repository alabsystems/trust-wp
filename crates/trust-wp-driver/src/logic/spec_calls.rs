// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What a specification's type-dependent calls denote, read from rustc's
//! type check of that specification.
//!
//! The identity resolver reads a specification as TEXT and decides by hand
//! which definition a receiver-style call `x.m(..)`, a `Self::m(..)`, a
//! `T::m(..)` or a `Tr::m(x, ..)` names: it types the receiver from the
//! owner's signature and looks the name up among the family's members.
//! Rust's method probe decides otherwise wherever the hand lookup cannot see
//! a candidate: an in-scope trait's blanket impl taken by value before the
//! bound's by-reference method is reached by autoref, a where-clause on an
//! associated type, a bound trait that is not in scope at a projection, a
//! user `Deref` level, an associated function that is not a method. Each of
//! those bound a clause to the wrong definition and a false contract verified
//! (refinement_self_receiver_by_value_blanket_over_ref_trait_method.rs,
//! method_call_user_deref_other_trait_out_of_scope.rs).
//!
//! rustc type-checks every clause in the body `trust-wp-macros` emits for it
//! (`callbacks::spec_typecheck`), and tags that body with the clause's marker
//! kind and text. So a call the hand lookup binds is kept only where the
//! clause's OWN type-checked body holds calls of that form, name and arity on
//! a receiver of that type, and rustc resolved every one of them to the
//! definition the lookup chose. A clause with no such body, a body the
//! vehicle dropped a subterm of, or a disagreement refuses the call: the
//! lookup's answer is a guess wherever rustc's cannot confirm it.

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    intravisit::Visitor,
    Expr, ExprKind, QPath,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{GenericArgs, Ty, TyCtxt, TyKind, TypeVisitableExt, TypeckResults},
};

use crate::callbacks::spec_typecheck;

/// Which specification an expression the identity resolver reads is, so its
/// calls can be read against that specification's type-checked body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ClauseRef {
    /// The clause written under the `trust-wp:<kind>:` marker with exactly
    /// this text, owned by the item the resolver reads it for.
    Written { kind: String, text: String },
    /// One of the owner's own fn-level `requires` / `ensures` clauses whose
    /// text is not at hand (a logic function's contract, rewritten before
    /// the resolver sees it). Read against all of them together, and only
    /// where every such marker of the owner has its body.
    OwnFnLevel,
    /// The owner's logic body.
    LogicBody,
    /// Nothing rustc type-checked is known to be this expression.
    Unknown,
    /// Tests of the hand lookup alone: its answer is kept as it is. Only a
    /// test build has this variant, so no verification can read a call this
    /// way.
    #[cfg(test)]
    HandLookupUnderTest,
}

impl ClauseRef {
    pub(crate) fn written(kind: &str, text: &str) -> Self {
        Self::Written {
            kind: kind.to_string(),
            text: text.to_string(),
        }
    }
}

/// How a call is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CallForm {
    /// `recv.m(..)`.
    Method,
    /// A path call, `Q::m(..)` or `m(..)`.
    Path,
}

/// One call of a type-checked specification body.
#[derive(Debug, Clone)]
struct TypedSite<'tcx> {
    form: CallForm,
    name: String,
    /// Arguments including the receiver of a method call.
    arity: usize,
    /// The receiver's type (a path call's first argument), regions erased
    /// and references peeled, as the hand lookup reads it.
    receiver: Option<Ty<'tcx>>,
    /// The local variable the receiver is, through dereferences, borrows and
    /// the vehicle's own wrappers (`*old(x)`): what the hand lookup typed.
    receiver_root: Option<String>,
    /// A path call's callee path as written (`<S as Tr>::m`, `Tr::m`,
    /// `Self::m`), as tokens (`path_tokens`); `None` for a method call.
    path: Option<Vec<String>>,
    /// What rustc resolved the call to, and its generic arguments.
    resolved: Option<(DefId, GenericArgs<'tcx>)>,
    /// The item whose typing environment the call is resolved in.
    typing_owner: DefId,
}

/// The type-dependent calls of one specification, as rustc resolved them.
#[derive(Debug, Clone)]
pub(crate) struct SpecCalls<'tcx> {
    sites: Vec<TypedSite<'tcx>>,
}

impl<'tcx> SpecCalls<'tcx> {
    /// The calls of the specification `clause` of `owner`, or `None` when
    /// rustc's type check of it cannot be told: no body carries its tag, or
    /// a body dropped a subterm (whose calls then have no counterpart).
    pub(crate) fn of(tcx: TyCtxt<'tcx>, owner: DefId, clause: &ClauseRef) -> Option<Self> {
        let bodies = paired_bodies(tcx, owner, clause)?;
        Self::of_bodies(tcx, &bodies)
    }

    /// The calls of `bodies`, read as one specification's type-checked form.
    pub(crate) fn of_bodies(tcx: TyCtxt<'tcx>, bodies: &[LocalDefId]) -> Option<Self> {
        if bodies.is_empty() {
            return None;
        }
        let mut sites = Vec::new();
        for &body in bodies {
            sites.extend(body_sites(tcx, body)?);
        }
        Some(Self { sites })
    }

    /// The calls of `form`, `name` and `arity` that stand for a call the hand
    /// lookup read on a receiver of type `receiver` rooted at the variable
    /// `root`, or `None` where rustc's typing of that variable is not the
    /// lookup's.
    ///
    /// A path call stands only for calls whose callee path is written as the
    /// lookup's `path` is: the qualifier, not the first argument, decides
    /// what `<S as Tr>::m(x)` and `Tr::m(x)` name, so a call of one qualifier
    /// must not answer for another's, and pooled with it neither is confirmed
    /// (program_ensures_ufcs_two_impls_read_as_one.rs). The spelling selects
    /// the calls without trusting the lookup's reading of it: the call the
    /// lookup read is among them, and each must denote that reading. A path
    /// call given no spelling stands for nothing.
    ///
    /// With a root, the calls are those on a receiver rooted at the same
    /// variable, and each must have the lookup's type: a clause may name a
    /// parameter that a body binding shadows where the clause is written, and
    /// a same-typed call on another receiver must not stand in for it
    /// (proof_assert_shadowed_param_receiver_beside_same_typed_receiver.rs).
    /// Without one, every call whose receiver has the lookup's type (all of
    /// them when it is not known).
    #[allow(clippy::too_many_arguments)]
    fn matching(
        &self,
        tcx: TyCtxt<'tcx>,
        form: CallForm,
        name: &str,
        path: Option<&str>,
        arity: usize,
        receiver: Option<Ty<'tcx>>,
        root: Option<&str>,
    ) -> Option<Vec<&TypedSite<'tcx>>> {
        let key = receiver.map(|ty| lookup_type(tcx, ty));
        let written = match form {
            CallForm::Path => Some(path_tokens(path?)),
            CallForm::Method => None,
        };
        let same_call = |site: &&TypedSite<'tcx>| {
            site.form == form
                && site.name == name
                && site.arity == arity
                && (form == CallForm::Method || site.path == written)
        };
        let sites: Vec<&TypedSite<'tcx>> = match root {
            Some(root) => {
                let rooted: Vec<&TypedSite<'tcx>> = self
                    .sites
                    .iter()
                    .filter(same_call)
                    .filter(|site| site.receiver_root.as_deref() == Some(root))
                    .collect();
                let typed_alike = rooted.iter().all(|site| match (key, site.receiver) {
                    (Some(key), Some(site_ty)) => key == site_ty,
                    (None, _) => true,
                    (Some(_), None) => false,
                });
                if !typed_alike {
                    return None;
                }
                rooted
            }
            None => self
                .sites
                .iter()
                .filter(same_call)
                .filter(|site| match (key, site.receiver) {
                    (Some(key), Some(site_ty)) => key == site_ty,
                    _ => true,
                })
                .collect(),
        };
        (!sites.is_empty()).then_some(sites)
    }

    /// Whether rustc resolved every call that stands for the lookup's call
    /// (`matching`) to `chosen`, and there is at least one.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn confirms(
        &self,
        tcx: TyCtxt<'tcx>,
        form: CallForm,
        name: &str,
        path: Option<&str>,
        arity: usize,
        receiver: Option<Ty<'tcx>>,
        root: Option<&str>,
        chosen: DefId,
    ) -> bool {
        self.matching(tcx, form, name, path, arity, receiver, root)
            .is_some_and(|sites| sites.iter().all(|site| denotes(tcx, site, chosen)))
    }

    /// Whether the specification holds a call of `form`, `name` and `arity`.
    pub(crate) fn holds(&self, form: CallForm, name: &str, arity: usize) -> bool {
        self.sites
            .iter()
            .any(|site| site.form == form && site.name == name && site.arity == arity)
    }

    /// The one trait method declaration rustc resolved every call that stands
    /// for the lookup's call (`matching`) to, when they agree: what the calls
    /// name at a receiver whose type is still generic, to be instantiated
    /// wherever it is known.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn trait_method_resolved(
        &self,
        tcx: TyCtxt<'tcx>,
        form: CallForm,
        name: &str,
        path: Option<&str>,
        arity: usize,
        receiver: Option<Ty<'tcx>>,
        root: Option<&str>,
    ) -> Option<DefId> {
        let sites = self.matching(tcx, form, name, path, arity, receiver, root)?;
        let mut resolved = sites.iter().map(|site| site.resolved.map(|(def, _)| def));
        let first = resolved.next()??;
        (resolved.all(|def| def == Some(first))
            && tcx.trait_of_assoc(first).is_some()
            && tcx.impl_of_assoc(first).is_none())
        .then_some(first)
    }
}

/// The tokens of a written callee path, whitespace dropped, so that the
/// lookup's spelling of a path (`<S as Tr>::m`) and rustc's print of the
/// same path compare equal however either spaces it.
pub(crate) fn path_tokens(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch.is_whitespace() {
            continue;
        }
        let mut token = String::from(ch);
        if ch.is_alphanumeric() || ch == '_' {
            while let Some(&next) = chars.peek() {
                if !(next.is_alphanumeric() || next == '_') {
                    break;
                }
                token.push(next);
                chars.next();
            }
        }
        tokens.push(token);
    }
    tokens
}

/// A receiver type as the hand lookup reads it: references peeled, regions
/// erased, and every alias marked non-rigid. rustc's type check marks an
/// alias it could not normalize rigid (`Self::In` in a trait), while the
/// lookup reads the same alias off a signature unmarked; the mark records
/// what one environment's normalization found, not which type it is, so two
/// spellings of one type must compare equal.
fn lookup_type<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    rustc_middle::ty::set_aliases_to_non_rigid(tcx, tcx.erase_and_anonymize_regions(ty.peel_refs()))
        .skip_norm_wip()
}

/// Whether the call `site` denotes `chosen`. A call of a function that is no
/// trait method (an inherent method, a free function) denotes the function
/// rustc named. A trait method call denotes the item rustc's instance
/// resolution selects where it selects one, the trait's default body where
/// that is what runs, and the declaration itself where the receiver is still
/// generic: there the declaration is the method at an abstract `Self`, which
/// every implementation owes.
fn denotes<'tcx>(tcx: TyCtxt<'tcx>, site: &TypedSite<'tcx>, chosen: DefId) -> bool {
    use rustc_middle::ty::{Instance, InstanceKind, TypingEnv};
    let Some((def, args)) = site.resolved else {
        return false;
    };
    if tcx.trait_of_assoc(def).is_none() || tcx.impl_of_assoc(def).is_some() {
        return def == chosen;
    }
    let generic = tcx.erase_and_anonymize_regions(args).has_non_region_param();
    if args.has_escaping_bound_vars() {
        return false;
    }
    let typing_env = TypingEnv::post_analysis(tcx, site.typing_owner);
    // Resolution may reach trait selection on shapes nothing else asks
    // about; a panic there is an unknown callee, not a crash.
    let instance = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let args = tcx
            .try_normalize_erasing_regions(
                typing_env,
                rustc_middle::ty::set_aliases_to_non_rigid(tcx, args),
            )
            .ok()?;
        Instance::try_resolve(tcx, typing_env, def, args).ok()
    }))
    .ok()
    .flatten();
    match instance {
        Some(Some(instance)) => match instance.def {
            InstanceKind::Item(item) if item == def => chosen == def,
            InstanceKind::Item(item) => chosen == item || (generic && chosen == def),
            _ => false,
        },
        Some(None) => generic && chosen == def,
        None => false,
    }
}

/// The type-check bodies of `owner`'s specification `clause`.
fn paired_bodies(tcx: TyCtxt<'_>, owner: DefId, clause: &ClauseRef) -> Option<Vec<LocalDefId>> {
    match clause {
        ClauseRef::Unknown => None,
        #[cfg(test)]
        ClauseRef::HandLookupUnderTest => None,
        ClauseRef::LogicBody => {
            let closure = spec_typecheck::logic_body_tc_closure(tcx, owner.as_local()?)?;
            Some(vec![closure.def_id])
        }
        ClauseRef::Written { kind, text } => {
            let bodies: Vec<LocalDefId> = tc_bodies_of(tcx, owner)
                .into_iter()
                .filter(|&body| {
                    spec_typecheck::clause_tag(tcx, body)
                        .is_some_and(|(k, t)| k == *kind && t == *text)
                })
                .collect();
            (!bodies.is_empty()).then_some(bodies)
        }
        ClauseRef::OwnFnLevel => {
            let fn_level = |kind: &str| kind == "requires" || kind == "ensures";
            let mut tagged: Vec<(String, String)> = Vec::new();
            let mut bodies = Vec::new();
            for body in tc_bodies_of(tcx, owner) {
                if let Some((kind, text)) = spec_typecheck::clause_tag(tcx, body) {
                    if fn_level(&kind) {
                        tagged.push((kind, text));
                        bodies.push(body);
                    }
                }
            }
            let mut written: Vec<(String, String)> = spec_typecheck::clause_markers(tcx, owner)
                .into_iter()
                .filter(|(kind, _)| fn_level(kind))
                .collect();
            tagged.sort();
            written.sort();
            // Every fn-level clause of the owner has its body, and no body
            // answers a clause the owner does not carry.
            (tagged == written && !bodies.is_empty()).then_some(bodies)
        }
    }
}

/// Every honoured clause type-check body that may belong to `owner`: the
/// sibling helpers of a bodyless trait method, and otherwise the marked
/// closures in the body of `owner`'s type-check root (a closure's clauses
/// are type-checked beside it, in the enclosing body), not nested in one
/// another.
fn tc_bodies_of(tcx: TyCtxt<'_>, owner: DefId) -> Vec<LocalDefId> {
    let Some(local) = owner.as_local() else {
        return Vec::new();
    };
    if tcx.def_kind(local) == DefKind::AssocFn
        && tcx.def_kind(tcx.local_parent(local)) == DefKind::Trait
        && tcx.hir_maybe_body_owned_by(local).is_none()
    {
        let prefix = format!(
            "{}{}_",
            spec_typecheck::SPEC_TC_HELPER_PREFIX,
            tcx.item_name(owner)
        );
        return tcx
            .associated_items(tcx.local_parent(local).to_def_id())
            .in_definition_order()
            .filter_map(|item| item.def_id.as_local())
            .filter(|&helper| {
                tcx.opt_item_name(helper.to_def_id()).is_some_and(|name| {
                    name.as_str()
                        .strip_prefix(prefix.as_str())
                        .is_some_and(|rest| {
                            !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit())
                        })
                }) && spec_typecheck::is_spec_tc_trait_helper(tcx, helper)
            })
            .collect();
    }
    let root = tcx.typeck_root_def_id(owner);
    let Some(root) = root.as_local() else {
        return Vec::new();
    };
    let Some(body) = tcx.hir_maybe_body_owned_by(root) else {
        return Vec::new();
    };
    let mut finder = TcClosureFinder {
        tcx,
        found: Vec::new(),
    };
    finder.visit_expr(body.value);
    finder.found
}

struct TcClosureFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    found: Vec<LocalDefId>,
}

impl<'tcx> Visitor<'tcx> for TcClosureFinder<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Closure(closure) = expr.kind {
            if spec_typecheck::is_spec_tc_body(self.tcx, closure.def_id) {
                self.found.push(closure.def_id);
                return;
            }
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

/// The type-dependent calls of one type-check body, or `None` when the
/// vehicle replaced a subterm of it by an unconstrained value
/// (`__spec_tc::dead`), whose calls have no counterpart here.
fn body_sites<'tcx>(tcx: TyCtxt<'tcx>, body: LocalDefId) -> Option<Vec<TypedSite<'tcx>>> {
    let typing_owner = tcx.typeck_root_def_id(body.to_def_id());
    let mut collector = SiteCollector {
        tcx,
        typeck: tcx.typeck(body),
        typing_owner,
        sites: Vec::new(),
        dropped: false,
    };
    collector.visit_expr(tcx.hir_body_owned_by(body).value);
    (!collector.dropped).then_some(collector.sites)
}

struct SiteCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    typing_owner: DefId,
    sites: Vec<TypedSite<'tcx>>,
    dropped: bool,
}

impl<'tcx> Visitor<'tcx> for SiteCollector<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.record(expr);
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

impl<'tcx> SiteCollector<'_, 'tcx> {
    fn receiver_type(&self, expr: &Expr<'_>) -> Option<Ty<'tcx>> {
        self.typeck
            .expr_ty_opt(expr)
            .map(|ty| lookup_type(self.tcx, ty))
    }

    fn record(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::MethodCall(segment, receiver, args, _) => {
                let name = crate::logic::call_resolution::call_spelling(segment.ident.as_str());
                if name.starts_with(VEHICLE_METHOD_PREFIX) {
                    return;
                }
                let resolved = self
                    .typeck
                    .type_dependent_def_id(expr.hir_id)
                    .map(|def_id| (def_id, self.typeck.node_args(expr.hir_id)));
                self.sites.push(TypedSite {
                    form: CallForm::Method,
                    name: name.to_string(),
                    arity: args.len() + 1,
                    receiver: self.receiver_type(receiver),
                    receiver_root: receiver_root(receiver),
                    path: None,
                    resolved,
                    typing_owner: self.typing_owner,
                });
            }
            ExprKind::Call(callee, args) => {
                let ExprKind::Path(ref qpath) = callee.kind else {
                    return;
                };
                let fn_item = match self
                    .typeck
                    .node_type_opt(callee.hir_id)
                    .map(|ty| *ty.kind())
                {
                    Some(TyKind::FnDef(def_id, fn_args)) => Some((def_id, fn_args.skip_binder())),
                    _ => None,
                };
                if fn_item.is_some_and(|(def_id, _)| is_vehicle_dead(self.tcx, def_id)) {
                    self.dropped = true;
                    return;
                }
                if is_vehicle_path(qpath) {
                    return;
                }
                let segment = match qpath {
                    QPath::Resolved(_, path) => path.segments.last(),
                    QPath::TypeRelative(_, segment) => Some(*segment),
                };
                let Some(segment) = segment else {
                    return;
                };
                self.sites.push(TypedSite {
                    form: CallForm::Path,
                    name: crate::logic::call_resolution::call_spelling(segment.ident.as_str())
                        .to_string(),
                    arity: args.len(),
                    receiver: args.first().and_then(|first| self.receiver_type(first)),
                    receiver_root: args.first().and_then(receiver_root),
                    path: Some(path_tokens(&rustc_hir_pretty::qpath_to_string(
                        // TyCtxt prints HIR through its `HirTyCtxt` annotation.
                        &(&self.tcx as &dyn rustc_hir::intravisit::HirTyCtxt<'_>),
                        qpath,
                    ))),
                    resolved: fn_item,
                    typing_owner: self.typing_owner,
                });
            }
            _ => {}
        }
    }
}

/// The local variable `expr` is, through dereferences, borrows and the
/// vehicle's own one-argument wrappers (`old(x)` is `*__spec_tc::old(x)`),
/// or the unit struct a bare name `S` is the value of.
///
/// The hand lookup types a bare receiver name as a binder, a parameter, a
/// body local or, failing those, the unit struct the owner's scope gives it
/// (`identity::unit_struct_value_type`), and roots the call at that name in
/// every case. rustc resolves the clause's `S` to the struct's constructor
/// rather than to a local, so the constructor roots its calls under the same
/// spelling; `matching` still requires rustc's type of `S` to be the
/// lookup's, and `denotes` the definition. A qualified `m::S` is not a bare
/// name and roots nothing.
fn receiver_root(expr: &Expr<'_>) -> Option<String> {
    use rustc_hir::def::{CtorKind, CtorOf, Res};
    let mut expr = expr;
    loop {
        match expr.kind {
            ExprKind::Path(QPath::Resolved(None, path)) => {
                let rooted = match path.res {
                    Res::Local(_) => true,
                    Res::Def(DefKind::Ctor(CtorOf::Struct, CtorKind::Const), _) => {
                        path.segments.len() == 1
                    }
                    _ => false,
                };
                return rooted
                    .then(|| path.segments.last())
                    .flatten()
                    .map(|segment| segment.ident.to_string());
            }
            ExprKind::Unary(rustc_hir::UnOp::Deref, inner)
            | ExprKind::AddrOf(_, _, inner)
            | ExprKind::DropTemps(inner) => expr = inner,
            ExprKind::Call(callee, [only]) => match callee.kind {
                ExprKind::Path(ref qpath) if is_vehicle_path(qpath) => expr = only,
                _ => return None,
            },
            _ => return None,
        }
    }
}

/// The prefix of the methods the vehicle calls for Pearlite operators
/// (`x@` is `x.__trust_wp_tc_view()`); specification text may not spell one.
const VEHICLE_METHOD_PREFIX: &str = "__trust_wp_tc_";

/// A path the vehicle writes for a helper of its own: global and rooted at
/// `trust_wp_std`.
fn is_vehicle_path(qpath: &QPath<'_>) -> bool {
    let rooted = |path: &rustc_hir::Path<'_>| {
        path.is_global()
            && path
                .segments
                .get(1)
                .is_some_and(|segment| segment.ident.as_str() == "trust_wp_std")
    };
    match qpath {
        QPath::Resolved(None, path) => rooted(path),
        QPath::TypeRelative(qself, _) => matches!(
            qself.kind,
            rustc_hir::TyKind::Path(QPath::Resolved(None, path)) if rooted(path)
        ),
        QPath::Resolved(Some(_), _) => false,
    }
}

/// `trust_wp_std`'s `dead`: the vehicle's stand-in for a subterm it does not
/// lower, and Pearlite's own `dead`.
fn is_vehicle_dead(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    !def_id.is_local()
        && tcx.crate_name(def_id.krate).as_str() == "trust_wp_std"
        && tcx.item_name(def_id).as_str() == "dead"
}

#[cfg(test)]
#[path = "spec_calls_tests.rs"]
mod tests;
