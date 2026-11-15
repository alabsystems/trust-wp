// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic-function identity and scope resolution (driver side).
//!
//! Every local logic function (singletons included: a short name is shared
//! with same-named methods of other types) gets a unique id (`trust_wp_core::logic::identity`), and the
//! collision families are installed for the encoder. Clause call sites that
//! spell a colliding name are resolved here in the clause OWNER's scope, the
//! way rustc resolves the path: bare names and `use` imports through the
//! owner's module, `crate::`/`self::`/`super::`/module paths through module
//! children, `Self::m` through the enclosing impl or trait, `Type::m` through
//! inherent impls, `Trait::m`/`T::m` to the trait declaration and
//! `<Type as Trait>::m` to the one impl for that type. A name that cannot be
//! resolved here is left untouched and the encoder refuses it (receiver-style
//! calls are dispatched by the encoder on the receiver's sort).

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::{
    def::{DefKind, Namespace, Res},
    def_id::{DefId, LocalDefId, CRATE_DEF_ID, LOCAL_CRATE},
};
use rustc_middle::ty::{AssocContainer, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use trust_wp_core::{
    formula::{MatchArm, Pattern, PureExpr},
    logic::{
        identity::{
            dispatches_on_receiver, install_logic_fn_identity_registry, logic_fn_identity_registry,
            logic_fn_short_name, logic_fn_unique_id, logic_fn_unresolved_marker,
            LogicFnFamilyMember, LogicFnIdentityRegistry, LogicFnOwnerKind,
        },
        LogicFnDef,
    },
};

pub(crate) use crate::logic::block_scope::ClausePosition;
use crate::logic::{
    block_scope::{self, BlockBinding},
    spec_calls::{CallForm, ClauseRef, SpecCalls},
};

thread_local! {
    /// Unique id -> `DefId` of every collision member of the crate under
    /// verification (resolution needs the definitions, the registry is
    /// `DefId`-free so the encoder can share it).
    static MEMBER_DEF_IDS: RefCell<HashMap<String, DefId>> = RefCell::new(HashMap::new());
    /// Ids of trait-declaration members whose visible default body calls no
    /// logic function or method (it cannot reach a declaration symbol shared
    /// by every instantiation).
    static SELF_CONTAINED_DEFAULTS: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
    /// Ids shared by two local definitions: rustc prints the same path for
    /// items declared in different blocks of one body (`host::k` twice), and
    /// every table here is keyed by that path, so which definition such an id
    /// stands for is not known. No resolution may produce one.
    static AMBIGUOUS_IDS: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
}

/// Local ADT names whose solver sort is canonicalized to a builtin model sort
/// (or otherwise shared with library types); never nominal.
const NON_NOMINAL_ADT_NAMES: &[&str] = &[
    "Seq", "Vec", "VecDeque", "FMap", "FSet", "HashMap", "HashSet", "BTreeMap", "BTreeSet",
    "GhostMap", "Mapping", "Option", "Result", "Box", "String", "Int", "Snapshot", "Ghost", "Rc",
    "Arc", "Cell", "RefCell", "List", "Ordering", "Range", "Id",
];

fn crate_qualified_path(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    format!("{crate_name}::{}", tcx.def_path_str(def_id))
}

/// Give every member of a short-name collision a unique id, install the
/// collision registry, and resolve the defs' own clause/body call sites in
/// their own scope.
pub(crate) fn assign_logic_fn_identities(
    tcx: TyCtxt<'_>,
    defs: &mut [LogicFnDef],
    def_ids_by_path: &HashMap<String, DefId>,
) {
    let mut groups: HashMap<String, Vec<usize>> = HashMap::new();
    for (index, def) in defs.iter().enumerate() {
        groups
            .entry(def.short_name().to_string())
            .or_default()
            .push(index);
    }

    crate::logic::method_lookup::reset();
    let adt_name_counts = local_adt_name_counts(tcx);
    let mut path_counts: HashMap<String, usize> = HashMap::new();
    for local_def_id in tcx.iter_local_def_id() {
        if matches!(tcx.def_kind(local_def_id), DefKind::Fn | DefKind::AssocFn) {
            *path_counts
                .entry(crate_qualified_path(tcx, local_def_id.to_def_id()))
                .or_insert(0) += 1;
        }
    }
    let mut ambiguous_ids = HashSet::new();
    let mut members = Vec::new();
    let mut member_def_ids = HashMap::new();
    let mut self_contained_defaults = HashSet::new();
    // EVERY local definition gets a unique id, singletons included: a short
    // name defined once locally is still shared with every same-named method
    // of other types (`u.view()` on `u32` is `View::view`, not a local
    // `A::view`), and a free function never answers a method call. Keying a
    // singleton by its short name let it answer those calls; with an id, a
    // call binds only through scope or typed-receiver resolution, or is
    // refused.
    for (short, indices) in &groups {
        for &index in indices {
            let def = &mut defs[index];
            let id = logic_fn_unique_id(def.full_path());
            if path_counts.get(def.full_path()).copied().unwrap_or(0) > 1 {
                ambiguous_ids.insert(id.clone());
            }
            let def_id = def_ids_by_path.get(def.full_path()).copied();
            let member = match def_id {
                Some(def_id) => family_member(tcx, def, def_id, &id, short, &adt_name_counts),
                None => LogicFnFamilyMember {
                    id: id.clone(),
                    full_path: def.full_path().to_string(),
                    short_name: short.clone(),
                    kind: LogicFnOwnerKind::Free,
                    trait_path: None,
                    nominal_self_sort: None,
                    receiver_is_self: false,
                    decl_has_visible_body: false,
                    receiver_dispatch: false,
                    decl_default_runs: false,
                    arity: def.params().len(),
                },
            };
            if let Some(def_id) = def_id {
                member_def_ids.insert(id.clone(), def_id);
            }
            if member.kind == LogicFnOwnerKind::TraitDecl
                && member.decl_has_visible_body
                && body_calls_nothing(def.body())
            {
                self_contained_defaults.insert(id.clone());
            }
            members.push(member);
            def.assign_unique_id(id);
        }
    }
    MEMBER_DEF_IDS.with(|cell| *cell.borrow_mut() = member_def_ids);
    SELF_CONTAINED_DEFAULTS.with(|cell| *cell.borrow_mut() = self_contained_defaults);
    AMBIGUOUS_IDS.with(|cell| *cell.borrow_mut() = ambiguous_ids);
    install_logic_fn_identity_registry(LogicFnIdentityRegistry::new(members));

    for def in defs.iter_mut() {
        let Some(&def_id) = def_ids_by_path.get(def.full_path()) else {
            continue;
        };
        let params: Vec<String> = def.params().to_vec();
        // A logic function's body and contract are read at the top of its
        // body; its contract reaches here rewritten, so its clauses are read
        // against all of the function's own fn-level bodies.
        let resolve = |expr: &PureExpr, clause: &ClauseRef| {
            resolve_with_params(
                tcx,
                def_id,
                expr,
                &params,
                ResolveMode::LogicDef,
                ClausePosition::Signature,
                clause,
            )
        };
        let body = resolve(def.body(), &ClauseRef::LogicBody);
        def.set_body(body);
        let own = ClauseRef::OwnFnLevel;
        let requires = def
            .requires()
            .iter()
            .map(|expr| resolve(expr, &own))
            .collect();
        def.set_requires(requires);
        let ensures = def
            .ensures()
            .iter()
            .map(|expr| resolve(expr, &own))
            .collect();
        def.set_ensures(ensures);
    }
}

fn local_adt_name_counts(tcx: TyCtxt<'_>) -> HashMap<String, usize> {
    let mut counts = HashMap::new();
    for local_def_id in tcx.iter_local_def_id() {
        if matches!(
            tcx.def_kind(local_def_id),
            DefKind::Struct | DefKind::Enum | DefKind::Union
        ) {
            *counts
                .entry(tcx.item_name(local_def_id.to_def_id()).to_string())
                .or_insert(0) += 1;
        }
    }
    counts
}

fn family_member(
    tcx: TyCtxt<'_>,
    def: &LogicFnDef,
    def_id: DefId,
    id: &str,
    short: &str,
    adt_name_counts: &HashMap<String, usize>,
) -> LogicFnFamilyMember {
    let mut kind = LogicFnOwnerKind::Free;
    let mut trait_path = None;
    let mut self_ty = None;
    if let Some(assoc) = tcx.opt_associated_item(def_id) {
        let container = tcx.parent(def_id);
        match assoc.container {
            AssocContainer::Trait => {
                kind = LogicFnOwnerKind::TraitDecl;
                trait_path = Some(tcx.def_path_str(container));
                self_ty = Some(tcx.types.self_param);
            }
            AssocContainer::TraitImpl(_) => {
                kind = LogicFnOwnerKind::TraitImpl;
                trait_path = tcx
                    .impl_opt_trait_id(container)
                    .map(|trait_id| tcx.def_path_str(trait_id));
                self_ty = Some(
                    tcx.type_of(container)
                        .instantiate_identity()
                        .skip_norm_wip(),
                );
            }
            AssocContainer::InherentImpl => {
                kind = LogicFnOwnerKind::Inherent;
                self_ty = Some(
                    tcx.type_of(container)
                        .instantiate_identity()
                        .skip_norm_wip(),
                );
            }
        }
    }

    let receiver_is_self = self_ty.is_some_and(|self_ty| {
        let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
        sig.inputs()
            .first()
            .is_some_and(|first| first.peel_refs() == self_ty)
    });

    let nominal_self_sort = match (kind, self_ty) {
        (LogicFnOwnerKind::TraitImpl | LogicFnOwnerKind::Inherent, Some(self_ty)) => {
            match self_ty.kind() {
                TyKind::Adt(adt, args)
                    if adt.did().is_local() && !adt.is_box() && {
                        // Every instantiation shares one solver sort name, so
                        // only an impl covering all of them is nominal.
                        let mut seen = HashSet::new();
                        args.consts().next().is_none()
                            && args.types().all(|arg| {
                                matches!(arg.kind(), TyKind::Param(p) if seen.insert(p.index))
                            })
                    } =>
                {
                    let name = tcx.item_name(adt.did()).to_string();
                    let unique = adt_name_counts.get(&name).copied() == Some(1);
                    if unique && !NON_NOMINAL_ADT_NAMES.contains(&name.as_str()) {
                        crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, self_ty)
                            .filter(|sort| {
                                matches!(sort, trust_wp_core::formula::ExprSort::Datatype(_))
                            })
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    };

    // The encoder dispatches a method call it receives unresolved on its
    // receiver's nominal sort, never knowing whether the receiver was the
    // self type or a reference to it: the member may be picked only where
    // Rust's lookup selects it from every one of those.
    let receiver_dispatch = nominal_self_sort.is_some()
        && self_ty.is_some_and(|self_ty| {
            let region = tcx.lifetimes.re_erased;
            [
                self_ty,
                Ty::new_imm_ref(tcx, region, self_ty),
                Ty::new_mut_ref(tcx, region, self_ty),
            ]
            .into_iter()
            .all(|receiver| {
                crate::logic::method_lookup::selects_only(tcx, short, receiver, def_id, false)
            })
        });

    LogicFnFamilyMember {
        id: id.to_string(),
        full_path: def.full_path().to_string(),
        short_name: short.to_string(),
        kind,
        trait_path,
        nominal_self_sort,
        receiver_is_self,
        decl_has_visible_body: kind == LogicFnOwnerKind::TraitDecl && !def.is_opaque(),
        receiver_dispatch,
        decl_default_runs: kind == LogicFnOwnerKind::TraitDecl
            && default_runs_somewhere(tcx, def_id),
        arity: def.params().len(),
    }
}

/// Whether the trait method `decl` has a default body that some impl of its
/// trait does not override, so that the default is the callee at that impl.
fn default_runs_somewhere(tcx: TyCtxt<'_>, decl: DefId) -> bool {
    let trait_id = tcx.parent(decl);
    tcx.def_kind(trait_id) == DefKind::Trait
        && tcx.defaultness(decl).has_value()
        && tcx
            .all_impls(trait_id)
            .any(|impl_id| !tcx.impl_item_implementor_ids(impl_id).contains_key(&decl))
}

/// Whether `id` is a trait declaration with a self-contained default body.
pub(crate) fn is_self_contained_default(id: &str) -> bool {
    SELF_CONTAINED_DEFAULTS.with(|cell| cell.borrow().contains(id))
}

/// A body with no logic-function call and no method call. The unit literal
/// is lowered to the synthetic constant `__trust_wp_tuple0()`, which names no
/// definition, so it is not a call.
fn body_calls_nothing(body: &PureExpr) -> bool {
    use trust_wp_core::formula::{
        internal::tuple_lowering::tuple_logic_fn_name, PureExprDepthLimitedTraversalExt,
    };
    let unit = tuple_logic_fn_name(0);
    !body.any_recursive_with_depth_limit(256, true, |node| match node {
        PureExpr::LogicFnCall { name, args } => !(args.is_empty() && *name == unit),
        PureExpr::MethodCall { .. } => true,
        _ => false,
    })
}

/// The refusal marker of ONE call the resolver refuses: the encoder refuses
/// it as it refuses every `logic_fn_unresolved_marker`, and no other refused
/// call is spelled like it. Two refused calls of one name may denote
/// different definitions (`<T as Tr>::m(a)` and `<U as Tr>::m(a)` at two
/// instantiations the lookup cannot read), and one symbol for both would
/// make an equality between them reflexive: a check that reads `e == e` as
/// true without encoding `e` would prove it, and no encoder would see the
/// marker it refuses
/// (callee_requires_generic_qualified_refused_calls_share_no_symbol.rs).
pub(crate) fn refused_call_marker(short: &str) -> String {
    static NEXT_SITE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let site = NEXT_SITE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    format!("{}_N{site}_", logic_fn_unresolved_marker(short))
}

pub(crate) fn member_def_id(id: &str) -> Option<DefId> {
    MEMBER_DEF_IDS.with(|cell| cell.borrow().get(id).copied())
}

/// What a path qualifier in clause TEXT names, read in `owner`'s scope as
/// its clauses are: block scopes first, then the module.
pub(crate) enum QualifierTarget {
    Trait(DefId),
    Adt(DefId),
    Other,
}

/// Resolve the qualifier `Q` of a written `Q::m(..)` in `owner`'s scope.
pub(crate) fn qualifier_in_scope(
    tcx: TyCtxt<'_>,
    owner: DefId,
    qualifier: &str,
) -> QualifierTarget {
    let Some(resolver) = text_resolver(tcx, owner) else {
        return QualifierTarget::Other;
    };
    let segments: Vec<&str> = strip_generic_args(qualifier).split("::").collect();
    match resolver.resolve_prefix(&segments) {
        Some(PathTarget::Trait(trait_id)) => QualifierTarget::Trait(trait_id),
        Some(PathTarget::Adt(adt)) => QualifierTarget::Adt(adt),
        Some(PathTarget::Module(_)) | None => QualifierTarget::Other,
    }
}

/// The model trait (`View`, `Resolve`) a written bare `short(..)` in
/// `owner`'s clause TEXT is a method of, or `None`: then the bare call names
/// no logic method at all (`Resolver::bare_model_trait`).
pub(crate) fn bare_call_model_trait(
    tcx: TyCtxt<'_>,
    owner: DefId,
    short: &str,
) -> Option<&'static str> {
    let resolver = text_resolver(tcx, owner)?;
    let in_blocks = resolver.block_lookup(short, Namespace::ValueNS);
    resolver.bare_model_trait(short, in_blocks)
}

/// A resolver that reads names in `owner`'s scope and types nothing.
fn text_resolver(tcx: TyCtxt<'_>, owner: DefId) -> Option<Resolver<'_>> {
    let registry = logic_fn_identity_registry()?;
    owner.is_local().then(|| Resolver {
        tcx,
        owner,
        registry,
        bound: Vec::new(),
        bound_tys: Vec::new(),
        signature: None,
        mode: ResolveMode::Text,
        position: ClausePosition::Signature,
        body_locals: std::cell::OnceCell::new(),
        outcomes: HashMap::new(),
        clause: ClauseRef::Unknown,
        spec_calls: std::cell::OnceCell::new(),
    })
}

/// The members of `family` that are local impls of the model trait
/// `model_trait` (`trust_wp_std`'s `View` or `Resolve`).
pub(crate) fn model_trait_impls(
    tcx: TyCtxt<'_>,
    family: &[LogicFnFamilyMember],
    model_trait: &str,
) -> Vec<LogicFnFamilyMember> {
    family
        .iter()
        .filter(|member| {
            member.kind == LogicFnOwnerKind::TraitImpl
                && member_def_id(&member.id).is_some_and(|def_id| {
                    tcx.impl_opt_trait_id(tcx.parent(def_id))
                        .is_some_and(|trait_id| is_model_item(tcx, trait_id, model_trait))
                })
        })
        .cloned()
        .collect()
}

/// The members of `family` that are `trait_id`'s (`member_of_trait`).
pub(crate) fn trait_members(
    tcx: TyCtxt<'_>,
    family: &[LogicFnFamilyMember],
    trait_id: DefId,
) -> Vec<LogicFnFamilyMember> {
    family
        .iter()
        .filter(|member| {
            member_def_id(&member.id).is_some_and(|def_id| member_of_trait(tcx, def_id, trait_id))
        })
        .cloned()
        .collect()
}

/// What a clause of `owner`, read at `position`, names by the type-namespace
/// name of a generic TYPE parameter of `owner` or of an item whose generics
/// `owner` inherits (the impl or trait of an associated item, the function
/// around a closure).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum GenericTypeParam {
    /// The parameter with this index: no block between the clause and the
    /// item that declares it binds the name.
    Visible(u32),
    /// No such parameter, or a block item or import nearer the clause
    /// shadows it (body_struct_shadows_generic_param_path_granted.rs): the
    /// scope lookup reads the name.
    NotParam,
    /// A block binds the name where the lookup cannot place the binding
    /// relative to the clause (`BlockBinding::Refused`): the name is neither.
    Refused,
}

/// Resolve `name` against the generic type parameters a clause of `owner`
/// sees. Rust consults the body's scopes BEFORE the generics of the item
/// that holds the body, so a body item of that name hides the parameter.
pub(crate) fn visible_generic_type_param(
    tcx: TyCtxt<'_>,
    owner: DefId,
    name: &str,
    position: ClausePosition,
) -> GenericTypeParam {
    let mut current = owner;
    let (declaring, index) = loop {
        let generics = tcx.generics_of(current);
        if let Some(param) = generics.own_params.iter().find(|param| {
            param.name.as_str() == name
                && matches!(
                    param.kind,
                    rustc_middle::ty::GenericParamDefKind::Type { .. }
                )
        }) {
            break (current, param.index);
        }
        match generics.parent {
            Some(parent) => current = parent,
            None => return GenericTypeParam::NotParam,
        }
    };
    // A foreign item's body is not read here; its generics cannot be
    // separated from what its body declares.
    let (Some(owner), Some(declaring)) = (owner.as_local(), declaring.as_local()) else {
        return GenericTypeParam::Refused;
    };
    match block_scope::lookup_within(tcx, owner, name, Namespace::TypeNS, position, declaring) {
        BlockBinding::Unbound => GenericTypeParam::Visible(index),
        BlockBinding::Def(..) => GenericTypeParam::NotParam,
        BlockBinding::Refused => GenericTypeParam::Refused,
    }
}

/// Whether `id` is shared by two local definitions (`AMBIGUOUS_IDS`).
pub(crate) fn is_ambiguous_id(id: &str) -> bool {
    AMBIGUOUS_IDS.with(|cell| cell.borrow().contains(id))
}

/// The variable a receiver is, through `old`, `*` and `^`: the name whose
/// type `Resolver::receiver_type` reads (`spec_calls::SpecCalls::confirms`
/// checks rustc typed it alike).
fn receiver_root(receiver: &PureExpr) -> Option<&str> {
    match receiver {
        PureExpr::Var(name, _) => Some(name),
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            receiver_root(inner)
        }
        _ => None,
    }
}

/// Resolve colliding logic-function call names in `expr` in the scope of
/// `owner` (the item whose clause, body or proof assertion `expr` is), read
/// at `position` in it.
/// `clause` says which of `owner`'s specifications `expr` is: a
/// type-dependent call is kept only where rustc's type check of it agrees
/// (`spec_calls`).
pub(crate) fn resolve_logic_fn_paths_in_scope(
    tcx: TyCtxt<'_>,
    owner: DefId,
    expr: &PureExpr,
    position: ClausePosition,
    clause: &ClauseRef,
) -> PureExpr {
    let params = owner_param_names(tcx, owner);
    resolve_with_params(
        tcx,
        owner,
        expr,
        &params,
        ResolveMode::OwnerVc,
        position,
        clause,
    )
}

/// Where a resolved expression is used; decides what a GENERIC receiver or
/// qualifier may resolve to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ResolveMode {
    /// A clause or assertion checked in the verification of `owner` itself:
    /// a generic parameter of `owner` denotes the abstract trait method (the
    /// declaration symbol).
    OwnerVc,
    /// A logic-function body / clause, axiomatized for every use: a generic
    /// receiver stays unresolved (refused by the encoder), because the
    /// declaration symbol would be shared by every instantiation.
    LogicDef,
    /// Callee clause text re-parsed at call sites: never a declaration
    /// symbol (generic receivers are marked by `identity_typed`).
    Text,
    /// A trait method's clause read for the refinement check at one impl,
    /// first step: its METHOD CALLS resolved in the trait method's own scope as
    /// `OwnerVc` resolves them there (a receiver of abstract type is the
    /// declaration its bound declares), and nothing else. A path call (`k(..)`,
    /// `m::k(..)`, `Tr::m(..)`, `Self::m(..)`) is left as written: its reading
    /// rests on the module lookup, which cannot see the items of a block that
    /// encloses the trait, and the refinement's scope closure refuses what is
    /// left. `DeclAtImpl` then instantiates the declarations at the impl.
    TraitMethodCalls,
    /// A trait method's clause AS ITS GRANT READS IT (already resolved in the
    /// trait's scope) instantiated at one impl, where each implementation owes
    /// that grant: only a call of a trait declaration is rewritten, to the
    /// implementation rustc's instance resolution selects for its receiver's
    /// type there (`instantiate_decl_call`). Nothing unresolved is bound, so
    /// every other name keeps the meaning the grant gave it.
    DeclAtImpl,
}

/// `trait_method`'s clause `expr`, as the trait's grant reads it, instantiated
/// at `impl_method` (see `ResolveMode::DeclAtImpl`). `params` are the names the
/// clause gives the trait method's parameters. A declaration call that does
/// not instantiate is left in place: it is the method at an abstract `Self`,
/// which the caller refuses.
pub(crate) fn instantiate_trait_decl_calls_at_impl(
    tcx: TyCtxt<'_>,
    trait_method: DefId,
    impl_method: DefId,
    params: &[String],
    expr: &PureExpr,
) -> PureExpr {
    let Some(registry) = logic_fn_identity_registry() else {
        return expr.clone();
    };
    if registry.is_empty() || !trait_method.is_local() || !impl_method.is_local() {
        return expr.clone();
    }
    let Some(signature) =
        crate::logic::identity_typed::trait_signature_at_impl(tcx, trait_method, impl_method)
            .filter(|(inputs, _)| inputs.len() == params.len())
    else {
        return expr.clone();
    };
    let bound_tys = signature.0.iter().copied().map(Some).collect();
    let mut resolver = Resolver {
        tcx,
        owner: trait_method,
        registry,
        bound: params.to_vec(),
        bound_tys,
        signature: Some(signature),
        mode: ResolveMode::DeclAtImpl,
        position: ClausePosition::Signature,
        body_locals: std::cell::OnceCell::new(),
        outcomes: HashMap::new(),
        clause: ClauseRef::Unknown,
        spec_calls: std::cell::OnceCell::new(),
    };
    resolver.rewrite(expr)
}

/// `trait_method`'s clause `expr` as it reads at `impl_method`, the impl item
/// that refines it: its method calls resolved in the trait method's own scope
/// (`ResolveMode::TraitMethodCalls`), where the grant generic callers receive
/// reads them, and then instantiated at the impl
/// (`instantiate_trait_decl_calls_at_impl`), so a call of a trait declaration
/// on a receiver the impl makes concrete is the item rustc's instance
/// resolution selects there. A receiver-type lookup at the impl is not the
/// clause's meaning: the trait names the declaration its bound declares, and
/// the lookup sees whatever the impl type happens to have (an inherent
/// method, another trait's). What does not bind stays as written or as the
/// declaration, which the refinement check's scope closure refuses.
pub(crate) fn resolve_trait_clause_at_impl(
    tcx: TyCtxt<'_>,
    trait_method: DefId,
    impl_method: DefId,
    expr: &PureExpr,
    clause: &ClauseRef,
) -> PureExpr {
    if logic_fn_identity_registry().is_none_or(|registry| registry.is_empty())
        || !trait_method.is_local()
        || !impl_method.is_local()
    {
        return expr.clone();
    }
    let params = owner_param_names(tcx, trait_method);
    let in_trait_scope = resolve_with_params(
        tcx,
        trait_method,
        expr,
        &params,
        ResolveMode::TraitMethodCalls,
        ClausePosition::Signature,
        clause,
    );
    instantiate_trait_decl_calls_at_impl(tcx, trait_method, impl_method, &params, &in_trait_scope)
}

fn resolve_with_params(
    tcx: TyCtxt<'_>,
    owner: DefId,
    expr: &PureExpr,
    params: &[String],
    mode: ResolveMode,
    position: ClausePosition,
    clause: &ClauseRef,
) -> PureExpr {
    let Some(registry) = logic_fn_identity_registry() else {
        return expr.clone();
    };
    if registry.is_empty() || !owner.is_local() {
        return expr.clone();
    }
    let signature = crate::logic::identity_typed::owner_signature(tcx, owner)
        .filter(|(inputs, _)| inputs.len() == params.len());
    let bound_tys = match signature.as_ref() {
        Some((inputs, _)) => inputs.iter().copied().map(Some).collect(),
        None => vec![None; params.len()],
    };
    let mut resolver = Resolver {
        tcx,
        owner,
        registry,
        bound: params.to_vec(),
        bound_tys,
        signature,
        mode,
        position,
        body_locals: std::cell::OnceCell::new(),
        outcomes: HashMap::new(),
        clause: clause.clone(),
        spec_calls: std::cell::OnceCell::new(),
    };
    resolver.rewrite(expr)
}

fn owner_param_names(tcx: TyCtxt<'_>, owner: DefId) -> Vec<String> {
    if matches!(
        tcx.def_kind(owner),
        DefKind::Fn | DefKind::AssocFn | DefKind::Closure
    ) {
        tcx.fn_arg_idents(owner)
            .iter()
            .flatten()
            .map(|ident| ident.name.to_string())
            .collect()
    } else {
        Vec::new()
    }
}

/// Resolve colliding logic-function names in clause TEXT owned by `owner`.
///
/// Callee contracts are kept as text and re-parsed at every call site, far
/// from the callee's scope, so they are resolved here once, textually: a
/// written call name is replaced by its unique id only when every occurrence
/// of that name in the clause resolved to the same id (a name that is also
/// shadowed or unresolved somewhere is left for the encoder to refuse).
///
/// `clause` is the specification of `owner` the text was written as, before
/// any rewrite (`spec_calls`).
pub(crate) fn resolve_clause_text_in_scope(
    tcx: TyCtxt<'_>,
    owner: DefId,
    text: &str,
    clause: &ClauseRef,
) -> String {
    let Some(registry) = logic_fn_identity_registry() else {
        return text.to_string();
    };
    if registry.is_empty() || !owner.is_local() {
        return text.to_string();
    }
    let Ok(parsed) = trust_wp_core::contract_parser::parse_contract(text) else {
        return text.to_string();
    };
    let bound = owner_param_names(tcx, owner);
    let mut resolver = Resolver {
        tcx,
        owner,
        registry,
        bound_tys: vec![None; bound.len()],
        bound,
        signature: None,
        mode: ResolveMode::Text,
        position: ClausePosition::Signature,
        body_locals: std::cell::OnceCell::new(),
        outcomes: HashMap::new(),
        clause: clause.clone(),
        spec_calls: std::cell::OnceCell::new(),
    };
    let _ = resolver.rewrite(&parsed);
    let mut out = text.to_string();
    let mut replacements: Vec<(String, String)> = resolver
        .outcomes
        .into_iter()
        .filter_map(|(written, outcomes)| {
            if written.starts_with('<') {
                return None;
            }
            // A spelling refused at one occurrence is refused at every one: each
            // refusal is its own marker (D-164), never one outcome, and a spelling
            // left as written is dispatched on its receiver by the encoder
            // (callee_contract_repeated_module_path_program_fn_call_read_as_logic_method_granted.rs).
            let short = logic_fn_short_name(&written);
            let refusal = logic_fn_unresolved_marker(short);
            if outcomes.iter().flatten().any(|id| id.starts_with(&refusal)) {
                let marker = refused_call_marker(short);
                return Some((written, marker));
            }
            let mut iter = outcomes.into_iter();
            match (iter.next(), iter.next()) {
                (Some(Some(id)), None) => Some((written, id)),
                _ => None,
            }
        })
        .collect();
    // Longer spellings first so `b::k` is replaced before a bare `k`.
    replacements.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
    for (written, id) in replacements {
        out = replace_call_name(&out, &written, &id);
    }
    out
}

/// Replace `written` where it is spelled as a call head: not preceded by an
/// identifier character, `:` or `.`, and followed (after whitespace) by `(`
/// or a `::<` turbofish.
fn replace_call_name(text: &str, written: &str, id: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut index = 0;
    while index < text.len() {
        if text[index..].starts_with(written) {
            let before_ok = index == 0 || {
                let prev = bytes[index - 1];
                !(prev.is_ascii_alphanumeric() || prev == b'_' || prev == b':' || prev == b'.')
            };
            let rest = text[index + written.len()..].trim_start();
            let after_ok = rest.starts_with('(') || rest.starts_with("::<");
            let next_is_ident = text[index + written.len()..]
                .bytes()
                .next()
                .is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_');
            if before_ok && after_ok && !next_is_ident {
                out.push_str(id);
                index += written.len();
                continue;
            }
        }
        let ch = text[index..].chars().next().unwrap_or(' ');
        out.push(ch);
        index += ch.len_utf8();
    }
    out
}

/// Resolve the callee clause texts of a user/trait spec table in each
/// callee's own scope.
pub(crate) fn resolve_spec_table_texts(
    tcx: TyCtxt<'_>,
    specs: &mut HashMap<DefId, trust_wp_driver::StdSpec>,
) {
    if logic_fn_identity_registry().is_none_or(|registry| registry.is_empty()) {
        return;
    }
    for (def_id, spec) in specs.iter_mut() {
        resolve_spec_clauses_in_scope(tcx, *def_id, spec);
    }
}

/// Resolve the clause texts of ONE callee spec in that callee's own scope.
///
/// A spec that skips this reaches call sites with a colliding short name the
/// encoder must refuse, even though the table copy of the same contract is
/// resolved — see `effective_user_specs_for_extraction`, which rebuilds a
/// recursive function's own spec from the raw contract text.
pub(crate) fn resolve_spec_clauses_in_scope(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    spec: &mut trust_wp_driver::StdSpec,
) {
    if logic_fn_identity_registry().is_none_or(|registry| registry.is_empty()) {
        return;
    }
    for (kind, clauses) in [
        ("requires", &mut spec.requires),
        ("ensures", &mut spec.ensures),
    ] {
        for clause in clauses.iter_mut() {
            let written = ClauseRef::written(kind, clause);
            let typed = crate::logic::identity_typed::resolve_family_calls_in_text(
                tcx, def_id, clause, &written,
            );
            *clause = resolve_clause_text_in_scope(tcx, def_id, &typed, &written);
        }
    }
}

struct Resolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    registry: Arc<LogicFnIdentityRegistry>,
    bound: Vec<String>,
    /// Rust type of each `bound` name, when it is known: the owner's
    /// parameters, and every `let`/match binding whose type follows from the
    /// value or scrutinee. `None` wherever it is not known.
    bound_tys: Vec<Option<rustc_middle::ty::Ty<'tcx>>>,
    /// The owner's parameter and return types (aligned with the parameters).
    signature: Option<(Vec<rustc_middle::ty::Ty<'tcx>>, rustc_middle::ty::Ty<'tcx>)>,
    mode: ResolveMode,
    /// Where in the owner the resolved text stands (which locals it may see).
    position: ClausePosition,
    /// Rust type of every name the owner's own body binds exactly once (lazy).
    body_locals: std::cell::OnceCell<HashMap<String, Option<rustc_middle::ty::Ty<'tcx>>>>,
    /// Written colliding call name -> every resolution outcome seen.
    outcomes: HashMap<String, HashSet<Option<String>>>,
    /// Which specification of `owner` the expression is: a type-dependent
    /// call is kept only where rustc's type check of it agrees.
    clause: ClauseRef,
    /// That specification's calls as rustc resolved them (lazy; `None` when
    /// they cannot be told).
    spec_calls: std::cell::OnceCell<Option<SpecCalls<'tcx>>>,
}

impl<'tcx> Resolver<'tcx> {
    fn with_bound<T>(&mut self, names: &[String], f: impl FnOnce(&mut Self) -> T) -> T {
        let mark = self.bound.len();
        self.bound.extend(names.iter().cloned());
        self.bound_tys.resize(self.bound.len(), None);
        let out = f(self);
        self.bound.truncate(mark);
        self.bound_tys.truncate(mark);
        out
    }

    /// Bind names that carry a known Rust type (match-arm and `let` bindings).
    fn with_bound_typed<T>(
        &mut self,
        bindings: &[(String, Option<rustc_middle::ty::Ty<'tcx>>)],
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let mark = self.bound.len();
        for (name, ty) in bindings {
            self.bound.push(name.clone());
            self.bound_tys.push(*ty);
        }
        let out = f(self);
        self.bound.truncate(mark);
        self.bound_tys.truncate(mark);
        out
    }

    fn rewrite(&mut self, expr: &PureExpr) -> PureExpr {
        match expr {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(..) => {
                expr.clone()
            }
            PureExpr::BinOp(l, op, r) => {
                PureExpr::BinOp(Arc::new(self.rewrite(l)), *op, Arc::new(self.rewrite(r)))
            }
            PureExpr::UnOp(op, inner) => PureExpr::UnOp(*op, Arc::new(self.rewrite(inner))),
            PureExpr::Ite(c, t, e) => PureExpr::Ite(
                Arc::new(self.rewrite(c)),
                Arc::new(self.rewrite(t)),
                Arc::new(self.rewrite(e)),
            ),
            PureExpr::Old(inner) => PureExpr::Old(Arc::new(self.rewrite(inner))),
            PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(self.rewrite(inner))),
            PureExpr::Final(inner) => PureExpr::Final(Arc::new(self.rewrite(inner))),
            PureExpr::View(inner) => PureExpr::View(Arc::new(self.rewrite(inner))),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let receiver = self.rewrite(receiver);
                let args: Vec<PureExpr> = args.iter().map(|arg| self.rewrite(arg)).collect();
                if args.is_empty() && self.is_model_view_call(method, &receiver) {
                    return PureExpr::View(Arc::new(receiver));
                }
                if self.mode != ResolveMode::Text
                    && self.registry.unresolved_family_for_call(method).is_some()
                    && self.is_opaque_deref(&receiver)
                {
                    let mut call_args = Vec::with_capacity(args.len() + 1);
                    call_args.push(receiver);
                    call_args.extend(args);
                    return PureExpr::LogicFnCall {
                        name: refused_call_marker(method),
                        args: call_args,
                    };
                }
                if let Some(id) = self.resolve_typed_receiver(method, &receiver, args.len() + 1) {
                    let id = self.kept_if_rustc_agrees(
                        CallForm::Method,
                        method,
                        args.len() + 1,
                        Some(&receiver),
                        id,
                    );
                    let mut call_args = Vec::with_capacity(args.len() + 1);
                    call_args.push(receiver);
                    call_args.extend(args);
                    return PureExpr::LogicFnCall {
                        name: id,
                        args: call_args,
                    };
                }
                PureExpr::MethodCall {
                    receiver: Arc::new(receiver),
                    method: method.clone(),
                    args,
                }
            }
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => self.with_bound(std::slice::from_ref(var), |this| PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(this.rewrite(body)),
                triggers: triggers
                    .iter()
                    .map(|trigger| trigger.iter().map(|t| this.rewrite(t)).collect())
                    .collect(),
            }),
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => self.with_bound(std::slice::from_ref(var), |this| PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(this.rewrite(body)),
                triggers: triggers
                    .iter()
                    .map(|trigger| trigger.iter().map(|t| this.rewrite(t)).collect())
                    .collect(),
            }),
            PureExpr::Match { scrutinee, arms } => {
                let scrutinee_ty = self.receiver_type(scrutinee);
                PureExpr::Match {
                    scrutinee: Arc::new(self.rewrite(scrutinee)),
                    arms: arms
                        .iter()
                        .map(|arm| {
                            let mut bindings = Vec::new();
                            pattern_binding_types(
                                self.tcx,
                                &arm.pattern,
                                scrutinee_ty,
                                &mut bindings,
                            );
                            self.with_bound_typed(&bindings, |this| MatchArm {
                                pattern: arm.pattern.clone(),
                                body: this.rewrite(&arm.body),
                            })
                        })
                        .collect(),
                }
            }
            PureExpr::Let { var, value, body } => {
                let value_ty = self.receiver_type(value);
                let value = Arc::new(self.rewrite(value));
                self.with_bound_typed(&[(var.clone(), value_ty)], |this| PureExpr::Let {
                    var: var.clone(),
                    value,
                    body: Arc::new(this.rewrite(body)),
                })
            }
            PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
                assumption: Arc::new(self.rewrite(assumption)),
                body: Arc::new(self.rewrite(body)),
            },
            PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
                obligation: Arc::new(self.rewrite(obligation)),
                body: Arc::new(self.rewrite(body)),
            },
            PureExpr::Closure { params, body } => {
                let names: Vec<String> = params.iter().map(|(name, _)| name.clone()).collect();
                self.with_bound(&names, |this| PureExpr::Closure {
                    params: params.clone(),
                    body: Arc::new(this.rewrite(body)),
                })
            }
            PureExpr::LogicFnCall { name, args } => {
                let args: Vec<PureExpr> = args.iter().map(|arg| self.rewrite(arg)).collect();
                if self.mode == ResolveMode::DeclAtImpl {
                    let name = self
                        .instantiate_decl_call(name, &args)
                        .unwrap_or_else(|| name.clone());
                    return PureExpr::LogicFnCall { name, args };
                }
                if let [receiver] = args.as_slice() {
                    if self.is_model_view_call(name, receiver) {
                        return PureExpr::View(Arc::new(receiver.clone()));
                    }
                }
                let resolved = self.resolve_call_name(name, &args);
                if self.registry.unresolved_family_for_call(name).is_some()
                    && std::env::var_os("TRUST_WP_LOGIC_IDENTITY_TRACE").is_some()
                {
                    eprintln!(
                        "trust-wp: logic-identity driver owner={} call={name} resolved={resolved:?}",
                        self.tcx.def_path_str(self.owner)
                    );
                }
                if self.registry.unresolved_family_for_call(name).is_some() {
                    self.outcomes
                        .entry(name.clone())
                        .or_default()
                        .insert(resolved.clone());
                }
                PureExpr::LogicFnCall {
                    name: resolved.unwrap_or_else(|| name.clone()),
                    args,
                }
            }
            _ => expr.clone(),
        }
    }

    /// The Rust type of a name the OWNER's own body binds — a `let` local or
    /// a match binding a loop invariant or assertion mentions.
    ///
    /// Only a name the body binds exactly once, at one type, is answered: two
    /// bindings of one name (shadowing, separate arms) leave the clause's
    /// spelling ambiguous, and an ambiguous receiver must refuse, not guess.
    ///
    /// INVARIANT — a name the CLAUSE itself binds is never typed from the
    /// body. A quantifier, a `let`, a match arm, a closure parameter and the
    /// owner's own parameters all push onto `bound`, and a bound name means
    /// the clause's own binder, whatever the body happens to call its locals.
    /// Today `receiver_type` is the only caller and reaches this solely in
    /// the arm where `bound` holds no such name, so the guard below changes
    /// no answer — that redundancy IS the point. The invariant used to be
    /// stated in this comment and checked nowhere, and a later edit that
    /// consulted the body first, or that forgot to push a binder, would have
    /// typed a quantified `s` with an unrelated body local named `s` and
    /// silently picked THAT type's definition: a wrong definition, not a
    /// refusal. Fail closed instead. `body_local_type_refuses_a_clause_binder`
    /// is the test.
    fn body_local_type(&self, name: &str) -> Option<rustc_middle::ty::Ty<'tcx>> {
        // A trait clause read at an impl has no body of its own to type from.
        if self.bound.iter().any(|bound| bound == name)
            || matches!(
                self.mode,
                ResolveMode::TraitMethodCalls | ResolveMode::DeclAtImpl
            )
        {
            return None;
        }
        self.body_locals
            .get_or_init(|| body_local_types(self.tcx, self.owner))
            .get(name)
            .copied()
            .flatten()
    }

    /// Whether the owner's own body binds `name` anywhere (at any type).
    fn is_body_local(&self, name: &str) -> bool {
        self.body_locals
            .get_or_init(|| body_local_types(self.tcx, self.owner))
            .contains_key(name)
    }

    /// The Rust type of a receiver expression, when it is (a dereference or
    /// `old` of) an owner parameter, `result` or a body local not shadowed by
    /// a binder, or a unit struct value.
    fn receiver_type(&self, expr: &PureExpr) -> Option<rustc_middle::ty::Ty<'tcx>> {
        match expr {
            PureExpr::Old(inner) => self.receiver_type(inner),
            // `*x` and `^x` of a reference or box have the pointee's type,
            // where Rust's method lookup on them starts: a step `&mut A` it
            // never tries would let the prelude's blanket `Invariant for
            // &mut T` refuse `A`'s inherent method (syntax/09_maintains.rs).
            // Any other `*x` (a snapshot's or a model type's `Deref`) is
            // untyped: see `Resolver::is_opaque_deref`.
            PureExpr::Deref(inner) | PureExpr::Final(inner) => {
                let ty = self.receiver_type(inner)?;
                match ty.kind() {
                    TyKind::Ref(_, pointee, _) => Some(*pointee),
                    TyKind::Adt(adt, args) if adt.is_box() => Some(args.type_at(0)),
                    _ => None,
                }
            }
            PureExpr::Var(name, _) => match self.bound.iter().rposition(|bound| bound == name) {
                Some(position) => self.bound_tys.get(position).copied().flatten(),
                None if name == "result" => self.signature.as_ref().map(|(_, output)| *output),
                None if self.is_body_local(name) => self.body_local_type(name),
                None => unit_struct_value_type(self.tcx, self.owner, name),
            },
            _ => None,
        }
    }

    /// Whether `expr` is `*x` or `^x` (under any `old`) of an `x` whose Rust
    /// type is known and is neither a reference nor a box: a snapshot, or a
    /// model type read through its `Deref`. Rust's method lookup on it starts
    /// at the `Deref` target, which the resolver does not compute; typed at
    /// `x`'s own type, a method the target never has was read
    /// (method_call_deref_snapshot_receiver_read_at_snapshot_type_granted.rs),
    /// and the encoder's dispatch reads the operand's sort, not the target's.
    fn is_opaque_deref(&self, expr: &PureExpr) -> bool {
        match expr {
            PureExpr::Old(inner) => self.is_opaque_deref(inner),
            PureExpr::Deref(inner) | PureExpr::Final(inner) => match self.receiver_type(inner) {
                Some(ty) => !matches!(ty.kind(), TyKind::Ref(..)) && !ty.is_box(),
                None => self.is_opaque_deref(inner),
            },
            _ => false,
        }
    }

    /// Resolve a METHOD CALL `receiver.name(..)` on the receiver's Rust type:
    /// the logic definition the typed resolution selects at a concrete type
    /// stands only where Rust's method lookup can select nothing else
    /// (`method_lookup::selects_only`, method_call_*_granted.rs).
    fn resolve_typed_receiver(
        &self,
        name: &str,
        receiver: &PureExpr,
        arity: usize,
    ) -> Option<String> {
        let family = self.registry.unresolved_family_for_call(name)?;
        self.resolve_typed_receiver_in(family, name, receiver, arity)
    }

    /// `resolve_typed_receiver` over `family`.
    fn resolve_typed_receiver_in(
        &self,
        family: &[LogicFnFamilyMember],
        name: &str,
        receiver: &PureExpr,
        arity: usize,
    ) -> Option<String> {
        if matches!(self.mode, ResolveMode::Text | ResolveMode::DeclAtImpl) {
            return None;
        }
        let ty = self.receiver_type(receiver)?;
        let (outcome, at_concrete_type) = self.typed_outcome(family, ty, arity);
        let outcome = outcome.filter(|id| {
            !at_concrete_type
                || member_def_id(id).is_some_and(|def_id| {
                    crate::logic::method_lookup::selects_only(
                        self.tcx,
                        logic_fn_short_name(name),
                        ty,
                        def_id,
                        true,
                    )
                })
        });
        if std::env::var_os("TRUST_WP_LOGIC_IDENTITY_TRACE").is_some() {
            eprintln!(
                "trust-wp: logic-identity typed owner={} mode={:?} call={name} ty={ty:?} resolved={outcome:?}",
                self.tcx.def_path_str(self.owner),
                self.mode
            );
        }
        outcome
    }

    /// The typed resolution of a receiver-style call among `family` on the
    /// Rust type `ty`, and whether it selected a definition at a CONCRETE type
    /// (an impl, an inherent method, or a default body at that type) rather
    /// than a generic parameter's declaration.
    fn typed_outcome(
        &self,
        family: &[LogicFnFamilyMember],
        ty: rustc_middle::ty::Ty<'tcx>,
        arity: usize,
    ) -> (Option<String>, bool) {
        use crate::logic::identity_typed::{
            decl_for_generic_param, decl_for_projection, resolve_family_on_type, TypedOutcome,
        };
        if self.mode == ResolveMode::Text {
            return (None, false);
        }
        let (outcome, at_concrete_type) =
            match resolve_family_on_type(self.tcx, family, arity, ty, true, Some(self.owner)) {
                TypedOutcome::Id(id) => (Some(id), true),
                TypedOutcome::Generic(index) if self.decl_allowed() => (
                    decl_for_generic_param(self.tcx, self.owner, family, arity, index),
                    false,
                ),
                TypedOutcome::Projection(assoc) if self.decl_allowed() => {
                    (decl_for_projection(self.tcx, assoc, family, arity), false)
                }
                TypedOutcome::Generic(_) | TypedOutcome::Projection(_) | TypedOutcome::Refused => {
                    (None, false)
                }
            };
        (outcome.filter(|id| !is_ambiguous_id(id)), at_concrete_type)
    }

    /// `x.view()` of the external `View` trait on a receiver whose type has no
    /// local impl: exactly the model operator `x@`.
    fn is_model_view_call(&self, name: &str, receiver: &PureExpr) -> bool {
        use crate::logic::identity_typed::{
            is_external_view_family, resolve_family_on_type, TypedOutcome,
        };
        if name != "view"
            || matches!(
                self.mode,
                ResolveMode::Text | ResolveMode::TraitMethodCalls | ResolveMode::DeclAtImpl
            )
        {
            return false;
        }
        let Some(family) = self.registry.unresolved_family_for_call(name) else {
            return false;
        };
        let Some(ty) = self.receiver_type(receiver) else {
            return false;
        };
        if !is_external_view_family(family) {
            // A family of local free/inherent `view`s (and `View` impls): only
            // a primitive receiver, which none of them can apply to, is
            // certainly `View::view`.
            return matches!(
                resolve_family_on_type(self.tcx, family, 1, ty, true, Some(self.owner)),
                TypedOutcome::Refused
            ) && crate::logic::identity_typed::model_view_applies_to_primitive(
                self.tcx, family, ty,
            );
        }
        matches!(
            resolve_family_on_type(self.tcx, family, 1, ty, true, Some(self.owner)),
            TypedOutcome::Refused | TypedOutcome::Generic(_) | TypedOutcome::Projection(_)
        ) && {
            let peeled = self.tcx.erase_and_anonymize_regions(ty.peel_refs());
            // A concrete type with NO local impl, or a generic one (whose
            // instantiations `@` resolves per type).
            !family.iter().any(|member| {
                member_def_id(&member.id).is_some_and(|def_id| {
                    let impl_id = self.tcx.parent(def_id);
                    self.tcx
                        .type_of(impl_id)
                        .instantiate_identity()
                        .skip_norm_wip()
                        == peeled
                })
            })
        }
    }

    /// A declaration id (the method at an abstract `Self`) is usable in the
    /// owner's own verification, and in the definition/clauses of a TRAIT
    /// item: those are only ever applied at the trait's abstract `Self` (every
    /// concrete use resolves to an impl's own id), so no two instantiations
    /// can share them.
    fn decl_allowed(&self) -> bool {
        match self.mode {
            ResolveMode::OwnerVc | ResolveMode::TraitMethodCalls => true,
            ResolveMode::LogicDef => self
                .tcx
                .opt_associated_item(self.owner)
                .is_some_and(|item| matches!(item.container, AssocContainer::Trait)),
            ResolveMode::Text | ResolveMode::DeclAtImpl => false,
        }
    }

    /// The implementation a call of the trait declaration `name` denotes when
    /// its receiver has the concrete type the impl gives it.
    ///
    /// The grant resolved `recv.m(..)` to the declaration because at the trait
    /// the receiver's type was abstract (a parameter or `Self::Assoc`), with the
    /// reference peeled as the typed resolution peels it. At the impl that type
    /// is concrete, and the declaration applied to it IS the item rustc's
    /// instance resolution selects for `<ty as Trait>::m` -- not whatever a
    /// receiver-style lookup would find there (an inherent `m` shadows the
    /// trait's for a method call, but the grant never named it). Only a trait
    /// whose one generic parameter is `Self` and a method with no generics of
    /// its own are instantiated, a box or alias receiver is not, and the
    /// answer must be a local logic implementation of exactly this
    /// declaration; the declaration's own default body is not one (its body
    /// may call other methods at an abstract `Self`).
    fn instantiate_decl_call(&self, name: &str, args: &[PureExpr]) -> Option<String> {
        use rustc_middle::ty::TypeVisitableExt as _;
        let member = self.registry.member(name)?;
        if member.kind != LogicFnOwnerKind::TraitDecl
            || !member.receiver_is_self
            || member.arity != args.len()
        {
            return None;
        }
        let decl = member_def_id(name)?;
        let trait_id = self.tcx.parent(decl);
        if self.tcx.def_kind(trait_id) != DefKind::Trait
            || self.tcx.generics_of(trait_id).count() != 1
            || !self.tcx.generics_of(decl).own_params.is_empty()
        {
            return None;
        }
        let ty = self.receiver_type(args.first()?)?;
        let ty = self.tcx.erase_and_anonymize_regions(ty.peel_refs());
        if ty.has_non_region_param()
            || ty.has_escaping_bound_vars()
            || ty.has_aliases()
            || ty.is_box()
        {
            return None;
        }
        let instance = rustc_middle::ty::Instance::try_resolve(
            self.tcx,
            rustc_middle::ty::TypingEnv::fully_monomorphized(),
            decl,
            self.tcx.mk_args(&[ty.into()]),
        )
        .ok()
        .flatten()?;
        let rustc_middle::ty::InstanceKind::Item(item) = instance.def else {
            return None;
        };
        if item == decl
            || self
                .tcx
                .opt_associated_item(item)
                .and_then(|assoc| assoc.trait_item_def_id())
                != Some(decl)
        {
            return None;
        }
        let id = self.id_for_def(item)?;
        (self.registry.member(&id)?.kind == LogicFnOwnerKind::TraitImpl).then_some(id)
    }

    fn resolve_call_name(&self, name: &str, args: &[PureExpr]) -> Option<String> {
        if matches!(
            self.mode,
            ResolveMode::TraitMethodCalls | ResolveMode::DeclAtImpl
        ) {
            return None;
        }
        // `Self::m` in an impl that inherits `m` is the default at the impl's
        // concrete `Self`, not the declaration at an abstract one.
        let (resolved, at_concrete_type) = match self.inherited_self_default(name, args.len()) {
            Some(id) => (id, true),
            None => match self.resolve_call_name_unchecked(name, args)? {
                Resolution::Id(id) => (id, false),
                Resolution::AtConcreteType(id) => (id, true),
                Resolution::Refused => return Some(refused_call_marker(logic_fn_short_name(name))),
            },
        };
        if is_ambiguous_id(&resolved) {
            return None;
        }
        // A declaration symbol stands for the method at an ABSTRACT `Self`:
        // only in the owner's own verification and never with a visible
        // default body (an impl may override it). At a concrete type whose
        // impl does not override it, the default body IS the callee.
        let resolved = match self.registry.member(&resolved) {
            Some(member) if member.kind == LogicFnOwnerKind::TraitDecl && !at_concrete_type => {
                (self.decl_allowed() && !member.decl_has_visible_body).then_some(resolved)?
            }
            _ => resolved,
        };
        Some(match self.type_dependent_form(name, args.len()) {
            Some(form) => self.kept_if_rustc_agrees(form, name, args.len(), args.first(), resolved),
            None => resolved,
        })
    }

    /// How a call `name(..)` with `arity` arguments is written when what it
    /// names depends on a type (`Some`), so rustc's type check must confirm
    /// the reading: a method call the parser lowered to `m(recv, ..)`, and a
    /// path through `Self`, a generic parameter, a trait (`Tr::m`) or a
    /// qualified `<X as Tr>::m`. A path through a module or a type's inherent
    /// items is read as Rust's path resolution reads it (`None`).
    fn type_dependent_form(&self, name: &str, arity: usize) -> Option<CallForm> {
        if name.starts_with('<') {
            return Some(CallForm::Path);
        }
        let segments: Vec<&str> = name.split("::").collect();
        match segments.as_slice() {
            [_single] => {
                let family = self.registry.unresolved_family_for_call(name)?;
                (arity > 0 && dispatches_on_receiver(family, arity)).then_some(CallForm::Method)
            }
            ["Self", _] => Some(CallForm::Path),
            [prefix @ .., _] => {
                if let [param] = prefix {
                    if self.generic_type_param(param) != GenericTypeParam::NotParam {
                        return Some(CallForm::Path);
                    }
                }
                matches!(self.resolve_prefix(prefix), Some(PathTarget::Trait(_)))
                    .then_some(CallForm::Path)
            }
            [] => None,
        }
    }

    /// `id`, the definition the hand lookup chose for a type-dependent call
    /// of `form`, `name` and `arity` on `receiver`, where rustc's type check
    /// of this specification resolved every such call to it; the refusal
    /// marker otherwise. rustc's method probe sees candidates the lookup
    /// does not (a blanket impl of an in-scope trait taken by value, a
    /// where-clause, a user `Deref` level), so an answer it does not confirm
    /// is a guess, and a guess is refused (`spec_calls`). A lowered method
    /// call is refused beside a path call of its name: which one a parsed
    /// `m(recv, ..)` is cannot be told.
    ///
    /// `written` is the call's name as written: a method's name, or a path
    /// call's whole callee path, whose qualifier decides what it names.
    /// `receiver` is the call's receiver (a path call's first argument): its
    /// type as the lookup read it, and the variable it is rooted at, whose
    /// typing rustc must share.
    fn kept_if_rustc_agrees(
        &self,
        form: CallForm,
        written: &str,
        arity: usize,
        receiver: Option<&PureExpr>,
        id: String,
    ) -> String {
        let name = logic_fn_short_name(written);
        #[cfg(test)]
        if self.clause == ClauseRef::HandLookupUnderTest {
            return id;
        }
        let confirmed = member_def_id(&id).is_some_and(|chosen| {
            self.spec_calls
                .get_or_init(|| SpecCalls::of(self.tcx, self.owner, &self.clause))
                .as_ref()
                .is_some_and(|calls| {
                    calls.confirms(
                        self.tcx,
                        form,
                        name,
                        (form == CallForm::Path).then_some(written),
                        arity,
                        receiver.and_then(|receiver| self.receiver_type(receiver)),
                        receiver.and_then(receiver_root),
                        chosen,
                    ) && (form == CallForm::Path || !calls.holds(CallForm::Path, name, arity))
                })
        });
        if std::env::var_os("TRUST_WP_LOGIC_IDENTITY_TRACE").is_some() {
            eprintln!(
                "trust-wp: logic-identity rustc-check owner={} mode={:?} clause={:?} call={written} form={form:?} chosen={id} confirmed={confirmed}",
                self.tcx.def_path_str(self.owner),
                self.mode,
                self.clause
            );
        }
        if confirmed {
            id
        } else {
            refused_call_marker(name)
        }
    }

    fn resolve_call_name_unchecked(&self, name: &str, args: &[PureExpr]) -> Option<Resolution> {
        let family = self.registry.unresolved_family_for_call(name)?;
        let head = name.split("::").next().unwrap_or(name);
        if self.bound.iter().any(|bound| bound == head) {
            // A bare name a parameter or binder binds is that binding, which
            // no definition of the family is; left under its written name,
            // the encoder would dispatch it on its first argument's sort
            // (bare_call_parameter_read_as_logic_method_granted.rs). A path
            // whose head a binding spells is refused with it, not read.
            return Some(Resolution::Refused);
        }
        let short = logic_fn_short_name(name);
        let arity = args.len();
        // Method-style exactly where the encoder would dispatch the call on
        // its first argument's sort: a call left unresolved here is then one
        // the encoder refuses, never one it reads as a method.
        let method_style = arity > 0 && dispatches_on_receiver(family, arity);
        // Every name below is looked up through the owner's MODULE; one the
        // owner's body (or an enclosing body) redeclares means something else
        // in the clause. Withheld, a method-style call is refused, not left
        // for the encoder's receiver dispatch (D-214).
        if path_scope_names(name)
            .any(|written| shadowed_by_body_item(self.tcx, self.owner, written))
        {
            return method_style.then_some(Resolution::Refused);
        }
        if let Some(rest) = name.strip_prefix('<') {
            return self.resolve_qualified(rest, short, arity);
        }
        let segments: Vec<&str> = name.split("::").collect();
        match segments.as_slice() {
            [_single] => {
                let in_blocks = self.block_lookup(short, Namespace::ValueNS);
                if method_style {
                    return self.resolve_bare_method_style(short, &args[0], arity, in_blocks);
                }
                match in_blocks {
                    BlockBinding::Unbound => {}
                    BlockBinding::Def(DefKind::Fn, def_id) => {
                        return self.id_for_def(def_id).map(Resolution::Id)
                    }
                    BlockBinding::Def(..) | BlockBinding::Refused => return None,
                }
                let module = self.owner_module();
                let hits: Vec<DefId> = self
                    .module_children(module, short)
                    .into_iter()
                    .filter(|(kind, _)| matches!(kind, DefKind::Fn))
                    .map(|(_, def_id)| def_id)
                    .collect();
                match hits.as_slice() {
                    [def_id] => self.id_for_def(*def_id).map(Resolution::Id),
                    _ => None,
                }
            }
            // What a `Self` path names is the enclosing impl's or trait's own
            // business; one it does not resolve to a logic definition refuses
            // a method-style call, as an unplaced prefix does below (D-209)
            // (self_path_call_to_program_assoc_fn_read_as_logic_method_granted.rs).
            ["Self", _] => match self.resolve_self_item(short) {
                Some(id) => Some(Resolution::Id(id)),
                None => method_style.then_some(Resolution::Refused),
            },
            [prefix @ .., _] => {
                if let [param] = prefix {
                    match self.generic_type_param(param) {
                        GenericTypeParam::Visible(index) => {
                            if !self.decl_allowed() {
                                return None;
                            }
                            return crate::logic::identity_typed::decl_for_generic_param(
                                self.tcx, self.owner, family, arity, index,
                            )
                            .map(Resolution::Id);
                        }
                        GenericTypeParam::Refused => return Some(Resolution::Refused),
                        GenericTypeParam::NotParam => {}
                    }
                }
                // A prefix the lookup cannot place (an alias, a path into
                // another crate) refuses a method-style call: left under its
                // written name, the encoder would dispatch it on its receiver,
                // which a path call never is (D-196)
                // (path_call_through_type_alias_to_program_assoc_fn_read_as_logic_method_granted.rs).
                let Some(target) = self.resolve_prefix(prefix) else {
                    return method_style.then_some(Resolution::Refused);
                };
                match target {
                    // A local module's `m` is a free function or an import: a
                    // logic definition, or nothing the clause may read.
                    PathTarget::Module(module) => {
                        let hits: Vec<DefId> = self
                            .module_children(module, short)
                            .into_iter()
                            .filter(|(kind, _)| matches!(kind, DefKind::Fn))
                            .map(|(_, def_id)| def_id)
                            .collect();
                        Some(match hits.as_slice() {
                            [def_id] => self
                                .id_for_def(*def_id)
                                .map_or(Resolution::Refused, Resolution::Id),
                            _ => Resolution::Refused,
                        })
                    }
                    PathTarget::Adt(adt) => {
                        self.resolve_on_adt_path(adt, short, args, arity, method_style)
                    }
                    PathTarget::Trait(trait_id) if method_style => {
                        self.resolve_on_trait_path(trait_id, short, &args[0], arity)
                    }
                    PathTarget::Trait(_) => None,
                }
            }
            [] => None,
        }
    }

    /// A written bare `m(recv, ..)` whose every local logic definition is a
    /// method. Rust reads a bare name in the value namespace, where no
    /// associated function is ever in scope, so the call is whatever the block
    /// scopes or the module bind `m` to (bare_call_*_granted.rs). Two bindings
    /// are a trait method in disguise: the model functions `view` (the macros
    /// write `x@` as `view(x)`) and `resolve`, each its trait's method at the
    /// argument's type. A local impl of that trait for the argument's type is
    /// the callee; without one the call is left to the encoder's own reading
    /// of the model function. Every other binding is refused: a program
    /// function, a local, any other item or import.
    fn resolve_bare_method_style(
        &self,
        short: &str,
        receiver: &PureExpr,
        arity: usize,
        in_blocks: BlockBinding,
    ) -> Option<Resolution> {
        let Some(model_trait) = self.bare_model_trait(short, in_blocks) else {
            return Some(Resolution::Refused);
        };
        let family = self.registry.unresolved_family_for_call(short)?;
        let own = model_trait_impls(self.tcx, family, model_trait);
        if own.is_empty() {
            return None;
        }
        let ty = self.receiver_type(receiver)?;
        match self.typed_outcome(&own, ty, arity) {
            (Some(id), true) => Some(Resolution::AtConcreteType(id)),
            _ => None,
        }
    }

    /// `Type::m(..)`. Rust takes the type's inherent associated function
    /// `m`; only when it has none, a method of a trait implemented by the
    /// type. For a local type that is the inherent definition (refused when it
    /// is not a logic one), else the one logic method Rust's lookup at that
    /// very type can select, else refused. An external type's paths
    /// (`Seq::empty`, `Int::min`) keep their reading: the encoder's built-ins.
    fn resolve_on_adt_path(
        &self,
        adt: DefId,
        short: &str,
        args: &[PureExpr],
        arity: usize,
        method_style: bool,
    ) -> Option<Resolution> {
        if !adt.is_local() {
            // A non-local type's item is never a local logic definition, and a
            // method-style call left under its written name is read on its
            // receiver by the encoder
            // (imported_external_adt_path_call_read_as_logic_method_granted.rs).
            return self
                .inherent_item(adt, short)
                .map(Resolution::Id)
                .or_else(|| method_style.then_some(Resolution::Refused));
        }
        let inherent = self.inherent_items(adt, short);
        match inherent.as_slice() {
            [def_id] => {
                return Some(
                    self.id_for_def(*def_id)
                        .map_or(Resolution::Refused, Resolution::Id),
                )
            }
            [] => {}
            _ => return Some(Resolution::Refused),
        }
        let refused = Some(Resolution::Refused);
        let family = self.registry.unresolved_family_for_call(short)?;
        let Some(ty) = args
            .first()
            .filter(|_| method_style)
            .and_then(|arg| self.receiver_type(arg))
        else {
            return refused;
        };
        let at_type = self.tcx.erase_and_anonymize_regions(ty.peel_refs());
        if !matches!(at_type.kind(), TyKind::Adt(def, _) if def.did() == adt) {
            return refused;
        }
        match self.typed_outcome(family, at_type, arity) {
            (Some(id), true)
                if member_def_id(&id).is_some_and(|def_id| {
                    crate::logic::method_lookup::selects_only(
                        self.tcx, short, at_type, def_id, true,
                    )
                }) =>
            {
                Some(Resolution::AtConcreteType(id))
            }
            _ => refused,
        }
    }

    /// `Trait::m(x, ..)`: `<X as Trait>::m` for `x`'s type `X`, an impl of
    /// THAT trait or its default body, whatever else of the name `X` has
    /// (trait_path_call_*_granted.rs). Unresolved, a local trait's path is
    /// refused; an external trait's is left to the encoder.
    fn resolve_on_trait_path(
        &self,
        trait_id: DefId,
        short: &str,
        receiver: &PureExpr,
        arity: usize,
    ) -> Option<Resolution> {
        let refused = trait_id.is_local().then_some(Resolution::Refused);
        let family = self.registry.unresolved_family_for_call(short)?;
        let own = trait_members(self.tcx, family, trait_id);
        let Some(ty) = self.receiver_type(receiver).filter(|_| !own.is_empty()) else {
            return refused;
        };
        match self.typed_outcome(&own, ty, arity) {
            (Some(id), true) => Some(Resolution::AtConcreteType(id)),
            (Some(id), false) => Some(Resolution::Id(id)),
            (None, _) => refused,
        }
    }

    /// The model trait a bare `short(..)` stands for a method of: `View` for
    /// the model `view`, `Resolve` for the model `resolve`, when the scopes
    /// around the clause bind the name to that function (or record no binding:
    /// a dependency's prelude glob). `None` for any other name or binding.
    fn bare_model_trait(&self, short: &str, in_blocks: BlockBinding) -> Option<&'static str> {
        let model_trait = match short {
            "view" => "View",
            "resolve" => "Resolve",
            _ => return None,
        };
        let binding = match in_blocks {
            BlockBinding::Unbound => self.module_value_binding(short),
            BlockBinding::Def(_, def_id) => ValueBinding::Item(def_id),
            BlockBinding::Refused => return None,
        };
        match binding {
            ValueBinding::Item(def_id) if is_model_item(self.tcx, def_id, short) => {
                Some(model_trait)
            }
            ValueBinding::Unbound => Some(model_trait),
            ValueBinding::Item(_) | ValueBinding::Several => None,
        }
    }

    /// What the owner's module binds `name` to in the value namespace.
    fn module_value_binding(&self, name: &str) -> ValueBinding {
        let hits: Vec<DefId> = self
            .tcx
            .module_children_local(self.owner_module())
            .iter()
            .filter(|child| {
                child.ident.name.as_str() == name && child.res.ns() == Some(Namespace::ValueNS)
            })
            .filter_map(|child| child.res.opt_def_id())
            .collect();
        match hits.as_slice() {
            [] => ValueBinding::Unbound,
            [def_id] => ValueBinding::Item(*def_id),
            _ => ValueBinding::Several,
        }
    }

    fn id_for_def(&self, def_id: DefId) -> Option<String> {
        if !def_id.is_local() {
            return None;
        }
        let path = crate_qualified_path(self.tcx, def_id);
        let id = self.registry.id_for_full_path(&path)?;
        // Two definitions printing one path share one id and one `DefId`
        // slot: which of them `id` stands for is not known.
        (member_def_id(id) == Some(def_id) && !is_ambiguous_id(id)).then(|| id.to_string())
    }

    /// The block scopes' answer for `name` around this clause.
    fn block_lookup(&self, name: &str, ns: Namespace) -> BlockBinding {
        match self.owner.as_local() {
            Some(owner) => block_scope::lookup(self.tcx, owner, name, ns, self.position),
            None => BlockBinding::Refused,
        }
    }

    fn owner_module(&self) -> LocalDefId {
        let local = self.owner.expect_local();
        if self.tcx.def_kind(local) == DefKind::Mod {
            return local;
        }
        self.tcx.parent_module_from_def_id(local).to_local_def_id()
    }

    fn module_children(&self, module: LocalDefId, name: &str) -> Vec<(DefKind, DefId)> {
        self.tcx
            .module_children_local(module)
            .iter()
            .filter(|child| child.ident.name.as_str() == name)
            .filter_map(|child| match child.res {
                Res::Def(kind, def_id) => Some((kind, def_id)),
                _ => None,
            })
            .collect()
    }

    fn resolve_prefix(&self, prefix: &[&str]) -> Option<PathTarget> {
        let (first, rest) = prefix.split_first()?;
        let mut current = match *first {
            // `self` and `super` name normal modules: rustc skips the block
            // scopes for both.
            "crate" => PathTarget::Module(CRATE_DEF_ID),
            "self" => PathTarget::Module(self.owner_module()),
            "super" => PathTarget::Module(self.parent_module(self.owner_module())?),
            ident => match self.block_lookup(ident, Namespace::TypeNS) {
                BlockBinding::Unbound => self.type_or_module_child(self.owner_module(), ident)?,
                BlockBinding::Def(kind, def_id) => path_target(kind, def_id)?,
                BlockBinding::Refused => return None,
            },
        };
        for segment in rest {
            let PathTarget::Module(module) = current else {
                return None;
            };
            current = if *segment == "super" {
                PathTarget::Module(self.parent_module(module)?)
            } else {
                self.type_or_module_child(module, segment)?
            };
        }
        Some(current)
    }

    fn parent_module(&self, module: LocalDefId) -> Option<LocalDefId> {
        if module == CRATE_DEF_ID {
            return None;
        }
        Some(self.tcx.parent_module_from_def_id(module).to_local_def_id())
    }

    fn type_or_module_child(&self, module: LocalDefId, name: &str) -> Option<PathTarget> {
        let targets: Vec<PathTarget> = self
            .module_children(module, name)
            .into_iter()
            .filter_map(|(kind, def_id)| path_target(kind, def_id))
            .collect();
        match targets.as_slice() {
            [only] => Some(*only),
            _ => None,
        }
    }

    fn inherent_item(&self, adt: DefId, short: &str) -> Option<String> {
        match self.inherent_items(adt, short).as_slice() {
            [def_id] => self.id_for_def(*def_id),
            _ => None,
        }
    }

    /// Every item named `short` of an inherent impl of `adt`, logic or not.
    fn inherent_items(&self, adt: DefId, short: &str) -> Vec<DefId> {
        let symbol = Symbol::intern(short);
        self.tcx
            .inherent_impls(adt)
            .iter()
            .flat_map(|impl_id| {
                self.tcx
                    .associated_items(*impl_id)
                    .filter_by_name_unhygienic(symbol)
                    .map(|item| item.def_id)
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    fn trait_item_id(&self, trait_id: DefId, short: &str) -> Option<String> {
        let symbol = Symbol::intern(short);
        let item = self
            .tcx
            .associated_items(trait_id)
            .filter_by_name_unhygienic(symbol)
            .next()?;
        self.id_for_def(item.def_id)
    }

    /// The impl or trait whose `Self` the owner sees: the one the owner (or,
    /// for a closure, the item whose body it is in) is an associated item
    /// of. An item nested in an associated function's body does not see it
    /// (E0401), so the walk never passes a second item.
    fn enclosing_impl_or_trait(&self) -> Option<(DefKind, DefId)> {
        let mut current = self.owner;
        while self.tcx.is_typeck_child(current) {
            current = self.tcx.opt_parent(current)?;
        }
        let kind = self.tcx.def_kind(current);
        if matches!(kind, DefKind::Impl { .. } | DefKind::Trait) {
            return Some((kind, current));
        }
        let parent = self.tcx.opt_parent(current)?;
        let parent_kind = self.tcx.def_kind(parent);
        matches!(parent_kind, DefKind::Impl { .. } | DefKind::Trait)
            .then_some((parent_kind, parent))
    }

    /// `Self::m(..)` written inside a trait impl whose CONCRETE self type does
    /// not define `m`: Rust's instance resolution at that type selects the
    /// trait item itself, so the callee is the declaration's default body.
    /// Only `inherited_default` answers — the same rule a receiver-style call
    /// at a concrete type gets — which admits a default that calls nothing,
    /// where the declaration's definition and the default at this `Self` are
    /// one term. This is not the abstract-`Self` meaning the declaration
    /// symbol carries elsewhere, so it bypasses the visible-body refusal in
    /// `resolve_call_name` and nothing else does.
    fn inherited_self_default(&self, name: &str, arity: usize) -> Option<String> {
        use rustc_middle::ty::TypeVisitableExt as _;

        use crate::logic::identity_typed::{inherited_default, TypedOutcome};
        let ["Self", short] = name.split("::").collect::<Vec<_>>()[..] else {
            return None;
        };
        let (DefKind::Impl { of_trait: true }, impl_id) = self.enclosing_impl_or_trait()? else {
            return None;
        };
        if self
            .tcx
            .associated_items(impl_id)
            .filter_by_name_unhygienic(Symbol::intern(short))
            .next()
            .is_some()
        {
            return None;
        }
        let trait_id = self.tcx.impl_opt_trait_id(impl_id)?;
        let self_ty = self.tcx.erase_and_anonymize_regions(
            self.tcx
                .type_of(impl_id)
                .instantiate_identity()
                .skip_norm_wip(),
        );
        if self_ty.has_non_region_param() || self_ty.has_escaping_bound_vars() {
            return None;
        }
        let family = self.registry.family(short)?;
        let members: Vec<&LogicFnFamilyMember> = family
            .iter()
            .filter(|member| {
                member.arity == arity
                    && member_def_id(&member.id)
                        .is_some_and(|def_id| self.tcx.parent(def_id) == trait_id)
            })
            .collect();
        match inherited_default(self.tcx, &members, self_ty) {
            TypedOutcome::Id(id) => Some(id),
            _ => None,
        }
    }

    fn resolve_self_item(&self, short: &str) -> Option<String> {
        let (kind, container) = self.enclosing_impl_or_trait()?;
        let symbol = Symbol::intern(short);
        if let Some(item) = self
            .tcx
            .associated_items(container)
            .filter_by_name_unhygienic(symbol)
            .next()
        {
            return self.id_for_def(item.def_id);
        }
        // A trait impl that does not define the item inherits the trait's
        // default. That is `inherited_self_default`'s case; here the
        // declaration symbol would be read at an abstract `Self`.
        let _ = kind;
        None
    }

    fn generic_type_param(&self, name: &str) -> GenericTypeParam {
        visible_generic_type_param(self.tcx, self.owner, name, self.position)
    }

    /// `<Ty as Trait>::m` (`rest` is the text after `<`): the impl of that
    /// trait for that type, or the trait's default body when the type's impl
    /// does not override it. A local trait's call no rule resolves is
    /// refused: the encoder's receiver dispatch would ignore the trait named
    /// (qualified_trait_call_default_read_as_inherent_granted.rs).
    fn resolve_qualified(&self, rest: &str, short: &str, arity: usize) -> Option<Resolution> {
        let close = rest.rfind(">::")?;
        let inner = &rest[..close];
        let (ty_text, trait_text) = inner.split_once(" as ")?;
        let ty_text = ty_text.trim();
        let trait_segments: Vec<&str> = strip_generic_args(trait_text.trim()).split("::").collect();
        let trait_id = match self.resolve_prefix(&trait_segments)? {
            PathTarget::Trait(trait_id) => trait_id,
            _ => return None,
        };
        if ty_text == "Self" {
            let (kind, container) = self.enclosing_impl_or_trait()?;
            return match kind {
                DefKind::Trait if container == trait_id => self.trait_item_id(trait_id, short),
                DefKind::Impl { .. } if self.tcx.impl_opt_trait_id(container) == Some(trait_id) => {
                    self.resolve_self_item(short)
                }
                _ => None,
            }
            .map(Resolution::Id);
        }
        let generic = self.generic_type_param(ty_text);
        if generic == GenericTypeParam::Refused {
            return Some(Resolution::Refused);
        }
        if let GenericTypeParam::Visible(index) = generic {
            if !self.decl_allowed() {
                return None;
            }
            let family = self.registry.family(short)?;
            return crate::logic::identity_typed::decl_for_generic_param(
                self.tcx, self.owner, family, arity, index,
            )
            .filter(|id| {
                member_def_id(id).is_some_and(|def_id| self.tcx.parent(def_id) == trait_id)
            })
            .map(Resolution::Id);
        }
        let family = self.registry.family(short)?;
        let wanted_adt = if is_primitive_type_name(ty_text) {
            None
        } else {
            let segments: Vec<&str> = strip_generic_args(ty_text).split("::").collect();
            match self.resolve_prefix(&segments)? {
                PathTarget::Adt(adt) => Some(adt),
                _ => return None,
            }
        };
        let ty_has_args = ty_text.contains('<');
        let mut hits = Vec::new();
        for member in family
            .iter()
            .filter(|member| member.kind == LogicFnOwnerKind::TraitImpl)
        {
            let Some(def_id) = member_def_id(&member.id) else {
                continue;
            };
            let impl_id = self.tcx.parent(def_id);
            if self.tcx.impl_opt_trait_id(impl_id) != Some(trait_id) {
                continue;
            }
            let self_ty = self
                .tcx
                .type_of(impl_id)
                .instantiate_identity()
                .skip_norm_wip();
            let matches = match (wanted_adt, self_ty.kind()) {
                (Some(adt), TyKind::Adt(impl_adt, args)) if impl_adt.did() == adt => {
                    // The impl must cover every instantiation, or the written
                    // type must carry no arguments and the ADT none either.
                    let fully_generic = {
                        let mut seen = HashSet::new();
                        args.types().all(
                            |arg| matches!(arg.kind(), TyKind::Param(p) if seen.insert(p.index)),
                        )
                    };
                    fully_generic && (!ty_has_args || args.types().count() > 0)
                }
                (None, _) => self_ty.to_string() == ty_text,
                _ => false,
            };
            if matches {
                hits.push(member.id.clone());
            }
        }
        let refused = trait_id.is_local().then_some(Resolution::Refused);
        match hits.as_slice() {
            [id] => Some(Resolution::Id(id.clone())),
            [] => {
                // No impl member: the default body, at a type the written path
                // names exactly (no generic arguments to instantiate).
                let at_type = wanted_adt
                    .filter(|adt| !ty_has_args && self.tcx.generics_of(*adt).count() == 0)
                    .map(|adt| self.tcx.type_of(adt).instantiate_identity().skip_norm_wip());
                let own: Vec<LogicFnFamilyMember> = family
                    .iter()
                    .filter(|member| {
                        member.kind == LogicFnOwnerKind::TraitDecl
                            && member_def_id(&member.id)
                                .is_some_and(|def_id| self.tcx.parent(def_id) == trait_id)
                    })
                    .cloned()
                    .collect();
                match at_type.map(|ty| {
                    crate::logic::identity_typed::resolve_family_on_type(
                        self.tcx, &own, arity, ty, false, None,
                    )
                }) {
                    Some(crate::logic::identity_typed::TypedOutcome::Id(id)) => {
                        Some(Resolution::AtConcreteType(id))
                    }
                    _ => refused,
                }
            }
            _ => refused,
        }
    }
}

/// What a written call resolved to.
enum Resolution {
    /// A definition; a trait declaration among them stands for the method at
    /// an abstract `Self` (subject to the declaration-symbol rule).
    Id(String),
    /// The definition Rust selects at a concrete type: an impl's method, an
    /// inherent method, or a trait's default body where that type's impl does
    /// not override it.
    AtConcreteType(String),
    /// No logic definition may be read for the written call: refused
    /// outright, never left for the encoder's receiver dispatch.
    Refused,
}

/// What a module binds a bare name to in the value namespace.
enum ValueBinding {
    Unbound,
    Item(DefId),
    Several,
}

/// Whether `def_id` is the model crate's item called `name` (the function or
/// trait a clause spells through `creusot_std`'s prelude).
fn is_model_item(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    !def_id.is_local()
        && tcx.crate_name(def_id.krate).as_str() == "trust_wp_std"
        && tcx
            .opt_item_name(def_id)
            .is_some_and(|item| item.as_str() == name)
}

/// Whether the logic definition `def_id` is `trait_id`'s: the trait's own
/// declaration, or a method of an impl of that trait.
fn member_of_trait(tcx: TyCtxt<'_>, def_id: DefId, trait_id: DefId) -> bool {
    let parent = tcx.parent(def_id);
    parent == trait_id
        || (matches!(tcx.def_kind(parent), DefKind::Impl { of_trait: true })
            && tcx.impl_opt_trait_id(parent) == Some(trait_id))
}

#[derive(Clone, Copy)]
enum PathTarget {
    Module(LocalDefId),
    Adt(DefId),
    Trait(DefId),
}

/// What a path segment bound to `kind` can lead to; `None` refuses the path
/// (an alias, an external module, a value).
fn path_target(kind: DefKind, def_id: DefId) -> Option<PathTarget> {
    match kind {
        DefKind::Mod => def_id.as_local().map(PathTarget::Module),
        DefKind::Struct | DefKind::Enum | DefKind::Union => Some(PathTarget::Adt(def_id)),
        DefKind::Trait => Some(PathTarget::Trait(def_id)),
        _ => None,
    }
}

fn strip_generic_args(text: &str) -> &str {
    text.split('<').next().unwrap_or(text).trim()
}

fn is_primitive_type_name(text: &str) -> bool {
    matches!(
        text,
        "bool"
            | "char"
            | "str"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f32"
            | "f64"
            | "()"
    )
}

/// The type of a bare path expression `name` that denotes a UNIT STRUCT value
/// in the scope of `owner` (`S` in `S.m(..)`), the way rustc resolves it: the
/// one value-namespace item of that name in the owner's module (items and
/// `use` imports alike) is the constructor of a fieldless, non-generic struct.
///
/// Callers must first rule out every binder that could shadow `name` (clause
/// binders, parameters, `result`, body locals): this looks only at the owner's
/// generic parameters, the items its body declares, and the module.
/// Anything else — no such item, a `const`/`fn`/`static`, a tuple struct's
/// constructor, a generic struct whose arguments the clause leaves to
/// inference — is `None`, so the call stays unresolved and is refused.
pub(crate) fn unit_struct_value_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    name: &str,
) -> Option<rustc_middle::ty::Ty<'tcx>> {
    let ty = unit_struct_value_type_in_scope(tcx, owner, name)?;
    // D-178: an impl method that writes no clause of its own is verified
    // against its trait method's (`apply_trait_contract_inheritance`), which
    // were written in the TRAIT's scope. The name is typed only where both
    // scopes give the same answer, so this lookup never reads an inherited
    // clause in the impl's module; a disagreement is a refusal
    // (trait_clause_inherited_resolved_in_impl_scope_unit_struct).
    if let Some(trait_method) = inherited_clause_source(tcx, owner) {
        if unit_struct_value_type_in_scope(tcx, trait_method, name) != Some(ty) {
            return None;
        }
    }
    Some(ty)
}

/// The trait method whose clauses `owner` is verified against, when `owner`
/// is a trait impl method with no `requires`/`ensures` of its own and the
/// trait method has some.
fn inherited_clause_source(tcx: TyCtxt<'_>, owner: DefId) -> Option<DefId> {
    use crate::attr_utils::get_contract_attrs_from_doc;
    let trait_method = tcx.opt_associated_item(owner)?.trait_item_def_id()?;
    let has_clauses = |def_id: DefId| {
        let attrs = tcx.get_all_attrs(def_id);
        !get_contract_attrs_from_doc(attrs, "requires").is_empty()
            || !get_contract_attrs_from_doc(attrs, "ensures").is_empty()
    };
    (!has_clauses(owner) && has_clauses(trait_method)).then_some(trait_method)
}

fn unit_struct_value_type_in_scope<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    name: &str,
) -> Option<rustc_middle::ty::Ty<'tcx>> {
    use rustc_hir::def::{CtorKind, CtorOf, Namespace};
    let local = owner.as_local()?;
    let module = if tcx.def_kind(local) == DefKind::Mod {
        local
    } else {
        tcx.parent_module_from_def_id(local).to_local_def_id()
    };
    if shadowed_by_body_item(tcx, owner, name) {
        return None;
    }
    // A generic parameter of the owner or of a generics parent (its impl or
    // trait, or the function a closure is in) shadows the module's item for
    // the clause: a const parameter is a VALUE of that name
    // (logic_unit_struct_receiver_const_param_shadows).
    if tcx.def_kind(local) != DefKind::Mod
        && std::iter::successors(Some(tcx.generics_of(owner)), |generics| {
            generics.parent.map(|parent| tcx.generics_of(parent))
        })
        .any(|generics| {
            generics
                .own_params
                .iter()
                .any(|param| param.name.as_str() == name)
        })
    {
        return None;
    }
    let values: Vec<(DefKind, DefId)> = tcx
        .module_children_local(module)
        .iter()
        .filter(|child| child.ident.name.as_str() == name)
        .filter_map(|child| match child.res {
            Res::Def(kind, def_id) if kind.ns() == Some(Namespace::ValueNS) => Some((kind, def_id)),
            _ => None,
        })
        .collect();
    let [(DefKind::Ctor(CtorOf::Struct, CtorKind::Const), ctor)] = values.as_slice() else {
        return None;
    };
    let adt = tcx.parent(*ctor);
    if tcx.generics_of(adt).count() != 0 {
        return None;
    }
    Some(tcx.type_of(adt).instantiate_identity().skip_norm_wip())
}

/// Whether a clause of `owner` sees an item named `name` that a lookup through
/// `owner`'s MODULE cannot: one declared inside the body of `owner`, or of a
/// body `owner` is itself nested in.
///
/// A contract clause is type-checked at the head of its owner's body — the
/// `spec_tc` closure there, as Creusot inserts its spec item there — so such an
/// item shadows every module-level item of that name for the clause, and an
/// answer read off the module is a DIFFERENT definition, not a refusal. A glob
/// `use` in one of those bodies counts when what it globs has a child of that
/// name, and whenever that cannot be read. Over-approximate on purpose (an item
/// in an inner block is counted too): the cost of a `true` is a refusal.
pub(crate) fn shadowed_by_body_item(tcx: TyCtxt<'_>, owner: DefId, name: &str) -> bool {
    use rustc_hir::{ItemKind, UseKind};
    let Some(owner) = owner.as_local() else {
        return true;
    };
    tcx.hir_crate_items(()).free_items().any(|item_id| {
        let item = tcx.hir_item(item_id);
        let declares = match item.kind {
            ItemKind::Use(_) => {
                crate::hir_use::item_use_leaves(item)
                    .into_iter()
                    .any(|(path, kind)| match kind {
                        UseKind::Single(ident) => ident.name.as_str() == name,
                        UseKind::Glob => glob_may_import(tcx, path, name),
                        UseKind::Nested { .. } => false,
                    })
            }
            _ => item
                .kind
                .ident()
                .is_some_and(|ident| ident.name.as_str() == name),
        };
        declares
            && tcx
                .opt_local_parent(item.owner_id.def_id)
                .is_some_and(|scope| {
                    tcx.def_kind(scope) != DefKind::Mod
                        && (scope == owner
                            || tcx.is_descendant_of(owner.to_def_id(), scope.to_def_id()))
                })
    })
}

/// Whether the glob import `path::*` can bring `name` into scope: a child of
/// that name in the module (imports included), or a variant of that name of
/// the enum. rustc records a module glob in the type namespace and an enum
/// glob in the value namespace; anything else is unreadable here and counts.
fn glob_may_import(tcx: TyCtxt<'_>, path: &rustc_hir::UsePath<'_>, name: &str) -> bool {
    match (path.res.type_ns, path.res.value_ns) {
        (Some(Res::Def(DefKind::Mod, module)), _) => match module.as_local() {
            Some(local) => tcx
                .module_children_local(local)
                .iter()
                .any(|child| child.ident.name.as_str() == name),
            None => tcx
                .module_children(module)
                .iter()
                .any(|child| child.ident.name.as_str() == name),
        },
        (None, Some(Res::Def(DefKind::Enum, adt))) => tcx
            .adt_def(adt)
            .variants()
            .iter()
            .any(|variant| variant.name.as_str() == name),
        _ => true,
    }
}

/// The written names of a logic-function call path that resolution looks up
/// in the owner's scope: a bare name itself, else every identifier of its
/// qualifier (`a::b::m` -> `a`, `b`; `<T as x::Tr>::m` -> `T`, `x`, `Tr`).
pub(crate) fn path_scope_names(name: &str) -> impl Iterator<Item = &str> {
    let qualifier = name
        .rsplit_once("::")
        .map_or(name, |(qualifier, _)| qualifier);
    qualifier
        .split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
        .filter(|word| {
            !word.is_empty()
                && !word.as_bytes()[0].is_ascii_digit()
                && !matches!(
                    *word,
                    "Self" | "crate" | "self" | "super" | "as" | "mut" | "dyn"
                )
        })
}

/// Every name the body of `owner` binds (its parameters included), at the
/// one type it is bound at; `None` for a name bound at two types.
pub(crate) fn body_binding_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
) -> HashMap<String, Option<rustc_middle::ty::Ty<'tcx>>> {
    body_local_types(tcx, owner)
}

/// Every name the body of `owner` binds, mapped to its Rust type — `None`
/// where the name is bound more than once at different types, or where
/// typeck has no type for the binding.
///
/// Nested bodies (closures, nested items) are NOT visited: their bindings are
/// not in scope of `owner`'s clauses.
fn body_local_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
) -> HashMap<String, Option<rustc_middle::ty::Ty<'tcx>>> {
    use rustc_hir::intravisit::{walk_body, Visitor};

    struct Collect<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        out: &'a mut HashMap<String, Option<rustc_middle::ty::Ty<'tcx>>>,
    }

    impl<'tcx> Visitor<'tcx> for Collect<'_, 'tcx> {
        fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
            if let rustc_hir::PatKind::Binding(_, hir_id, ident, _) = pat.kind {
                let ty = self
                    .typeck
                    .node_type_opt(hir_id)
                    .map(|ty| self.tcx.erase_and_anonymize_regions(ty));
                match self.out.entry(ident.name.to_string()) {
                    std::collections::hash_map::Entry::Occupied(mut slot) => {
                        if *slot.get() != ty {
                            slot.insert(None);
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(slot) => {
                        slot.insert(ty);
                    }
                }
            }
            rustc_hir::intravisit::walk_pat(self, pat);
        }
    }

    let mut out = HashMap::new();
    let Some(local) = owner.as_local() else {
        return out;
    };
    let Some(body_id) = tcx.hir_maybe_body_owned_by(local) else {
        return out;
    };
    if tcx.has_typeck_results(local) {
        let typeck = tcx.typeck(local);
        let mut collect = Collect {
            tcx,
            typeck,
            out: &mut out,
        };
        walk_body(&mut collect, &body_id);
    }
    out
}

/// The names a pattern binds, each with the Rust type it has when the matched
/// value has type `ty`.
///
/// Type-free in exactly the places rustc is: a binding whose type does not
/// follow from `ty` and the pattern gets `None`, and an unknown type refuses
/// a call rather than resolving it.
fn pattern_binding_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    pattern: &Pattern,
    ty: Option<rustc_middle::ty::Ty<'tcx>>,
    out: &mut Vec<(String, Option<rustc_middle::ty::Ty<'tcx>>)>,
) {
    match pattern {
        Pattern::Binding(name) => out.push((name.clone(), ty)),
        Pattern::Alias { alias, pattern } => {
            out.push((alias.clone(), ty));
            pattern_binding_types(tcx, pattern, ty, out);
        }
        Pattern::Constructor { name, inner } => {
            if let Some(inner) = inner {
                let fields = ty.and_then(|ty| constructor_field_types(tcx, ty, name));
                match inner.as_ref() {
                    Pattern::Tuple(items) => {
                        let aligned = fields
                            .as_ref()
                            .is_some_and(|fields| fields.len() == items.len());
                        for (index, item) in items.iter().enumerate() {
                            let field = aligned
                                .then(|| fields.as_ref().and_then(|f| f.get(index).copied()))
                                .flatten();
                            pattern_binding_types(tcx, item, field, out);
                        }
                    }
                    single => {
                        let field = fields
                            .as_ref()
                            .filter(|fields| fields.len() == 1)
                            .and_then(|fields| fields.first().copied());
                        pattern_binding_types(tcx, single, field, out);
                    }
                }
            }
        }
        Pattern::Tuple(items) => {
            let elements = ty.and_then(|ty| match ty.peel_refs().kind() {
                TyKind::Tuple(elements) if elements.len() == items.len() => Some(elements.to_vec()),
                _ => None,
            });
            for (index, item) in items.iter().enumerate() {
                let element = elements.as_ref().and_then(|e| e.get(index).copied());
                pattern_binding_types(tcx, item, element, out);
            }
        }
        _ => {}
    }
}

/// The field types of the variant `name` of `ty`, instantiated at `ty`'s own
/// arguments. `None` unless `ty` is an ADT carrying exactly that variant.
fn constructor_field_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    name: &str,
) -> Option<Vec<rustc_middle::ty::Ty<'tcx>>> {
    let ty = ty.peel_refs();
    let TyKind::Adt(adt, args) = ty.kind() else {
        return None;
    };
    if adt.is_box() {
        return None;
    }
    let short = name.rsplit("::").next().unwrap_or(name);
    let variant = if adt.is_enum() {
        adt.variants()
            .iter()
            .find(|variant| tcx.item_name(variant.def_id).as_str() == short)?
    } else {
        let variant = adt.non_enum_variant();
        if tcx.item_name(adt.did()).as_str() != short {
            return None;
        }
        variant
    };
    Some(
        variant
            .fields
            .iter()
            .map(|field| tcx.erase_and_anonymize_regions(field.ty(tcx, *args).skip_norm_wip()))
            .collect(),
    )
}

#[cfg(test)]
#[path = "identity_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "identity_spelling_tests.rs"]
mod spelling_tests;
