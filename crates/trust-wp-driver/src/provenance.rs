// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! DefId provenance for builtin / library-spec identity.
//!
//! Standard-library and spec-library contracts are stored in tables keyed by
//! PRINTED paths (`core::cmp::max`, `alloc::vec::Vec::len`, ...). A printed
//! path is not an identity: `tcx.def_path_str` omits the crate for LOCAL items,
//! so a user item `crate::core::cmp::max` prints exactly like the real
//! `core::cmp::max`. Any site that grants a fact (a spec, an axiom, a sort, a
//! passthrough) from a printed-path match must therefore first establish, from
//! the `DefId`, that the item really comes from the crate the table describes.
//!
//! Every such check goes through this module.

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;

/// Crates whose items the hardcoded std spec tables describe.
pub(crate) const STD_CRATES: &[&str] = &["core", "alloc", "std"];

/// Crates whose items the trust-wp-std / creusot spec tables describe.
/// `creusot_std`, `creusot_contracts` and `trust_wp` are re-export shims of
/// `trust_wp_std`.
pub(crate) const SPEC_LIBRARY_CRATES: &[&str] = &[
    "trust_wp_std",
    "creusot_std",
    "creusot_contracts",
    "trust_wp",
];

/// Where an item is defined, as far as builtin-spec identity is concerned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ItemProvenance {
    /// Defined in the crate being verified. Never a library item, whatever it
    /// prints as.
    Local,
    /// Defined in `core`, `alloc` or `std`.
    Std,
    /// Defined in a trust-wp / creusot spec library crate.
    SpecLibrary,
    /// Defined in some other foreign crate.
    OtherForeign,
}

impl ItemProvenance {
    /// True when builtin (std / spec-library) tables may describe this item.
    pub(crate) fn is_builtin_provider(self) -> bool {
        matches!(self, Self::Std | Self::SpecLibrary)
    }
}

/// Pure classification from `(is_local, crate_name)`.
pub(crate) fn classify_crate(is_local: bool, crate_name: &str) -> ItemProvenance {
    if is_local {
        ItemProvenance::Local
    } else if STD_CRATES.contains(&crate_name) {
        ItemProvenance::Std
    } else if SPEC_LIBRARY_CRATES.contains(&crate_name) {
        ItemProvenance::SpecLibrary
    } else {
        ItemProvenance::OtherForeign
    }
}

/// Classify the crate an item is defined in.
///
/// `core` and `alloc` are additionally anchored on lang items (`Sized` lives in
/// the real `core`, `Box` in the real `alloc`): a foreign crate that merely
/// carries one of those names is `OtherForeign`.
pub(crate) fn item_provenance(tcx: TyCtxt<'_>, def_id: DefId) -> ItemProvenance {
    if def_id.is_local() {
        return ItemProvenance::Local;
    }
    let name = tcx.crate_name(def_id.krate);
    let class = classify_crate(false, name.as_str());
    if class == ItemProvenance::Std {
        let anchor = match name.as_str() {
            "core" => tcx.lang_items().sized_trait(),
            "alloc" => tcx.lang_items().owned_box(),
            _ => None,
        };
        if anchor.is_some_and(|anchor| anchor.krate != def_id.krate) {
            return ItemProvenance::OtherForeign;
        }
    }
    class
}

/// True when builtin std / spec-library tables may describe `def_id`.
pub(crate) fn is_builtin_provider(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    item_provenance(tcx, def_id).is_builtin_provider()
}

/// True when `def_id` is defined in `core`, `alloc` or `std`.
pub(crate) fn is_std_item(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    item_provenance(tcx, def_id) == ItemProvenance::Std
}

/// True when `def_id` is defined in a trust-wp / creusot spec library.
pub(crate) fn is_spec_library_item(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    item_provenance(tcx, def_id) == ItemProvenance::SpecLibrary
}

/// Path roots owned by the builtin tables. A printed path starting with one of
/// these names a library item ONLY if its `DefId` says so.
pub(crate) const RESERVED_PATH_ROOTS: &[&str] = &[
    "core",
    "alloc",
    "std",
    "trust_wp_std",
    "creusot_std",
    "creusot_contracts",
    "trust_wp",
];

/// The first path segment of a printed path, skipping a leading `::`, `<`,
/// `&`, `&mut ` or `*const `/`*mut ` so that UFCS and reference-qualified forms
/// are covered.
pub(crate) fn printed_path_root(path: &str) -> &str {
    let mut rest = path.trim_start();
    loop {
        let before = rest;
        for prefix in ["::", "<", "&mut ", "&", "*const ", "*mut ", "dyn "] {
            if let Some(stripped) = rest.strip_prefix(prefix) {
                rest = stripped.trim_start();
            }
        }
        if rest == before {
            break;
        }
    }
    let end = rest
        .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
        .unwrap_or(rest.len());
    &rest[..end]
}

/// True when a printed path starts at a root owned by the builtin tables.
pub(crate) fn path_has_reserved_root(path: &str) -> bool {
    RESERVED_PATH_ROOTS.contains(&printed_path_root(path))
}

/// Whether a printed-path lookup for `def_id` in the builtin/extern spec
/// tables is permitted, and which tables it may consult.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PathLookupScope {
    /// No path-keyed table may describe this item.
    None,
    /// Only user `extern_spec!` entries, and only for a path outside the
    /// reserved roots (a foreign non-library crate).
    ExternOnly,
    /// Extern specs and the builtin std/spec-library tables.
    Full,
}

/// Pure decision behind [`path_lookup_scope`].
pub(crate) fn path_lookup_scope_for(provenance: ItemProvenance, path: &str) -> PathLookupScope {
    match provenance {
        ItemProvenance::Local => PathLookupScope::None,
        ItemProvenance::Std | ItemProvenance::SpecLibrary => PathLookupScope::Full,
        ItemProvenance::OtherForeign if path_has_reserved_root(path) => PathLookupScope::None,
        ItemProvenance::OtherForeign => PathLookupScope::ExternOnly,
    }
}

pub(crate) fn path_lookup_scope(tcx: TyCtxt<'_>, def_id: DefId, path: &str) -> PathLookupScope {
    path_lookup_scope_for(item_provenance(tcx, def_id), path)
}

/// Whether a BUILTIN table contract (std / spec-library, as opposed to a
/// user-authored `extern_spec!`) may describe one particular call.
///
/// The builtin tables state facts about library code, but library code can run
/// USER code: a trait method call dispatches to the impl of the Self type
/// (`a == a` on a local `S` calls the local `<S as PartialEq>::eq`), a trait
/// default method calls the other methods of that impl, and a generic library
/// item calls user code through its trait bounds (`Option<S>::eq` calls
/// `S::eq`, `core::cmp::max::<S>` calls `S::cmp`). A concrete table fact such as
/// `result == (self@ == rhs@)` is only a fact about the library's OWN
/// behaviour, so it is admitted only when that is the behaviour that runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BuiltinSpecAdmission {
    /// The call runs library code on library semantics: builtin contracts apply.
    Admitted,
    /// The call may run user code (or could not be resolved): no builtin
    /// contract may describe it. User `extern_spec!` entries still apply.
    Refused,
}

/// A call site: the callee `FnDef` with its generic arguments, and the item
/// whose body contains the call (for the typing environment of a generic call).
#[derive(Clone, Copy, Debug)]
pub(crate) struct CallSite<'tcx> {
    pub(crate) callee: DefId,
    pub(crate) args: rustc_middle::ty::GenericArgs<'tcx>,
    pub(crate) caller: Option<DefId>,
}

impl<'tcx> CallSite<'tcx> {
    /// The call site of a MIR call operand, when it is a direct `FnDef`.
    pub(crate) fn of_operand(
        func: &rustc_middle::mir::Operand<'tcx>,
        caller: Option<DefId>,
    ) -> Option<Self> {
        let rustc_middle::mir::Operand::Constant(constant) = func else {
            return None;
        };
        let rustc_middle::ty::TyKind::FnDef(callee, args) = constant.const_.ty().kind() else {
            return None;
        };
        Some(Self {
            callee: *callee,
            args: args.skip_binder(),
            caller,
        })
    }
}

/// Decide [`BuiltinSpecAdmission`] for a call site. `None` (no call site
/// available) is refused.
pub(crate) fn builtin_spec_admission<'tcx>(
    tcx: TyCtxt<'tcx>,
    site: Option<CallSite<'tcx>>,
) -> BuiltinSpecAdmission {
    let admitted = site.is_some_and(|site| {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            call_runs_builtin_semantics(tcx, site)
        }))
        .unwrap_or(false)
    });
    if std::env::var_os("TRUST_WP_ADMISSION_DUMP").is_some() {
        match site {
            Some(site) => eprintln!(
                "TRUST_WP_ADMISSION callee={} args={:?} admitted={admitted}",
                tcx.def_path_str(site.callee),
                site.args
            ),
            None => eprintln!("TRUST_WP_ADMISSION no-call-site admitted=false"),
        }
    }
    if admitted {
        BuiltinSpecAdmission::Admitted
    } else {
        BuiltinSpecAdmission::Refused
    }
}

/// Admission for a MIR call operand inside `caller`'s body.
pub(crate) fn builtin_spec_admission_for_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &rustc_middle::mir::Operand<'tcx>,
    caller: Option<DefId>,
) -> BuiltinSpecAdmission {
    builtin_spec_admission(tcx, CallSite::of_operand(func, caller))
}

/// True when the trait method `def_id` belongs to `Fn` / `FnMut` / `FnOnce`.
///
/// The builtin contracts of those methods are stated entirely through the
/// callee's OWN `precondition` / `postcondition` predicates (the closure's or
/// function's contract), so they describe any callee, user code included.
fn is_fn_family_trait_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.trait_of_assoc(def_id)
        .is_some_and(|trait_def_id| tcx.fn_trait_kind_from_def_id(trait_def_id).is_some())
}

/// Trait bounds that cannot route a library item into user-defined behaviour:
/// auto traits, the sizedness / tuple / destruct / unsize marker lang items,
/// the closure traits (whose contracts are the callee's own predicates), and
/// the SEALED `core::slice::SliceIndex` (no impl outside `core` is possible).
fn trait_bound_is_semantics_free(tcx: TyCtxt<'_>, trait_def_id: DefId) -> bool {
    use rustc_attr_ir::LangItem;
    if tcx.trait_is_auto(trait_def_id) || tcx.fn_trait_kind_from_def_id(trait_def_id).is_some() {
        return true;
    }
    if [
        LangItem::Sized,
        LangItem::MetaSized,
        LangItem::PointeeSized,
        LangItem::Tuple,
        LangItem::Destruct,
        LangItem::Unsize,
        LangItem::PointeeTrait,
        LangItem::DiscriminantKind,
    ]
    .into_iter()
    .any(|item| tcx.is_lang_item(trait_def_id, item))
    {
        return true;
    }
    if is_std_item(tcx, trait_def_id)
        && tcx.crate_name(trait_def_id.krate).as_str() == "core"
        && tcx
            .opt_item_name(trait_def_id)
            .is_some_and(|name| name.as_str() == "SliceIndex")
    {
        return true;
    }
    is_code_free_library_trait(tcx, trait_def_id)
}

/// A library trait that declares NO associated functions and whose supertraits
/// are all semantics-free (for example the spec library's
/// `SnapshotMutRefCapture`, which only carries associated types). A bound on it cannot make library code run any impl's
/// code: there is no method to call through it, and no supertrait method is
/// reachable through it. Associated types it projects are normalized into the
/// instance's arguments, whose own bounds are checked separately.
fn is_code_free_library_trait(tcx: TyCtxt<'_>, trait_def_id: DefId) -> bool {
    if !is_builtin_provider(tcx, trait_def_id) {
        return false;
    }
    let has_fn = tcx
        .associated_items(trait_def_id)
        .in_definition_order()
        .any(|item| matches!(item.kind, rustc_middle::ty::AssocKind::Fn { .. }));
    if has_fn {
        return false;
    }
    // Every supertrait must itself be semantics-free (the implicit sizedness
    // supertraits are); outlives clauses carry no code, and neither do
    // projection bounds on a semantics-free trait's associated types. Trait hierarchies are
    // acyclic, so the recursion terminates.
    tcx.explicit_super_clauses_of(trait_def_id)
        .skip_binder()
        .iter()
        .all(|(clause, _)| match clause.as_trait_clause() {
            Some(super_trait) => {
                let super_def_id = super_trait.skip_binder().trait_ref.def_id;
                super_def_id != trait_def_id && trait_bound_is_semantics_free(tcx, super_def_id)
            }
            // A projection bound (`Thin` is `Pointee<Metadata = ()>`) only
            // constrains an associated type of a semantics-free trait.
            None => {
                clause.as_type_outlives_clause().is_some()
                    || clause.as_projection_clause().is_some_and(|projection| {
                        let trait_of_term =
                            projection.skip_binder().projection_term.trait_def_id(tcx);
                        trait_of_term != trait_def_id
                            && trait_bound_is_semantics_free(tcx, trait_of_term)
                    })
            }
        })
}

/// True when every type inside `ty` has library-defined behaviour: scalars,
/// `str`, `!`, references / pointers / arrays / slices / tuples / fn pointers
/// of such types, and ADTs DEFINED in a builtin provider crate. A local or
/// other-foreign ADT, a type parameter, an unnormalized projection, a `dyn`
/// object or a function item may carry user-defined impls. A closure counts
/// when its captures do (see the arm below).
fn type_has_builtin_semantics(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> bool {
    use rustc_middle::ty::TyKind;
    ty.walk().all(|arg| {
        let Some(component) = arg.as_type() else {
            return true;
        };
        match component.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Never
            | TyKind::Array(..)
            | TyKind::Slice(_)
            | TyKind::Ref(..)
            | TyKind::RawPtr(..)
            | TyKind::Tuple(_)
            | TyKind::FnPtr(..) => true,
            TyKind::Adt(adt, _) => is_builtin_provider(tcx, adt.did()),
            // A closure type cannot receive a user impl of a library trait
            // (it is unnameable, and a blanket impl of a foreign trait over an
            // uncovered type parameter is an orphan). Its non-`Fn` impls are
            // the compiler's structural ones (`Clone`/`Copy` over the captures,
            // auto traits) or library blanket impls that call it through the
            // `Fn` traits, whose builtin contracts are the closure's OWN
            // predicates. The walk continues into the closure's generic
            // arguments, so every capture type must itself have builtin
            // semantics (a captured local type with a hand-written `Clone`
            // makes the closure's `Clone` user code).
            TyKind::Closure(..) => true,
            _ => false,
        }
    })
}

/// `PartialEq`, `PartialOrd`, `Eq` or `Ord`.
fn is_comparison_trait(tcx: TyCtxt<'_>, trait_def_id: DefId) -> bool {
    let lang = tcx.lang_items();
    lang.eq_trait() == Some(trait_def_id)
        || lang.partial_ord_trait() == Some(trait_def_id)
        || tcx.is_diagnostic_item(rustc_span::sym::Eq, trait_def_id)
        || tcx.is_diagnostic_item(rustc_span::sym::Ord, trait_def_id)
}

/// The comparison trait `def_id` is a method of, directly or through the impl
/// it belongs to.
fn comparison_trait_of_method(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    let trait_def_id = tcx.trait_of_assoc(def_id).or_else(|| {
        let impl_def_id = tcx.impl_of_assoc(def_id)?;
        matches!(
            tcx.def_kind(impl_def_id),
            rustc_hir::def::DefKind::Impl { of_trait: true }
        )
        .then(|| tcx.impl_trait_ref(impl_def_id).skip_binder().def_id)
    })?;
    is_comparison_trait(tcx, trait_def_id).then_some(trait_def_id)
}

fn type_contains_float(ty: rustc_middle::ty::Ty<'_>) -> bool {
    ty.walk().any(|arg| {
        arg.as_type()
            .is_some_and(|component| matches!(component.kind(), rustc_middle::ty::TyKind::Float(_)))
    })
}

fn call_runs_builtin_semantics<'tcx>(tcx: TyCtxt<'tcx>, site: CallSite<'tcx>) -> bool {
    use rustc_middle::ty::{self, TypeVisitableExt};

    if !is_builtin_provider(tcx, site.callee) {
        return false;
    }
    // The builtin comparison contracts read `PartialEq` as logical equality
    // and `PartialOrd` as a total order (`self@ == rhs@`, `self@ < rhs@`),
    // which is what they are on integers and never on a float: IEEE `==` is
    // false of NaN and true of `0.0 == -0.0`, and every ordered comparison
    // with NaN is false. So a comparison method over a float-carrying type,
    // or a library item whose comparison bound a float discharges
    // (`[f64]::contains`, `Option<f64>: PartialEq`), runs no builtin contract.
    if comparison_trait_of_method(tcx, site.callee).is_some()
        && site.args.types().any(type_contains_float)
    {
        return false;
    }
    if is_fn_family_trait_method(tcx, site.callee) {
        return true;
    }
    let typing_env = if site.args.has_non_region_param() || site.args.has_aliases() {
        match site.caller {
            Some(caller) => ty::TypingEnv::post_analysis(tcx, caller),
            None => return false,
        }
    } else {
        ty::TypingEnv::fully_monomorphized()
    };
    let Ok(args) = tcx.try_normalize_erasing_regions(
        typing_env,
        rustc_middle::ty::set_aliases_to_non_rigid(tcx, site.args),
    ) else {
        return false;
    };
    // The same question over the arguments as they resolve: an opaque return
    // type (`fn hide(x: f64) -> impl PartialEq`) names its float only once
    // revealed, and the primitive float impl it resolves to has no arguments
    // left to show it to the check below.
    if comparison_trait_of_method(tcx, site.callee).is_some()
        && args.types().any(type_contains_float)
    {
        return false;
    }
    let resolution = ty::Instance::try_resolve(tcx, typing_env, site.callee, args);
    if std::env::var_os("TRUST_WP_ADMISSION_DUMP").is_some() {
        eprintln!("TRUST_WP_ADMISSION_RESOLVE {resolution:?}");
    }
    let Ok(Some(instance)) = resolution else {
        // Unresolvable (for example a `T: PartialEq` call in a generic body):
        // the impl that runs is unknown.
        return false;
    };
    let resolved = match instance.def {
        ty::InstanceKind::Item(did) | ty::InstanceKind::Intrinsic(did) => did,
        _ => return false,
    };
    if comparison_trait_of_method(tcx, resolved).is_some()
        && instance.args.types().any(type_contains_float)
    {
        return false;
    }
    // The item that actually runs must itself be library code.
    if !is_builtin_provider(tcx, resolved) {
        return false;
    }
    // A trait DEFAULT method body runs the other methods of Self's impl.
    if tcx.trait_of_assoc(resolved).is_some()
        && !tcx.impl_of_assoc(resolved).is_some()
        && instance
            .args
            .types()
            .next()
            .is_none_or(|self_ty| !type_has_builtin_semantics(tcx, self_ty))
    {
        return false;
    }
    // Every trait bound the running item relies on must be discharged by
    // library behaviour: its types (Self and trait arguments) must have
    // builtin semantics, unless the trait cannot carry user behaviour.
    let predicates = tcx.clauses_of(resolved).instantiate(tcx, instance.args);
    for clause in predicates.clauses {
        let clause = clause.skip_norm_wip();
        let Some(trait_clause) = clause.as_trait_clause() else {
            continue;
        };
        let trait_ref = trait_clause.skip_binder().trait_ref;
        if trait_bound_is_semantics_free(tcx, trait_ref.def_id) {
            continue;
        }
        if is_comparison_trait(tcx, trait_ref.def_id)
            && trait_ref.args.types().any(type_contains_float)
        {
            return false;
        }
        for ty_arg in trait_ref.args.types() {
            if ty_arg.has_escaping_bound_vars() {
                return false;
            }
            let ty_arg = tcx
                .try_normalize_erasing_regions(
                    typing_env,
                    rustc_middle::ty::set_aliases_to_non_rigid(tcx, ty_arg),
                )
                .unwrap_or(ty_arg);
            if !type_has_builtin_semantics(tcx, ty_arg) {
                if std::env::var_os("TRUST_WP_ADMISSION_DUMP").is_some() {
                    eprintln!(
                        "TRUST_WP_ADMISSION_BOUND {} on {ty_arg:?}",
                        tcx.def_path_str(trait_ref.def_id)
                    );
                }
                return false;
            }
        }
    }
    true
}

/// Look up a path-keyed spec (extern_spec! table, then builtin std tables) for
/// the item `def_id` whose printed path is `path`, honouring provenance.
///
/// `path` must be a printed path OF `def_id` (plain or UFCS form). A local item
/// never matches; a foreign non-library item only matches user extern specs.
/// A builtin-table contract is returned only under
/// [`BuiltinSpecAdmission::Admitted`] for the call being described.
///
/// `site` is the call the spec is looked up for. The std-spec terms only a
/// call can resolve (the byte size of the element type an allocation-sizing
/// function is instantiated at) are rewritten here, from that call's own
/// generic arguments, so every lane that reads a spec through this function
/// owes the same precondition the ensures it is granted rests on. Without a
/// site those terms stay markers, and the encoder refuses them.
pub(crate) fn lookup_spec_for_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    admission: BuiltinSpecAdmission,
    extern_specs: Option<&std::collections::HashMap<String, trust_wp_driver::StdSpec>>,
    path: &str,
    site: Option<CallSite<'tcx>>,
) -> Option<trust_wp_driver::StdSpec> {
    lookup_spec_for_def_uninstantiated(tcx, def_id, admission, extern_specs, path)
        .map(|spec| crate::std_site::instantiate_std_site_markers(tcx, site, spec))
}

fn lookup_spec_for_def_uninstantiated(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    admission: BuiltinSpecAdmission,
    extern_specs: Option<&std::collections::HashMap<String, trust_wp_driver::StdSpec>>,
    path: &str,
) -> Option<trust_wp_driver::StdSpec> {
    match path_lookup_scope(tcx, def_id, path) {
        PathLookupScope::None => None,
        PathLookupScope::ExternOnly => {
            trust_wp_driver::lookup_extern_spec_only(extern_specs?, path)
        }
        PathLookupScope::Full => extern_specs
            .and_then(|specs| trust_wp_driver::lookup_extern_spec_only(specs, path))
            .or_else(|| {
                let spec = trust_wp_driver::lookup_spec_with_extern(None, path)?;
                match admission {
                    BuiltinSpecAdmission::Admitted => Some(spec),
                    BuiltinSpecAdmission::Refused => opaque_predicate_restriction(&spec),
                }
            }),
    }
}

/// The part of a builtin contract that still describes a call whose running
/// impl is local or unknown ([`BuiltinSpecAdmission::Refused`]).
///
/// A clause that is ONE application of an opaque per-impl predicate
/// `T::<method>.{precondition,postcondition,postcondition_once,
/// postcondition_mut}(<args>)` states nothing about any particular impl
/// (`T::clone`'s postcondition is whatever the impl that runs guarantees), so
/// it describes a local or generic impl as faithfully as a library one. Every
/// other clause is a library fact: `T::clone.postcondition(..) ==> result ==
/// *self` would make ANY clone an identity.
///
/// - `ensures`: only the opaque clauses are kept (dropping a fact is sound);
/// - `requires`: every clause must be opaque, otherwise nothing is returned
///   (dropping an obligation would check less);
/// - the result must keep at least one clause.
///
/// The `T::` receiver form is required literally: a concrete receiver such as
/// `core::default::Default::default` carries ground axioms and is excluded.
fn opaque_predicate_restriction(
    spec: &trust_wp_driver::StdSpec,
) -> Option<trust_wp_driver::StdSpec> {
    if !spec
        .requires
        .iter()
        .all(|clause| is_opaque_trait_predicate_clause(clause))
    {
        return None;
    }
    let ensures: Vec<String> = spec
        .ensures
        .iter()
        .filter(|clause| is_opaque_trait_predicate_clause(clause))
        .cloned()
        .collect();
    if spec.requires.is_empty() && ensures.is_empty() {
        return None;
    }
    Some(trust_wp_driver::StdSpec {
        inv_requires: Vec::new(),
        capture_inv_requires: Vec::new(),
        requires: spec.requires.clone(),
        ensures,
        param_names: spec.param_names.clone(),
    })
}

fn is_opaque_trait_predicate_clause(clause: &str) -> bool {
    let clause = clause.trim();
    let Some(rest) = clause.strip_prefix("T::") else {
        return false;
    };
    let method_end = rest
        .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
        .unwrap_or(rest.len());
    if method_end == 0 {
        return false;
    }
    let rest = &rest[method_end..];
    let Some(rest) = [
        "precondition(",
        "postcondition_once(",
        "postcondition_mut(",
        "postcondition(",
    ]
    .iter()
    .find_map(|predicate| {
        rest.strip_prefix('.')
            .and_then(|r| r.strip_prefix(predicate))
    }) else {
        return false;
    };
    // `rest` is `<args>)`: balanced, ending exactly at the closing paren of the
    // predicate application, over plain argument syntax only.
    let mut depth = 1usize;
    for (idx, ch) in rest.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return idx + 1 == rest.len();
                }
            }
            c if c.is_ascii_alphanumeric() || matches!(c, '_' | ',' | ' ' | '^' | '*') => {}
            _ => return false,
        }
    }
    false
}

/// Whether ANY spec (user extern or builtin) is known for `def_id`, regardless
/// of call-site admission. For existence checks that REFUSE when no contract
/// is known; never use it to grant a fact.
pub(crate) fn spec_exists_for_def(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    extern_specs: Option<&std::collections::HashMap<String, trust_wp_driver::StdSpec>>,
    path: &str,
) -> bool {
    match path_lookup_scope(tcx, def_id, path) {
        PathLookupScope::None => false,
        PathLookupScope::ExternOnly => extern_specs
            .and_then(|specs| trust_wp_driver::lookup_extern_spec_only(specs, path))
            .is_some(),
        PathLookupScope::Full => {
            trust_wp_driver::lookup_spec_with_extern(extern_specs, path).is_some()
        }
    }
}

/// Printed path of `def_id` when builtin tables may describe it, else `None`.
/// Use this for recognisers that match a printed path against a builtin name.
pub(crate) fn builtin_def_path_str(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    is_builtin_provider(tcx, def_id).then(|| tcx.def_path_str(def_id))
}

/// Local items whose printed path starts at a reserved root (for example
/// `mod core { pub mod cmp { .. } }` at the crate root).
///
/// Every table lookup is DefId-gated, but hundreds of recognisers still read
/// printed paths; a crate that defines lookalike library paths is refused
/// outright so that no recogniser can be fooled by one. Returns the printed
/// paths of the offending crate-root items.
pub(crate) fn local_reserved_root_items(tcx: TyCtxt<'_>) -> Vec<String> {
    let mut offenders = Vec::new();
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        // Only items directly under the crate root decide the printed root.
        let Some(parent) = tcx.opt_parent(def_id) else {
            continue;
        };
        if parent != rustc_hir::def_id::CRATE_DEF_ID.to_def_id() {
            continue;
        }
        if !matches!(
            tcx.def_kind(def_id),
            DefKind::Mod
                | DefKind::Struct
                | DefKind::Enum
                | DefKind::Union
                | DefKind::Trait
                | DefKind::TraitAlias
                | DefKind::TyAlias
                | DefKind::Fn
                | DefKind::Const { .. }
                | DefKind::Static { .. }
                | DefKind::Macro(_)
        ) {
            continue;
        }
        let Some(name) = tcx.opt_item_name(def_id) else {
            continue;
        };
        if RESERVED_PATH_ROOTS.contains(&name.as_str()) {
            offenders.push(tcx.def_path_str(def_id));
        }
    }
    offenders.sort();
    offenders
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opaque_trait_predicate_clauses_are_recognised() {
        for clause in [
            "T::clone.postcondition((self,), result)",
            "T::deref_mut.precondition((self,))",
            "T::deref_mut.postcondition((self,), result)",
            "  T::add_assign.postcondition((self, rhs), result) ",
        ] {
            assert!(is_opaque_trait_predicate_clause(clause), "{clause}");
        }
    }

    #[test]
    fn concrete_or_compound_clauses_are_not_opaque() {
        for clause in [
            "result == (self@ == rhs@)",
            "result == *self",
            "core::default::Default::default.postcondition((), result)",
            "T::clone.postcondition((self,), result) && result == *self",
            "T::clone.postcondition((self,), result) || true",
            "T::eq.postcondition((self, rhs), result == true)",
            "(*self).postcondition(arg, result)",
            "T::.postcondition((self,), result)",
            "T::clone.postcondition((self,), result)x",
        ] {
            assert!(!is_opaque_trait_predicate_clause(clause), "{clause}");
        }
    }

    fn spec(requires: &[&str], ensures: &[&str]) -> trust_wp_driver::StdSpec {
        trust_wp_driver::StdSpec {
            inv_requires: Vec::new(),
            capture_inv_requires: Vec::new(),
            requires: requires.iter().map(|c| c.to_string()).collect(),
            ensures: ensures.iter().map(|c| c.to_string()).collect(),
            param_names: None,
        }
    }

    #[test]
    fn restriction_drops_concrete_ensures_and_keeps_opaque_ones() {
        // The generic Clone contract: the implication would make any clone an
        // identity, so only the opaque predicate survives.
        let clone = spec(
            &[],
            &[
                "T::clone.postcondition((self,), result)",
                "T::clone.postcondition((self,), result) ==> result == *self",
            ],
        );
        let restricted = opaque_predicate_restriction(&clone).expect("opaque clause kept");
        assert_eq!(
            restricted.ensures,
            vec!["T::clone.postcondition((self,), result)".to_string()]
        );
        assert!(restricted.requires.is_empty());
    }

    #[test]
    fn restriction_refuses_concrete_requires_and_fully_concrete_specs() {
        assert!(opaque_predicate_restriction(&spec(&[], &[])).is_none());
        assert!(opaque_predicate_restriction(&spec(&[], &["result == (self@ == rhs@)"])).is_none());
        // A concrete requires cannot be dropped (that would check less).
        assert!(opaque_predicate_restriction(&spec(
            &["min@ <= max@"],
            &["T::clamp.postcondition((self, min, max), result)"],
        ))
        .is_none());
        let deref_mut = spec(
            &["T::deref_mut.precondition((self,))"],
            &["T::deref_mut.postcondition((self,), result)"],
        );
        let restricted = opaque_predicate_restriction(&deref_mut).expect("fully opaque");
        assert_eq!(restricted.requires.len(), 1);
        assert_eq!(restricted.ensures.len(), 1);
    }

    #[test]
    fn local_is_never_a_builtin_provider_whatever_its_crate_name() {
        for name in [
            "core",
            "alloc",
            "std",
            "trust_wp_std",
            "creusot_std",
            "user",
        ] {
            assert_eq!(classify_crate(true, name), ItemProvenance::Local);
            assert!(!classify_crate(true, name).is_builtin_provider());
        }
    }

    #[test]
    fn foreign_crates_classify_by_name() {
        assert_eq!(classify_crate(false, "core"), ItemProvenance::Std);
        assert_eq!(classify_crate(false, "alloc"), ItemProvenance::Std);
        assert_eq!(classify_crate(false, "std"), ItemProvenance::Std);
        for name in SPEC_LIBRARY_CRATES {
            assert_eq!(classify_crate(false, name), ItemProvenance::SpecLibrary);
        }
        assert_eq!(classify_crate(false, "serde"), ItemProvenance::OtherForeign);
        assert_eq!(
            classify_crate(false, "mycore"),
            ItemProvenance::OtherForeign
        );
        // Crate names are normalized with underscores; a hyphenated spelling
        // is not a spec library.
        assert_eq!(
            classify_crate(false, "trust-wp"),
            ItemProvenance::OtherForeign
        );
    }

    #[test]
    fn printed_root_skips_ufcs_and_reference_prefixes() {
        assert_eq!(printed_path_root("core::cmp::max"), "core");
        assert_eq!(printed_path_root("::core::cmp::max"), "core");
        assert_eq!(
            printed_path_root("<alloc::vec::Vec<T> as core::ops::Index>::index"),
            "alloc"
        );
        assert_eq!(printed_path_root("<&mut std::vec::Vec<T> as X>::f"), "std");
        assert_eq!(
            printed_path_root("core::option::Option::<T>::is_some"),
            "core"
        );
        assert_eq!(printed_path_root("mycore::cmp::max"), "mycore");
        assert_eq!(printed_path_root("u32::max"), "u32");
        assert!(path_has_reserved_root(
            "<core::option::Option as Clone>::clone"
        ));
        assert!(path_has_reserved_root("trust_wp_std::logic::Seq::len"));
        assert!(!path_has_reserved_root("corelib::cmp::max"));
        assert!(!path_has_reserved_root("my_std::mem::swap"));
    }

    #[test]
    fn lookup_scope_refuses_local_lookalikes() {
        // sp1/sp3/sp4: local items printing as std paths get nothing.
        for path in [
            "core::cmp::max",
            "alloc::vec::Vec::<T>::len",
            "core::option::Option::<T>::is_some",
            "std::mem::swap",
            "mycore::cmp::max",
        ] {
            assert_eq!(
                path_lookup_scope_for(ItemProvenance::Local, path),
                PathLookupScope::None
            );
        }
    }

    #[test]
    fn lookup_scope_for_library_and_foreign_items() {
        assert_eq!(
            path_lookup_scope_for(ItemProvenance::Std, "std::vec::Vec::<T>::len"),
            PathLookupScope::Full
        );
        assert_eq!(
            path_lookup_scope_for(ItemProvenance::SpecLibrary, "creusot_std::logic::Seq::len"),
            PathLookupScope::Full
        );
        assert_eq!(
            path_lookup_scope_for(ItemProvenance::OtherForeign, "serde::de::from_str"),
            PathLookupScope::ExternOnly
        );
        // A foreign crate reachable under a reserved name (e.g. `extern crate
        // foo as core;`) must not reach the std tables.
        assert_eq!(
            path_lookup_scope_for(ItemProvenance::OtherForeign, "core::cmp::max"),
            PathLookupScope::None
        );
    }
}
