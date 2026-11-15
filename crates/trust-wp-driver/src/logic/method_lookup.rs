// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Whether Rust's method lookup of `recv.m(..)` can select nothing but the
//! one LOGIC definition the typed resolution picked.
//!
//! The typed resolution (`identity_typed::resolve_family_on_type`) and the
//! encoder's receiver dispatch know only the crate's logic definitions. Rust's
//! lookup (rustc's method probe) sees every method: it walks the receiver's
//! autoderef steps, at each step prefers an inherent method to a trait method,
//! and takes a trait method only from a trait in scope, whether it is a
//! program method, a trait's default body or an impl. So the logic pick is
//! the callee Rust names only when nothing else called `m` can apply to any
//! step of the receiver (method_call_*_granted.rs). This answers that
//! question over-approximately: a candidate it cannot rule out refuses the
//! pick, and a refused pick leaves the call to be refused, never guessed.

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    fast_reject::{simplify_type, TreatParams},
    Instance, Ty, TyCtxt, TyKind, TypeVisitableExt, TypingEnv,
};
use rustc_span::Symbol;

thread_local! {
    /// Method name -> every trait in the crate graph that declares a method
    /// (an associated fn with a `self` parameter) of that name.
    static TRAITS_WITH_METHOD: RefCell<HashMap<Symbol, Rc<Vec<DefId>>>> =
        RefCell::new(HashMap::new());
}

/// Forget the per-crate cache (a new crate is being verified).
pub(crate) fn reset() {
    TRAITS_WITH_METHOD.with(|cell| cell.borrow_mut().clear());
}

/// Whether a method call `.name(..)` on a receiver of Rust type `receiver`
/// can resolve to nothing but `pick`, a method (an inherent method, a trait
/// impl's method, or a trait's declaration standing for its default body at
/// the receiver's type).
///
/// `receiver_by_value` says the receiver's type is exactly `receiver` (not a
/// type the caller could only bound from below): then an inherent `pick`
/// taking `self` by value at that very type is selected before every trait
/// method, as Rust's lookup tries inherent candidates first at each step.
pub(crate) fn selects_only<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
    receiver: Ty<'tcx>,
    pick: DefId,
    receiver_by_value: bool,
) -> bool {
    let symbol = Symbol::intern(name);
    let mut chain = autoderef_chain(tcx, receiver);
    let pick_parent = tcx.parent(pick);
    // Lookup stops at the first step where a method applies, so no step past
    // the pick's own self type can compete (`Box<W>`'s method against `W`'s).
    if matches!(
        tcx.def_kind(pick_parent),
        rustc_hir::def::DefKind::Impl { .. }
    ) {
        let impl_self = tcx.erase_and_anonymize_regions(
            tcx.type_of(pick_parent)
                .instantiate_identity()
                .skip_norm_wip(),
        );
        if let Some(step) = chain.iter().position(|ty| same_type_head(*ty, impl_self)) {
            chain.truncate(step + 1);
        }
    }
    if chain.is_empty() {
        return false;
    }
    let pick_trait = match tcx.def_kind(pick_parent) {
        rustc_hir::def::DefKind::Trait => Some(pick_parent),
        rustc_hir::def::DefKind::Impl { of_trait: true } => tcx.impl_opt_trait_id(pick_parent),
        _ => None,
    };

    for ty in &chain {
        for impl_id in inherent_impls_of(tcx, *ty) {
            let competing = tcx
                .associated_items(impl_id)
                .filter_by_name_unhygienic(symbol)
                .any(|item| item.is_method() && item.def_id != pick);
            if competing {
                return false;
            }
        }
    }

    // An inherent method taking `self` at the receiver's own type is found by
    // value at the first step, before any trait candidate of any step.
    let inherent_first = pick_trait.is_none()
        && receiver_by_value
        && chain.len() == 1
        && takes_self_by_value(tcx, pick);
    if inherent_first {
        return true;
    }

    for &trait_id in traits_with_method(tcx, symbol).iter() {
        if is_vehicle_only(tcx, trait_id) {
            continue;
        }
        for (step, ty) in chain.iter().enumerate() {
            let at_target = step + 1 == chain.len();
            if Some(trait_id) == pick_trait {
                // The pick is this trait's method at the target type. At an
                // earlier step (a reference or box around the target) an impl
                // of the same trait for that wrapper is selected first; the
                // standard library's and the model crates' impls there forward
                // to the target's, a local one is its own definition.
                if at_target {
                    continue;
                }
                if relevant_impls(tcx, trait_id, *ty)
                    .iter()
                    .any(|impl_id| impl_id.is_local())
                {
                    return false;
                }
                continue;
            }
            if trait_may_apply(tcx, trait_id, symbol, *ty) {
                return false;
            }
        }
    }
    true
}

/// The receiver's autoderef steps as trust-wp's typed resolution peels them:
/// references and boxes, outermost first, ending at the type the pick was
/// selected on.
fn autoderef_chain<'tcx>(tcx: TyCtxt<'tcx>, receiver: Ty<'tcx>) -> Vec<Ty<'tcx>> {
    let mut chain = Vec::new();
    let mut current = tcx.erase_and_anonymize_regions(receiver);
    // Bounded: a type nests finitely, the cap only guards a pathological one.
    for _ in 0..16 {
        chain.push(current);
        current = match current.kind() {
            TyKind::Ref(_, inner, _) => *inner,
            TyKind::Adt(adt, args) if adt.is_box() => match args.types().next() {
                Some(inner) => inner,
                None => break,
            },
            _ => break,
        };
    }
    chain
}

/// Whether the step type `step` is the impl self type `impl_self`: equal, or
/// the same ADT when the impl is generic over its arguments.
fn same_type_head<'tcx>(step: Ty<'tcx>, impl_self: Ty<'tcx>) -> bool {
    step == impl_self
        || matches!(
            (step.kind(), impl_self.kind()),
            (TyKind::Adt(a, _), TyKind::Adt(b, _)) if a.did() == b.did() && impl_self.has_non_region_param()
        )
}

/// Every inherent impl whose methods a receiver of type `ty` can call at
/// that step: the ADT's own, and any the standard library keeps for a
/// primitive or foreign type (`incoherent_impls`).
fn inherent_impls_of<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Vec<DefId> {
    let mut impls = Vec::new();
    if let TyKind::Adt(adt, _) = ty.kind() {
        impls.extend(tcx.inherent_impls(adt.did()).iter().copied());
    }
    if let Some(simplified) = simplify_type(tcx, ty, TreatParams::AsRigid) {
        impls.extend(tcx.incoherent_impls(simplified).iter().copied());
    }
    impls
}

/// Whether an inherent method's receiver is `self` by value: its first input
/// is its impl's self type itself.
fn takes_self_by_value(tcx: TyCtxt<'_>, method: DefId) -> bool {
    let impl_self = tcx
        .type_of(tcx.parent(method))
        .instantiate_identity()
        .skip_norm_wip();
    let sig = tcx.fn_sig(method).instantiate_identity().skip_binder();
    sig.inputs().first().is_some_and(|first| {
        tcx.erase_and_anonymize_regions(*first) == tcx.erase_and_anonymize_regions(impl_self)
    })
}

/// Every trait that declares a method named `symbol` and that code in this
/// crate could have in scope: every local trait, and every public trait of a
/// dependency (a crate-private trait of a dependency cannot be imported).
fn traits_with_method(tcx: TyCtxt<'_>, symbol: Symbol) -> Rc<Vec<DefId>> {
    if let Some(cached) = TRAITS_WITH_METHOD.with(|cell| cell.borrow().get(&symbol).cloned()) {
        return cached;
    }
    let traits: Vec<DefId> = tcx
        .all_traits_including_private()
        .filter(|trait_id| trait_id.is_local() || tcx.visibility(*trait_id).is_public())
        .filter(|trait_id| {
            tcx.associated_items(*trait_id)
                .filter_by_name_unhygienic(symbol)
                .any(|item| item.is_method())
        })
        .collect();
    let traits = Rc::new(traits);
    TRAITS_WITH_METHOD.with(|cell| cell.borrow_mut().insert(symbol, Rc::clone(&traits)));
    traits
}

/// The type-check vehicle's helper traits (`trust_wp_std::__spec_tc`): they
/// are imported only inside the vehicle closures the driver erases, never in
/// the scope a clause is read in.
fn is_vehicle_only(tcx: TyCtxt<'_>, trait_id: DefId) -> bool {
    !trait_id.is_local()
        && tcx.def_path(trait_id).data.iter().any(|component| {
            component
                .data
                .get_opt_name()
                .is_some_and(|n| n.as_str() == "__spec_tc")
        })
}

fn relevant_impls<'tcx>(tcx: TyCtxt<'tcx>, trait_id: DefId, ty: Ty<'tcx>) -> Vec<DefId> {
    let mut impls = Vec::new();
    tcx.for_each_relevant_impl(trait_id, ty, |impl_id| impls.push(impl_id));
    impls
}

/// Whether `trait_id`'s method `symbol` may be callable on a receiver of
/// type `ty`: some impl may apply (blanket impls included), confirmed by
/// instance resolution where the trait and the type are closed enough to ask.
fn trait_may_apply<'tcx>(tcx: TyCtxt<'tcx>, trait_id: DefId, symbol: Symbol, ty: Ty<'tcx>) -> bool {
    if relevant_impls(tcx, trait_id, ty).is_empty() {
        return false;
    }
    let Some(method) = tcx
        .associated_items(trait_id)
        .filter_by_name_unhygienic(symbol)
        .find(|item| item.is_method())
    else {
        return false;
    };
    let closed = tcx.generics_of(trait_id).count() == 1
        && tcx.generics_of(method.def_id).own_params.is_empty()
        && !ty.has_non_region_param()
        && !ty.has_escaping_bound_vars();
    if !closed {
        return true;
    }
    !matches!(
        Instance::try_resolve(
            tcx,
            TypingEnv::fully_monomorphized(),
            method.def_id,
            tcx.mk_args(&[ty.into()]),
        ),
        Ok(None)
    )
}

#[cfg(test)]
#[path = "method_lookup_tests.rs"]
mod tests;
