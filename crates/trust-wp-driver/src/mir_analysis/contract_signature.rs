// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A contract's parameters as its signature types them, read one way for a
//! function's own lane and for every call of it.
//!
//! `formula::elaborate::state` reads each parameter's state from a
//! [`Signature`]; the lane that proves a clause and the call credited with it
//! must read it over the same one, so both build it here from the function's
//! `DefId`.

use std::{cell::RefCell, sync::Arc};

use rustc_hir::{def::DefKind, def_id::DefId, PatKind};
use rustc_middle::ty::{GenericArgKind, Mutability, RegionKind, Ty, TyCtxt, TyKind};
use trust_wp_core::{
    formula::elaborate::{ParamReference, Signature},
    logic::final_reads::FinalReaders,
};

use crate::mir_analysis::mut_borrow::{
    may_carry_borrow, type_analysis::type_contains_mut_ref_with_tcx,
};

thread_local! {
    /// The logic functions of the crate under verification that read a final
    /// value, to a fixed point over their bodies: every signature reads a
    /// call of one as a final read of its arguments (D-109).
    static FINAL_READERS: RefCell<Arc<FinalReaders>> = RefCell::new(Arc::default());
}

/// Install the crate's final readers ([`FINAL_READERS`]), once its logic
/// functions are read.
pub(crate) fn install_final_readers(readers: FinalReaders) {
    FINAL_READERS.with(|cell| *cell.borrow_mut() = Arc::new(readers));
}

/// Whether a parameter of type `ty` holds a `&mut` without being one
/// ([`ParamReference::HeldMutable`]): the state rule places no postcondition
/// read through that `&mut` (D-101). A pattern binding projected from such a
/// parameter is read by the same rule, so its `*`, `^` and `@` are refused
/// there as a tuple parameter's are (D-179), and so is any other
/// postcondition read of the `&mut` a plain parameter of such a type holds
/// (D-181).
pub(crate) fn is_held_mutable_parameter_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> bool {
    reference_of(tcx, typing_env, ty, false) == Some(ParamReference::HeldMutable)
}

/// What `ty` makes of `*`, `^` and `@` of a parameter of that type, when the
/// parameter is the function's own (`held` false) or a binding of a
/// destructuring parameter pattern (`held` true).
///
/// A `&mut` is held through a struct's fields as well as through generic
/// arguments (`t: (W, i32)` with `W { r: &mut i32 }` holds one): a `Value`
/// parameter's every read is placed at entry, so a held `&mut` this walk
/// missed would be read at entry on both sides of `old` (D-181).
fn reference_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    held: bool,
) -> Option<ParamReference> {
    let holds_mut_ref = crate::param_patterns::reaches_a_mutable_reference(tcx, typing_env, ty);
    match ty.kind() {
        TyKind::Ref(_, _, Mutability::Mut) if held => Some(ParamReference::HeldMutable),
        TyKind::Ref(_, _, Mutability::Mut) => Some(ParamReference::Mutable),
        _ if held && holds_mut_ref => Some(ParamReference::HeldMutable),
        TyKind::Ref(_, _, Mutability::Not) => Some(ParamReference::Shared),
        TyKind::Tuple(_) | TyKind::Array(..) | TyKind::Slice(_) if holds_mut_ref => {
            Some(ParamReference::HeldMutable)
        }
        TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Bool
        | TyKind::Char
        | TyKind::Tuple(_) => Some(ParamReference::Value),
        _ => None,
    }
}

/// The input types of `def_id`, by position: a closure's are its parameters
/// (its environment is not one), anything else's its signature's inputs.
/// Late-bound regions are liberated, so each is a `ReLateParam` a type can be
/// searched for.
pub(crate) fn input_types<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Vec<Ty<'tcx>>> {
    match tcx.def_kind(def_id) {
        DefKind::Closure => {
            let ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
            let TyKind::Closure(_, args) = ty.kind() else {
                return None;
            };
            let sig = tcx.liberate_late_bound_regions(def_id, args.as_closure().sig());
            match sig.inputs().first()?.kind() {
                TyKind::Tuple(params) => Some(params.iter().collect()),
                _ => None,
            }
        }
        DefKind::Fn | DefKind::AssocFn => {
            let sig = tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip();
            let sig = tcx.liberate_late_bound_regions(def_id, sig);
            Some(sig.inputs().to_vec())
        }
        _ => None,
    }
}

/// [`reference_of`] a parameter of `def_id` read by a clause of the std
/// model: a crate this one has no lane for writes `^self` of a `&Cell<T>`
/// (interior mutability) for the value the cell holds after the call, so a
/// shared reference to a referent that exposes interior mutability is one the
/// signature does not classify there. A local function's own lane refuses
/// that `^` of a shared reference, so each of its calls does too.
fn param_reference_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    ty: Ty<'tcx>,
) -> Option<ParamReference> {
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id);
    if let TyKind::Ref(_, referent, Mutability::Not) = ty.kind() {
        if !def_id.is_local() && !referent.is_freeze(tcx, typing_env) {
            return None;
        }
    }
    reference_of(tcx, typing_env, ty, false)
}

/// The signature of `def_id`'s contract over `param_names` (its parameters
/// by position, without a closure's environment), with each binding of a
/// destructuring parameter pattern the function's own HIR writes. A name past
/// the signature's inputs (a const generic argument a call appends), or of a
/// function whose inputs cannot be read, is recorded untyped.
pub(crate) fn contract_signature(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    param_names: &[String],
) -> Signature {
    let mut signature = Signature::new();
    signature.read_finals_through(FINAL_READERS.with(|cell| Arc::clone(&cell.borrow())));
    let (may_carry, writes_by_interior_mutability) = result_may_carry_a_borrow(tcx, def_id);
    signature.set_result_may_carry_a_borrow(may_carry);
    signature.set_result_writes_by_interior_mutability(writes_by_interior_mutability);
    let inputs = input_types(tcx, def_id).unwrap_or_default();
    let lent_into_a_parameter = params_lent_into_another_parameter(tcx, def_id);
    for (at, name) in param_names.iter().enumerate() {
        match inputs.get(at) {
            Some(ty) => {
                signature.insert(
                    name.clone(),
                    param_reference_of(tcx, def_id, *ty),
                    type_contains_mut_ref_with_tcx(tcx, *ty),
                );
                if over_interior_mutable_memory(tcx, def_id, *ty) {
                    signature.over_interior_mutable_memory(name.clone());
                }
            }
            None => signature.insert_untyped(name.clone()),
        }
        if lent_into_a_parameter.contains(&at) {
            signature.lend_into_a_parameter(name.clone());
        }
    }
    if let Some(local) = def_id.as_local() {
        if let Some(body_id) = tcx.hir_node_by_def_id(local).body_id() {
            let typeck = tcx.typeck(local);
            for param in tcx.hir_body(body_id).params {
                if matches!(param.pat.kind, PatKind::Binding(_, _, _, None)) {
                    continue;
                }
                let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id);
                param.pat.each_binding(|_, hir_id, _, ident| {
                    let name = ident.as_str().to_string();
                    if !signature.has(&name) {
                        signature.insert(
                            name,
                            reference_of(tcx, typing_env, typeck.node_type(hir_id), true),
                            false,
                        );
                    }
                });
            }
        }
    }
    signature
}

/// Whether `ty` is, or holds, a `&mut` whose referent holds memory a shared
/// reference writes (`&mut Cell<i32>`, `&mut S` with `S { c: &Cell<i32> }`,
/// `&mut Option<&Cell<i32>>`; `extract::ty_exposes_interior_mutability`).
/// Whoever holds such a shared reference writes the referent by a route no
/// prophecy records, so the value the parameter is left with is no fact of
/// the function (D-108).
fn over_interior_mutable_memory<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, ty: Ty<'tcx>) -> bool {
    if !type_contains_mut_ref_with_tcx(tcx, ty) {
        return false;
    }
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id);
    // A projection the signature names (`<() as Tr<'a>>::Slot`) is read as
    // its normalized type; one that does not normalize is read as may-be.
    let erased = tcx.erase_and_anonymize_regions(ty);
    let ty = tcx
        .try_normalize_erasing_regions(
            typing_env,
            rustc_middle::ty::set_aliases_to_non_rigid(tcx, erased),
        )
        .unwrap_or(erased);
    crate::mir_analysis::extract::ty_exposes_interior_mutability(tcx, typing_env, ty)
}

/// Whether the return type of `def_id` could carry the borrow of a `&mut`
/// parameter: the predicate the function's own lane frees a lent
/// parameter's final value by (`mut_borrow::may_carry_borrow`, which counts
/// a reference, a raw pointer, a type whose fields reach one and any type it
/// cannot see into), read here from the signature, so the function's lane
/// and every call of it refuse the same pre-Creusot reads of a lent final
/// value (`formula::elaborate::place_parameter_reads`). An output that cannot
/// be read may carry anything.
///
/// The second answer is whether that borrow may be written through by
/// interior mutability reachable from the output
/// (`extract::ty_exposes_interior_mutability`: `&Cell<T>`, `&Box<Cell<T>>`):
/// a write no prophecy of the result records, so the final value of a `&mut`
/// parameter is not the function's to state in either dialect.
fn result_may_carry_a_borrow(tcx: TyCtxt<'_>, def_id: DefId) -> (bool, bool) {
    let sig = match tcx.def_kind(def_id) {
        DefKind::Closure => {
            let ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
            match ty.kind() {
                TyKind::Closure(_, args) => Some(args.as_closure().sig()),
                _ => None,
            }
        }
        DefKind::Fn | DefKind::AssocFn => {
            Some(tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip())
        }
        _ => None,
    };
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id);
    sig.map_or((true, true), |sig| {
        let output = tcx.instantiate_bound_regions_with_erased(sig).output();
        output_may_carry_a_borrow(tcx, typing_env, output)
    })
}

/// [`result_may_carry_a_borrow`] of a returned type `output`, read in
/// `typing_env`.
fn output_may_carry_a_borrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    output: Ty<'tcx>,
) -> (bool, bool) {
    let may_carry = may_carry_borrow(tcx, typing_env, output, 0);
    let interior = may_carry
        && crate::mir_analysis::extract::ty_exposes_interior_mutability(
            tcx,
            typing_env,
            tcx.erase_and_anonymize_regions(output),
        );
    (may_carry, interior)
}

/// A call whose callee's clauses are read: the body that makes it and its
/// callee operand.
#[derive(Clone, Copy)]
pub(crate) struct CallSite<'a, 'tcx> {
    pub(crate) body: &'a rustc_middle::mir::Body<'tcx>,
    pub(crate) func: &'a rustc_middle::mir::Operand<'tcx>,
}

/// The type a call of the foreign `def_id` at `site` returns, and the
/// caller's typing environment it is read in: the callee's signature
/// instantiated with the call's generic arguments and normalized there.
/// `Iterator::next` declares `Option<<Self as Iterator>::Item>`, a projection
/// the declared signature cannot see into, so it may carry anything; called
/// on a `Range<isize>` it returns `Option<isize>`, which carries nothing.
///
/// Read only where no lane of this crate reads the callee: a foreign item,
/// and a call that resolution pins to one foreign item. A local callee, a
/// call that may run a local body (a local impl of a foreign trait, a
/// receiver still generic, a shim that calls a local closure), a callee
/// reached other than by its `FnDef` operand, or an output that does not
/// normalize is `None`, and the declared signature is read: there the
/// function's own lane reads its clauses over that signature, and the call
/// must refuse whatever the lane refuses.
fn foreign_output_at_the_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    site: CallSite<'_, 'tcx>,
) -> Option<(rustc_middle::ty::TypingEnv<'tcx>, Ty<'tcx>)> {
    use rustc_middle::ty::{Instance, InstanceKind, TypeVisitableExt, TypingEnv};
    if def_id.is_local() {
        return None;
    }
    let rustc_middle::mir::Operand::Constant(constant) = site.func else {
        return None;
    };
    let TyKind::FnDef(callee, args) = constant.const_.ty().kind() else {
        return None;
    };
    // A FnDef binds its late-bound lifetimes; unbound, any of them escapes,
    // and the check below refuses the site.
    let args = args.skip_binder();
    if *callee != def_id || args.has_escaping_bound_vars() {
        return None;
    }
    let typing_env = TypingEnv::post_analysis(tcx, site.body.source.def_id());
    // Resolution and normalization may reach trait selection on shapes the
    // verifier never otherwise asks about; a panic there is a callee read by
    // its declared signature, not a crash.
    let output = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let args = tcx
            .try_normalize_erasing_regions(
                typing_env,
                rustc_middle::ty::set_aliases_to_non_rigid(tcx, args),
            )
            .ok()?;
        let instance = Instance::try_resolve(tcx, typing_env, def_id, args)
            .ok()
            .flatten()?;
        let InstanceKind::Item(item) = instance.def else {
            return None;
        };
        if item.is_local() {
            return None;
        }
        let sig = tcx.fn_sig(def_id).instantiate(tcx, args).skip_norm_wip();
        let output = tcx.instantiate_bound_regions_with_erased(sig).output();
        tcx.try_normalize_erasing_regions(
            typing_env,
            rustc_middle::ty::set_aliases_to_non_rigid(tcx, output),
        )
        .ok()
    }))
    .ok()
    .flatten()?;
    Some((typing_env, output))
}

/// The positions of the `&mut` parameters of `def_id` whose borrow may be
/// stored where another parameter's holder reads it after the call
/// (`stash<'a>(p: &'a mut i32, slot: &mut Option<&'a mut i32>)`), decided
/// from the signature as borrowck decides it, so the function's lane and
/// every call of it read the same clauses (D-107).
///
/// A borrow `&'r mut T` (or one derived from it) can be stored only in a
/// slot whose region `'r` outlives ([`outlived_by`]; the relation holds
/// what the inputs, the output and an enclosing impl header imply, as
/// borrowck assumes them well-formed), or as a raw pointer (a safe cast) in
/// a raw-pointer slot; a slot counts when it is memory another parameter's
/// holder writes. A type parameter there may hold it when a bound can name
/// `'r`, i.e. `'r` is not late-bound; a projection may also hold it when it
/// names a region `'r` outlives (it is its normalized type); a `'static`
/// borrow may also be stored in a global. A closure's captures are searched
/// as another parameter is, each one memory its holder writes: the closure
/// keeps what it captures by value from one call to the next. A signature
/// whose inputs cannot be read has no `&mut` parameter to lend: every name
/// of it is recorded untyped, and every reading that depends on it is
/// refused.
pub(crate) fn params_lent_into_another_parameter(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> std::collections::HashSet<usize> {
    let Some(inputs) = input_types(tcx, def_id) else {
        return std::collections::HashSet::new();
    };
    let captures = closure_capture_types(tcx, def_id);
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id);
    let outlives = Outlives::of(
        tcx,
        def_id,
        inputs
            .iter()
            .chain(&captures)
            .copied()
            .chain(wf_types_beyond_inputs(tcx, def_id)),
    );
    let mut lent = std::collections::HashSet::new();
    for (at, ty) in inputs.iter().enumerate() {
        let TyKind::Ref(region, _, Mutability::Mut) = ty.kind() else {
            continue;
        };
        let slots = Slots {
            receives: outlives.outlived_by(*region),
            type_params: !matches!(region.kind(), RegionKind::ReLateParam(_)),
        };
        let may_lend = matches!(region.kind(), RegionKind::ReStatic)
            || inputs.iter().enumerate().any(|(other, input)| {
                other != at && absorbs(tcx, typing_env, *input, false, &slots, 0)
            })
            || captures
                .iter()
                .any(|capture| absorbs(tcx, typing_env, *capture, true, &slots, 0));
        if may_lend {
            lent.insert(at);
        }
    }
    lent
}

/// The types beyond the inputs whose well-formedness the body may assume, as
/// borrowck assumes it: the output (`-> Option<&'b &'a ()>` implies `'a:
/// 'b`), the header of an enclosing impl (`impl<'a, 'b> P<'a, 'b>` implies
/// what `P` requires of its regions), and, for a closure, the signature of
/// every function it is nested in. Each lets the body store a borrow where
/// the inputs alone relate no regions (D-108).
fn wf_types_beyond_inputs<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<Ty<'tcx>> {
    let mut types = Vec::new();
    let mut item = Some(def_id);
    while let Some(did) = item {
        match tcx.def_kind(did) {
            DefKind::Closure => {
                let ty = tcx.type_of(did).instantiate_identity().skip_norm_wip();
                if let TyKind::Closure(_, args) = ty.kind() {
                    let sig = tcx.liberate_late_bound_regions(did, args.as_closure().sig());
                    types.extend(sig.inputs_and_output.iter());
                }
            }
            DefKind::Fn | DefKind::AssocFn => {
                let sig = tcx.fn_sig(did).instantiate_identity().skip_norm_wip();
                types.extend(
                    tcx.liberate_late_bound_regions(did, sig)
                        .inputs_and_output
                        .iter(),
                );
            }
            DefKind::Impl { of_trait } => {
                types.push(tcx.type_of(did).instantiate_identity().skip_norm_wip());
                if of_trait {
                    types.extend(tcx.impl_trait_ref(did).skip_binder().args.types());
                }
            }
            _ => {}
        }
        // A closure assumes what its enclosing function does, and an
        // associated function what its impl's header does; a nested item
        // has generics of its own.
        item = matches!(tcx.def_kind(did), DefKind::Closure | DefKind::AssocFn)
            .then(|| tcx.opt_parent(did))
            .flatten();
    }
    types
}

/// The outlives relation a signature gives its regions: each region
/// outlives itself; a region under a reference outlives the reference's
/// region (the implied bound of `&'x T`); the explicit bounds of the item and
/// its parents; and, read loosely, every region of an ADT, trait object or
/// other type whose own bounds it does not read outlives every other region
/// of it.
struct Outlives<'tcx> {
    edges: std::collections::HashMap<
        rustc_middle::ty::Region<'tcx>,
        Vec<rustc_middle::ty::Region<'tcx>>,
    >,
}

impl<'tcx> Outlives<'tcx> {
    fn of(tcx: TyCtxt<'tcx>, def_id: DefId, types: impl Iterator<Item = Ty<'tcx>>) -> Self {
        let mut outlives = Self {
            edges: std::collections::HashMap::new(),
        };
        for ty in types {
            outlives.implied_by(ty);
        }
        let mut item = Some(def_id);
        while let Some(did) = item {
            let predicates = tcx.clauses_of(did);
            for (clause, _) in predicates.clauses {
                match clause.kind().skip_binder() {
                    rustc_middle::ty::ClauseKind::RegionOutlives(
                        rustc_middle::ty::OutlivesClause(long, short),
                    ) => outlives.add(long, short),
                    rustc_middle::ty::ClauseKind::TypeOutlives(
                        rustc_middle::ty::OutlivesClause(ty, short),
                    ) => {
                        for arg in ty.walk() {
                            if let GenericArgKind::Lifetime(long) = arg.kind() {
                                outlives.add(long, short);
                            }
                        }
                    }
                    _ => {}
                }
            }
            item = predicates.parent;
        }
        outlives
    }

    fn add(&mut self, long: rustc_middle::ty::Region<'tcx>, short: rustc_middle::ty::Region<'tcx>) {
        self.edges.entry(long).or_default().push(short);
    }

    fn implied_by(&mut self, ty: Ty<'tcx>) {
        for arg in ty.walk() {
            let GenericArgKind::Type(ty) = arg.kind() else {
                continue;
            };
            let regions = |ty: Ty<'tcx>| -> Vec<rustc_middle::ty::Region<'tcx>> {
                ty.walk()
                    .filter_map(|arg| match arg.kind() {
                        GenericArgKind::Lifetime(region) => Some(region),
                        _ => None,
                    })
                    .collect()
            };
            match ty.kind() {
                TyKind::Ref(short, inner, _) => {
                    for long in regions(*inner) {
                        self.add(long, *short);
                    }
                }
                TyKind::Adt(..)
                | TyKind::Dynamic(..)
                | TyKind::Closure(..)
                | TyKind::Coroutine(..)
                | TyKind::CoroutineClosure(..)
                | TyKind::Alias(..)
                | TyKind::FnPtr(..) => {
                    let all = regions(ty);
                    for long in &all {
                        for short in &all {
                            self.add(*long, *short);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// The regions `region` outlives, or `None` when that is every region:
    /// `'static`, or a region that is no parameter of the signature (a
    /// closure's inferred one), or one some such region is reached from.
    fn outlived_by(
        &self,
        region: rustc_middle::ty::Region<'tcx>,
    ) -> Option<std::collections::HashSet<rustc_middle::ty::Region<'tcx>>> {
        let named = |region: rustc_middle::ty::Region<'tcx>| {
            matches!(
                region.kind(),
                RegionKind::ReLateParam(_) | RegionKind::ReEarlyParam(_)
            )
        };
        let mut seen = std::collections::HashSet::from([region]);
        let mut stack = vec![region];
        while let Some(long) = stack.pop() {
            if !named(long) {
                return None;
            }
            for short in self.edges.get(&long).into_iter().flatten() {
                if seen.insert(*short) {
                    stack.push(*short);
                }
            }
        }
        Some(seen)
    }
}

/// The types a closure captures (by reference or by value), or none for any
/// other item.
fn closure_capture_types<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<Ty<'tcx>> {
    if !matches!(tcx.def_kind(def_id), DefKind::Closure) {
        return Vec::new();
    }
    let ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
    match ty.kind() {
        TyKind::Closure(_, args) => args.as_closure().upvar_tys().iter().collect(),
        // A closure whose captures cannot be read may hold anything: a raw
        // pointer in memory its holder writes receives any borrow.
        _ => vec![Ty::new_mut_ptr(tcx, tcx.types.unit)],
    }
}

/// Which slots of memory another parameter's holder writes may receive the
/// borrow: a slot naming a region the borrow's region outlives (`receives`;
/// `None` is every region), and a type parameter or projection, whose bounds
/// may name the borrow's region (`type_params`). A projection naming a
/// region the borrow's region outlives is a slot either way.
struct Slots<'tcx> {
    receives: Option<std::collections::HashSet<rustc_middle::ty::Region<'tcx>>>,
    type_params: bool,
}

impl<'tcx> Slots<'tcx> {
    /// A region bound inside the slot's own type (`dyn for<'x> FnMut(&'x mut
    /// T)`) is no one region a borrow could be stored at; a region that is no
    /// parameter of the signature (a closure's inferred one) may be any.
    fn receives(&self, region: rustc_middle::ty::Region<'tcx>) -> bool {
        match region.kind() {
            RegionKind::ReBound(..) => false,
            RegionKind::ReLateParam(_) | RegionKind::ReEarlyParam(_) | RegionKind::ReStatic => self
                .receives
                .as_ref()
                .is_none_or(|regions| regions.contains(&region)),
            _ => true,
        }
    }

    fn receives_any_of(&self, ty: Ty<'tcx>) -> bool {
        ty.walk().any(
            |arg| matches!(arg.kind(), GenericArgKind::Lifetime(region) if self.receives(region)),
        )
    }
}

/// Whether a value of `ty` gives its holder memory, readable after the call,
/// that a borrow may be stored in: `writable` when the value itself sits in
/// such memory (behind a `&mut`, a raw pointer, or a shared reference to
/// interior-mutable memory). A slot there naming a region the borrow may
/// fill ([`Slots::receives`]: a reference, an ADT's region argument, a trait
/// object's) receives it; a raw-pointer slot always does; a type parameter
/// does when `slots.type_params`, and a projection then or when it names a
/// region the borrow may fill. The contents of an owned value
/// are walked for such memory: std types by their type arguments (shared,
/// like `Rc`'s, when they are interior-mutable), other ADTs by their fields.
fn absorbs<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    writable: bool,
    slots: &Slots<'tcx>,
    depth: usize,
) -> bool {
    if depth > 16 {
        return true;
    }
    let interior = |ty: Ty<'tcx>| {
        crate::mir_analysis::extract::ty_exposes_interior_mutability(
            tcx,
            typing_env,
            tcx.erase_and_anonymize_regions(ty),
        )
    };
    let recurse = |ty, writable| absorbs(tcx, typing_env, ty, writable, slots, depth + 1);
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never
        | TyKind::FnDef(..)
        | TyKind::FnPtr(..) => false,
        TyKind::Ref(region, inner, mutability) => {
            (writable && slots.receives(*region))
                || recurse(*inner, *mutability == Mutability::Mut || interior(ty))
        }
        TyKind::RawPtr(inner, _) => writable || recurse(*inner, true),
        TyKind::Tuple(fields) => fields.iter().any(|field| recurse(field, writable)),
        TyKind::Array(inner, _) | TyKind::Slice(inner) => recurse(*inner, writable),
        TyKind::Adt(adt_def, args) => {
            if writable && args.regions().any(|region| slots.receives(region)) {
                return true;
            }
            if matches!(
                tcx.crate_name(adt_def.did().krate).as_str(),
                "core" | "alloc" | "std"
            ) {
                args.types()
                    .any(|arg| recurse(arg, writable || interior(arg)))
            } else {
                adt_def
                    .all_fields()
                    .any(|field| recurse(field.ty(tcx, *args).skip_norm_wip(), writable))
            }
        }
        TyKind::Param(_) => slots.type_params,
        // A projection is its normalized type, which the signature does not
        // show: `<() as Tr<'a>>::Slot` may be `Option<&'a mut i32>` for a
        // late-bound `'a`. It may hold the borrow wherever a region it names
        // may (D-108).
        TyKind::Alias(..) => slots.type_params || slots.receives_any_of(ty),
        _ => slots.receives_any_of(ty),
    }
}

/// The signature a call reads `def_id`'s clauses over: its parameters by
/// `param_names` (the names its clauses are substituted by, spec names
/// included), each binding of a destructuring parameter its own lane reads,
/// and every positional alias a std spec may spell a parameter by (`argN`,
/// `self` for the first, `value`/`default`/`arg`/`rhs` for the first that is
/// not `self`) at that parameter's type. With no names, every alias is read
/// at its position's type.
///
/// At a `site` that calls a foreign item, what the returned value may carry
/// is read from the type the call returns ([`foreign_output_at_the_call`]):
/// no lane of this crate reads that callee's clauses, so the call's own types
/// decide it, not the projections that hide them in the declared signature.
/// The parameters are read over the declared signature at every call.
pub(crate) fn call_signature<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    param_names: Option<&[String]>,
    site: Option<CallSite<'_, 'tcx>>,
) -> Signature {
    let inputs = input_types(tcx, def_id);
    let names: Vec<String> = match param_names {
        Some(names) => names.to_vec(),
        None => inputs.as_ref().map_or_else(Vec::new, |inputs| {
            (0..inputs.len()).map(|at| format!("arg{at}")).collect()
        }),
    };
    let mut signature = contract_signature(tcx, def_id, &names);
    let arity = inputs.as_ref().map_or(names.len(), Vec::len);
    let value_at = if arity > 1 { 1 } else { 0 };
    let mut aliases: Vec<(String, usize)> = (0..arity).map(|at| (format!("arg{at}"), at)).collect();
    if arity > 0 {
        aliases.push(("self".to_string(), 0));
        for alias in ["value", "default", "arg", "rhs"] {
            aliases.push((alias.to_string(), value_at));
        }
    }
    let lent_into_a_parameter = params_lent_into_another_parameter(tcx, def_id);
    for (alias, at) in aliases {
        if signature.has(&alias) || names.iter().any(|name| *name == alias) {
            continue;
        }
        if lent_into_a_parameter.contains(&at) {
            signature.lend_into_a_parameter(alias.clone());
        }
        match inputs.as_ref().and_then(|inputs| inputs.get(at)) {
            Some(ty) => {
                if over_interior_mutable_memory(tcx, def_id, *ty) {
                    signature.over_interior_mutable_memory(alias.clone());
                }
                signature.insert(
                    alias,
                    param_reference_of(tcx, def_id, *ty),
                    type_contains_mut_ref_with_tcx(tcx, *ty),
                );
            }
            None => signature.insert_untyped(alias),
        }
    }
    if let Some((typing_env, output)) =
        site.and_then(|site| foreign_output_at_the_call(tcx, def_id, site))
    {
        let (may_carry, writes_by_interior_mutability) =
            output_may_carry_a_borrow(tcx, typing_env, output);
        signature.set_result_may_carry_a_borrow(may_carry);
        signature.set_result_writes_by_interior_mutability(writes_by_interior_mutability);
    }
    signature
}
