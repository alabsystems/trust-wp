// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Callables handed to a callee whose body trust-wp does not verify (D-118).
//!
//! A closure, fn item or `F: Fn` value passed to `Option::map`,
//! `Iterator::for_each`, `bool::then`, ... is invoked by library code no lane
//! walks. Creusot charges the callable's precondition through the combinator's
//! own spec (`f.precondition((t,))`); trust-wp's builtin specs state only the
//! result, so every obligation inside such a closure — a bounds check, an
//! `assert!`, a callee `#[requires]` — was charged to nobody, and the host
//! that handed it over was credited.
//!
//! The rule: every hand-off is recorded here, by ONE scan that both the
//! target discovery and the end-of-run credit join read. A requires-free local
//! closure that owes anything is verified as a target under `requires true` —
//! every argument the library can pass, every capture value its type allows —
//! and the host's credit rests on that verdict. Anything whose precondition
//! cannot be stated for every argument (a closure or fn item WITH a
//! `#[requires]`, a fn item whose body holds a parameter invariant premise, a
//! type parameter, `dyn Fn`, a fn pointer, an unspecified foreign fn item)
//! refuses the host.
//!
//! A hand-off also carries the callable's WRITES. A closure that captured a
//! `&mut`, or a callable run beside a `&mut` nested in another by-value
//! argument, writes host memory inside the library; no call lane gives that
//! memory a post-call value (only a top-level `&mut` argument gets one), so
//! the host's proof would read it at its pre-call value. Such a hand-off
//! refuses the host too. A closure's capture write is unseen wherever the
//! closure goes except a direct call: a VERIFIED callee owes the closure's
//! precondition but its contract cannot name the host local the closure
//! borrows, and a coercion to a trait object hides the capture from every
//! later walk.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::{Body, Operand, TerminatorKind, START_BLOCK},
    ty::{self, Ty, TyCtxt, TyKind},
};
use trust_wp_core::logic::TypeInvariantDef;
use trust_wp_driver::StdSpec;

/// What a host handed to a callee it does not verify.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::callbacks) enum EscapedCallable {
    /// A requires-free local closure. Its obligations are owed by its own
    /// verification under `requires true` (it is a target through
    /// `fn_owes_abort_or_callee_precondition`), and the host rests on it.
    Closure(LocalDefId),
    /// A callable whose precondition nothing in this run states for every
    /// argument the callee may pass. The host cannot be credited.
    Unresolved(String),
    /// A callable that writes host memory through a `&mut` no call lane
    /// advances, run where no lane sees the write. The host's proof reads the
    /// memory at its pre-call value, so the host cannot be credited.
    UnseenWrite(String),
}

/// One hand-off of a callable to a callee trust-wp does not verify.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::callbacks) struct CallableEscape {
    /// The callee's printed path, for the report.
    pub(in crate::callbacks) callee: String,
    pub(in crate::callbacks) callable: EscapedCallable,
}

/// Every hand-off in the crate, keyed by the body that makes it.
pub(in crate::callbacks) type CallableEscapes = HashMap<LocalDefId, Vec<CallableEscape>>;

/// The crate's own `extern_spec!` requires by normalized target path, with the
/// parameter names each declaration spells.
type ExternRequires = HashMap<String, (Vec<String>, Option<Vec<String>>)>;

/// What the scan reads to decide whether a callable's precondition is stated.
struct ScanSpecs<'a> {
    extern_requires: ExternRequires,
    /// The session's invariant definitions: the set the spec tables grant a
    /// local fn item's parameter premises from.
    type_invariant_defs: &'a [TypeInvariantDef],
}

thread_local! {
    // Session-scoped (cleared by `thread_locals::clear_caches`): discovery, the
    // extraction gate and the credit join must read ONE scan, never three.
    static CRATE_ESCAPES: RefCell<Option<Rc<CallableEscapes>>> = const { RefCell::new(None) };
}

pub(crate) fn clear_callable_escape_cache() {
    CRATE_ESCAPES.with(|cell| cell.borrow_mut().take());
}

/// The crate's hand-offs, computed once per session.
///
/// `type_invariant_defs` is the session's final definition set; every reader
/// passes that one set, so the scan the first reader computes is the scan
/// each later reader would have.
pub(in crate::callbacks) fn crate_callable_escapes(
    tcx: TyCtxt<'_>,
    type_invariant_defs: &[TypeInvariantDef],
) -> Rc<CallableEscapes> {
    if let Some(cached) = CRATE_ESCAPES.with(|cell| cell.borrow().clone()) {
        return cached;
    }
    let specs = ScanSpecs {
        extern_requires: local_extern_spec_requires(tcx),
        type_invariant_defs,
    };
    let mut escapes = CallableEscapes::new();
    for host in tcx.hir_body_owners() {
        if !is_program_host(tcx, host) {
            continue;
        }
        let root = tcx.typeck_root_def_id(host.to_def_id()).expect_local();
        let _ = tcx.mir_borrowck(root);
        let Some(body_with_facts) = super::super::try_get_body_with_context(tcx, host) else {
            // A program body this run cannot read hands over what it likes:
            // reading the silence as "nothing" would credit it.
            if tcx.is_mir_available(host.to_def_id()) {
                escapes.insert(
                    host,
                    vec![CallableEscape {
                        callee: "code this run could not read".to_string(),
                        callable: EscapedCallable::Unresolved(
                            "whatever its unread body holds".to_string(),
                        ),
                    }],
                );
            }
            continue;
        };
        let found = body_callable_escapes(tcx, host, &body_with_facts.body, &specs);
        if !found.is_empty() {
            escapes.insert(host, found);
        }
    }
    let escapes = Rc::new(escapes);
    CRATE_ESCAPES.with(|cell| *cell.borrow_mut() = Some(escapes.clone()));
    escapes
}

/// Every local closure keyed by the body that defines it (a fn, a method or
/// an enclosing closure), one level deep.
///
/// A closure written inside an inline or anonymous const is keyed by the body
/// around the const: the const only builds the value, and the closure runs
/// wherever that body sends it.
pub(in crate::callbacks) fn closures_defined_by_body(
    tcx: TyCtxt<'_>,
) -> HashMap<LocalDefId, Vec<LocalDefId>> {
    let mut defined: HashMap<LocalDefId, Vec<LocalDefId>> = HashMap::new();
    for owner in tcx.hir_body_owners() {
        if matches!(tcx.def_kind(owner.to_def_id()), DefKind::Closure) {
            let mut body = tcx.local_parent(owner);
            while matches!(tcx.def_kind(body.to_def_id()), DefKind::AnonConst) {
                body = tcx.local_parent(body);
            }
            defined.entry(body).or_default().push(owner);
        }
    }
    defined
}

/// Whether `closure` is handed, by any body of the crate, to a callee whose
/// body trust-wp does not verify.
pub(in crate::callbacks) fn closure_escapes_to_unverified_code(
    tcx: TyCtxt<'_>,
    closure: LocalDefId,
    type_invariant_defs: &[TypeInvariantDef],
) -> bool {
    crate_callable_escapes(tcx, type_invariant_defs)
        .values()
        .flatten()
        .any(|escape| matches!(escape.callable, EscapedCallable::Closure(c) if c == closure))
}

/// Program code whose hand-offs are owed: a fn, method or closure body that is
/// not specification (logic, spec type-check, a `proof_assert!` carrier) and
/// not `#[trusted]` (whose contract is the author's claim), walking out through
/// every enclosing closure to the item that owns it.
///
/// A const's OWN body runs at compile time and hands nothing over at run time,
/// so a const, static or inline const is never a host itself. A closure it
/// builds is a run-time value all the same (`o.map(const { |j| w[j] })`): the
/// walk goes out through an inline or anonymous const to the code around it,
/// and a closure a const or static item builds is program code unless that
/// item is trusted or logic. Any other owner a closure's walk reaches is read
/// as program code too: "not program" silences every hand-off of the closure,
/// so it needs a positive reason.
fn is_program_host(tcx: TyCtxt<'_>, host: LocalDefId) -> bool {
    let mut cur = host;
    loop {
        let def_id = cur.to_def_id();
        match tcx.def_kind(def_id) {
            DefKind::Closure => {
                if is_specification_closure(tcx, def_id) {
                    return false;
                }
                cur = tcx.local_parent(cur);
            }
            DefKind::Fn | DefKind::AssocFn => {
                if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, cur) {
                    return false;
                }
                let attrs = tcx.get_all_attrs(def_id);
                return !crate::logic::has_logic_marker(attrs)
                    && !super::trusted::has_trusted_marker(tcx, def_id, attrs);
            }
            _ if cur == host => return false,
            DefKind::AnonConst => cur = tcx.local_parent(cur),
            DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::Static { .. } => {
                let attrs = tcx.get_all_attrs(def_id);
                return !crate::logic::has_logic_marker(attrs)
                    && !super::trusted::has_trusted_marker(tcx, def_id, attrs);
            }
            _ => return true,
        }
    }
}

/// A closure that is a specification term, never program code: a
/// `proof_assert!`-family carrier or a spec type-check closure.
fn is_specification_closure(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.get_all_attrs(def_id).iter().any(|attr| {
        crate::attr_utils::doc_marker_str(attr).is_some_and(|value| {
            let value = value.as_str();
            value.starts_with("trust-wp:proof_assert:")
                || value.starts_with("trust-wp:trusted_proof_assert:")
                || value.starts_with("trust-wp:proof_by:")
                || value.starts_with("trust-wp:spec_tc")
        })
    }) || def_id
        .as_local()
        .is_some_and(|local| crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local))
}

/// The hand-offs of one body: every argument of every reachable call whose
/// callee trust-wp does not verify, walked for the callables its type carries.
fn body_callable_escapes<'tcx>(
    tcx: TyCtxt<'tcx>,
    host: LocalDefId,
    body: &Body<'tcx>,
    specs: &ScanSpecs<'_>,
) -> Vec<CallableEscape> {
    let mut escapes = Vec::new();
    let mut visited = HashSet::new();
    let mut worklist = vec![START_BLOCK];
    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        let data = &body.basic_blocks[bb];
        if data.is_cleanup {
            continue;
        }
        for statement in &data.statements {
            if let Some(write) = unsized_capture_write(tcx, body, statement) {
                push_escape(
                    &mut escapes,
                    "an unsizing coercion to a trait object",
                    write,
                );
            }
        }
        let terminator = data.terminator();
        if let TerminatorKind::Call { func, args, .. }
        | TerminatorKind::TailCall { func, args, .. } = &terminator.kind
        {
            let arg_tys: Vec<Ty<'tcx>> = args.iter().map(|arg| arg.node.ty(body, tcx)).collect();
            call_escapes(tcx, host, func, &arg_tys, specs, &mut escapes);
        }
        for successor in terminator.successors() {
            if !body.basic_blocks[successor].is_cleanup {
                worklist.push(successor);
            }
        }
    }
    escapes
}

fn call_escapes<'tcx>(
    tcx: TyCtxt<'tcx>,
    host: LocalDefId,
    func: &Operand<'tcx>,
    arg_tys: &[Ty<'tcx>],
    specs: &ScanSpecs<'_>,
    escapes: &mut Vec<CallableEscape>,
) {
    // A call through a value (fn pointer, `dyn Fn`) runs code no lane names;
    // its own precondition is the call lane's, its arguments escape.
    let Some((callee, generic_args)) = func.const_fn_def() else {
        for &ty in arg_tys {
            collect_escaping_callables(
                tcx,
                host,
                ty,
                "a call through a fn pointer or `dyn Fn`",
                specs,
                escapes,
            );
        }
        return;
    };
    let callee_path = tcx.def_path_str(callee);
    if is_fn_family_trait_method(tcx, callee) {
        // `Fn::call(f, args)` INVOKES `f`: its precondition is the goal the
        // call lane states right here (D-54). The tupled arguments flow into
        // `f`'s body, which is verified when `f` is a local closure or fn and
        // unknown otherwise.
        let receiver_is_local_body = generic_args
            .types()
            .next()
            .is_some_and(|self_ty| names_local_body(self_ty.peel_refs()));
        for &ty in arg_tys.iter().skip(1) {
            if receiver_is_local_body {
                // The local body that runs is verified as the callee of a
                // generic hop is: see the verified-callee arm below.
                if let Some(write) = charged_callable_capture_write(tcx, ty) {
                    push_escape(escapes, &callee_path, write);
                }
            } else {
                collect_escaping_callables(tcx, host, ty, &callee_path, specs, escapes);
            }
        }
        return;
    }
    if callee_body_is_verified(tcx, host, callee, generic_args) {
        // The verified callee owes the callable's precondition (D-54 charges
        // it at the hop), but what a closure WRITES through a `&mut` it
        // captured lands in host memory, and the host's call lane gives a
        // post-call value only to a top-level `&mut` argument, never to the
        // local a closure argument borrows.
        for &ty in arg_tys {
            if let Some(write) = charged_callable_capture_write(tcx, ty) {
                push_escape(escapes, &callee_path, write);
            }
        }
        return;
    }
    if never_runs_its_callable(tcx, callee) || stores_without_running(tcx, callee) {
        return;
    }
    let charged = spec_charged_positions(tcx, callee, &callee_path, specs);
    for (position, &ty) in arg_tys.iter().enumerate() {
        if charged.contains(&position) {
            // The spec states this callable's precondition and the call lane
            // charges it here. What the callable WRITES through a `&mut` it
            // captured, the call lane advances only for a spec that states
            // the callable's post-state, and this body is walked by nobody.
            if let Some(write) = charged_callable_capture_write(tcx, ty) {
                push_escape(escapes, &callee_path, write);
            }
            continue;
        }
        collect_escaping_callables(tcx, host, ty, &callee_path, specs, escapes);
    }
    // A callee that runs a callable can hand it a `&mut` it holds inside a
    // by-value argument (`Some(&mut c).map(|r| *r = 5)`): the write lands in
    // the host's memory through a borrow no call lane advances, because only
    // a TOP-LEVEL `&mut` argument gets a post-call value.
    if arg_tys.iter().any(|&ty| carries_callable(tcx, host, ty)) {
        for &ty in arg_tys {
            if held_unique_borrow_below_top(tcx, ty) {
                push_escape(
                    escapes,
                    &callee_path,
                    EscapedCallable::UnseenWrite(format!(
                        "a `&mut` held inside `{ty}`, which the callable it also runs can write through"
                    )),
                );
            }
        }
    }
}

fn push_escape(escapes: &mut Vec<CallableEscape>, callee: &str, callable: EscapedCallable) {
    let escape = CallableEscape {
        callee: callee.to_string(),
        callable,
    };
    if !escapes.contains(&escape) {
        escapes.push(escape);
    }
}

/// A local closure that captures a `&mut` (by unique borrow, or a `&mut` or
/// a value holding one moved in) writes host memory wherever it runs. Run by
/// code no lane walks, that write reaches the host through no call lane: the
/// capture's owner keeps its pre-call value in the host's WP, so the closure
/// is a hand-off whose effect this run cannot state.
fn closure_capture_write<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: ty::GenericArgs<'tcx>,
) -> Option<EscapedCallable> {
    let writes = args
        .as_closure()
        .upvar_tys()
        .iter()
        .any(|upvar| holds_unique_borrow(tcx, upvar, &mut HashSet::new(), 0));
    writes.then(|| {
        EscapedCallable::UnseenWrite(format!(
            "the closure {}, which writes through a `&mut` it captures",
            tcx.def_path_str(def_id)
        ))
    })
}

/// A closure that writes through a captured `&mut`, coerced to a trait object
/// (`&mut || c = 5` as `&mut dyn FnMut()`, a `Box<{closure}>` as
/// `Box<dyn FnMut()>`). The erased type hides the capture from every walk of
/// the calls the object reaches, verified callee or not, so the write is
/// unseen from here on.
fn unsized_capture_write<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    statement: &rustc_middle::mir::Statement<'tcx>,
) -> Option<EscapedCallable> {
    use rustc_middle::{
        mir::{CastKind, Rvalue, StatementKind},
        ty::adjustment::PointerCoercion,
    };
    let StatementKind::Assign(assign) = &statement.kind else {
        return None;
    };
    let Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize, _), operand, _) = &assign.1
    else {
        return None;
    };
    charged_callable_capture_write(tcx, operand.ty(body, tcx))
}

/// [`closure_capture_write`] for every local closure a charged argument
/// carries.
fn charged_callable_capture_write<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> Option<EscapedCallable> {
    let mut found = None;
    walk_value_types(tcx, ty, &mut HashSet::new(), &mut |component| {
        if found.is_some() {
            return;
        }
        if let TyKind::Closure(def_id, args) = component.kind() {
            if def_id.is_local() {
                found = closure_capture_write(tcx, *def_id, *args);
            }
        }
    });
    found
}

/// Whether a value of type `ty` carries anything a callee can call.
fn carries_callable<'tcx>(tcx: TyCtxt<'tcx>, host: LocalDefId, ty: Ty<'tcx>) -> bool {
    let mut found = false;
    walk_value_types(tcx, ty, &mut HashSet::new(), &mut |component| {
        found |= match component.kind() {
            TyKind::Closure(..)
            | TyKind::FnDef(..)
            | TyKind::FnPtr(..)
            | TyKind::CoroutineClosure(..)
            | TyKind::Coroutine(..) => true,
            TyKind::Dynamic(predicates, ..) => {
                predicates.principal_def_id().is_some_and(|principal| {
                    trait_is_callable_family(tcx, principal, &mut HashSet::new())
                })
            }
            TyKind::Param(_) | TyKind::Alias(..) => bounded_callable(tcx, host, component),
            _ => false,
        };
    });
    found
}

/// The walk [`collect_rec`] makes over what a value holds: references,
/// std ADTs through their type arguments, tuples, arrays and slices, a
/// closure's captures.
fn walk_value_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    seen: &mut HashSet<Ty<'tcx>>,
    visit: &mut dyn FnMut(Ty<'tcx>),
) {
    if !seen.insert(ty) {
        return;
    }
    if let Some(denoted) = normalized_alias(tcx, ty) {
        return walk_value_types(tcx, denoted, seen, visit);
    }
    visit(ty);
    match ty.kind() {
        TyKind::Ref(_, inner, _)
        | TyKind::RawPtr(inner, _)
        | TyKind::Slice(inner)
        | TyKind::Array(inner, _)
        | TyKind::Pat(inner, _) => walk_value_types(tcx, *inner, seen, visit),
        TyKind::Tuple(elements) => {
            for element in elements.iter() {
                walk_value_types(tcx, element, seen, visit);
            }
        }
        TyKind::Adt(_, args) => {
            for arg in args.types() {
                walk_value_types(tcx, arg, seen, visit);
            }
        }
        TyKind::Closure(_, args) => {
            for upvar in args.as_closure().upvar_tys() {
                walk_value_types(tcx, upvar, seen, visit);
            }
        }
        _ => {}
    }
}

/// A parameter-free alias (a projection or an opaque type) read as the type it
/// denotes, or `None` when it has a parameter or does not normalize. Every
/// walk here reads what a VALUE holds: a field declared `I::Item` of an
/// adapter over `Range<u32>` holds a `u32`, and read unnormalized it is an
/// alias the walks must treat as holding anything.
fn normalized_alias<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    use rustc_middle::ty::TypeVisitableExt;
    if !matches!(ty.kind(), TyKind::Alias(..)) || ty.has_param() {
        return None;
    }
    tcx.try_normalize_erasing_regions(
        ty::TypingEnv::fully_monomorphized(),
        rustc_middle::ty::set_aliases_to_non_rigid(tcx, ty),
    )
    .ok()
    .filter(|denoted| *denoted != ty)
}

/// Whether `ty` holds a `&mut` strictly below its outermost constructor: a
/// top-level `&mut T` argument is advanced to its post-call value by the call
/// lane, what its pointee or any other value holds is not. A closure is left
/// to [`closure_capture_write`].
fn held_unique_borrow_below_top<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let below = match ty.kind() {
        TyKind::Ref(_, pointee, ty::Mutability::Mut) => *pointee,
        TyKind::Closure(..) => return false,
        _ => ty,
    };
    holds_unique_borrow(tcx, below, &mut HashSet::new(), 0)
}

/// Whether a value of type `ty` holds a `&mut` (or a raw pointer) through
/// which whoever runs with it can write memory someone else reads later.
///
/// A shared reference is a dead end (a write through `&&mut T` does not
/// compile; interior mutability is D-37's lane). std ADTs are read through
/// their type arguments, user ADTs through their fields, a closure through
/// its captures. A type parameter, and an alias built from one, holds
/// nothing by itself (the structural rule the interior-mutability lane
/// uses); anything else this walk cannot see into (a trait object, a
/// concrete opaque type, a coroutine) holds one.
fn holds_unique_borrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    seen: &mut HashSet<Ty<'tcx>>,
    depth: usize,
) -> bool {
    if depth > 32 {
        return true;
    }
    if !seen.insert(ty) {
        return false;
    }
    let recurse = |inner: Ty<'tcx>, seen: &mut HashSet<Ty<'tcx>>| {
        holds_unique_borrow(tcx, inner, seen, depth + 1)
    };
    match ty.kind() {
        TyKind::Ref(_, _, ty::Mutability::Mut) | TyKind::RawPtr(..) => true,
        TyKind::Ref(_, _, ty::Mutability::Not) => false,
        TyKind::Adt(adt, args) => {
            if matches!(
                tcx.crate_name(adt.did().krate).as_str(),
                "core" | "alloc" | "std"
            ) {
                args.types().any(|arg| recurse(arg, seen))
            } else {
                adt.all_fields()
                    .any(|field| recurse(field.ty(tcx, *args).skip_norm_wip(), seen))
            }
        }
        TyKind::Tuple(elements) => elements.iter().any(|element| recurse(element, seen)),
        TyKind::Array(inner, _) | TyKind::Slice(inner) | TyKind::Pat(inner, _) => {
            recurse(*inner, seen)
        }
        TyKind::Closure(_, args) => args
            .as_closure()
            .upvar_tys()
            .iter()
            .any(|upvar| recurse(upvar, seen)),
        TyKind::Dynamic(..)
        | TyKind::Coroutine(..)
        | TyKind::CoroutineClosure(..)
        | TyKind::CoroutineWitness(..) => true,
        TyKind::Alias(..) => match normalized_alias(tcx, ty) {
            Some(denoted) => recurse(denoted, seen),
            None => {
                use rustc_middle::ty::TypeVisitableExt;
                !ty.has_param()
            }
        },
        _ => false,
    }
}

fn is_fn_family_trait_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.trait_of_assoc(def_id)
        .is_some_and(|trait_def_id| tcx.fn_trait_kind_from_def_id(trait_def_id).is_some())
}

/// A closure or fn item of this crate: invoking it runs a body this run walks.
fn names_local_body(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Closure(def_id, _) | TyKind::FnDef(def_id, _) => def_id.is_local(),
        _ => false,
    }
}

/// Whether the body that runs for this call is one trust-wp verifies: a local,
/// non-`#[trusted]`, non-logic item with MIR (or a local trait method, whose
/// every implementation owes the contract, D-94). A trait method is resolved
/// to the implementation that runs where the call's arguments determine it.
fn callee_body_is_verified<'tcx>(
    tcx: TyCtxt<'tcx>,
    host: LocalDefId,
    callee: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> bool {
    let runs =
        crate::trait_credit::impl_item_that_runs(tcx, callee, generic_args, host.to_def_id())
            .unwrap_or(callee);
    if !runs.is_local() {
        return false;
    }
    let attrs = tcx.get_all_attrs(runs);
    if crate::logic::has_logic_marker(attrs) || super::trusted::has_trusted_marker(tcx, runs, attrs)
    {
        return false;
    }
    let bodyless_trait_method = tcx.trait_of_assoc(runs).is_some()
        && tcx.impl_of_assoc(runs).is_none()
        && !tcx.is_mir_available(runs);
    bodyless_trait_method || tcx.is_mir_available(runs)
}

/// Specification-library constructors that take a closure as the TERM it
/// denotes and never call it: a pearlite closure becomes a `Mapping`, and a
/// `snapshot!` body is deferred into a zero-sized `Snapshot`. Anything else in
/// the specification library that takes a closure (`PredCell::update`,
/// `thread::spawn`, an invariant's `open`) runs it, and is a hand-off.
const TERM_ONLY_CLOSURE_CONSTRUCTORS: &[&str] = &[
    "Mapping::from_closure",
    "Snapshot::from_fn",
    "spec_tc::mapping_from_fn",
    "spec_tc::for_loop_tc",
];

fn never_runs_its_callable(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if !crate::provenance::is_spec_library_item(tcx, callee) {
        return false;
    }
    let path = tcx.def_path_str(callee);
    let base = path.split('<').next().unwrap_or(&path);
    TERM_ONLY_CLOSURE_CONSTRUCTORS
        .iter()
        .any(|suffix| base.ends_with(suffix) || strip_generic_segments(&path).ends_with(suffix))
}

/// std constructors that move their argument into the value they build and
/// never call it. The callable escapes only where that value goes next, and
/// every walk here sees it again there through the built type's arguments
/// (`Option::map(Box<{closure}>)` is the closure's hand-off to `map`).
const STORE_ONLY_STD_CONSTRUCTORS: &[&str] = &["boxed::Box::new", "rc::Rc::new", "sync::Arc::new"];

fn stores_without_running(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if !crate::provenance::is_std_item(tcx, callee) {
        return false;
    }
    let path = strip_generic_segments(&tcx.def_path_str(callee));
    STORE_ONLY_STD_CONSTRUCTORS
        .iter()
        .any(|suffix| path.ends_with(&format!("::{suffix}")))
}

/// `a::B::<T>::c` -> `a::B::c`, so a suffix match ignores generic arguments.
fn strip_generic_segments(path: &str) -> String {
    let mut out = String::with_capacity(path.len());
    let mut depth = 0usize;
    for ch in path.chars() {
        match ch {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(ch),
            _ => {}
        }
    }
    out.replace("::::", "::")
}

/// Argument positions whose precondition the callee's OWN spec states — a
/// requires clause applying `<param>.precondition(..)` — so the call lane
/// charges it at this call (D-54 resolves it). Every other position is a
/// hand-off. A spec this cannot read charges nothing.
fn spec_charged_positions(
    tcx: TyCtxt<'_>,
    callee: DefId,
    callee_path: &str,
    specs: &ScanSpecs<'_>,
) -> HashSet<usize> {
    let (requires, param_names): (Vec<String>, Option<Vec<String>>) = if callee.is_local() {
        let attrs = tcx.get_all_attrs(callee);
        let mut requires = crate::attr_utils::get_contract_attrs_from_doc(attrs, "requires");
        requires.extend(crate::attr_utils::get_contract_attrs_from_proc_macro(
            attrs, "requires",
        ));
        (requires, None)
    } else if let Some((requires, names)) = specs
        .extern_requires
        .get(&trust_wp_driver::normalize_extern_spec_path(callee_path))
    {
        (requires.clone(), names.clone())
    } else if let Some(StdSpec {
        requires,
        param_names,
        ..
    }) = trust_wp_driver::lookup_spec_with_extern(None, callee_path)
    {
        (requires, param_names)
    } else {
        return HashSet::new();
    };
    let receivers: HashSet<String> = requires
        .iter()
        .flat_map(|clause| precondition_receivers(clause))
        .collect();
    if receivers.is_empty() {
        return HashSet::new();
    }
    let names: Vec<String> = param_names.unwrap_or_else(|| {
        tcx.fn_arg_idents(callee)
            .iter()
            .map(|ident| ident.map(|ident| ident.to_string()).unwrap_or_default())
            .collect()
    });
    names
        .iter()
        .enumerate()
        .filter(|(_, name)| receivers.contains(name.as_str()))
        .map(|(position, _)| position)
        .collect()
}

/// The identifiers `X` of every `X.precondition(` in a clause, with the
/// `(*X)` / `*X` spellings unwrapped.
fn precondition_receivers(clause: &str) -> Vec<String> {
    const NEEDLE: &str = ".precondition(";
    let mut receivers = Vec::new();
    let mut rest = clause;
    let mut offset = 0usize;
    while let Some(found) = rest.find(NEEDLE) {
        let end = offset + found;
        let before = &clause[..end];
        let trimmed = before.trim_end_matches(')');
        let ident: String = trimmed
            .chars()
            .rev()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        // `T::deref.precondition(..)` names a function, not a parameter.
        let qualified = trimmed[..trimmed.len() - ident.len()].ends_with("::");
        if !ident.is_empty() && !qualified {
            receivers.push(ident);
        }
        offset = end + NEEDLE.len();
        rest = &clause[offset..];
    }
    receivers
}

fn local_extern_spec_requires(tcx: TyCtxt<'_>) -> ExternRequires {
    let mut specs = HashMap::new();
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let doc_values: Vec<String> = tcx
            .get_all_attrs(def_id)
            .iter()
            .filter_map(|attr| crate::attr_utils::doc_marker_str(attr).map(|s| s.to_string()))
            .collect();
        if let Ok(Some(entry)) =
            trust_wp_driver::parse_extern_spec_docs(doc_values.iter().map(String::as_str))
        {
            specs.insert(
                trust_wp_driver::normalize_extern_spec_path(&entry.target_path),
                (entry.requires, entry.param_names),
            );
        }
    }
    specs
}

/// Record every callable the value of type `ty` carries.
///
/// The walk follows what a VALUE of the type holds — references, boxes and
/// other ADT arguments, tuples, arrays, a closure's captures — and stops at a
/// callable, which it classifies. A type parameter or opaque type is a
/// callable when a bound makes it one.
fn collect_escaping_callables<'tcx>(
    tcx: TyCtxt<'tcx>,
    host: LocalDefId,
    ty: Ty<'tcx>,
    callee: &str,
    specs: &ScanSpecs<'_>,
    escapes: &mut Vec<CallableEscape>,
) {
    let mut seen = HashSet::new();
    collect_rec(tcx, host, ty, callee, specs, escapes, &mut seen);
}

fn collect_rec<'tcx>(
    tcx: TyCtxt<'tcx>,
    host: LocalDefId,
    ty: Ty<'tcx>,
    callee: &str,
    specs: &ScanSpecs<'_>,
    escapes: &mut Vec<CallableEscape>,
    seen: &mut HashSet<Ty<'tcx>>,
) {
    if !seen.insert(ty) {
        return;
    }
    let mut push = |callable: EscapedCallable| push_escape(escapes, callee, callable);
    match ty.kind() {
        TyKind::Closure(def_id, args) => {
            match def_id.as_local() {
                Some(local) if !is_program_host(tcx, local) => {
                    // A closure of `#[trusted]` or specification code: its
                    // body is covered by the same claim as its owner's.
                }
                Some(_) if closure_has_requires(tcx, *def_id) => {
                    push(EscapedCallable::Unresolved(format!(
                        "the closure {}, whose `#[requires]` it does not establish",
                        tcx.def_path_str(*def_id)
                    )))
                }
                Some(local) => {
                    push(EscapedCallable::Closure(local));
                    if let Some(write) = closure_capture_write(tcx, *def_id, *args) {
                        push(write);
                    }
                }
                None => push(EscapedCallable::Unresolved(format!(
                    "the foreign closure {}",
                    tcx.def_path_str(*def_id)
                ))),
            }
            for upvar in args.as_closure().upvar_tys() {
                collect_rec(tcx, host, upvar, callee, specs, escapes, seen);
            }
        }
        TyKind::FnDef(def_id, args) => {
            if let Some(why) =
                fn_item_precondition_unstated(tcx, host, *def_id, args.skip_binder(), specs)
            {
                push(EscapedCallable::Unresolved(why));
            }
        }
        TyKind::FnPtr(..) => push(EscapedCallable::Unresolved(format!("a fn pointer `{ty}`"))),
        TyKind::Dynamic(predicates, ..) => {
            if predicates.principal_def_id().is_some_and(|principal| {
                trait_is_callable_family(tcx, principal, &mut HashSet::new())
            }) {
                push(EscapedCallable::Unresolved(format!(
                    "a trait object `{ty}`"
                )));
            }
        }
        TyKind::Param(_) | TyKind::Alias(..) => {
            if let Some(denoted) = normalized_alias(tcx, ty) {
                collect_rec(tcx, host, denoted, callee, specs, escapes, seen);
            } else if bounded_callable(tcx, host, ty) {
                push(EscapedCallable::Unresolved(format!(
                    "a value of type `{ty}`, whose precondition is unknown here"
                )));
            }
        }
        TyKind::CoroutineClosure(..) | TyKind::Coroutine(..) => {
            push(EscapedCallable::Unresolved(format!("the coroutine `{ty}`")))
        }
        TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) | TyKind::Slice(inner) => {
            collect_rec(tcx, host, *inner, callee, specs, escapes, seen);
        }
        TyKind::Array(inner, _) | TyKind::Pat(inner, _) => {
            collect_rec(tcx, host, *inner, callee, specs, escapes, seen);
        }
        TyKind::Tuple(elements) => {
            for element in elements.iter() {
                collect_rec(tcx, host, element, callee, specs, escapes, seen);
            }
        }
        TyKind::Adt(_, args) => {
            for arg in args.types() {
                collect_rec(tcx, host, arg, callee, specs, escapes, seen);
            }
        }
        _ => {}
    }
}

fn closure_has_requires(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    super::has_requires_clause(tcx, def_id)
}

/// Why a fn item's precondition is not established by a callee that may call
/// it with any argument, or `None` when it has none to establish: a
/// constructor, or a function whose contract (local, the crate's
/// `extern_spec!`, or the builtin table) states no `requires` and whose body
/// holds no parameter invariant premise.
///
/// A parameter invariant the body was granted is a precondition like a
/// written one: every call into it owes it (D-141), and the callee that calls
/// the item here owes nothing, so the hand-off is refused on the same
/// predicate that makes a direct caller a target.
fn fn_item_precondition_unstated<'tcx>(
    tcx: TyCtxt<'tcx>,
    host: LocalDefId,
    def_id: DefId,
    args: ty::GenericArgs<'tcx>,
    specs: &ScanSpecs<'_>,
) -> Option<String> {
    if matches!(tcx.def_kind(def_id), DefKind::Ctor(..)) {
        return None;
    }
    let path = tcx.def_path_str(def_id);
    if super::call_may_enter_invariant_grant(
        tcx,
        host.to_def_id(),
        def_id,
        args,
        specs.type_invariant_defs,
    ) {
        return Some(format!(
            "the fn item {path}, whose parameters' type invariants it does not establish"
        ));
    }
    if def_id.is_local() {
        return super::has_requires_clause(tcx, def_id)
            .then(|| format!("the fn item {path}, whose `#[requires]` it does not establish"));
    }
    if let Some((requires, _)) = specs
        .extern_requires
        .get(&trust_wp_driver::normalize_extern_spec_path(&path))
    {
        return (!requires.is_empty())
            .then(|| format!("the fn item {path}, whose `requires` it does not establish"));
    }
    match trust_wp_driver::lookup_spec_with_extern(None, &path) {
        Some(spec) if spec.requires.is_empty() => None,
        Some(_) => Some(format!(
            "the fn item {path}, whose `requires` it does not establish"
        )),
        None => Some(format!("the fn item {path}, which has no specification")),
    }
}

/// `Fn`, `FnMut`, `FnOnce`, their async forms, `Pattern` (which the library
/// implements for `FnMut(char) -> bool`), or a trait with one of them as a
/// supertrait.
fn trait_is_callable_family(
    tcx: TyCtxt<'_>,
    trait_def_id: DefId,
    seen: &mut HashSet<DefId>,
) -> bool {
    if !seen.insert(trait_def_id) {
        return false;
    }
    if tcx.fn_trait_kind_from_def_id(trait_def_id).is_some()
        || tcx.async_fn_trait_kind_from_def_id(trait_def_id).is_some()
    {
        return true;
    }
    if crate::provenance::is_std_item(tcx, trait_def_id)
        && tcx.def_path_str(trait_def_id).ends_with("pattern::Pattern")
    {
        return true;
    }
    tcx.explicit_super_clauses_of(trait_def_id)
        .skip_binder()
        .iter()
        .any(|(clause, _)| {
            clause.as_trait_clause().is_some_and(|super_trait| {
                trait_is_callable_family(tcx, super_trait.skip_binder().trait_ref.def_id, seen)
            })
        })
}

/// Whether a type parameter or alias type is bounded by a callable trait, in
/// the host's own where-clauses or (for an opaque or associated type) its
/// item bounds.
fn bounded_callable<'tcx>(tcx: TyCtxt<'tcx>, host: LocalDefId, ty: Ty<'tcx>) -> bool {
    let callable_clause = |clause: ty::Clause<'tcx>| {
        clause.as_trait_clause().is_some_and(|trait_clause| {
            let predicate = trait_clause.skip_binder();
            predicate.self_ty() == ty
                && trait_is_callable_family(tcx, predicate.trait_ref.def_id, &mut HashSet::new())
        })
    };
    if tcx
        .param_env(host.to_def_id())
        .caller_bounds()
        .any(callable_clause)
    {
        return true;
    }
    // An opaque type's bounds, and an associated type's declared bounds
    // (`type F: Fn(usize) -> u32;`), are item bounds, not caller bounds: a
    // generic host's `T::F` is a callable the where-clauses never mention.
    let item_bounds_of = match ty.kind() {
        TyKind::Alias(_, alias) => match alias.kind {
            ty::AliasTyKind::Opaque { def_id } => def_id,
            ty::AliasTyKind::Projection { def_id } => def_id,
            // An alias this walk does not see through could hold anything.
            ty::AliasTyKind::Inherent { .. } | ty::AliasTyKind::Free { .. } => return true,
        },
        _ => return false,
    };
    tcx.explicit_item_bounds(item_bounds_of)
        .skip_binder()
        .iter()
        .any(|(clause, _)| {
            clause.as_trait_clause().is_some_and(|trait_clause| {
                trait_is_callable_family(
                    tcx,
                    trait_clause.skip_binder().trait_ref.def_id,
                    &mut HashSet::new(),
                )
            })
        })
}

#[cfg(test)]
mod tests {
    use super::{precondition_receivers, strip_generic_segments};

    #[test]
    fn precondition_receivers_unwrap_deref_and_skip_paths() {
        assert_eq!(
            precondition_receivers("(*self).precondition(arg)"),
            vec!["self"]
        );
        assert_eq!(
            precondition_receivers("forall<x: _> self@[x] ==> f.precondition((x,))"),
            vec!["f"]
        );
        assert!(precondition_receivers("T::deref.precondition((self,))").is_empty());
        assert!(precondition_receivers("result == Some(f(v))").is_empty());
    }

    #[test]
    fn generic_segments_are_ignored_by_suffix_match() {
        assert_eq!(
            strip_generic_segments("trust_wp_std::logic::Mapping::<A, B>::from_closure"),
            "trust_wp_std::logic::Mapping::from_closure"
        );
    }
}
