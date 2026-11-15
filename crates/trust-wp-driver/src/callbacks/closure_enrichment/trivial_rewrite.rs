// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract-free closure precondition resolution.
//!
//! A closure without `#[requires]` is TRANSPARENT, not vacuous: Creusot defines
//! its `precondition` as its body's weakest precondition over the formals, and
//! the caller discharges that definition at the call. This module identifies
//! the one concrete closure a `precondition` receiver denotes and substitutes
//! that body WP. When the receiver denotes no single closure, or the WP cannot
//! be computed in full, the obligation is WITHHELD — never rewritten to `true`,
//! which hands a callee's `#[requires]` to a place that drops it.

use std::{cell::RefCell, collections::HashMap, sync::Arc};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{Body, Local, Rvalue, StatementKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_logic_fn_arity, tuple_logic_fn_name},
    PureExpr,
};
use trust_wp_driver::StdSpec;

use super::{
    super::try_get_body_with_context, body_extraction::closure_body_precondition_over_formals,
    closure_env_ctor_arity, closure_receiver_base_name, collect_sole_env_owners,
};
use crate::mir_analysis::get_mir_body;

/// The contract-free closures of a body, keyed by the source name of the local
/// that holds each one, plus the capture arities that identify a contract-free
/// closure only by SHAPE.
///
/// Both maps must resolve to ONE closure or to nothing. A closure environment
/// lowers to `__trust_wp_tuple<N>(captures..)`, a term of capture VALUES that
/// carries no identity, so an arity is an identification only while exactly one
/// non-carrier closure of the body has it — `collect_sole_env_owners` is what
/// establishes that, and without it an arity-keyed match drops a contracted
/// sibling's real precondition (D-30,
/// `tests/adversarial/cases/s71_trivial_sibling_drops_precondition.rs`).
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(in crate::callbacks) struct ContractFreeClosureReceivers {
    pub(in crate::callbacks) names: HashMap<String, DefId>,
    pub(in crate::callbacks) env_arities: HashMap<usize, DefId>,
}

impl ContractFreeClosureReceivers {
    pub(in crate::callbacks) fn is_empty(&self) -> bool {
        self.names.is_empty() && self.env_arities.is_empty()
    }
}

/// The single producer of a contract-free closure's `precondition`.
///
/// The credit a generic `Fn` hop takes and the obligation its caller discharges
/// must be the same predicate, computed by the same code in the same
/// environment; two producers is how this hole was opened. Results are memoised
/// per closure `DefId` so every use of one closure's precondition — goal or
/// premise, this pass or the next — reads the same term.
pub(in crate::callbacks) struct ClosurePreconditions<'a, 'tcx> {
    specs: Option<ClosureSpecEnv<'a, 'tcx>>,
    memo: RefCell<HashMap<DefId, Option<(Vec<String>, PureExpr)>>>,
}

struct ClosureSpecEnv<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    user_specs: &'a HashMap<DefId, StdSpec>,
    trait_specs: &'a HashMap<DefId, StdSpec>,
    extern_specs: &'a HashMap<String, StdSpec>,
}

impl<'a, 'tcx> ClosurePreconditions<'a, 'tcx> {
    pub(in crate::callbacks) fn new(
        tcx: TyCtxt<'tcx>,
        user_specs: &'a HashMap<DefId, StdSpec>,
        trait_specs: &'a HashMap<DefId, StdSpec>,
        extern_specs: &'a HashMap<String, StdSpec>,
    ) -> Self {
        Self {
            specs: Some(ClosureSpecEnv {
                tcx,
                user_specs,
                trait_specs,
                extern_specs,
            }),
            memo: RefCell::new(HashMap::new()),
        }
    }

    /// A resolver for a lane that does not hold the trait and extern spec maps.
    ///
    /// Computing a body WP without them would silently miss the obligations of
    /// every callee whose contract lives in one — a weaker precondition, which
    /// is a false credit. The lane withholds instead.
    pub(in crate::callbacks) fn withholding() -> Self {
        Self {
            specs: None,
            memo: RefCell::new(HashMap::new()),
        }
    }

    fn over_formals(&self, closure_def_id: DefId) -> Option<(Vec<String>, PureExpr)> {
        let specs = self.specs.as_ref()?;
        if let Some(cached) = self.memo.borrow().get(&closure_def_id) {
            return cached.clone();
        }
        let computed = closure_body_precondition_over_formals(
            specs.tcx,
            closure_def_id,
            specs.user_specs,
            specs.trait_specs,
            specs.extern_specs,
        );
        self.memo
            .borrow_mut()
            .insert(closure_def_id, computed.clone());
        computed
    }

    /// The closure's precondition at a call passing `args`, or `None` to
    /// withhold the obligation.
    fn at_call(&self, closure_def_id: DefId, args: &[PureExpr]) -> Option<PureExpr> {
        let (formals, wp) = self.over_formals(closure_def_id)?;
        let actuals = destructure_precondition_args(args, formals.len())?;
        let substitutions: HashMap<String, PureExpr> =
            formals.into_iter().zip(actuals.into_iter()).collect();
        Some(wp.substitute(&substitutions))
    }
}

/// Bind a `precondition` call's argument list to the closure's formals.
///
/// Creusot passes the arguments as ONE tuple and destructures it into the
/// formals (`Term::let_(Pattern::tuple(inputs[1..]), args, pre)`), so the
/// single-tuple spelling is preferred over a positional read of the same list.
/// A shape that matches neither binds nothing and withholds.
fn destructure_precondition_args(args: &[PureExpr], arity: usize) -> Option<Vec<PureExpr>> {
    if args.len() == 1 {
        if let PureExpr::LogicFnCall { name, args: tuple } = &args[0] {
            // `tuple_logic_fn_arity` rejects arity 0 (a unit tuple has no field
            // to project), but a nullary closure's argument tuple IS the unit
            // tuple, so it is matched by name.
            let tuple_arity = if tuple.is_empty() && *name == tuple_logic_fn_name(0) {
                Some(0)
            } else {
                tuple_logic_fn_arity(name).filter(|a| *a == tuple.len())
            };
            if tuple_arity == Some(arity) {
                return Some(tuple.clone());
            }
        }
    }
    (args.len() == arity).then(|| args.to_vec())
}

/// Resolve the source-level name for a MIR local, if available.
///
/// Arguments are resolved from `arg_names` first, then local debug bindings.
fn source_name_for_local<'tcx>(
    body: &Body<'tcx>,
    local: Local,
    arg_names: &[String],
) -> Option<String> {
    let idx = local.as_u32() as usize;
    if idx >= 1 && idx <= arg_names.len() {
        return Some(arg_names[idx - 1].clone());
    }

    for info in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &info.value {
            if place.local == local && place.projection.is_empty() {
                return Some(info.name.to_string());
            }
        }
    }
    None
}

/// Identify the contract-free closures of a body and the receivers that denote
/// them.
pub(in crate::callbacks) fn collect_contract_free_closure_receivers(
    tcx: TyCtxt<'_>,
    parent_local_def_id: LocalDefId,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
) -> ContractFreeClosureReceivers {
    let mut receivers = ContractFreeClosureReceivers::default();
    let Some(body_with_facts) = try_get_body_with_context(tcx, parent_local_def_id) else {
        return receivers;
    };
    let mir_body: &Body<'_> = get_mir_body(&body_with_facts);
    let has_requires = |def_id: &DefId| {
        user_specs
            .get(def_id)
            .is_some_and(|spec| !spec.requires.is_empty())
    };
    receivers.env_arities = collect_sole_env_owners(tcx, parent_local_def_id)
        .into_iter()
        .filter(|(def_id, _)| !has_requires(def_id))
        .map(|(def_id, arity)| (arity, def_id))
        .collect();

    for bb_data in mir_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            let StatementKind::Assign((
                place,
                Rvalue::Aggregate(rustc_middle::mir::AggregateKind::Closure(def_id, _), _),
            )) = &stmt.kind
            else {
                continue;
            };

            // Keep explicit closure requires as obligations.
            if has_requires(def_id) {
                continue;
            }

            if let Some(name) = source_name_for_local(mir_body, place.local, arg_names) {
                // A name reused by two closure aggregates (a rebound `let c =
                // ...` in two arms) denotes neither: drop it rather than pick.
                match receivers.names.entry(name) {
                    std::collections::hash_map::Entry::Occupied(mut slot) => {
                        if slot.get() != def_id {
                            slot.insert(DefId::from(rustc_hir::def_id::CRATE_DEF_ID));
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(slot) => {
                        slot.insert(*def_id);
                    }
                }
            }
        }
    }

    receivers
}

/// Replace every `precondition` obligation whose receiver denotes ONE concrete
/// contract-free closure with that closure's body weakest precondition, the
/// hop's arguments bound to its formals.
///
/// Identity or nothing, and the WP or nothing: a receiver that names no single
/// closure, and a closure whose body WP cannot be computed in full, both leave
/// the obligation standing as an uninterpreted `precondition` the caller cannot
/// discharge. A partial WP would be a strictly weaker precondition, which is
/// the same false credit in a new place.
pub(in crate::callbacks) fn rewrite_contract_free_closure_precondition_goal(
    goal: &mut PureExpr,
    receivers: &ContractFreeClosureReceivers,
    preconditions: &ClosurePreconditions<'_, '_>,
) -> bool {
    rewrite_contract_free_closure_preconditions(goal, receivers, preconditions) > 0
}

fn rewrite_contract_free_closure_preconditions(
    expr: &mut PureExpr,
    trivial_receivers: &ContractFreeClosureReceivers,
    preconditions: &ClosurePreconditions<'_, '_>,
) -> usize {
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
        ..
    } = expr
    {
        if method == "precondition" {
            let identified = match closure_env_ctor_arity(receiver) {
                Some(arity) => trivial_receivers.env_arities.get(&arity),
                None => closure_receiver_base_name(receiver)
                    .and_then(|receiver_name| trivial_receivers.names.get(receiver_name)),
            };
            let resolved = identified.and_then(|def_id| preconditions.at_call(*def_id, args));
            if let Some(precondition) = resolved {
                *expr = precondition;
                return 1;
            }
        }
    }

    match expr {
        PureExpr::BinOp(left, _, right) => {
            rewrite_contract_free_closure_preconditions(
                Arc::make_mut(left),
                trivial_receivers,
                preconditions,
            ) + rewrite_contract_free_closure_preconditions(
                Arc::make_mut(right),
                trivial_receivers,
                preconditions,
            )
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => rewrite_contract_free_closure_preconditions(
            Arc::make_mut(inner),
            trivial_receivers,
            preconditions,
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            rewrite_contract_free_closure_preconditions(
                Arc::make_mut(cond),
                trivial_receivers,
                preconditions,
            ) + rewrite_contract_free_closure_preconditions(
                Arc::make_mut(then_expr),
                trivial_receivers,
                preconditions,
            ) + rewrite_contract_free_closure_preconditions(
                Arc::make_mut(else_expr),
                trivial_receivers,
                preconditions,
            )
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            let mut rewritten = rewrite_contract_free_closure_preconditions(
                Arc::make_mut(receiver),
                trivial_receivers,
                preconditions,
            );
            for arg in args {
                rewritten += rewrite_contract_free_closure_preconditions(
                    arg,
                    trivial_receivers,
                    preconditions,
                );
            }
            rewritten
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter_mut()
            .map(|arg| {
                rewrite_contract_free_closure_preconditions(arg, trivial_receivers, preconditions)
            })
            .sum(),
        PureExpr::LetAssume { assumption, body } => {
            rewrite_contract_free_closure_preconditions(
                Arc::make_mut(assumption),
                trivial_receivers,
                preconditions,
            ) + rewrite_contract_free_closure_preconditions(
                Arc::make_mut(body),
                trivial_receivers,
                preconditions,
            )
        }
        PureExpr::LetObligation { obligation, body } => {
            rewrite_contract_free_closure_preconditions(
                Arc::make_mut(obligation),
                trivial_receivers,
                preconditions,
            ) + rewrite_contract_free_closure_preconditions(
                Arc::make_mut(body),
                trivial_receivers,
                preconditions,
            )
        }
        PureExpr::Let { value, body, .. } => {
            rewrite_contract_free_closure_preconditions(
                Arc::make_mut(value),
                trivial_receivers,
                preconditions,
            ) + rewrite_contract_free_closure_preconditions(
                Arc::make_mut(body),
                trivial_receivers,
                preconditions,
            )
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            let mut rewritten = rewrite_contract_free_closure_preconditions(
                Arc::make_mut(body),
                trivial_receivers,
                preconditions,
            );
            for trigger_set in triggers {
                for trigger in trigger_set {
                    rewritten += rewrite_contract_free_closure_preconditions(
                        trigger,
                        trivial_receivers,
                        preconditions,
                    );
                }
            }
            rewritten
        }
        PureExpr::Match { scrutinee, arms } => {
            let mut rewritten = rewrite_contract_free_closure_preconditions(
                Arc::make_mut(scrutinee),
                trivial_receivers,
                preconditions,
            );
            for arm in arms {
                rewritten += rewrite_contract_free_closure_preconditions(
                    &mut arm.body,
                    trivial_receivers,
                    preconditions,
                );
            }
            rewritten
        }
        PureExpr::Closure { body, .. } => rewrite_contract_free_closure_preconditions(
            Arc::make_mut(body),
            trivial_receivers,
            preconditions,
        ),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(..) => 0,
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => 0,
    }
}
