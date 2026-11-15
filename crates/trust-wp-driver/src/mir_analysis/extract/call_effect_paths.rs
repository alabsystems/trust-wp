// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The value of each local at each block the block-slice walker
//! (`collect_call_effects_for_blocks`) reads before every loop, path by path
//! (D-243).
//!
//! A depth-first walk that keeps one binding per local for the whole slice
//! lets the arm it walks first decide the value at a join
//! (`if c { n = 1 } else { i = 0 }; need7(i)` read `i` as 7 on both paths).
//! Here each block starts from the merge of its predecessors' bindings, in
//! reverse postorder: a local every predecessor binds alike keeps that value;
//! one they bind apart is a symbol of its own for this join. When each
//! predecessor lies behind exactly one target of the switch ending the join's
//! immediate dominator (several behind one target being told apart, in turn,
//! by the switch of their nearest common dominator), the symbol is DEFINED by
//! one fact per arm, `cond(arm) ==> symbol == value(arm)`
//! ([`PathBindings::definitions`]): the arm's value is selected by the
//! conditions that took it. The facts are true in every execution: the arms'
//! conditions are disjoint, and where the join is not reached the symbol's
//! value is free.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::{
    mir::{BasicBlock, Body, Local, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{
    super::translate::{translate_rvalue_typed, ty_to_expr_sort_enriched},
    call_effect_reach::{exact_branch_conditions, normal_predecessors},
    helpers::translate_rvalue_with_enum_variants,
    loop_merges::normal_successors,
    past_loop_names::PastLoopNames,
};

/// The bindings the walk reads before every loop.
pub(super) struct PathBindings {
    /// The bindings at the terminator of every block of the walk.
    pub(super) at_terminator: HashMap<BasicBlock, HashMap<Local, PureExpr>>,
    /// Each join symbol's defining facts.
    pub(super) definitions: Vec<JoinDefinition>,
}

/// One arm's defining fact of a join symbol.
pub(super) struct JoinDefinition {
    /// The symbol's name.
    pub(super) symbol: String,
    /// The join the symbol is the value at: the fact speaks of the names it
    /// reads as they are there.
    pub(super) join: BasicBlock,
    /// `cond(arm) ==> symbol == value(arm)`.
    pub(super) fact: PureExpr,
}

impl PathBindings {
    /// The defining facts of every join symbol `effects` read, directly or
    /// through another such fact: the dependency closure of the premises and
    /// goals a slice states.
    pub(super) fn definitions_read_by<'e>(
        &self,
        effects: impl IntoIterator<Item = &'e PureExpr>,
    ) -> Vec<PureExpr> {
        if self.definitions.is_empty() {
            return Vec::new();
        }
        let mut read: HashSet<String> = HashSet::new();
        for expr in effects {
            read.extend(expr.free_vars());
        }
        let mut taken = vec![false; self.definitions.len()];
        let mut facts = Vec::new();
        let mut changed = true;
        while changed {
            changed = false;
            for (index, definition) in self.definitions.iter().enumerate() {
                if !taken[index] && read.contains(&definition.symbol) {
                    taken[index] = true;
                    read.extend(definition.fact.free_vars());
                    facts.push(definition.fact.clone());
                    changed = true;
                }
            }
        }
        facts
    }

    /// Keep only the defining facts `keep` accepts, by their join and fact.
    /// A join symbol whose arm's fact is dropped is free on that arm.
    pub(super) fn retain_definitions(
        &mut self,
        mut keep: impl FnMut(BasicBlock, &PureExpr) -> bool,
    ) {
        self.definitions
            .retain(|definition| keep(definition.join, &definition.fact));
    }
}

impl PathBindings {
    /// For each block of the walk whose one normal successor is a loop's
    /// header, `name == value` for every named local other than a parameter
    /// whose value there reads a join symbol, that only whole definitions
    /// change, and that nothing changes once a loop is entered (D-243). The
    /// loop's lane reads such a local at the loop's entry by its name, and so
    /// does the code after the loop; the loop lane's own entry walk states no
    /// value for a local set on one path
    /// (`loops::pre_loop_extract::drop_bindings_set_on_one_path`).
    ///
    /// The fact equates the local's bare name with the value, so every name
    /// the value reads, directly or through the join definitions it pulls in,
    /// must denote there the value the walk bound it to
    /// (`PastLoopNames::names_its_walk_value`). One rule covers every such
    /// name, the local's own included: an arm whose value is the local's own
    /// call result reads the local's name, which the walk spells for that
    /// result only where the destination keeps it up to the loops (D-244).
    ///
    /// `entry_only` is for a slice whose premises are read at the first loop's
    /// entry alone (the slice before every loop, whose premises initiate the
    /// first outermost loop): there a local a loop changes is stated too, at
    /// the entry of the loop whose header is the body's first block on a
    /// cycle, the loop that initiation reads.
    pub(super) fn loop_entry_values(
        &self,
        body: &Body<'_>,
        past_loop: &PastLoopNames<'_, '_>,
        seed: &HashMap<Local, PureExpr>,
        param_locals: &HashSet<Local>,
        entry_only: bool,
    ) -> Vec<(BasicBlock, PureExpr)> {
        let local_of_name: HashMap<&str, Local> = seed
            .iter()
            .filter_map(|(&local, expr)| match expr {
                PureExpr::Var(name, _) => Some((name.as_str(), local)),
                _ => None,
            })
            .collect();
        let mut facts = Vec::new();
        let mut entries: Vec<&BasicBlock> = self.at_terminator.keys().collect();
        entries.sort();
        for &bb in entries {
            let successors = normal_successors(body, bb);
            let [header] = successors[..] else {
                continue;
            };
            if !past_loop.is_in_loop(header)
                || matches!(
                    body.basic_blocks[bb].terminator().kind,
                    TerminatorKind::Call { .. }
                )
            {
                continue;
            }
            let bindings = &self.at_terminator[&bb];
            let mut locals: Vec<&Local> = bindings.keys().collect();
            locals.sort();
            let at_first_loop_entry = entry_only && past_loop.is_first_cycle_block(header);
            for &local in locals {
                let value = &bindings[&local];
                let Some(name @ PureExpr::Var(_, _)) = seed.get(&local) else {
                    continue;
                };
                let reads_a_join = value
                    .free_vars()
                    .iter()
                    .any(|var| var.contains("$walk_join"));
                if param_locals.contains(&local)
                    || !reads_a_join
                    || !past_loop.names_its_walk_value(local, at_first_loop_entry)
                {
                    continue;
                }
                let mut read = value.free_vars();
                for definition in self.definitions_read_by(std::iter::once(value)) {
                    read.extend(definition.free_vars());
                }
                let reads_walk_values = read.iter().all(|var| {
                    local_of_name.get(var.as_str()).is_none_or(|&other| {
                        past_loop.names_its_walk_value(other, at_first_loop_entry)
                    })
                });
                if !reads_walk_values {
                    continue;
                }
                let joins: Vec<String> = value
                    .free_vars()
                    .into_iter()
                    .filter(|var| var.contains("$walk_join"))
                    .collect();
                let equal_to = |value: PureExpr| {
                    PureExpr::BinOp(Arc::new(name.clone()), BinOp::Eq, Arc::new(value))
                };
                match &joins[..] {
                    // A value reading one join is stated arm by arm,
                    // `cond(arm) ==> name == value[join := value(arm)]`, so the
                    // name is never equated with a bare symbol: ay withholds an
                    // UNSAT whose preprocessing chains such variable
                    // substitutions (`a == join`, `join == 0`), and an
                    // equality invariant initiated from it was `unknown`. An
                    // `ite` selection would be encoded through auxiliary
                    // clauses whose proof ay does not certify either, in every
                    // goal the fact premises.
                    [join] => {
                        for (condition, arm_value) in self.arm_definitions(join) {
                            let at_arm = value
                                .substitute(&HashMap::from([(join.clone(), arm_value.clone())]));
                            // An arm whose value is the local's own call
                            // result states nothing: `name == name`.
                            if at_arm == *name {
                                continue;
                            }
                            facts.push((
                                bb,
                                PureExpr::BinOp(
                                    Arc::new(condition.clone()),
                                    BinOp::Implies,
                                    Arc::new(equal_to(at_arm)),
                                ),
                            ));
                        }
                    }
                    _ => facts.push((bb, equal_to(value.clone()))),
                }
            }
        }
        facts
    }

    /// The `(condition, value)` of each arm defining `join`
    /// (`condition ==> join == value`), in arm order; none for a join the
    /// dominating switch does not tell apart.
    fn arm_definitions(&self, join: &str) -> Vec<(&PureExpr, &PureExpr)> {
        self.definitions
            .iter()
            .filter(|definition| definition.symbol == join)
            .filter_map(|definition| match &definition.fact {
                PureExpr::BinOp(condition, BinOp::Implies, defined) => match defined.as_ref() {
                    PureExpr::BinOp(symbol, BinOp::Eq, value)
                        if matches!(symbol.as_ref(), PureExpr::Var(name, _) if name == join) =>
                    {
                        Some((condition.as_ref(), value.as_ref()))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }
}

/// The bindings at the terminator of every block of `allowed_blocks` that no
/// loop reaches.
///
/// A whole-local assignment whose right-hand side does not translate binds
/// the local to its name when that assignment is the local's one change in
/// the body (the name then denotes that value wherever the local is read),
/// and to a symbol of the assignment's site otherwise, never leaving the
/// value it had before. A call's destination is its result symbol after the
/// call.
#[allow(clippy::too_many_arguments)]
pub(super) fn path_bindings_before_loops<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    allowed_blocks: &HashSet<BasicBlock>,
    past_loop: &PastLoopNames<'_, 'tcx>,
    seed: &HashMap<Local, PureExpr>,
    local_names: &HashMap<Local, String>,
    param_locals: &HashSet<Local>,
    result_expr: impl Fn(BasicBlock, Local) -> PureExpr,
) -> PathBindings {
    // The local's index keeps two bindings that share a name apart.
    let symbol_for = |local: Local, tag: String| {
        let name = local_names.get(&local).map_or("", String::as_str);
        PureExpr::Var(
            format!("{name}$walk_{tag}_{}", local.as_u32()),
            ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty),
        )
    };
    let in_walk = |bb: BasicBlock| allowed_blocks.contains(&bb) && !past_loop.is_past_a_loop(bb);
    let predecessors = normal_predecessors(body);
    // Bindings at each block's terminator, and after it (its destination).
    let mut at_terminator: HashMap<BasicBlock, HashMap<Local, PureExpr>> = HashMap::new();
    let mut at_exit: HashMap<BasicBlock, HashMap<Local, PureExpr>> = HashMap::new();
    let mut definitions: Vec<JoinDefinition> = Vec::new();
    for &bb in body.basic_blocks.reverse_postorder() {
        if !in_walk(bb) || body.basic_blocks[bb].is_cleanup {
            continue;
        }
        let preds = predecessors.get(&bb).map_or(&[][..], Vec::as_slice);
        let mut state = if bb == rustc_middle::mir::START_BLOCK {
            if !preds.is_empty() {
                // The entry is re-entered: a cycle, which the walk never reads.
                continue;
            }
            seed.clone()
        } else {
            let incoming: Vec<(BasicBlock, &HashMap<Local, PureExpr>)> = preds
                .iter()
                .filter_map(|pred| at_exit.get(pred).map(|exit| (*pred, exit)))
                .collect();
            if incoming.is_empty() {
                continue;
            }
            // A predecessor not walked (a back edge, or a block outside the
            // walk) brings bindings this merge does not see.
            let complete = incoming.len() == preds.len();
            let arms = if complete && incoming.len() > 1 {
                arm_conditions(tcx, body, bb, &incoming, &at_terminator)
            } else {
                None
            };
            let mut locals: Vec<Local> = Vec::new();
            for (_, bindings) in &incoming {
                for local in bindings.keys() {
                    if !locals.contains(local) {
                        locals.push(*local);
                    }
                }
            }
            let mut merged: HashMap<Local, PureExpr> = HashMap::new();
            for local in locals {
                let values: Option<Vec<&PureExpr>> = incoming
                    .iter()
                    .map(|(_, bindings)| bindings.get(&local))
                    .collect();
                if let Some(values) = &values {
                    if complete && values.iter().all(|v| *v == values[0]) {
                        merged.insert(local, values[0].clone());
                        continue;
                    }
                }
                let symbol = symbol_for(local, format!("join{}", bb.as_u32()));
                if let (Some(values), Some(conditions), PureExpr::Var(name, Some(_))) =
                    (&values, &arms, &symbol)
                {
                    for (condition, value) in conditions.iter().zip(values) {
                        definitions.push(JoinDefinition {
                            symbol: name.clone(),
                            join: bb,
                            fact: PureExpr::BinOp(
                                Arc::new(condition.clone()),
                                BinOp::Implies,
                                Arc::new(PureExpr::BinOp(
                                    Arc::new(symbol.clone()),
                                    BinOp::Eq,
                                    Arc::new((*value).clone()),
                                )),
                            ),
                        });
                    }
                }
                merged.insert(local, symbol);
            }
            merged
        };
        let data = &body.basic_blocks[bb];
        for (index, stmt) in data.statements.iter().enumerate() {
            let StatementKind::Assign((place, rvalue)) = &stmt.kind else {
                continue;
            };
            if !place.projection.is_empty() {
                continue;
            }
            let expr =
                translate_rvalue_with_enum_variants(tcx, rvalue, &state, Some(body), None, None)
                    .or_else(|| translate_rvalue_typed(tcx, rvalue, &state, Some(body)))
                    .unwrap_or_else(|| match seed.get(&place.local) {
                        Some(name) if past_loop.changes_once(place.local) => name.clone(),
                        _ => symbol_for(place.local, format!("bb{}_{index}", bb.as_u32())),
                    });
            state.insert(place.local, expr);
        }
        let mut exit = state.clone();
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind {
            if destination.projection.is_empty() && !param_locals.contains(&destination.local) {
                exit.insert(destination.local, result_expr(bb, destination.local));
            }
        }
        at_terminator.insert(bb, state);
        at_exit.insert(bb, exit);
    }
    PathBindings {
        at_terminator,
        definitions,
    }
}

/// The condition under which the execution arrives at `join` through each
/// of its predecessors, in `incoming`'s order.
///
/// The switch ending the join's immediate dominator runs on every path to
/// the join. Each predecessor must lie behind exactly one of its targets (be
/// reachable from that target without passing the join); the predecessor
/// then arrives only where the switch took that target, and its condition is
/// that target's exact condition. Several predecessors behind one target are
/// told apart the same way by the switch ending their nearest common
/// dominator, which runs on every path to each of them (an `if` / `else if` /
/// `else` chain whose arms all meet at one join), and the condition is the
/// conjunction of both. Two predecessors' conditions are therefore disjoint:
/// they part at a switch that runs on both paths, by targets whose
/// conditions are. Anything else (a predecessor behind two targets, a
/// dominator that is no switch, a switch with no exact condition) leaves the
/// join undefined (`None`).
///
/// The conditions are translated with the walk's bindings at each switch,
/// which follow every whole assignment path by path: a discriminant needs
/// stability only against writes the walk does not see
/// (`exact_branch_conditions`, flow-sensitive).
fn arm_conditions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    join: BasicBlock,
    incoming: &[(BasicBlock, &HashMap<Local, PureExpr>)],
    at_terminator: &HashMap<BasicBlock, HashMap<Local, PureExpr>>,
) -> Option<Vec<PureExpr>> {
    let preds: Vec<BasicBlock> = incoming.iter().map(|(pred, _)| *pred).collect();
    let dom = body.basic_blocks.dominators().immediate_dominator(join)?;
    let mut conditions: HashMap<BasicBlock, PureExpr> = HashMap::new();
    tell_arms_apart(
        tcx,
        body,
        join,
        dom,
        &preds,
        None,
        at_terminator,
        &mut conditions,
        0,
    )?;
    preds.iter().map(|pred| conditions.remove(pred)).collect()
}

/// [`arm_conditions`] for the predecessors `preds` of `join`, all dominated
/// by `dom`, each arriving under `outer` and the condition of the target of
/// `dom`'s switch it lies behind.
#[allow(clippy::too_many_arguments)]
fn tell_arms_apart<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    join: BasicBlock,
    dom: BasicBlock,
    preds: &[BasicBlock],
    outer: Option<&PureExpr>,
    at_terminator: &HashMap<BasicBlock, HashMap<Local, PureExpr>>,
    conditions: &mut HashMap<BasicBlock, PureExpr>,
    depth: usize,
) -> Option<()> {
    if depth > body.basic_blocks.len() {
        return None;
    }
    let TerminatorKind::SwitchInt { discr, targets } = &body.basic_blocks[dom].terminator().kind
    else {
        return None;
    };
    let exprs = at_terminator.get(&dom)?;
    let target_conditions = exact_branch_conditions(tcx, body, dom, discr, targets, exprs, false)?;
    let regions: Vec<(BasicBlock, HashSet<BasicBlock>)> = target_conditions
        .keys()
        .map(|&target| (target, region_before(body, target, join)))
        .collect();
    let mut groups: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
    for &pred in preds {
        let behind: Vec<BasicBlock> = regions
            .iter()
            .filter(|(target, region)| {
                if *target == join {
                    pred == dom
                } else {
                    region.contains(&pred)
                }
            })
            .map(|(target, _)| *target)
            .collect();
        let [target] = behind[..] else {
            return None;
        };
        groups.entry(target).or_default().push(pred);
    }
    for (target, group) in groups {
        let condition = target_conditions.get(&target)?;
        let condition = match outer {
            Some(outer) => PureExpr::BinOp(
                Arc::new(outer.clone()),
                BinOp::And,
                Arc::new(condition.clone()),
            ),
            None => condition.clone(),
        };
        if let [pred] = group[..] {
            conditions.insert(pred, condition);
            continue;
        }
        let inner = nearest_common_dominator(body, &group)?;
        if inner == dom {
            return None;
        }
        tell_arms_apart(
            tcx,
            body,
            join,
            inner,
            &group,
            Some(&condition),
            at_terminator,
            conditions,
            depth + 1,
        )?;
    }
    Some(())
}

/// The nearest block that dominates every block of `blocks`.
fn nearest_common_dominator(body: &Body<'_>, blocks: &[BasicBlock]) -> Option<BasicBlock> {
    let dominators = body.basic_blocks.dominators();
    let (&first, rest) = blocks.split_first()?;
    let mut candidate = first;
    loop {
        if rest
            .iter()
            .all(|&block| dominators.dominates(candidate, block))
        {
            return Some(candidate);
        }
        candidate = dominators.immediate_dominator(candidate)?;
    }
}

/// `start` and the blocks reachable from it without passing `stop`.
fn region_before(body: &Body<'_>, start: BasicBlock, stop: BasicBlock) -> HashSet<BasicBlock> {
    let mut seen = HashSet::new();
    if start == stop {
        return seen;
    }
    let mut stack = vec![start];
    while let Some(next) = stack.pop() {
        if next == stop || !seen.insert(next) {
            continue;
        }
        stack.extend(normal_successors(body, next));
    }
    seen
}
