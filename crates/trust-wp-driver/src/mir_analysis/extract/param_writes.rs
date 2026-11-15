// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parameters whose OWN storage a write may reach before a program point
//! (D-241).
//!
//! The walks to a `proof_assert!` start each parameter at its own name, which
//! is its ENTRY value: the value a `#[requires]` and the parameter's type
//! invariant speak of. Every value they record afterwards reads the parameter
//! as it was at that program point, so after a write the name inside a
//! recorded value is the entry value while the substitution key of the same
//! name is the value at the assertion. Two questions are asked of the MIR,
//! not of the walks, whose record of a write is exactly what can go missing:
//!
//! - [`params_with_renamable_entry`]: is the parameter's own name inside
//!   every recorded value its entry value, and nothing else: every write is a
//!   plain store the walks record as a value of its own (a whole or field
//!   store, a call's result), outside any loop, with no borrow lent mutably,
//!   no closure capture and no shared borrow of a value a shared borrow can
//!   change. Then the entry value can be given a symbol of its own, and, for
//!   plain data, keep its entry facts.
//! - [`param_writes_before`]: may anything have written the parameter: a
//!   field store, a `&mut` borrow of it or of a field handed to a call, a
//!   write in a loop, a reference parameter re-bound (`x = y`). The entry
//!   facts of a written part that cannot be versioned are withdrawn. A write
//!   THROUGH a reference parameter (`*x = 5`, `&mut *x`) is a write of its
//!   pointee, not of its own storage; D-38 and D-185 own that.

use std::collections::{BTreeSet, HashMap, HashSet};

use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, BorrowKind, Local, Location, Place, ProjectionElem,
        RawPtrKind, Rvalue, StatementKind, TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind, TypingEnv},
};

/// What a write may have changed of one parameter's own storage.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ParamWrite {
    /// The whole value: a store or `&mut` borrow of the parameter itself, or
    /// of a place inside it that does not start with a struct or tuple field.
    pub(crate) whole: bool,
    /// The first-level fields a store or `&mut` borrow reached
    /// (`p.a = 7`, `set7(&mut p.a)`, `p.a.0 = 1`).
    pub(crate) fields: BTreeSet<usize>,
    /// Whether a STORE reaches it (an assignment, a call's destination,
    /// `SetDiscriminant`), not only a `&mut` borrow. Past a store
    /// the parameter's name no longer reads its current value at the next
    /// borrow of it, which the walks name by the parameter's name.
    pub(crate) stored: bool,
}

/// The argument locals (`_1..=arg_count`) whose own storage a statement or
/// terminator that may run before `at` writes or lends mutably: an
/// assignment to the parameter or to a projection of it that does not go
/// through a dereference, a `&mut`/`&raw mut` borrow of such a place, a
/// call's destination, `SetDiscriminant`.
///
/// `at = None` asks without a program point and reports every such write in
/// the body. Over-reporting only withdraws premises.
pub(crate) fn params_written_before(body: &Body<'_>, at: Option<Location>) -> HashSet<Local> {
    param_writes_before(body, at).into_keys().collect()
}

/// [`params_written_before`], with the part of each parameter written.
pub(crate) fn param_writes_before(
    body: &Body<'_>,
    at: Option<Location>,
) -> HashMap<Local, ParamWrite> {
    let before = at.map(|at| blocks_that_may_run_before(body, at.block));
    let mut written: HashMap<Local, ParamWrite> = HashMap::new();
    let mut note = |place: &Place<'_>, stored: bool| {
        let Some(local) = own_storage(body, place) else {
            return;
        };
        let entry = written.entry(local).or_default();
        entry.stored |= stored;
        match place.projection.first() {
            Some(ProjectionElem::Field(field, _)) => {
                entry.fields.insert(field.as_usize());
            }
            _ => entry.whole = true,
        }
    };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(statement_limit) = statements_before(body, bb, at, before.as_ref()) else {
            continue;
        };
        for statement in &data.statements[..statement_limit] {
            match &statement.kind {
                StatementKind::Assign((place, rvalue)) => {
                    note(place, true);
                    match rvalue {
                        Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed)
                        | Rvalue::RawPtr(RawPtrKind::Mut, borrowed) => note(borrowed, false),
                        _ => {}
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    note(place, true);
                }
                _ => {}
            }
        }
        if !terminator_runs_before(bb, at, before.as_ref()) {
            continue;
        }
        if let Some(terminator) = &body.basic_blocks[bb].terminator {
            if let TerminatorKind::Call { destination, .. } = &terminator.kind {
                note(destination, true);
            }
        }
    }
    written
}

/// The parameters a write may reach before `at` whose own name inside every
/// value the walks to `at` record is their ENTRY value and nothing else, so
/// the `proof_assert` lane can name that value by a symbol of its own, apart
/// from their value at `at` (D-241), each with whether its entry facts may
/// then be stated of the entry symbol: its type is plain data
/// ([`holds_only_plain_data`]: scalars, and tuples, arrays, structs and
/// enums of plain data).
///
/// A parameter is one when it is of plain data or of a type parameter's
/// type, so no reference, raw pointer or `Box` inside it can carry a write
/// the store does not show; every write of it that may run before `at` is a
/// store to the parameter or to a field path of it, or a call's result stored
/// whole; no such write or `at` itself is in a block on a cycle; and before
/// `at` it is never borrowed `&mut` or `&raw`, never captured by a closure,
/// and never borrowed shared unless its type is `Freeze`. The walks name a
/// borrowed place by its owner's name, a reference identity that reads the
/// owner at the BORROW, and a write through a `&mut` borrow, a closure's
/// capture or a shared borrow of interior mutability changes the owner after
/// it: renamed to the entry symbol it would read the entry value where the
/// program reads a later one. A write through a `&mut` borrow of the owner is
/// also recorded twice (D-171), which the entry symbol would turn from a
/// contradiction into a consistent wrong value. A shared borrow of a `Freeze`
/// value is read at its binding when it is taken
/// (`resolve_ref_to_named_local`), which no write can change while it lives.
///
/// For each of these the walks record every write as a value (or a fresh
/// symbol where they cannot translate it), and the parameter's own name in a
/// recorded value is its entry value.
pub(crate) fn params_with_renamable_entry<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    at: Location,
) -> HashMap<Local, bool> {
    if !loop_free_before(body, at) {
        return HashMap::new();
    }
    let typing_env = TypingEnv::post_analysis(tcx, body.source.def_id());
    let before = blocks_that_may_run_before(body, at.block);
    let mut refused: HashSet<Local> = HashSet::new();
    // Locals holding a borrow of a parameter's place, so a closure capturing
    // the parameter by reference is seen through its capture operand.
    let mut borrow_holders: HashMap<Local, Local> = HashMap::new();
    for _ in 0..2 {
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign((
                    dest,
                    Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed),
                )) = &statement.kind
                else {
                    continue;
                };
                if !dest.projection.is_empty() {
                    continue;
                }
                let lent = if is_param(body, borrowed.local) {
                    Some(borrowed.local)
                } else {
                    borrow_holders.get(&borrowed.local).copied()
                };
                if let Some(param) = lent {
                    borrow_holders.insert(dest.local, param);
                }
            }
        }
    }
    let refuse_operand_capture = |operand: &rustc_middle::mir::Operand<'_>,
                                  refused: &mut HashSet<Local>| {
        if let Some(place) = operand.place() {
            if is_param(body, place.local) {
                refused.insert(place.local);
            }
            if let Some(&param) = borrow_holders.get(&place.local) {
                refused.insert(param);
            }
        }
    };
    let mut written: HashSet<Local> = HashSet::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(statement_limit) = statements_before(body, bb, Some(at), Some(&before)) else {
            continue;
        };
        let cyclic = super::collect_gate::block_on_cycle(body, bb);
        for statement in &data.statements[..statement_limit] {
            match &statement.kind {
                StatementKind::Assign((place, rvalue)) => {
                    if let Some(param) = own_storage(body, place) {
                        written.insert(param);
                        if cyclic {
                            refused.insert(param);
                        }
                    }
                    match rvalue {
                        Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed)
                        | Rvalue::RawPtr(_, borrowed) => {
                            if let Some(param) = own_storage(body, borrowed) {
                                refused.insert(param);
                            }
                        }
                        Rvalue::Ref(_, BorrowKind::Shared | BorrowKind::Fake(_), borrowed) => {
                            if let Some(param) = own_storage(body, borrowed) {
                                if !body.local_decls[param].ty.is_freeze(tcx, typing_env) {
                                    refused.insert(param);
                                }
                            }
                        }
                        Rvalue::Aggregate(
                            AggregateKind::Closure(..)
                            | AggregateKind::Coroutine(..)
                            | AggregateKind::CoroutineClosure(..),
                            operands,
                        ) => {
                            for operand in operands {
                                refuse_operand_capture(operand, &mut refused);
                            }
                        }
                        _ => {}
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if let Some(param) = own_storage(body, place) {
                        written.insert(param);
                        refused.insert(param);
                    }
                }
                _ => {}
            }
        }
        if !terminator_runs_before(bb, Some(at), Some(&before)) {
            continue;
        }
        let Some(terminator) = &data.terminator else {
            continue;
        };
        match &terminator.kind {
            TerminatorKind::Call { destination, .. } => {
                if let Some(param) = own_storage(body, destination) {
                    written.insert(param);
                    if cyclic || !destination.projection.is_empty() {
                        refused.insert(param);
                    }
                }
            }
            TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } => {
                refused.extend((1..=body.arg_count).map(Local::from_usize));
            }
            _ => {}
        }
    }
    written
        .into_iter()
        .filter(|param| !refused.contains(param) && !name_shared_with_another_binding(body, *param))
        .filter_map(|param| {
            let ty = body.local_decls[param].ty;
            let plain = holds_only_plain_data(tcx, typing_env, ty, 0);
            (plain || matches!(ty.kind(), TyKind::Param(_))).then_some((param, plain))
        })
        .collect()
}

/// Whether a name the parameter `param` is spelled by is also the debug
/// name of another binding, or that name with the entry-symbol suffix: a
/// recorded value naming it may then name that binding, which is no entry
/// value. D-237 renames a binding that shadows a parameter, so this holds
/// only where that renaming did not reach.
fn name_shared_with_another_binding(body: &Body<'_>, param: Local) -> bool {
    use rustc_middle::mir::VarDebugInfoContents;

    let is_param_itself = |contents: &VarDebugInfoContents<'_>| {
        matches!(contents, VarDebugInfoContents::Place(place)
            if place.local == param && place.projection.is_empty())
    };
    let names: Vec<String> = body
        .var_debug_info
        .iter()
        .filter(|info| is_param_itself(&info.value))
        .map(|info| info.name.to_string())
        .collect();
    body.var_debug_info.iter().any(|info| {
        let spelled = info.name.as_str();
        !is_param_itself(&info.value)
            && names.iter().any(|name| {
                spelled == name.as_str()
                    || spelled.strip_suffix(PARAM_ENTRY_VALUE_SUFFIX) == Some(name.as_str())
            })
    })
}

/// The suffix of the symbol a parameter's ENTRY value is read by where the
/// `proof_assert` lane names it apart from its current value (D-241).
pub(crate) const PARAM_ENTRY_VALUE_SUFFIX: &str = "__entry_value";

/// Whether no block on a cycle may run before `at`, nor holds it.
///
/// The substitution walk to `at` does not enter a loop it passes: it follows
/// the exit arm with the bindings from before the loop and, where the loop
/// arm fails on its cycle, names every binding the exit arm left unchanged
/// by the binding's own name. A value recorded after such a loop can read a
/// local the loop wrote at its value from before the loop, and a parameter's
/// own name stands for its value at the loop's exit, not its entry value.
/// Only on a loop-free path does a parameter's name inside a recorded value
/// mean its entry value (D-241).
fn loop_free_before(body: &Body<'_>, at: Location) -> bool {
    let before = blocks_that_may_run_before(body, at.block);
    !before
        .iter()
        .chain(std::iter::once(&at.block))
        .any(|&bb| super::collect_gate::block_on_cycle(body, bb))
}

/// Whether a value of `ty` is plain data: no reference, raw pointer, `Box`,
/// lifetime, interior mutability, union, type parameter or opaque type
/// anywhere in it, so nothing but a store to the value itself changes it.
fn holds_only_plain_data<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    depth: usize,
) -> bool {
    if depth > 8 {
        return false;
    }
    let plain = |ty: Ty<'tcx>| holds_only_plain_data(tcx, typing_env, ty, depth + 1);
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => true,
        TyKind::Tuple(fields) => fields.iter().all(plain),
        TyKind::Array(inner, _) => plain(*inner),
        TyKind::Adt(adt, args) => {
            (adt.is_struct() || adt.is_enum())
                && !adt.is_box()
                && !adt.is_unsafe_cell()
                && !adt.is_phantom_data()
                && args.regions().next().is_none()
                && ty.is_freeze(tcx, typing_env)
                && adt
                    .all_fields()
                    .all(|field| plain(field.ty(tcx, *args).skip_norm_wip()))
        }
        _ => false,
    }
}

fn own_storage(body: &Body<'_>, place: &Place<'_>) -> Option<Local> {
    (is_param(body, place.local) && !place.projection.contains(&ProjectionElem::Deref))
        .then_some(place.local)
}

fn is_param(body: &Body<'_>, local: Local) -> bool {
    (1..=body.arg_count).contains(&local.as_usize())
}

/// How many statements of `bb` may run before `at`: every statement of a
/// block that may run before it (which includes `at`'s own block when it is
/// on a cycle), else those of `at`'s block ahead of `at`. `None` when none
/// do. `at = None` asks of the whole body.
fn statements_before(
    body: &Body<'_>,
    bb: BasicBlock,
    at: Option<Location>,
    before: Option<&HashSet<BasicBlock>>,
) -> Option<usize> {
    let len = body.basic_blocks[bb].statements.len();
    match (at, before) {
        (None, _) => Some(len),
        (Some(_), Some(before)) if before.contains(&bb) => Some(len),
        (Some(at), _) if at.block == bb => Some(at.statement_index.min(len)),
        _ => None,
    }
}

/// Whether `bb`'s terminator may run before `at`. A terminator runs after
/// every statement of its block, so only a block that may run before `at`
/// contributes its terminator.
fn terminator_runs_before(
    bb: BasicBlock,
    at: Option<Location>,
    before: Option<&HashSet<BasicBlock>>,
) -> bool {
    at.is_none() || before.is_some_and(|before| before.contains(&bb))
}

/// The blocks whose statements and terminator can all run before `at` is
/// entered: every block from which a predecessor of `at` is reachable. `at`
/// itself is among them only when it lies on a cycle.
fn blocks_that_may_run_before(body: &Body<'_>, at: BasicBlock) -> HashSet<BasicBlock> {
    let predecessors = body.basic_blocks.predecessors();
    let mut seen = HashSet::new();
    let mut stack: Vec<BasicBlock> = predecessors[at].to_vec();
    while let Some(bb) = stack.pop() {
        if seen.insert(bb) {
            stack.extend(predecessors[bb].iter().copied());
        }
    }
    seen
}
