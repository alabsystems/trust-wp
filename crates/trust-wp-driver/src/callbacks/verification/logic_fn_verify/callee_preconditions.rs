// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The preconditions of the logic functions a logic function's body calls are
//! goals of that function.
//!
//! Creusot's logic VC generator (`backend/logic/vcgen.rs`, `TermKind::Call`)
//! reads a call `f(a)` as `requires_f(a) && variant && (ensures_f(a) ==> k)`,
//! so the `vc_` goal of every contracted logic function owes the precondition
//! of each call in its body at the point of the call: under the branch
//! conditions of the `if`/`match` arms around it, the `let` bindings in scope,
//! the left operand of a short-circuit `&&` / `||` / `==>`, and for all values
//! of the binders of an enclosing quantifier or closure. The postcondition
//! lane proves `ensures` from the body's value, and a callee's defining and
//! spec axioms are guarded by that callee's `requires`, so a call outside it
//! is merely unconstrained there and nothing noticed it
//! (logic_fn_callee_precondition_never_examined.rs).
//!
//! This module states those preconditions as one goal over the body's own
//! scoping. Which definition a call denotes is what rustc resolved it to
//! (`logic::call_resolution`, D-136): a call's spelling is only the name it is
//! written with, and a `use ... as` rename, a re-export, a `self::`/`super::`
//! path, a fn item bound to a local or a method of a bounded type spells one
//! definition with another's name or none. Every definition rustc resolves a
//! call of that spelling to owes its `requires`, and so does every contracted
//! definition the spelling itself names, so a resolution the encoder makes
//! differently can only add a goal, never drop one. A call the walk cannot
//! place, a call rustc resolves to a callee whose precondition the walk
//! cannot state, a call of the parsed body the type-checked body does not
//! hold, a call with a precondition the parsed body does not hold, and a
//! candidate whose arity does not fit the call are REFUSED, never dropped.
//!
//! Two kinds of callee are not in the lane's logic functions yet carry a
//! precondition the encoder never sees, because it reads the call as a total
//! function (a payload selector, an unconstrained value or an uninterpreted
//! placeholder): a standard-library logic function whose Creusot declaration
//! has a `requires` (`std_logic_precondition`), and a program function of the
//! crate, which Creusot does not admit in logic at all
//! (`ProgramFnsWithRequires`). The first owes its precondition where the walk
//! can state it and is refused where it cannot; the second is refused.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::{
    formula::{
        BinOp, CaptureAvoidingSubstOptions, ExprSort, MatchArm, PureExpr,
        PureExprDepthLimitedTraversalExt as _, UnOp,
    },
    logic::{identity::LOGIC_FN_ID_PREFIX, LogicFnDef},
};

use super::super::recursive_induction::is_integer_sort;
use crate::logic::call_resolution::{call_spelling, is_reserved_call_name, without_triggers};

/// The body walk's depth budget, the encoder's own (`MAX_ENCODING_DEPTH`).
const DEPTH_LIMIT: usize = 200;

/// What a logic function body owes for the preconditions of its calls.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum CalleePreconditionGoal {
    /// No call in the body can denote a definition with a `requires`.
    None,
    /// The condition every such call puts on the body's parameters.
    Goal(PureExpr),
    /// A call sits where this walk cannot place it; the reason names it.
    Refused(String),
}

/// A definition rustc resolved a call of a logic body to, as this walk reads
/// it (`prep::logic_body_callees`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::callbacks) enum ResolvedCallee {
    /// A logic function of the lane, by crate-qualified path: a call owes
    /// its `requires`.
    Logic(String),
    /// A function of another crate, by its resolved path: a call owes what
    /// Creusot's standard library requires of it (`std_logic_precondition`).
    Std(String),
    /// A callee whose precondition no logic body may owe; the reason.
    Refused(String),
    /// Owes nothing: a constructor, or a function with no precondition.
    Free,
}

/// One call of a logic body's type-checked form.
#[derive(Debug, Clone)]
struct ResolvedCall {
    /// The name it is written with (`call_spelling`); `None` for an operator.
    spelling: Option<String>,
    callees: Vec<ResolvedCallee>,
}

/// What rustc resolved the calls of one logic body to.
#[derive(Debug, Clone, Default)]
pub(in crate::callbacks) struct BodyCallees {
    calls: Vec<ResolvedCall>,
    /// Why the body's calls cannot be read against `calls` at all.
    refused: Option<String>,
    /// The name of every call of the body as written that the walked body
    /// still holds as itself (`call_resolution::ParsedCalls::kept`): an
    /// inlined callee's calls are in the walked body too, and none of them is
    /// the counterpart of a call of this body.
    written: Vec<String>,
}

impl BodyCallees {
    pub(in crate::callbacks) fn push(
        &mut self,
        spelling: Option<String>,
        callees: Vec<ResolvedCallee>,
    ) {
        self.calls.push(ResolvedCall { spelling, callees });
    }

    pub(in crate::callbacks) fn refuse(&mut self, why: String) {
        self.refused.get_or_insert(why);
    }

    pub(in crate::callbacks) fn keep_written_calls(&mut self, names: Vec<String>) {
        self.written = names;
    }
}

/// What is recorded of one logic body's calls.
#[derive(Debug, Clone)]
pub(in crate::callbacks) enum RecordedBody {
    /// rustc's resolution of every call of the body.
    Typed(BodyCallees),
    /// No type-checked form. `written_call` is the first call of the body as
    /// written, before inlining replaced any.
    Untyped { written_call: Option<String> },
    /// The body reads a call as something rustc says it is not, or cannot
    /// say it is (`call_resolution::settle_spelled_calls`); why.
    Misread(String),
}

/// Every logic function's recorded calls, by crate-qualified path.
#[derive(Debug, Default)]
pub(in crate::callbacks) struct LogicBodyCallees {
    by_fn: HashMap<String, RecordedBody>,
    /// The logic-lane tests read every body by spelling alone.
    #[cfg(test)]
    spelling_only: bool,
}

impl LogicBodyCallees {
    pub(in crate::callbacks) fn insert(&mut self, full_path: &str, recorded: RecordedBody) {
        self.by_fn.insert(full_path.to_string(), recorded);
    }

    /// The table the logic-lane tests read: every body by spelling alone.
    #[cfg(test)]
    pub(in crate::callbacks) fn spelling_only() -> Self {
        Self {
            by_fn: HashMap::new(),
            spelling_only: true,
        }
    }

    /// What is known of the calls of the logic function at `full_path`. A
    /// function the table does not hold has no type-checked form.
    pub(in crate::callbacks) fn resolution(&self, full_path: &str) -> CallResolution<'_> {
        #[cfg(test)]
        if self.spelling_only {
            return CallResolution::Spelling;
        }
        match self.by_fn.get(full_path) {
            Some(RecordedBody::Typed(callees)) => CallResolution::Typed(callees),
            Some(RecordedBody::Untyped { written_call }) => CallResolution::Untyped {
                written_call: written_call.as_deref(),
            },
            Some(RecordedBody::Misread(why)) => CallResolution::Misread(why),
            None => CallResolution::Untyped { written_call: None },
        }
    }
}

/// What the walk knows of the definitions a body's calls denote.
#[derive(Debug, Clone, Copy)]
pub(in crate::callbacks) enum CallResolution<'a> {
    /// rustc's resolution of every call of the body.
    Typed(&'a BodyCallees),
    /// Nothing: the body has no type-checked form, and only a body that
    /// makes no call is placed. `written_call` is a call of the body as
    /// written, which inlining may have replaced by a body that calls nothing.
    Untyped { written_call: Option<&'a str> },
    /// The body is misread, and every goal of it is refused; why.
    Misread(&'a str),
    /// Only the calls' spellings: the premise of the placement tests.
    #[cfg(test)]
    Spelling,
}

/// The program functions of the crate that carry a `#[requires]`, by every
/// name a logic body could spell a call to one with. The encoder reads such a
/// call as an uninterpreted placeholder, so no lane would owe the
/// precondition; the walk refuses it.
#[derive(Debug, Default)]
pub(in crate::callbacks) struct ProgramFnsWithRequires {
    /// Crate-qualified and crate-relative paths.
    paths: HashSet<String>,
    /// Item names of free functions: a bare call, or any path ending in one.
    free_names: HashSet<String>,
    /// `Owner::name` for an associated function, one per owner (the self
    /// type, the trait).
    associated: HashSet<String>,
}

impl ProgramFnsWithRequires {
    pub(in crate::callbacks) fn insert_path(&mut self, path: String) {
        self.paths.insert(path);
    }

    pub(in crate::callbacks) fn insert_free(&mut self, name: String) {
        self.free_names.insert(name);
    }

    pub(in crate::callbacks) fn insert_associated(&mut self, owner: &str, name: &str) {
        self.associated.insert(format!("{owner}::{name}"));
    }

    /// Whether a free-function call spelled `call_name` may denote one of
    /// them. A call resolved to a logic function's unique id never does: an id
    /// has no `::` and is no item name.
    fn may_denote(&self, call_name: &str) -> bool {
        if self.paths.contains(call_name) {
            return true;
        }
        let stem = strip_turbofish(call_name);
        let (qualifier, name) = match stem.rsplit_once("::") {
            Some((qualifier, name)) => (Some(qualifier), name),
            None => (None, stem),
        };
        self.free_names.contains(name)
            || qualifier.is_some_and(|qualifier| {
                qualifier_owners(qualifier)
                    .into_iter()
                    .any(|owner| self.associated.contains(&format!("{owner}::{name}")))
            })
    }
}

/// The owner names a call qualifier spells: `m::S` and `S::<T>` give `S`,
/// `<S as m::Tr>` gives `S` and `Tr`.
fn qualifier_owners(qualifier: &str) -> Vec<&str> {
    fn bare(path: &str) -> &str {
        let path = path.trim();
        let path = match path.find('<') {
            Some(generics) => path[..generics].trim_end_matches("::"),
            None => path,
        };
        path.rsplit("::").next().unwrap_or(path).trim()
    }
    match qualifier
        .strip_prefix('<')
        .and_then(|inner| inner.strip_suffix('>'))
        .and_then(|inner| inner.split_once(" as "))
    {
        Some((self_ty, trait_path)) => vec![bare(self_ty), bare(trait_path)],
        None => vec![bare(qualifier)],
    }
}

/// Creusot's standard-library logic functions whose declaration carries a
/// `requires` the walk cannot state. Each is refused wherever a contracted
/// logic body calls it: `such_that` (a witness exists), `inner_inj` and
/// `resolve_coherence` (laws over a subset type and a resolution), `union`
/// (`FMap` operands disjoint; the spelling cannot tell it from `FSet`'s),
/// `offset_logic` (the address stays in range), `new_frag` (a view
/// relation holds), and the laws `rel_mono`, `rel_none` (the view relation
/// holds of the fragment) and `get_timestamp_monotonic` (the views are
/// ordered). The standard library this crate is built against declares the
/// three laws with no contract at all, so nothing but this table owes them
/// (logic_fn_std_view_rel_law_refused.rs).
const STD_UNSTATED_PRECONDITIONS: &[&str] = &[
    "such_that",
    "inner_inj",
    "resolve_coherence",
    "union",
    "offset_logic",
    "new_frag",
    "rel_mono",
    "rel_none",
    "get_timestamp_monotonic",
];

/// The owners whose standard-library `new` has a precondition the walk
/// cannot state: `Nat::new` and `PositiveReal::new` (the value is in range)
/// and `View::new` (the view relation holds; declared with no contract in
/// the standard library this crate is built against,
/// logic_fn_std_view_new_refused.rs).
const STD_NEW_WITH_PRECONDITION: &[&str] = &["Nat", "PositiveReal", "View"];

/// The precondition Creusot's standard library declares for a logic call
/// spelled `name` with `args` (a method call's receiver first): `Some(Ok(p))`
/// when the walk states it, `Some(Err(why))` when it cannot, `None` when the
/// spelling names no such function.
fn std_logic_precondition(name: &str, args: &[PureExpr]) -> Option<Result<PureExpr, String>> {
    let tail = call_spelling(name);
    match (tail, args) {
        // `Option::unwrap_logic` requires `self != None`, spelled as a
        // contract spells it; the encoder reads the call as the `Some`
        // payload selector, total on `None`.
        ("unwrap_logic", [receiver]) => Some(Ok(PureExpr::BinOp(
            Arc::new(receiver.clone()),
            BinOp::Ne,
            Arc::new(PureExpr::Var("None".to_string(), None)),
        ))),
        // `logic::unreachable` requires `false`.
        ("unreachable", []) => Some(Ok(PureExpr::Bool(false))),
        _ if std_precondition_unstated(name) => Some(Err(format!(
            "a call `{name}` to a standard logic function whose precondition the \
                 logic lane cannot state"
        ))),
        _ => None,
    }
}

/// Whether a call spelled `name` may denote a standard logic function whose
/// precondition the walk cannot state.
fn std_precondition_unstated(name: &str) -> bool {
    let tail = call_spelling(name);
    STD_UNSTATED_PRECONDITIONS.contains(&tail)
        || (tail == "new"
            && strip_turbofish(name)
                .rsplit_once("::")
                .is_some_and(|(qualifier, _)| {
                    qualifier_owners(qualifier)
                        .iter()
                        .any(|owner| STD_NEW_WITH_PRECONDITION.contains(owner))
                }))
}

/// Whether a call spelled `name` may denote a standard logic function with a
/// precondition, at any arity: `std_logic_precondition` answers for the
/// arguments of one call.
fn std_names_a_precondition(name: &str) -> bool {
    matches!(call_spelling(name), "unwrap_logic" | "unreachable") || std_precondition_unstated(name)
}

/// The `requires` a caller owes: the clauses written in `#[requires]`
/// (`LogicFnDef::written_requires`), which is what Creusot's vcgen owes at a
/// call. The clauses the driver appends after them guard the definition: type
/// facts every well-typed argument satisfies, and an opaque definition's
/// `false` guard (`append_opaque_guard_if_needed`), which owed would refute
/// every call to an opaque function. A definition that recorded no written
/// clauses owes all of them but a trailing opaque guard.
pub(super) fn owed_requires(logic_fn: &LogicFnDef) -> &[PureExpr] {
    if let Some(written) = logic_fn.written_requires() {
        return written;
    }
    let requires = logic_fn.requires();
    match requires.split_last() {
        Some((PureExpr::Bool(false), rest)) if logic_fn.is_opaque() => rest,
        _ => requires,
    }
}

/// The premises of a logic function's own body goals: every `requires`
/// clause but an opaque function's `false` guard, which as a premise of the
/// function's OWN goal would discharge anything. The guard is the first literal
/// `false` after the written clauses (the type facts appended with it never
/// are one), or the last clause when no written clauses were recorded. The type
/// facts hold of every argument the function can be called with and stay.
pub(super) fn own_premises(logic_fn: &LogicFnDef) -> Vec<PureExpr> {
    let requires = logic_fn.requires();
    let is_guard = |clause: &PureExpr| matches!(clause, PureExpr::Bool(false));
    let guard_at = if logic_fn.is_opaque() {
        match logic_fn.written_requires() {
            Some(written) => requires[written.len()..]
                .iter()
                .position(is_guard)
                .map(|offset| written.len() + offset),
            None => requires
                .len()
                .checked_sub(1)
                .filter(|&last| is_guard(&requires[last])),
        }
    } else {
        None
    };
    requires
        .iter()
        .enumerate()
        .filter(|&(at, _)| Some(at) != guard_at)
        .map(|(_, clause)| clause.clone())
        .collect()
}

/// The goal `body` owes for the preconditions of the calls in it, with every
/// definition in `logic_fns` a candidate callee, every function in
/// `program_fns` a callee no logic body may call, and `resolution` what rustc
/// resolved the body's calls to. `int_params` are the caller's parameters
/// known to be integers (`integer_hypothesis`).
pub(super) fn callee_precondition_goal(
    body: &PureExpr,
    logic_fns: &[LogicFnDef],
    program_fns: Option<&ProgramFnsWithRequires>,
    resolution: CallResolution<'_>,
    int_params: &HashSet<String>,
) -> CalleePreconditionGoal {
    let typed = match resolution {
        CallResolution::Typed(callees) => Some(callees),
        CallResolution::Misread(why) => return CalleePreconditionGoal::Refused(why.to_string()),
        CallResolution::Untyped { written_call } => {
            if let Some(why) =
                first_call(body).or_else(|| written_call.map(|name| format!("a call `{name}`")))
            {
                return CalleePreconditionGoal::Refused(format!(
                    "{why} in a body with no type-checked form, so what it denotes is unknown"
                ));
            }
            None
        }
        #[cfg(test)]
        CallResolution::Spelling => None,
    };
    let walk = Walk {
        contracted: logic_fns
            .iter()
            .filter(|def| !owed_requires(def).is_empty())
            .collect(),
        all: logic_fns,
        program_fns,
        typed,
    };
    if let Some(typed) = typed {
        if let Some(why) = &typed.refused {
            return CalleePreconditionGoal::Refused(why.clone());
        }
        if let Err(why) = walk.every_owing_call_is_parsed(body) {
            return CalleePreconditionGoal::Refused(why);
        }
    }
    if !walk.owes_anything(body) {
        return CalleePreconditionGoal::None;
    }
    match walk.goal_of(body, 0, int_params) {
        Ok(Some(goal)) => CalleePreconditionGoal::Goal(goal),
        Ok(None) => CalleePreconditionGoal::Refused(
            "a call to a contracted logic function the body walk could not place".to_string(),
        ),
        Err(reason) => CalleePreconditionGoal::Refused(reason),
    }
}

/// The caller's parameters whose declared sort is an integer.
pub(super) fn integer_params(logic_fn: &LogicFnDef) -> HashSet<String> {
    logic_fn
        .params()
        .iter()
        .zip(logic_fn.param_sorts())
        .filter(|(_, sort)| sort.as_ref().is_some_and(is_integer_sort))
        .map(|(param, _)| param.clone())
        .collect()
}

/// Whether `expr` is certainly an integer where it stands: a literal, a
/// parameter in `int_params` no binder hides, or `+`, `-`, `*` or negation of
/// such. Anything else is not known to be one.
fn is_integer_term(expr: &PureExpr, int_params: &HashSet<String>) -> bool {
    match expr {
        PureExpr::Int(_) => true,
        PureExpr::Var(name, None) => int_params.contains(name),
        PureExpr::Var(_, Some(sort)) => is_integer_sort(sort),
        PureExpr::BinOp(left, BinOp::Add | BinOp::Sub | BinOp::Mul, right) => {
            is_integer_term(left, int_params) && is_integer_term(right, int_params)
        }
        PureExpr::UnOp(UnOp::Neg, inner) => is_integer_term(inner, int_params),
        _ => false,
    }
}

/// What `cond` holding (`holds`) or failing says, restated over the integers
/// where the restatement is one a proof certificate can check: a disequality
/// `a != b` of integers is `a <= b - 1 || a >= b + 1`. Over the rationals a
/// certificate replays in, `n >= 0 && n != 0` does not give `n >= 1`, so a
/// callee precondition such as `n - 1 >= 0` in the `else` arm of `n == 0`,
/// which ay proves, was refused as uncertified
/// (logic_fn_recursive_disequality_branch_control.rs). The restatement is an
/// equivalence ONLY over the integers, which is why both operands must be
/// certainly integer (`is_integer_term`): over the reals it would be a
/// stronger hypothesis than the branch gives.
fn integer_hypothesis(
    cond: &PureExpr,
    holds: bool,
    int_params: &HashSet<String>,
) -> Option<PureExpr> {
    let (left, right, differ) = match cond {
        PureExpr::BinOp(left, BinOp::Eq, right) => (left, right, !holds),
        PureExpr::BinOp(left, BinOp::Ne, right) => (left, right, holds),
        PureExpr::UnOp(UnOp::Not, inner) => return integer_hypothesis(inner, !holds, int_params),
        _ => return None,
    };
    if !differ || !is_integer_term(left, int_params) || !is_integer_term(right, int_params) {
        return None;
    }
    let offset = |delta: i64| match right.as_ref() {
        PureExpr::Int(value) => value.checked_add(delta).map(PureExpr::Int),
        _ => Some(PureExpr::BinOp(
            right.clone(),
            if delta < 0 { BinOp::Sub } else { BinOp::Add },
            Arc::new(PureExpr::Int(delta.abs())),
        )),
    };
    Some(PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            left.clone(),
            BinOp::Le,
            Arc::new(offset(-1)?),
        )),
        BinOp::Or,
        Arc::new(PureExpr::BinOp(
            left.clone(),
            BinOp::Ge,
            Arc::new(offset(1)?),
        )),
    ))
}

/// `goal` where `cond` is known to hold (`holds`) or fail, with the integer
/// restatement of that knowledge as an explicit premise when there is one.
fn under_integer_hypothesis(
    cond: &PureExpr,
    holds: bool,
    goal: PureExpr,
    int_params: &HashSet<String>,
) -> PureExpr {
    match integer_hypothesis(cond, holds, int_params) {
        Some(hypothesis) => implies(hypothesis, goal),
        None => goal,
    }
}

/// `int_params` with the names a binder introduces removed: inside it they
/// denote the binder, not the parameter.
fn hiding<'n>(
    int_params: &HashSet<String>,
    names: impl IntoIterator<Item = &'n str>,
) -> HashSet<String> {
    let mut visible = int_params.clone();
    for name in names {
        visible.remove(name);
    }
    visible
}

/// `name` without a trailing turbofish: `f::<T>` is `f`.
fn strip_turbofish(name: &str) -> &str {
    match name.rfind("::<") {
        Some(turbofish) if name.ends_with('>') => &name[..turbofish],
        _ => name,
    }
}

/// Whether a call spelled `call_name` may denote `def`. Deliberately loose:
/// the exact symbol, the crate-qualified path and the short name all count,
/// so a collision family's every member is a candidate of its short name.
fn may_denote(call_name: &str, def: &LogicFnDef) -> bool {
    let tail = call_spelling(call_name);
    call_name == def.name()
        || call_name == def.full_path()
        || tail == def.name()
        || tail == def.short_name()
}

/// Whether `def` takes a `&mut` parameter or its owed precondition reads a
/// final value (`^x`). The contract parser keeps a borrow as its operand, so
/// `f(&mut (*x)[2].0)` reaches the walk as `f((*x)[2].0)`, and the
/// precondition's `^x` would be read of a place, not of the borrow the call
/// makes (lang/logic_vcgen.rs).
fn reads_a_final_value(def: &LogicFnDef) -> bool {
    def.param_sorts()
        .iter()
        .any(|sort| matches!(sort, Some(ExprSort::MutRef(_))))
        || owed_requires(def).iter().any(|clause| {
            clause.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
                matches!(node, PureExpr::Final(_))
            })
        })
}

/// A method call's arguments as its callee's parameters read them: the
/// receiver first.
fn method_args(receiver: &PureExpr, args: &[PureExpr]) -> Vec<PureExpr> {
    let mut full = Vec::with_capacity(args.len() + 1);
    full.push(receiver.clone());
    full.extend(args.iter().cloned());
    full
}

/// The first call of `body` trust-wp did not synthesise, described; past the
/// depth budget, the budget.
fn first_call(body: &PureExpr) -> Option<String> {
    let mut found = None;
    let beyond_reach = body.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
        let name = match node {
            PureExpr::LogicFnCall { name, .. } => name,
            PureExpr::MethodCall { method, .. } => method,
            _ => return false,
        };
        if is_reserved_call_name(name) {
            return false;
        }
        found = Some(format!("a call `{name}`"));
        true
    });
    found.or_else(|| beyond_reach.then(|| "a call nested deeper than the walk reaches".to_string()))
}

/// The name of every call node: a path call's name, a method call's method.
fn call_name(node: &PureExpr) -> Option<&str> {
    match node {
        PureExpr::LogicFnCall { name, .. } => Some(name),
        PureExpr::MethodCall { method, .. } => Some(method),
        _ => None,
    }
}

/// The callees of an operator, for a refusal: the owing ones.
fn describe_callees(callees: &[ResolvedCallee]) -> String {
    let named: Vec<&str> = callees
        .iter()
        .filter_map(|callee| match callee {
            ResolvedCallee::Logic(path) | ResolvedCallee::Std(path) => Some(path.as_str()),
            ResolvedCallee::Refused(why) => Some(why.as_str()),
            ResolvedCallee::Free => None,
        })
        .collect();
    format!("`{}`", named.join("`, `"))
}

fn and(left: PureExpr, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), BinOp::And, Arc::new(right))
}

fn implies(premise: PureExpr, goal: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(premise), BinOp::Implies, Arc::new(goal))
}

fn conj(left: Option<PureExpr>, right: Option<PureExpr>) -> Option<PureExpr> {
    match (left, right) {
        (Some(l), Some(r)) => Some(and(l, r)),
        (l, r) => l.or(r),
    }
}

/// Whether any node of `expr` is a `proof_assert!`, whose term the goal must
/// never carry for the encoder to guess at. Past the depth budget the answer
/// is yes.
fn contains_proof_assert(expr: &PureExpr) -> bool {
    expr.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
        matches!(node, PureExpr::LogicFnCall { name, .. }
            if name == "proof_assert" || name.ends_with("::proof_assert"))
    })
}

struct Walk<'a> {
    /// Every definition whose `requires` a caller owes.
    contracted: Vec<&'a LogicFnDef>,
    /// Every definition of the lane: an identity-pass id names one of them.
    all: &'a [LogicFnDef],
    program_fns: Option<&'a ProgramFnsWithRequires>,
    /// What rustc resolved the body's calls to.
    typed: Option<&'a BodyCallees>,
}

impl<'a> Walk<'a> {
    /// The contracted definitions a call spelled `name` may denote: those
    /// the spelling names, and those rustc resolves a call of that spelling
    /// to.
    fn candidates(&self, name: &str) -> Vec<&'a LogicFnDef> {
        let resolved: HashSet<&str> = self
            .resolved_callees(name)
            .into_iter()
            .filter_map(|callee| match callee {
                ResolvedCallee::Logic(path) => Some(path.as_str()),
                _ => None,
            })
            .collect();
        self.contracted
            .iter()
            .copied()
            .filter(|def| may_denote(name, def) || resolved.contains(def.full_path()))
            .collect()
    }

    /// The path of the definition an identity-pass id names.
    fn id_path(&self, name: &str) -> Option<&'a str> {
        if !name.starts_with(LOGIC_FN_ID_PREFIX) {
            return None;
        }
        self.all
            .iter()
            .find(|def| def.name() == name)
            .map(LogicFnDef::full_path)
    }

    /// Every definition rustc resolves a call spelled like `name` to. A call
    /// the identity pass named by a definition's id is spelled every way
    /// rustc resolves a call to that definition.
    fn resolved_callees(&self, name: &str) -> Vec<&'a ResolvedCallee> {
        let Some(typed) = self.typed else {
            return Vec::new();
        };
        let spellings: HashSet<&str> = match self.id_path(name) {
            Some(path) => typed
                .calls
                .iter()
                .filter(|call| {
                    call.callees
                        .iter()
                        .any(|callee| matches!(callee, ResolvedCallee::Logic(p) if p == path))
                })
                .filter_map(|call| call.spelling.as_deref())
                .collect(),
            None => std::iter::once(call_spelling(name)).collect(),
        };
        let mut callees: Vec<&'a ResolvedCallee> = Vec::new();
        for call in &typed.calls {
            if call
                .spelling
                .as_deref()
                .is_some_and(|spelling| spellings.contains(spelling))
            {
                for callee in &call.callees {
                    if !callees.contains(&callee) {
                        callees.push(callee);
                    }
                }
            }
        }
        callees
    }

    /// Whether a call of `callee` owes something or is refused.
    fn callee_owes(&self, callee: &ResolvedCallee) -> bool {
        match callee {
            ResolvedCallee::Logic(path) => {
                self.contracted.iter().any(|def| def.full_path() == path)
            }
            ResolvedCallee::Std(path) => std_names_a_precondition(path),
            ResolvedCallee::Refused(_) => true,
            ResolvedCallee::Free => false,
        }
    }

    /// Every call of the type-checked body that owes something has a
    /// counterpart in `body` and among the calls of the body as written that
    /// `body` still holds as themselves: at least as many calls spelled as it
    /// is, or named by the identity-pass id of a definition a call so spelled
    /// resolves to. A call the parsed body lost, or keeps as an operator,
    /// would otherwise owe nothing, and so would one an inlined callee's
    /// same-spelled call stood in for
    /// (logic_fn_callee_precondition_view_beside_inlined_view.rs).
    fn every_owing_call_is_parsed(&self, body: &PureExpr) -> Result<(), String> {
        let Some(typed) = self.typed else {
            return Ok(());
        };
        let mut owing: HashMap<&str, usize> = HashMap::new();
        for call in &typed.calls {
            if !call.callees.iter().any(|callee| self.callee_owes(callee)) {
                continue;
            }
            let Some(spelling) = call.spelling.as_deref() else {
                return Err(format!(
                    "an operator that calls {}, which the parsed body keeps as no call",
                    describe_callees(&call.callees)
                ));
            };
            *owing.entry(spelling).or_default() += 1;
        }
        // A trigger is never evaluated, so a call in one stands for none.
        let body = without_triggers(body);
        for (spelling, owed) in owing {
            let paths: HashSet<&str> = typed
                .calls
                .iter()
                .filter(|call| call.spelling.as_deref() == Some(spelling))
                .flat_map(|call| &call.callees)
                .filter_map(|callee| match callee {
                    ResolvedCallee::Logic(path) => Some(path.as_str()),
                    _ => None,
                })
                .collect();
            let answers = |name: &str| {
                call_spelling(name) == spelling
                    || self.id_path(name).is_some_and(|path| paths.contains(path))
            };
            let mut walked = 0;
            let beyond_reach = body.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
                if call_name(node).is_some_and(answers) {
                    walked += 1;
                }
                false
            });
            if beyond_reach {
                return Err("a logic call nested deeper than the body walk reaches".to_string());
            }
            let written = typed.written.iter().filter(|name| answers(name)).count();
            let parsed = walked.min(written);
            if parsed < owed {
                return Err(format!(
                    "{owed} call(s) spelled `{spelling}` that owe a precondition in the body's \
                     type-checked form and {parsed} in the parsed body: a call the parsed body \
                     does not hold would owe nothing"
                ));
            }
        }
        Ok(())
    }

    fn denotes_program_fn(&self, name: &str) -> bool {
        self.program_fns.is_some_and(|fns| fns.may_denote(name))
    }

    /// Whether `node` is a call that owes something or is refused.
    fn is_owing_call(&self, node: &PureExpr) -> bool {
        match node {
            PureExpr::LogicFnCall { name, args } => {
                !self.candidates(name).is_empty()
                    || self.denotes_program_fn(name)
                    || std_logic_precondition(name, args).is_some()
                    || self
                        .resolved_callees(name)
                        .into_iter()
                        .any(|callee| self.callee_owes(callee))
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                !self.candidates(method).is_empty()
                    || std_logic_precondition(method, &method_args(receiver, args)).is_some()
                    || self
                        .resolved_callees(method)
                        .into_iter()
                        .any(|callee| self.callee_owes(callee))
            }
            _ => false,
        }
    }

    /// Whether `expr` holds a call this walk owes a precondition for. Past the
    /// depth budget the answer is yes: a call the walk cannot see is one it
    /// cannot place.
    fn owes_anything(&self, expr: &PureExpr) -> bool {
        expr.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| self.is_owing_call(node))
    }

    /// A body expression copied into the goal (an argument, a condition, a
    /// scrutinee, a bound value).
    fn embed(expr: &PureExpr) -> Result<PureExpr, String> {
        if contains_proof_assert(expr) {
            return Err(
                "a proof_assert! inside an expression a callee precondition depends on".to_string(),
            );
        }
        Ok(expr.clone())
    }

    /// `requires_def[params := args]` for every candidate `def` of the call,
    /// and the standard-library precondition its spelling, or a function of
    /// another crate rustc resolves it to, names.
    fn preconditions_at(&self, name: &str, args: &[PureExpr]) -> Result<Option<PureExpr>, String> {
        let mut std_paths = vec![name];
        for callee in self.resolved_callees(name) {
            match callee {
                ResolvedCallee::Refused(why) => return Err(format!("a call `{name}` that {why}")),
                ResolvedCallee::Std(path) => std_paths.push(path),
                ResolvedCallee::Logic(_) | ResolvedCallee::Free => {}
            }
        }
        let mut goal = None;
        let mut stated = Vec::new();
        for path in std_paths {
            match std_logic_precondition(path, args) {
                Some(Ok(precondition)) => {
                    for arg in args {
                        Self::embed(arg)?;
                    }
                    if !stated.contains(&precondition) {
                        stated.push(precondition.clone());
                        goal = conj(goal, Some(precondition));
                    }
                }
                Some(Err(why)) => return Err(why),
                None => {}
            }
        }
        for def in self.candidates(name) {
            if reads_a_final_value(def) {
                return Err(format!(
                    "a call `{name}` that may denote `{}`, whose precondition reads a final \
                     value or takes a `&mut` parameter: a call's argument keeps no reference \
                     level, so the walk would read the borrowed place's final value as its \
                     current one",
                    def.full_path()
                ));
            }
            if def.params().len() != args.len() {
                return Err(format!(
                    "a call `{name}` with {} argument(s) that may denote `{}`, which takes {} \
                     and has a precondition",
                    args.len(),
                    def.full_path(),
                    def.params().len()
                ));
            }
            let substitution = def
                .params()
                .iter()
                .cloned()
                .zip(
                    args.iter()
                        .map(Self::embed)
                        .collect::<Result<Vec<_>, _>>()?,
                )
                .collect();
            for clause in owed_requires(def) {
                let at_call = clause.substitute_capture_avoiding(
                    &substitution,
                    &CaptureAvoidingSubstOptions::default(),
                );
                goal = conj(goal, Some(at_call));
            }
        }
        Ok(goal)
    }

    fn all_of(
        &self,
        exprs: &[PureExpr],
        depth: usize,
        ints: &HashSet<String>,
    ) -> Result<Option<PureExpr>, String> {
        let mut goal = None;
        for expr in exprs {
            goal = conj(goal, self.goal_of(expr, depth, ints)?);
        }
        Ok(goal)
    }

    /// The goal of the calls in `expr`, `None` when it owes nothing. `ints`
    /// are the integer parameters visible at `expr`.
    #[allow(clippy::too_many_lines)] // one arm per node kind, each a vcgen rule
    fn goal_of(
        &self,
        expr: &PureExpr,
        depth: usize,
        ints: &HashSet<String>,
    ) -> Result<Option<PureExpr>, String> {
        if depth > DEPTH_LIMIT {
            return Err("a logic call nested deeper than the body walk reaches".to_string());
        }
        if !self.owes_anything(expr) {
            return Ok(None);
        }
        let next = depth + 1;
        match expr {
            PureExpr::LogicFnCall { name, args } => {
                if self.denotes_program_fn(name) {
                    return Err(format!(
                        "a call `{name}` that may denote a program function with a \
                         precondition, which a logic body cannot call"
                    ));
                }
                let in_args = self.all_of(args, next, ints)?;
                Ok(conj(in_args, self.preconditions_at(name, args)?))
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let in_receiver = self.goal_of(receiver, next, ints)?;
                let in_args = self.all_of(args, next, ints)?;
                Ok(conj(
                    conj(in_receiver, in_args),
                    self.preconditions_at(method, &method_args(receiver, args))?,
                ))
            }
            // `a && b` evaluates `b` only where `a` holds, `a || b` only where
            // it fails, and `a ==> b` only where it holds.
            PureExpr::BinOp(left, op @ (BinOp::And | BinOp::Or | BinOp::Implies), right) => {
                let in_left = self.goal_of(left, next, ints)?;
                let in_right = match self.goal_of(right, next, ints)? {
                    Some(goal) => {
                        let reached_where_left_holds = *op != BinOp::Or;
                        let goal =
                            under_integer_hypothesis(left, reached_where_left_holds, goal, ints);
                        let left = Self::embed(left)?;
                        let reached = if reached_where_left_holds {
                            left
                        } else {
                            PureExpr::UnOp(UnOp::Not, Arc::new(left))
                        };
                        Some(implies(reached, goal))
                    }
                    None => None,
                };
                Ok(conj(in_left, in_right))
            }
            PureExpr::BinOp(left, _, right) => Ok(conj(
                self.goal_of(left, next, ints)?,
                self.goal_of(right, next, ints)?,
            )),
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => self.goal_of(inner, next, ints),
            PureExpr::Ite(cond, then_branch, else_branch) => {
                let in_cond = self.goal_of(cond, next, ints)?;
                let in_then = self.goal_of(then_branch, next, ints)?;
                let in_else = self.goal_of(else_branch, next, ints)?;
                if in_then.is_none() && in_else.is_none() {
                    return Ok(in_cond);
                }
                let branch = |goal: Option<PureExpr>, holds: bool| match goal {
                    Some(goal) => under_integer_hypothesis(cond, holds, goal, ints),
                    None => PureExpr::Bool(true),
                };
                Ok(conj(
                    in_cond,
                    Some(PureExpr::Ite(
                        Arc::new(Self::embed(cond)?),
                        Arc::new(branch(in_then, true)),
                        Arc::new(branch(in_else, false)),
                    )),
                ))
            }
            PureExpr::Match { scrutinee, arms } => {
                let in_scrutinee = self.goal_of(scrutinee, next, ints)?;
                let mut any = false;
                let mut goal_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    let bound = arm.pattern.bound_names();
                    let arm_ints = hiding(ints, bound.iter().copied());
                    let arm_goal = self.goal_of(&arm.body, next, &arm_ints)?;
                    any |= arm_goal.is_some();
                    goal_arms.push(MatchArm {
                        pattern: arm.pattern.clone(),
                        body: arm_goal.unwrap_or(PureExpr::Bool(true)),
                    });
                }
                if !any {
                    return Ok(in_scrutinee);
                }
                Ok(conj(
                    in_scrutinee,
                    Some(PureExpr::Match {
                        scrutinee: Arc::new(Self::embed(scrutinee)?),
                        arms: goal_arms,
                    }),
                ))
            }
            PureExpr::Let { var, value, body } => {
                let in_value = self.goal_of(value, next, ints)?;
                let body_ints = hiding(ints, [var.as_str()]);
                let in_body = match self.goal_of(body, next, &body_ints)? {
                    // A statement's unit binding (`proof_assert!(c); rest`) is
                    // read by nothing, so it is not carried into the goal.
                    Some(goal) if goal.free_vars().contains(var) => Some(PureExpr::Let {
                        var: var.clone(),
                        value: Arc::new(Self::embed(value)?),
                        body: Arc::new(goal),
                    }),
                    other => other,
                };
                Ok(conj(in_value, in_body))
            }
            // A binder's body is owed for every value of the binder, whatever
            // the quantifier or the closure's use.
            PureExpr::Forall {
                var,
                var_sort,
                body,
                ..
            }
            | PureExpr::Exists {
                var,
                var_sort,
                body,
                ..
            } => Ok(self
                .goal_of(body, next, &hiding(ints, [var.as_str()]))?
                .map(|goal| PureExpr::Forall {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: Arc::new(goal),
                    triggers: Vec::new(),
                })),
            PureExpr::Closure { params, body } => {
                let body_ints = hiding(ints, params.iter().map(|(param, _)| param.as_str()));
                Ok(self.goal_of(body, next, &body_ints)?.map(|goal| {
                    params
                        .iter()
                        .rev()
                        .fold(goal, |inner, (param, sort)| PureExpr::Forall {
                            var: param.clone(),
                            var_sort: sort.clone(),
                            body: Arc::new(inner),
                            triggers: Vec::new(),
                        })
                }))
            }
            _ => Err(
                "a call to a contracted logic function inside an expression the body walk \
                 does not place"
                    .to_string(),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn call(name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args,
        }
    }

    fn gt(left: PureExpr, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), BinOp::Gt, Arc::new(right))
    }

    /// `needs_pos(x)` requires `x > 0`.
    fn needs_pos() -> LogicFnDef {
        LogicFnDef::new_with_requires(
            "needs_pos".to_string(),
            "creusot_test::needs_pos".to_string(),
            vec!["x".to_string()],
            vec![gt(var("x"), PureExpr::Int(0))],
            var("x"),
        )
    }

    fn goal(body: &PureExpr) -> CalleePreconditionGoal {
        callee_precondition_goal(
            body,
            &[needs_pos()],
            None,
            CallResolution::Spelling,
            &HashSet::new(),
        )
    }

    #[test]
    fn a_call_owes_the_callee_precondition_at_its_arguments() {
        let body = call("needs_pos", vec![var("y")]);
        assert_eq!(
            goal(&body),
            CalleePreconditionGoal::Goal(gt(var("y"), PureExpr::Int(0)))
        );
    }

    #[test]
    fn a_call_to_a_callee_without_requires_owes_nothing() {
        let free = LogicFnDef::new(
            "free".to_string(),
            "creusot_test::free".to_string(),
            vec!["x".to_string()],
            var("x"),
        );
        let body = call("free", vec![var("y")]);
        assert_eq!(
            callee_precondition_goal(
                &body,
                &[free, needs_pos()],
                None,
                CallResolution::Spelling,
                &HashSet::new()
            ),
            CalleePreconditionGoal::None
        );
    }

    #[test]
    fn a_qualified_or_self_spelling_still_names_the_callee() {
        for name in [
            "creusot_test::needs_pos",
            "Self::needs_pos",
            "m::needs_pos::<T>",
        ] {
            let body = call(name, vec![var("y")]);
            assert_eq!(
                goal(&body),
                CalleePreconditionGoal::Goal(gt(var("y"), PureExpr::Int(0))),
                "{name}"
            );
        }
    }

    #[test]
    fn a_call_in_one_branch_is_owed_under_that_branch_only() {
        let body = PureExpr::Ite(
            Arc::new(var("c")),
            Arc::new(call("needs_pos", vec![var("y")])),
            Arc::new(PureExpr::Int(0)),
        );
        assert_eq!(
            goal(&body),
            CalleePreconditionGoal::Goal(PureExpr::Ite(
                Arc::new(var("c")),
                Arc::new(gt(var("y"), PureExpr::Int(0))),
                Arc::new(PureExpr::Bool(true)),
            ))
        );
    }

    #[test]
    fn a_short_circuit_operand_is_owed_only_where_it_is_evaluated() {
        let pos = |e| gt(call("needs_pos", vec![e]), PureExpr::Int(0));
        let body = PureExpr::BinOp(Arc::new(var("c")), BinOp::Or, Arc::new(pos(var("y"))));
        assert_eq!(
            goal(&body),
            CalleePreconditionGoal::Goal(implies(
                PureExpr::UnOp(UnOp::Not, Arc::new(var("c"))),
                gt(var("y"), PureExpr::Int(0)),
            ))
        );
    }

    #[test]
    fn a_quantified_call_is_owed_for_every_value_of_the_binder() {
        let body = PureExpr::Exists {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(gt(call("needs_pos", vec![var("i")]), PureExpr::Int(0))),
            triggers: Vec::new(),
        };
        assert_eq!(
            goal(&body),
            CalleePreconditionGoal::Goal(PureExpr::Forall {
                var: "i".to_string(),
                var_sort: None,
                body: Arc::new(gt(var("i"), PureExpr::Int(0))),
                triggers: Vec::new(),
            })
        );
    }

    #[test]
    fn a_let_bound_argument_keeps_its_binding() {
        let body = PureExpr::Let {
            var: "z".to_string(),
            value: Arc::new(var("y")),
            body: Arc::new(call("needs_pos", vec![var("z")])),
        };
        assert_eq!(
            goal(&body),
            CalleePreconditionGoal::Goal(PureExpr::Let {
                var: "z".to_string(),
                value: Arc::new(var("y")),
                body: Arc::new(gt(var("z"), PureExpr::Int(0))),
            })
        );
    }

    #[test]
    fn a_statement_binding_is_not_carried_into_the_goal() {
        let body = PureExpr::Let {
            var: "$stmt0".to_string(),
            value: Arc::new(call("proof_assert", vec![PureExpr::Bool(true)])),
            body: Arc::new(call("needs_pos", vec![var("y")])),
        };
        assert_eq!(
            goal(&body),
            CalleePreconditionGoal::Goal(gt(var("y"), PureExpr::Int(0)))
        );
    }

    #[test]
    fn a_nested_call_owes_both_preconditions() {
        let body = call("needs_pos", vec![call("needs_pos", vec![var("y")])]);
        assert_eq!(
            goal(&body),
            CalleePreconditionGoal::Goal(and(
                gt(var("y"), PureExpr::Int(0)),
                gt(call("needs_pos", vec![var("y")]), PureExpr::Int(0)),
            ))
        );
    }

    #[test]
    fn a_method_call_binds_its_receiver_to_the_first_parameter() {
        let body = PureExpr::MethodCall {
            receiver: Arc::new(var("y")),
            method: "needs_pos".to_string(),
            args: Vec::new(),
        };
        assert_eq!(
            goal(&body),
            CalleePreconditionGoal::Goal(gt(var("y"), PureExpr::Int(0)))
        );
    }

    #[test]
    fn every_candidate_of_a_colliding_short_name_is_owed() {
        let mut other = LogicFnDef::new_with_requires(
            "needs_pos".to_string(),
            "creusot_test::m::needs_pos".to_string(),
            vec!["x".to_string()],
            vec![gt(PureExpr::Int(9), var("x"))],
            var("x"),
        );
        other.assign_unique_id("__lfid__other".to_string());
        let body = call("needs_pos", vec![var("y")]);
        let CalleePreconditionGoal::Goal(goal) = callee_precondition_goal(
            &body,
            &[needs_pos(), other],
            None,
            CallResolution::Spelling,
            &HashSet::new(),
        ) else {
            panic!("a call owes its preconditions");
        };
        assert_eq!(
            goal,
            and(
                gt(var("y"), PureExpr::Int(0)),
                gt(PureExpr::Int(9), var("y"))
            )
        );
    }

    #[test]
    fn an_opaque_callee_owes_its_clauses_not_its_guard() {
        let mut opaque = needs_pos().with_opaque(true);
        opaque.extend_requires([PureExpr::Bool(false)]);
        let body = call("needs_pos", vec![var("y")]);
        assert_eq!(
            callee_precondition_goal(
                &body,
                &[opaque],
                None,
                CallResolution::Spelling,
                &HashSet::new()
            ),
            CalleePreconditionGoal::Goal(gt(var("y"), PureExpr::Int(0)))
        );
    }

    fn ge(left: PureExpr, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), BinOp::Ge, Arc::new(right))
    }

    /// `f(x, k)` wrote `x > 0`; `rest` is what the driver appended after it.
    fn written_one(rest: Vec<PureExpr>) -> LogicFnDef {
        let mut requires = vec![gt(var("x"), PureExpr::Int(0))];
        requires.extend(rest);
        LogicFnDef::new_with_requires(
            "f".to_string(),
            "creusot_test::f".to_string(),
            vec!["x".to_string(), "k".to_string()],
            requires,
            var("x"),
        )
        .with_written_requires(1)
    }

    #[test]
    fn a_caller_owes_the_written_requires_not_the_appended_type_facts() {
        let def = written_one(vec![ge(var("k"), PureExpr::Int(0))]);
        let body = call("f", vec![var("y"), var("j")]);
        assert_eq!(
            callee_precondition_goal(
                &body,
                &[def],
                None,
                CallResolution::Spelling,
                &HashSet::new()
            ),
            CalleePreconditionGoal::Goal(gt(var("y"), PureExpr::Int(0)))
        );
    }

    #[test]
    fn an_opaque_guard_before_appended_facts_is_neither_owed_nor_a_premise() {
        let range = ge(var("k"), PureExpr::Int(0));
        let def = written_one(vec![PureExpr::Bool(false), range.clone()]).with_opaque(true);
        assert_eq!(owed_requires(&def), &[gt(var("x"), PureExpr::Int(0))]);
        assert_eq!(
            own_premises(&def),
            vec![gt(var("x"), PureExpr::Int(0)), range]
        );
    }

    #[test]
    fn a_written_false_is_owed_and_only_the_guard_leaves_the_premises() {
        let def = LogicFnDef::new_with_requires(
            "f".to_string(),
            "creusot_test::f".to_string(),
            vec!["x".to_string()],
            vec![PureExpr::Bool(false), PureExpr::Bool(false)],
            var("x"),
        )
        .with_written_requires(1)
        .with_opaque(true);
        assert_eq!(owed_requires(&def), &[PureExpr::Bool(false)]);
        assert_eq!(own_premises(&def), vec![PureExpr::Bool(false)]);
    }

    /// p_unwrap_logic: Creusot's `unwrap_logic` requires `self != None`,
    /// which the encoder's payload selector never asks.
    #[test]
    fn unwrap_logic_owes_its_receiver_is_not_none() {
        let body = PureExpr::MethodCall {
            receiver: Arc::new(var("o")),
            method: "unwrap_logic".to_string(),
            args: Vec::new(),
        };
        assert_eq!(
            callee_precondition_goal(&body, &[], None, CallResolution::Spelling, &HashSet::new()),
            CalleePreconditionGoal::Goal(PureExpr::BinOp(
                Arc::new(var("o")),
                BinOp::Ne,
                Arc::new(var("None")),
            ))
        );
    }

    #[test]
    fn unreachable_owes_false_where_it_is_reached() {
        let body = PureExpr::Ite(
            Arc::new(var("c")),
            Arc::new(PureExpr::Int(0)),
            Arc::new(call("creusot_std::logic::unreachable", Vec::new())),
        );
        assert_eq!(
            callee_precondition_goal(&body, &[], None, CallResolution::Spelling, &HashSet::new()),
            CalleePreconditionGoal::Goal(PureExpr::Ite(
                Arc::new(var("c")),
                Arc::new(PureExpr::Bool(true)),
                Arc::new(PureExpr::Bool(false)),
            ))
        );
    }

    #[test]
    fn a_std_precondition_the_walk_cannot_state_is_refused() {
        for body in [
            call("creusot_std::logic::such_that", vec![var("p")]),
            PureExpr::MethodCall {
                receiver: Arc::new(var("a")),
                method: "union".to_string(),
                args: vec![var("b")],
            },
            call("PositiveReal::new", vec![var("r")]),
            call("View::new", vec![var("a"), var("f")]),
            call("View::<R>::new", vec![var("a"), var("f")]),
            call("R::rel_mono", vec![var("a"), var("f1"), var("f2")]),
            call("Self::rel_none", vec![var("a"), var("f")]),
            PureExpr::MethodCall {
                receiver: Arc::new(var("t")),
                method: "get_timestamp_monotonic".to_string(),
                args: vec![var("x"), var("y")],
            },
        ] {
            assert!(
                matches!(
                    callee_precondition_goal(
                        &body,
                        &[],
                        None,
                        CallResolution::Spelling,
                        &HashSet::new()
                    ),
                    CalleePreconditionGoal::Refused(_)
                ),
                "{body:?}"
            );
        }
        // Another owner's `new` is no standard function with a precondition.
        assert_eq!(
            callee_precondition_goal(
                &call("Test::new", vec![]),
                &[],
                None,
                CallResolution::Spelling,
                &HashSet::new()
            ),
            CalleePreconditionGoal::None
        );
    }

    /// p_program_callee: a program function is no logic callee in Creusot,
    /// and the encoder reads a call to it as a placeholder.
    #[test]
    fn a_call_that_may_denote_a_program_function_is_refused() {
        let mut program = ProgramFnsWithRequires::default();
        program.insert_free("prog".to_string());
        program.insert_path("creusot_test::prog".to_string());
        program.insert_associated("S", "m");
        program.insert_associated("Tr", "m");
        for name in [
            "prog",
            "creusot_test::prog",
            "S::m",
            "m::S::<T>::m",
            "<S as Tr>::m",
            "<X as Tr>::m",
        ] {
            assert!(
                matches!(
                    callee_precondition_goal(
                        &call(name, vec![var("y")]),
                        &[],
                        Some(&program),
                        CallResolution::Spelling,
                        &HashSet::new()
                    ),
                    CalleePreconditionGoal::Refused(_)
                ),
                "{name}"
            );
        }
        // A call resolved to a logic function's id, or to another owner's
        // method, denotes no program function.
        for name in ["__lfid__creusot_P__P_test_P__P_prog", "T::m", "m"] {
            assert_eq!(
                callee_precondition_goal(
                    &call(name, vec![var("y")]),
                    &[],
                    Some(&program),
                    CallResolution::Spelling,
                    &HashSet::new()
                ),
                CalleePreconditionGoal::None,
                "{name}"
            );
        }
    }

    fn int_params(names: &[&str]) -> HashSet<String> {
        names.iter().map(|name| (*name).to_string()).collect()
    }

    fn eq(left: PureExpr, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), BinOp::Eq, Arc::new(right))
    }

    /// `n != 0` restated over the integers.
    fn n_is_not_zero() -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(var("n")),
                BinOp::Le,
                Arc::new(PureExpr::Int(-1)),
            )),
            BinOp::Or,
            Arc::new(PureExpr::BinOp(
                Arc::new(var("n")),
                BinOp::Ge,
                Arc::new(PureExpr::Int(1)),
            )),
        )
    }

    /// logic_fn_recursive_disequality_branch_control.rs: the `else` arm of an
    /// integer equality states the disequality as its integer restatement.
    #[test]
    fn the_else_arm_of_an_integer_equality_holds_its_integer_restatement() {
        let body = PureExpr::Ite(
            Arc::new(eq(var("n"), PureExpr::Int(0))),
            Arc::new(PureExpr::Int(0)),
            Arc::new(call("needs_pos", vec![var("n")])),
        );
        assert_eq!(
            callee_precondition_goal(
                &body,
                &[needs_pos()],
                None,
                CallResolution::Spelling,
                &int_params(&["n"])
            ),
            CalleePreconditionGoal::Goal(PureExpr::Ite(
                Arc::new(eq(var("n"), PureExpr::Int(0))),
                Arc::new(PureExpr::Bool(true)),
                Arc::new(implies(n_is_not_zero(), gt(var("n"), PureExpr::Int(0)))),
            ))
        );
        // The `||` operand reached where `n == 0` fails holds the same.
        let body = PureExpr::BinOp(
            Arc::new(eq(var("n"), PureExpr::Int(0))),
            BinOp::Or,
            Arc::new(gt(call("needs_pos", vec![var("n")]), PureExpr::Int(0))),
        );
        assert_eq!(
            callee_precondition_goal(
                &body,
                &[needs_pos()],
                None,
                CallResolution::Spelling,
                &int_params(&["n"])
            ),
            CalleePreconditionGoal::Goal(implies(
                PureExpr::UnOp(UnOp::Not, Arc::new(eq(var("n"), PureExpr::Int(0)))),
                implies(n_is_not_zero(), gt(var("n"), PureExpr::Int(0))),
            ))
        );
    }

    /// The restatement is an equivalence only over the integers: an operand
    /// not known to be one, or a parameter a binder hides, gets none.
    #[test]
    fn no_integer_restatement_without_integer_operands() {
        let branch = |cond_var: &str| {
            PureExpr::Ite(
                Arc::new(eq(var(cond_var), PureExpr::Int(0))),
                Arc::new(PureExpr::Int(0)),
                Arc::new(call("needs_pos", vec![var("n")])),
            )
        };
        let plain = PureExpr::Ite(
            Arc::new(eq(var("n"), PureExpr::Int(0))),
            Arc::new(PureExpr::Bool(true)),
            Arc::new(gt(var("n"), PureExpr::Int(0))),
        );
        assert_eq!(
            callee_precondition_goal(
                &branch("n"),
                &[needs_pos()],
                None,
                CallResolution::Spelling,
                &HashSet::new()
            ),
            CalleePreconditionGoal::Goal(plain.clone())
        );
        let shadowed = PureExpr::Let {
            var: "n".to_string(),
            value: Arc::new(var("r")),
            body: Arc::new(branch("n")),
        };
        assert_eq!(
            callee_precondition_goal(
                &shadowed,
                &[needs_pos()],
                None,
                CallResolution::Spelling,
                &int_params(&["n"])
            ),
            CalleePreconditionGoal::Goal(PureExpr::Let {
                var: "n".to_string(),
                value: Arc::new(var("r")),
                body: Arc::new(plain),
            })
        );
    }

    /// lang/logic_vcgen.rs: `f(&mut (*x)[2].0)` reaches the walk without its
    /// borrow, so a precondition over the callee's `&mut` parameter would be
    /// read one reference level off.
    #[test]
    fn a_callee_that_reads_a_final_value_is_refused() {
        let takes_mut =
            needs_pos().with_param_sorts(vec![Some(ExprSort::MutRef(Box::new(ExprSort::Int)))]);
        let reads_final = LogicFnDef::new_with_requires(
            "needs_pos".to_string(),
            "creusot_test::needs_pos".to_string(),
            vec!["x".to_string()],
            vec![gt(PureExpr::Final(Arc::new(var("x"))), PureExpr::Int(0))],
            var("x"),
        );
        let body = call("needs_pos", vec![var("y")]);
        for def in [takes_mut, reads_final] {
            assert!(matches!(
                callee_precondition_goal(
                    &body,
                    &[def],
                    None,
                    CallResolution::Spelling,
                    &HashSet::new()
                ),
                CalleePreconditionGoal::Refused(_)
            ));
        }
    }

    #[test]
    fn a_call_whose_arity_does_not_fit_a_contracted_candidate_is_refused() {
        let body = call("needs_pos", vec![var("y"), var("z")]);
        assert!(matches!(goal(&body), CalleePreconditionGoal::Refused(_)));
    }

    #[test]
    fn an_argument_carrying_an_assertion_is_refused_not_dropped() {
        let body = call(
            "needs_pos",
            vec![PureExpr::Let {
                var: "$stmt0".to_string(),
                value: Arc::new(call("proof_assert", vec![PureExpr::Bool(true)])),
                body: Arc::new(var("y")),
            }],
        );
        assert!(matches!(goal(&body), CalleePreconditionGoal::Refused(_)));
    }

    /// A body whose calls rustc resolved: each entry is one call of its
    /// type-checked form, its spelling and callees.
    fn typed(calls: Vec<(Option<&str>, Vec<ResolvedCallee>)>) -> BodyCallees {
        let mut body = BodyCallees::default();
        for (spelling, callees) in calls {
            body.push(spelling.map(str::to_string), callees);
        }
        body
    }

    fn needs_pos_callee() -> ResolvedCallee {
        ResolvedCallee::Logic("creusot_test::needs_pos".to_string())
    }

    /// `callees` for a body written as `body` and walked uninlined: every
    /// call of it is one of the written body's.
    fn as_written(callees: &BodyCallees, body: &PureExpr) -> BodyCallees {
        let mut names = Vec::new();
        body.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| {
            names.extend(call_name(node).map(str::to_string));
            false
        });
        let mut callees = callees.clone();
        callees.keep_written_calls(names);
        callees
    }

    fn typed_goal(body: &PureExpr, callees: &BodyCallees) -> CalleePreconditionGoal {
        callee_precondition_goal(
            body,
            &[needs_pos()],
            None,
            CallResolution::Typed(&as_written(callees, body)),
            &HashSet::new(),
        )
    }

    /// logic_fn_callee_precondition_use_alias.rs: `np` names no definition;
    /// rustc resolves it to `needs_pos`, which owes its precondition there.
    #[test]
    fn a_renamed_call_owes_the_precondition_of_what_rustc_resolved() {
        let callees = typed(vec![(Some("np"), vec![needs_pos_callee()])]);
        for name in ["np", "m::np", "self::np", "super::np"] {
            assert_eq!(
                typed_goal(&call(name, vec![var("y")]), &callees),
                CalleePreconditionGoal::Goal(gt(var("y"), PureExpr::Int(0))),
                "{name}"
            );
        }
    }

    /// logic_fn_program_method_callee_builtin_name.rs: a method call rustc
    /// resolves to a program function with a precondition is refused however
    /// the encoder reads its name.
    #[test]
    fn a_method_rustc_resolves_to_a_program_function_is_refused() {
        let callees = typed(vec![(
            Some("get"),
            vec![ResolvedCallee::Refused(
                "denotes the program function `creusot_test::S::get`".to_string(),
            )],
        )]);
        let body = PureExpr::MethodCall {
            receiver: Arc::new(var("s")),
            method: "get".to_string(),
            args: vec![var("y")],
        };
        assert!(matches!(
            typed_goal(&body, &callees),
            CalleePreconditionGoal::Refused(why) if why.contains("S::get")
        ));
        // The same spelling on a receiver rustc resolves to a function with no
        // precondition owes nothing.
        let free = typed(vec![(Some("get"), vec![ResolvedCallee::Free])]);
        assert_eq!(typed_goal(&body, &free), CalleePreconditionGoal::None);
    }

    /// logic_fn_std_unwrap_logic_fn_item_binding.rs: `u(o)` with `u` bound to
    /// `Option::unwrap_logic` owes `o != None`.
    #[test]
    fn a_call_rustc_resolves_to_a_std_function_owes_its_precondition() {
        let callees = typed(vec![(
            Some("u"),
            vec![ResolvedCallee::Std(
                "creusot_std::std::option::OptionExt::unwrap_logic".to_string(),
            )],
        )]);
        assert_eq!(
            typed_goal(&call("u", vec![var("o")]), &callees),
            CalleePreconditionGoal::Goal(PureExpr::BinOp(
                Arc::new(var("o")),
                BinOp::Ne,
                Arc::new(var("None")),
            ))
        );
    }

    /// A call that owes a precondition in the type-checked body and that the
    /// parsed body does not hold is refused: it would owe nothing.
    #[test]
    fn an_owing_call_the_parsed_body_lost_is_refused() {
        let callees = typed(vec![
            (Some("needs_pos"), vec![needs_pos_callee()]),
            (Some("needs_pos"), vec![needs_pos_callee()]),
        ]);
        assert!(matches!(
            typed_goal(&call("needs_pos", vec![var("y")]), &callees),
            CalleePreconditionGoal::Refused(why) if why.contains("`needs_pos`")
        ));
        // An operator that calls a function with a precondition.
        let operator = typed(vec![(None, vec![needs_pos_callee()])]);
        assert!(matches!(
            typed_goal(&var("y"), &operator),
            CalleePreconditionGoal::Refused(why) if why.contains("operator")
        ));
    }

    /// A call the identity pass renamed to a definition's id owes every
    /// definition rustc resolves that definition's spellings to.
    #[test]
    fn an_identity_id_owes_what_its_spellings_resolve_to() {
        let mut def = needs_pos();
        def.assign_unique_id("__lfid__needs_pos".to_string());
        let other = ResolvedCallee::Refused("denotes another definition".to_string());
        let callees = typed(vec![(Some("needs_pos"), vec![needs_pos_callee(), other])]);
        let body = call("__lfid__needs_pos", vec![var("y")]);
        assert!(matches!(
            callee_precondition_goal(
                &body,
                &[def.clone()],
                None,
                CallResolution::Typed(&as_written(&callees, &body)),
                &HashSet::new()
            ),
            CalleePreconditionGoal::Refused(why) if why.contains("another definition")
        ));
        let callees = typed(vec![(Some("needs_pos"), vec![needs_pos_callee()])]);
        assert_eq!(
            callee_precondition_goal(
                &body,
                &[def],
                None,
                CallResolution::Typed(&as_written(&callees, &body)),
                &HashSet::new()
            ),
            CalleePreconditionGoal::Goal(gt(var("y"), PureExpr::Int(0)))
        );
    }

    /// A body with no type-checked form is placed only when it calls
    /// nothing, as walked and as written, and a body the resolution refused
    /// is refused.
    #[test]
    fn an_untyped_or_refused_body_places_no_call() {
        let untyped = |body: &PureExpr, written_call: Option<&str>| {
            callee_precondition_goal(
                body,
                &[needs_pos()],
                None,
                CallResolution::Untyped { written_call },
                &HashSet::new(),
            )
        };
        assert!(matches!(
            untyped(&call("np", vec![var("y")]), None),
            CalleePreconditionGoal::Refused(_)
        ));
        assert_eq!(
            untyped(&gt(var("y"), PureExpr::Int(0)), None),
            CalleePreconditionGoal::None
        );
        // The written body called `H::ignore`, which inlining replaced by a
        // body that calls nothing: what the call denoted is still unknown.
        assert!(matches!(
            untyped(&PureExpr::Int(0), Some("H::ignore")),
            CalleePreconditionGoal::Refused(why) if why.contains("H::ignore")
        ));
        let mut refused = typed(vec![]);
        refused.refuse("a call `np` that the body's type-checked form does not hold".to_string());
        assert!(matches!(
            typed_goal(&gt(var("y"), PureExpr::Int(0)), &refused),
            CalleePreconditionGoal::Refused(_)
        ));
    }

    /// logic_fn_callee_precondition_view_beside_inlined_view.rs: a call an
    /// inlined callee's body brings into the walked body is no counterpart of
    /// an owing call of this body, however it is spelled.
    #[test]
    fn an_inlined_callee_call_is_no_counterpart() {
        let mut callees = typed(vec![(Some("needs_pos"), vec![needs_pos_callee()])]);
        // Walked: `needs_pos(1)`, from an inlined body; written: nothing
        // spelled `needs_pos` survives (the written call was an operator's,
        // or sat in an argument inlining dropped).
        let walked = call("needs_pos", vec![PureExpr::Int(1)]);
        callees.keep_written_calls(vec!["__lfid__H_ignore".to_string()]);
        assert!(matches!(
            callee_precondition_goal(
                &walked,
                &[needs_pos()],
                None,
                CallResolution::Typed(&callees),
                &HashSet::new()
            ),
            CalleePreconditionGoal::Refused(why) if why.contains("`needs_pos`")
        ));
        // A written call the walked body still holds is its own counterpart.
        callees.keep_written_calls(vec!["needs_pos".to_string()]);
        assert_eq!(
            callee_precondition_goal(
                &walked,
                &[needs_pos()],
                None,
                CallResolution::Typed(&callees),
                &HashSet::new()
            ),
            CalleePreconditionGoal::Goal(gt(PureExpr::Int(1), PureExpr::Int(0)))
        );
    }
}
