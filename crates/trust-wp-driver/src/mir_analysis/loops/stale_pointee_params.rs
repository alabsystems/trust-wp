// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Which by-reference parameters a loop may invalidate.
//!
//! A `#[requires]` clause talks about the ENTRY value of a parameter's pointee,
//! and trust-wp's encoder names that value with the SAME symbol it uses for the
//! pointee's current value (`a_current` for `*a`). For straight-line code the
//! extraction records the written value against that symbol, but a write inside
//! a loop body is not walked, so the entry fact silently survives the loop:
//!
//! ```text
//! #[requires((*a)@ == 0)]
//! pub fn s08(a: &mut u32) {
//!     let mut i = 0u32;
//!     #[invariant(i@ <= 3)] while i < 3 { *a = 7; i += 1; }
//!     proof_assert!((*a)@ == 0);      // discharged by the stale precondition
//! }
//! ```
//!
//! [`params_invalidated_by_loops`] reports the argument locals a loop may write
//! — the pointee through a `&mut`/raw/`Box` deref, a `&mut` handed to a call,
//! or the reference local itself — from which a given program point is
//! reachable. The consumer drops the entry facts naming those parameters; a
//! dropped premise can only lose a proof, never create one.

use std::collections::HashSet;

use rustc_middle::{
    mir::{BasicBlock, Body, Local, TerminatorKind},
    ty::TyKind,
};

use super::{detection::detect_loops, write_sites::WriteSites};

/// Whether a parameter of this type denotes memory a callee's write can reach
/// through the parameter (a reference, a raw pointer, or a `Box`).
///
/// A closure's environment taken BY VALUE (an `FnOnce` body's `_1`) counts
/// too: it is the captured state itself, and a `#[requires]` about a capture
/// is an entry fact about it exactly as one about `*a` is about the pointee.
fn param_has_pointee(body: &Body<'_>, local: Local) -> bool {
    let ty = body.local_decls[local].ty;
    match ty.kind() {
        TyKind::Ref(..) | TyKind::RawPtr(..) | TyKind::Closure(..) => true,
        // `Box<T>` derefs to its pointee the same way; `*b = v` inside a loop
        // invalidates `#[requires((*b)@ == ..)]` exactly as `&mut` does.
        TyKind::Adt(adt, _) => adt.is_box(),
        _ => false,
    }
}

/// The source spellings a set of invalidated argument locals stands for.
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct InvalidatedEntryNames {
    /// Parameters, by their source name.
    pub(crate) params: HashSet<String>,
    /// An invalidated argument that has no parameter name of its own: a
    /// closure's environment (`_1`, which carries every capture) or a local
    /// the name list does not reach. Its entry facts are spelled in names
    /// this list cannot enumerate, so a consumer drops every entry fact.
    pub(crate) unnamed: bool,
}

impl InvalidatedEntryNames {
    pub(crate) fn is_empty(&self) -> bool {
        self.params.is_empty() && !self.unnamed
    }

    /// Whether an entry fact whose free variables are `free_vars` is stale.
    pub(crate) fn invalidates<'a>(&self, mut free_vars: impl Iterator<Item = &'a str>) -> bool {
        self.unnamed || free_vars.any(|name| self.params.contains(name))
    }
}

/// Name the argument locals [`params_invalidated_by_loops`] reported.
///
/// `arg_names` are the SOURCE parameters, which is what a `#[requires]` is
/// written over. A closure body's MIR puts its environment in `_1` and its
/// declared parameters from `_2` on, so the offset differs from a function
/// item's, where `_1` is the first parameter; reading a closure's `_2` as the
/// second name dropped the fact about a different parameter and kept the
/// stale one.
pub(crate) fn name_invalidated_args(
    invalidated: &HashSet<Local>,
    is_closure: bool,
    arg_names: &[String],
) -> InvalidatedEntryNames {
    let first_param = if is_closure { 2 } else { 1 };
    let mut names = InvalidatedEntryNames::default();
    for local in invalidated {
        let name = local
            .as_usize()
            .checked_sub(first_param)
            .and_then(|index| arg_names.get(index));
        match name {
            Some(name) => {
                names.params.insert(name.clone());
            }
            None => names.unnamed = true,
        }
    }
    names
}

/// Blocks from which any of `targets` is reachable, the targets included.
fn blocks_reaching(
    body: &Body<'_>,
    targets: impl IntoIterator<Item = BasicBlock>,
) -> HashSet<BasicBlock> {
    let mut predecessors: Vec<Vec<BasicBlock>> = vec![Vec::new(); body.basic_blocks.len()];
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(terminator) = &data.terminator {
            for succ in terminator.successors() {
                predecessors[succ.as_usize()].push(bb);
            }
        }
    }
    let mut seen = HashSet::new();
    let mut stack: Vec<BasicBlock> = Vec::new();
    for target in targets {
        if seen.insert(target) {
            stack.push(target);
        }
    }
    while let Some(bb) = stack.pop() {
        for pred in &predecessors[bb.as_usize()] {
            if seen.insert(*pred) {
                stack.push(*pred);
            }
        }
    }
    seen
}

/// Argument locals whose value — or whose pointee — a loop may write, where the
/// write reaches `at`.
///
/// `at = None` asks the question without a program point: every argument any
/// loop in the body may write is reported. That is the fail-closed answer for a
/// consumer that cannot locate itself in this body (an assertion inside a
/// nested closure), and it can only drop more facts.
pub(crate) fn params_invalidated_by_loops(
    body: &Body<'_>,
    at: Option<BasicBlock>,
) -> HashSet<Local> {
    let reaching = at.map(|target| blocks_reaching(body, [target]));
    params_invalidated_by_loops_reaching(body, reaching.as_ref())
}

/// Argument locals whose value — or whose pointee — a loop may write on a path
/// that reaches a RETURN of this body.
///
/// This is the ENSURES lane's program point. A postcondition is checked where
/// the function returns, so the parameters whose entry facts have gone stale
/// are exactly those a loop may write on some path to some exit — NOT the
/// assertion lane's point, which is the block the `proof_assert!` sits in and
/// which correctly keeps the entry fact for an assertion placed BEFORE the
/// loop. No such "before" exists for a postcondition.
///
/// Taking the union over every `Return` block is what the function-level VC
/// needs: it is one formula covering every exit, so a premise that is stale at
/// ANY reachable exit must go. A loop from which no return is reachable (a
/// diverging loop, or one every path out of which panics) contributes nothing,
/// because no postcondition is ever checked after it.
///
/// A body with no `Return` terminator at all cannot be located this way, so the
/// question is asked with no program point: every parameter any loop writes is
/// reported. That is the fail-closed direction and can only drop more facts.
pub(crate) fn params_invalidated_by_loops_at_exits(body: &Body<'_>) -> HashSet<Local> {
    let returns: Vec<BasicBlock> = body
        .basic_blocks
        .iter_enumerated()
        .filter(|(_, data)| {
            data.terminator
                .as_ref()
                .is_some_and(|t| matches!(t.kind, TerminatorKind::Return))
        })
        .map(|(bb, _)| bb)
        .collect();
    let reaching = if returns.is_empty() {
        None
    } else {
        Some(blocks_reaching(body, returns))
    };
    params_invalidated_by_loops_reaching(body, reaching.as_ref())
}

/// Shared core: `reaching` is the set of blocks from which the program point of
/// interest is reachable, or `None` to ask without a program point.
fn params_invalidated_by_loops_reaching(
    body: &Body<'_>,
    reaching: Option<&HashSet<BasicBlock>>,
) -> HashSet<Local> {
    let analysis = detect_loops(body);
    if !analysis.has_loops {
        return HashSet::new();
    }
    let args: Vec<Local> = (1..=body.arg_count)
        .map(Local::from_usize)
        .filter(|local| param_has_pointee(body, *local))
        .collect();
    if args.is_empty() {
        return HashSet::new();
    }

    let write_sites = WriteSites::new(body);
    let mut out = HashSet::new();
    for loop_info in &analysis.loops {
        // The loop is relevant when one of its blocks can reach the program
        // point (a write inside the loop is then visible there). A loop that
        // contains the point qualifies through the same test.
        if let Some(reaching) = reaching {
            if !loop_info.body_blocks.iter().any(|bb| reaching.contains(bb)) {
                continue;
            }
        }
        let writes = write_sites.writes_in_blocks(loop_info.body_blocks.iter().copied());
        for arg in &args {
            if writes.contains_key(arg) {
                out.insert(*arg);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn locals(indices: &[usize]) -> HashSet<Local> {
        indices.iter().copied().map(Local::from_usize).collect()
    }

    fn names(names: &[&str]) -> Vec<String> {
        names.iter().map(|name| (*name).to_string()).collect()
    }

    #[test]
    fn a_function_items_first_parameter_is_local_one() {
        let named = name_invalidated_args(&locals(&[2]), false, &names(&["a", "b"]));
        assert_eq!(named.params, HashSet::from(["b".to_string()]));
        assert!(!named.unnamed);
    }

    #[test]
    fn a_closures_first_parameter_is_local_two() {
        // Read with the function-item offset, `_2` named `z` here and the
        // fact about the written `y` survived the loop.
        let named = name_invalidated_args(&locals(&[3]), true, &names(&["z", "y"]));
        assert_eq!(named.params, HashSet::from(["y".to_string()]));
        assert!(!named.unnamed);
    }

    #[test]
    fn a_closures_environment_has_no_parameter_name_and_stales_every_fact() {
        let named = name_invalidated_args(&locals(&[1]), true, &names(&["y"]));
        assert!(named.params.is_empty());
        assert!(named.unnamed);
        assert!(named.invalidates(["unrelated"].into_iter()));
    }

    #[test]
    fn a_local_past_the_name_list_stales_every_fact() {
        let named = name_invalidated_args(&locals(&[3]), false, &names(&["a"]));
        assert!(named.unnamed);
    }
}
