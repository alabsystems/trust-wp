// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Where a fact established at one program point may be assumed at another
//! (D-189).
//!
//! A fact the proof_assert lane assumes at an assertion `Q` (a loop's
//! invariant, its negated condition at the exit, its condition on the in-body
//! arm) was established at some program point `P` and speaks of the values
//! the source names it mentions had THERE. It is a fact at `Q` only when
//!
//! 1. `P` dominates `Q`: every execution reaching `Q` passed `P`; and
//! 2. on no path from `P` to `Q` that does not pass `P` again is any local the
//!    fact names written (a store, a call destination, a borrow handed on, a
//!    write through a pointer that may reach it: [`WriteSites::writes_at`]).
//!    The paths include every back edge, and the test is per statement: a
//!    write after `Q` in `Q`'s own block counts only when a cycle carries it
//!    back round to `Q`, and a write after `Q` in a later loop's body counts
//!    because that loop's back edge does. Together, (1) and (2) say that at
//!    `Q` every name holds the value it held at the LAST visit of `P`.
//!
//! The question is about dynamic instances, which is why it is a path
//! question and not a comparison of reaching-definition sets: in `loop { P;
//! x = f(); Q; }` the one definition of `x` reaching `Q` also reaches `P`
//! round the back edge, yet the `x` at `Q` is not the `x` the fact at `P`
//! described. It is D-186's formulation (`reaches_avoiding_from`: a path that
//! executes none of the kills in between), with `P` itself the only kill.
//!
//! A fact names source names, and the lane reads each at `Q` by name. A name
//! bound to more than one local (a shadowing `let`, a block-local that shares
//! a parameter's name, a capture beside a local) does not say which of them
//! the fact meant or which the assertion reads, so a fact mentioning one is
//! never assumed.

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_middle::mir::{BasicBlock, Body, Local, Location, VarDebugInfoContents};
use rustc_span::Span;

use super::loops::WriteSites;

/// The written-since query of one body ([`FactScope::stale_names`]).
pub(crate) struct FactScope<'a, 'tcx> {
    body: &'a Body<'tcx>,
    sites: WriteSites<'a, 'tcx>,
    /// Source name -> the locals it is bound to (`None`: a constant).
    bindings: HashMap<String, HashSet<Option<Local>>>,
}

impl<'a, 'tcx> FactScope<'a, 'tcx> {
    pub(crate) fn new(body: &'a Body<'tcx>) -> Self {
        Self {
            body,
            sites: WriteSites::new(body),
            bindings: name_bindings(body),
        }
    }

    /// The names a fact established at the point just before the statement
    /// (or terminator) `established` may not mention at the point just before
    /// `at`, or `None` when no fact established there holds at `at` (it does
    /// not dominate `at`).
    pub(crate) fn stale_names(
        &self,
        established: Location,
        at: Location,
    ) -> Option<HashSet<String>> {
        if !self.dominates(established, at) {
            return None;
        }
        let written = self.locals_written_between(established, at);
        Some(
            self.bindings
                .iter()
                .filter(|(_, locals)| {
                    locals.len() > 1
                        || locals
                            .iter()
                            .any(|local| local.is_some_and(|local| written.contains(&local)))
                })
                .map(|(name, _)| name.clone())
                .collect(),
        )
    }

    /// The locals written on a path from `established` to `at` that does not
    /// pass `established` again, or `None` when `established` does not
    /// dominate `at`: the local-level half of [`Self::stale_names`], for a
    /// fact over a temporary no source name is bound to (a call's
    /// destination, a borrow handed to it).
    pub(crate) fn written_since(
        &self,
        established: Location,
        at: Location,
    ) -> Option<HashSet<Local>> {
        self.dominates(established, at)
            .then(|| self.locals_written_between(established, at))
    }

    /// The names a fact established inside the source region `region` (a
    /// ghost block) may not mention at `at`, or `None` when no such fact
    /// holds at `at`: [`Self::stale_names`] from the point just after the
    /// region's last location ([`Self::point_after_region`]).
    pub(crate) fn stale_names_after_region(
        &self,
        region: Span,
        at: Location,
    ) -> Option<HashSet<String>> {
        self.stale_names(self.point_after_region(region)?, at)
    }

    /// The point just after the one location of `region` (by source span)
    /// that every other location of it dominates: where everything the
    /// region did is done. `None` when the region has no location, no such
    /// last location (it branches out on more than one path), or its last
    /// location is a terminator with more than one normal successor or whose
    /// successor is entered from elsewhere too.
    pub(crate) fn point_after_region(&self, region: Span) -> Option<Location> {
        let region = region.source_callsite();
        let dominators = self.body.basic_blocks.dominators();
        let mut inside = Vec::new();
        for (block, data) in self.body.basic_blocks.iter_enumerated() {
            if !dominators.is_reachable(block) {
                continue;
            }
            for (statement_index, statement) in data.statements.iter().enumerate() {
                if region.contains(statement.source_info.span.source_callsite()) {
                    inside.push(Location {
                        block,
                        statement_index,
                    });
                }
            }
            if region.contains(data.terminator().source_info.span.source_callsite()) {
                inside.push(Location {
                    block,
                    statement_index: data.statements.len(),
                });
            }
        }
        let last = *inside.iter().find(|candidate| {
            inside
                .iter()
                .all(|other| self.dominates(*other, **candidate))
        })?;
        if last.statement_index < self.last_index(last.block) {
            return Some(Location {
                block: last.block,
                statement_index: last.statement_index + 1,
            });
        }
        let mut normal = self.body.basic_blocks[last.block]
            .terminator()
            .successors()
            .filter(|successor| !self.body.basic_blocks[*successor].is_cleanup);
        let successor = normal.next()?;
        if normal.next().is_some()
            || self.body.basic_blocks.predecessors()[successor].as_slice() != [last.block]
        {
            return None;
        }
        Some(Location {
            block: successor,
            statement_index: 0,
        })
    }

    fn dominates(&self, established: Location, at: Location) -> bool {
        let dominators = self.body.basic_blocks.dominators();
        if !dominators.is_reachable(at.block) {
            return false;
        }
        if established.block == at.block {
            return established.statement_index <= at.statement_index;
        }
        dominators.dominates(established.block, at.block)
    }

    /// The locals written by a statement or terminator that some path runs
    /// after `from` and before `to` without passing `from` again.
    fn locals_written_between(&self, from: Location, to: Location) -> HashSet<Local> {
        let after = self.after(from);
        let before = self.before(to, from);
        let mut written = HashSet::new();
        for location in after.intersection(&before) {
            written.extend(self.sites.writes_at(*location).into_keys());
        }
        written
    }

    fn last_index(&self, block: BasicBlock) -> usize {
        self.body.basic_blocks[block].statements.len()
    }

    /// Every location a path starting at the point before `from` executes
    /// before it reaches that point again.
    fn after(&self, from: Location) -> HashSet<Location> {
        let mut out = HashSet::new();
        for statement_index in from.statement_index..=self.last_index(from.block) {
            out.insert(Location {
                block: from.block,
                statement_index,
            });
        }
        let mut seen: HashSet<BasicBlock> = HashSet::new();
        let mut queue: VecDeque<BasicBlock> = self.body.basic_blocks[from.block]
            .terminator()
            .successors()
            .collect();
        while let Some(block) = queue.pop_front() {
            if !seen.insert(block) {
                continue;
            }
            let end = if block == from.block {
                // The path reaches `from` again before this statement.
                from.statement_index
            } else {
                self.last_index(block) + 1
            };
            for statement_index in 0..end {
                out.insert(Location {
                    block,
                    statement_index,
                });
            }
            if block != from.block {
                queue.extend(self.body.basic_blocks[block].terminator().successors());
            }
        }
        out
    }

    /// Every location some path runs before it reaches the point before `to`
    /// without passing the point before `barrier` on the way.
    fn before(&self, to: Location, barrier: Location) -> HashSet<Location> {
        let mut out = HashSet::new();
        let predecessors = self.body.basic_blocks.predecessors();
        // `barrier` earlier in `to`'s own block: walking back from `to`
        // reaches it before leaving the block.
        let barrier_in_block =
            to.block == barrier.block && barrier.statement_index <= to.statement_index;
        let start = if barrier_in_block {
            barrier.statement_index
        } else {
            0
        };
        for statement_index in start..to.statement_index {
            out.insert(Location {
                block: to.block,
                statement_index,
            });
        }
        if barrier_in_block {
            return out;
        }
        let mut seen: HashSet<BasicBlock> = HashSet::new();
        let mut queue: VecDeque<BasicBlock> = predecessors[to.block].iter().copied().collect();
        while let Some(block) = queue.pop_front() {
            if !seen.insert(block) {
                continue;
            }
            let first = if block == barrier.block {
                barrier.statement_index
            } else {
                0
            };
            for statement_index in first..=self.last_index(block) {
                out.insert(Location {
                    block,
                    statement_index,
                });
            }
            if block != barrier.block {
                queue.extend(predecessors[block].iter().copied());
            }
        }
        out
    }
}

/// Source name -> the locals (or constants) `body`'s debug info binds it to.
/// A name bound to a projection of a local (a closure's capture) is bound to
/// that local.
fn name_bindings(body: &Body<'_>) -> HashMap<String, HashSet<Option<Local>>> {
    let mut bindings: HashMap<String, HashSet<Option<Local>>> = HashMap::new();
    for debug in &body.var_debug_info {
        let local = match &debug.value {
            VarDebugInfoContents::Place(place) => Some(place.local),
            VarDebugInfoContents::Const(_) => None,
        };
        bindings
            .entry(debug.name.to_string())
            .or_default()
            .insert(local);
    }
    bindings
}

fn ambiguous_names_of(bindings: &HashMap<String, HashSet<Option<Local>>>) -> HashSet<String> {
    bindings
        .iter()
        .filter(|(_, locals)| locals.len() > 1)
        .map(|(name, _)| name.clone())
        .collect()
}

/// Names `body`'s debug info binds to more than one local or constant: a
/// fact stated over one by name cannot say which it meant (D-189).
pub(crate) fn ambiguous_debug_names(body: &Body<'_>) -> HashSet<String> {
    ambiguous_names_of(&name_bindings(body))
}
