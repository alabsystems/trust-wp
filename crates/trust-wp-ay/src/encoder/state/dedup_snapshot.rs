// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Snapshot of scope-sensitive assert-once state for obligation slice isolation.
//!
//! Created before an obligation slice loop, restored at the top of each
//! iteration. This ensures each slice sees the same baseline from the shared
//! encoding scope, preventing cross-slice assertion/axiom loss. (#2618)
//!
//! Any field that suppresses solver assertions or quantified axiom emission
//! inside an obligation slice must either be included here or moved to the
//! base scope.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::Term;

use super::super::{ground_pool::GroundTermPool, produces_ground::ProducesGroundCalls};

/// Snapshot of scope-sensitive assert-once state for obligation slice isolation.
///
/// The five encode-time dedup fields, logic function axiom dedup, and Seq
/// axiom flags are captured before the slice loop and restored per-iteration.
#[derive(Clone)]
pub(crate) struct DedupSnapshot {
    pub(in crate::encoder) is_option_asserted: HashSet<Term>,
    pub(in crate::encoder) view_identity_asserted: HashSet<String>,
    pub(in crate::encoder) asserted_quantified_neq_pairs: HashSet<(Term, Term)>,
    pub(in crate::encoder) produces_ground_calls: HashMap<String, ProducesGroundCalls>,
    pub(in crate::encoder) ground_pool: GroundTermPool,
    pub(in crate::encoder) logic_fn_axioms: HashSet<String>,
    pub(in crate::encoder) sum_axioms_asserted: bool,
    pub(in crate::encoder) get_axioms_asserted: bool,
    pub(in crate::encoder) contains_axioms_asserted: bool,
    pub(in crate::encoder) concat_axioms_asserted: bool,
    pub(in crate::encoder) reverse_axioms_asserted: bool,
    pub(in crate::encoder) permutation_axioms_asserted: bool,
}
