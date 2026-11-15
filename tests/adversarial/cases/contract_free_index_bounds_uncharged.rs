//@ expect: reject
//@ verdict: failed
//@ fn-failed: hop
//@ mechanism: a contract-free body whose only panic site is a MIR `Assert(BoundsCheck)` — the
//@ mechanism: goal kind Creusot calls `assertion`. `body_reaches_diverging_call` counts only
//@ mechanism: `Call { target: None }`, and the arithmetic predicate walked HIR binary,
//@ mechanism: assign-op and negation nodes, so a slice or array index made the body a
//@ mechanism: verification target of NOTHING. trust-wp already OWNED the obligation
//@ mechanism: (`bounds_check_obligation`, `ix < len` at the assert's program point): the
//@ mechanism: identical index in a host that carries a contract is refuted. Only the discovery
//@ mechanism: predicate could not see an `Assert` terminator. `Vec` indexing escapes this because
//@ mechanism: it lowers to an `Index::index` CALL with a builtin std spec; bare slice and array
//@ mechanism: indexing lowers to the terminator and nothing looked at it.
//@ accept-means: a body that panics with "index out of bounds" on a reachable input was examined
//@ accept-means: by nobody and the crate still reported a clean verification run
//@ fixed-by: D-95
//@ teeth: ACCEPTED (exit 0, `hop` named in no verdict line) both before and after the
//@ teeth: contract-free target rule of D-71; the same index under a contract is refuted, and the
//@ teeth: `Vec` spelling of the same program is refuted. It is not a blanket refusal of indexing
//@ teeth: bodies that closes it: contract_free_index_bounds_clausefree_control guards the SAME
//@ teeth: index with `i < v.len()` and verifies clause-free, and its `<=` twin
//@ teeth: contract_free_index_bounds_off_by_one is refuted.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// `hop(&[], 0)` panics: the index is unconstrained and the slice may be empty.
pub fn hop(v: &[u32], i: usize) -> u32 {
    v[i]
}
