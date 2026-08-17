//@ expect: reject
//@ mechanism: sort-fallback premise drop — a heuristic Bool sort plan on a datatype-view var makes
//@ mechanism: `v@ == <int literal outside {0,1}>` unencodable, and eq_term substitutes a
//@ mechanism: polarity-neutral `__trust_wp_unencodable_eq_*` placeholder for the whole equality
//@ fixed-by: 90fdf8f (sortplan — int-literal-equality evidence vetoes the Bool inference;
//@ fixed-by: PremiseNeutralizedEq demotes Failed(Counterexample) to Unknown)
//@ accept-means: an obligation trust-wp COULD NOT ENCODE was counted as verified. The placeholder
//@ accept-means: is only sound while it stays polarity-neutral in goal position; if a future
//@ accept-means: change lets a fabricated equality discharge a goal, this case accepts a claim
//@ accept-means: that is plainly false.
//@
//@ WHY THE CONTRACT IS FALSE: `b` holds 9, not 5. The literal 5 never appears in the program.
//@ teeth: UNVERIFIED (honest). Method (ii): the int-literal-equality evidence + annotation veto
//@ teeth: (90fdf8f a1/a2) disabled in-tree. This case still rejects. Like (b), the defect direction
//@ teeth: is premise weakening, so no accept is reachable through it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use ::std::sync::Arc;
use creusot_std::prelude::*;

pub fn arc_view_wrong_literal() {
    let a = Arc::new(5i32);
    let b = Arc::new(9i32);
    let same = Arc::ptr_eq(&a, &b);
    proof_assert!(!same);
    proof_assert!(*b@ == 5i32);
}
