//@ expect: reject
//@ verdict: error
//@ refused-with: lies in a namespace the verifier synthesizes names in
//@ mechanism: as s71_reserved_name_loop_invariant, with a FALSE invariant spelled through the
//@ mechanism: reserved name: `__trust_wp_tuple_get_1((i, 0)) == i` reads the second component
//@ mechanism: (0), so it is false from the first iteration on. Nothing in the driver refused
//@ mechanism: the spelling; only ay's incompleteness stood between it and credit.
//@ fixed-by: wp-s71 v2 (`spec_clauses_of_body_owner`)
//@ accept-means: a false loop invariant written in the encoder's own namespace verified.
//@ WHY THE CONTRACT IS FALSE: at i == 1 the invariant claims 0 == 1. count(3) reaches it.
//@ teeth: (i) pre-fix build wp-s71 75f19abf: `? count unknown (incomplete loop: loop invariant
//@ teeth: quantifier-ematching-exists-incomplete)` — unrefused, withheld by the solver only;
//@ teeth: `verdict: error` names that `unknown` as TEETH LOST
//@ teeth: (review probe p5e_reserved_invariant_false).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(n >= 0 && n < 1000)]
#[ensures(result == n)]
pub fn count(n: i32) -> i32 {
    let mut i = 0;
    #[invariant(i <= n && __trust_wp_tuple_get_1((i, 0)) == i)]
    while i < n {
        i += 1;
    }
    i
}

pub fn main() {
    let _ = count(3);
}
