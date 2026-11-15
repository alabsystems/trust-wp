//@ expect: reject
//@ verdict: error
//@ refused-with: lies in a namespace the verifier synthesizes names in
//@ mechanism: as s71_reserved_name_loop_invariant, with the reserved call in the SECOND
//@ mechanism: conjunct of the invariant (`i <= n && __trust_wp_tuple_get_0((i, 0)) == i`):
//@ mechanism: the loop-clause marker on the loop expression was outside the reserved-name scan.
//@ fixed-by: wp-s71 v2 (`spec_clauses_of_body_owner`)
//@ accept-means: reserved `__trust_wp_*` spellings in a loop clause reach the encoder unrefused.
//@ WHY THIS MUST BE REFUSED: `__trust_wp_tuple_get_0` is the driver's own synthesized name.
//@ teeth: (i) pre-fix build wp-s71 75f19abf: `count loop invariant + call obligations verified
//@ teeth: ✓`, `? count unknown (proof-trusted)` — credit, no refusal. The reserved
//@ teeth: spelling sits in the SECOND invariant conjunct.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(n >= 0 && n < 1000)]
#[ensures(result == n)]
pub fn count(n: i32) -> i32 {
    let mut i = 0;
    #[invariant(i <= n && __trust_wp_tuple_get_0((i, 0)) == i)]
    while i < n {
        i += 1;
    }
    i
}

pub fn main() {
    let _ = count(3);
}
