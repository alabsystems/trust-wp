//@ expect: reject
//@ verdict: error
//@ refused-with: lies in a namespace the verifier synthesizes names in
//@ mechanism: creusot_frontend_checks::validate_reserved_binding_names scanned only the body
//@ mechanism: OWNER's doc markers (`#[requires]`/`#[ensures]`), while a loop clause's marker
//@ mechanism: sits on the loop expression: `#[invariant(__trust_wp_tuple_get_0((i, i)) == i
//@ mechanism: && i <= n)]` was refused nowhere, and spec_tc::encode leaves a `__trust_wp_*`
//@ mechanism: call untyped on the premise that the driver refuses it — so the invariant lane
//@ mechanism: took `loop invariant + call obligations verified ✓` credit on reserved text.
//@ fixed-by: wp-s71 v2 (`spec_clauses_of_body_owner`: every guard over specification text
//@ fixed-by: reads the owner's markers, every marker inside the body, and the source-parsed
//@ fixed-by: loop clauses)
//@ accept-means: reserved `__trust_wp_*` spellings in a loop clause reach the encoder unrefused.
//@ WHY THIS MUST BE REFUSED: `__trust_wp_tuple_get_0` is the driver's own synthesized name;
//@ WHY THIS MUST BE REFUSED: whatever it denotes here is an encoder artefact, not a Rust item
//@ WHY THIS MUST BE REFUSED: (the contract itself is true — the FALSE twin is
//@ WHY THIS MUST BE REFUSED: s71_reserved_name_loop_invariant_false).
//@ teeth: (i) pre-fix build wp-s71 75f19abf printed `count loop invariant + call obligations
//@ teeth: verified ✓` and ended `? count unknown (proof-trusted)` — credit, no refusal, verdict
//@ teeth: `unknown`, which this case's `verdict: error` names as TEETH LOST
//@ teeth: on a probe carrying this reserved spelling in a loop invariant. Campaign: E0425 at
//@ teeth: spec_tc, no wire line.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(n >= 0 && n < 1000)]
#[ensures(result == n)]
pub fn count(n: i32) -> i32 {
    let mut i = 0;
    #[invariant(__trust_wp_tuple_get_0((i, i)) == i && i <= n)]
    while i < n {
        i += 1;
    }
    i
}

pub fn main() {
    let _ = count(3);
}
