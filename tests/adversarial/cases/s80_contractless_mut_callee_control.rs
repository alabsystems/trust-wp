//@ expect: verify
//@ mechanism: over-refusal control — a caller of a LOCAL contract-less callee whose postcondition does not mention what the callee touched must stay provable (Creusot gives a local contract-less callee an EMPTY contract; specification.rs:266-275 restricts `requires false` to non-local external-crate Program items)
//@ xfail: the local opaque call is owed `requires(false)` (fallback.rs:35), which makes every caller unprovable. XPASS is the signal that a route that credits non-recursive contract-less callers landed.
//@ xfail: MEASURED at 0bead8ec: rejected in both full adversarial runs — the fix-gate run and the post-merge run — and 3/3 in isolation. Route (a) does not credit a NON-recursive contract-less caller, which is the point.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

fn bump(x: &mut u32) {
    *x += 1;
}

// TRUE: the mutation lands in `scratch`, which the postcondition never mentions.
#[ensures(result@ == a@)]
pub fn caller_ok(a: u32) -> u32 {
    let mut scratch: u32 = 0;
    bump(&mut scratch);
    a
}
