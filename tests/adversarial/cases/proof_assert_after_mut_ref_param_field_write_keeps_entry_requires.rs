//@ expect: reject
//@ mechanism: proof_assert_after_param_field_write_keeps_entry_requires.rs through a `&mut` parameter: `p.a = 7;` on `p: &mut P` never reaches the proof_assert lane, which reads `(*p).a` at its entry value and discharges the assertion with the precondition about that entry value. The function-level lane sees the write: `#[ensures((^p).a@ == 3)]` on the same body is refuted. A scalar pointee (`*acc = 7;`) does reach the lane and is refused as a vacuous proof rather than credited.
//@ accept-means: an assertion about a field of a `&mut` parameter's pointee after the function wrote that field is proved from the precondition on the entry value, and the crate exits 0.
//@ WHY THE ASSERTION IS FALSE: `p.a = 7` writes through the borrow before the assertion, so `(*p).a` is 7 there, never 3.
//@ teeth: MEASURED ACCEPTED, exit 0: `proof_assert in creusot_test::k verified ✓` and `k verified ✓`. The other field is no different: `#[requires(p.b@ == 3)]`, `p.b = 7;`, `proof_assert!(p.b@ == 3)` is accepted the same way. Without the `requires` the TRUE `p.a@ == 7` is refuted.
//@ fixed-by: ?
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub a: u32,
    pub b: u32,
}

#[requires(p.a@ == 3)]
pub fn k(p: &mut P) {
    p.a = 7;
    proof_assert!(p.a@ == 3);
}
