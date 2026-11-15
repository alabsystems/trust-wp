//@ expect: reject
//@ mechanism: a copy of a BY-VALUE parameter taken before the body re-binds the parameter, then a
//@ mechanism: `proof_assert!` about the copy: `let y = x; x = 5; proof_assert!(y@ == 5)`. The substitution
//@ mechanism: walk binds `y` to the parameter's own name (`y -> x`, the value at the copy, which is the entry
//@ mechanism: value) and `x` to the write (`x -> 5`); the map's internal-reference resolution then reads the
//@ mechanism: `x` inside `y`'s binding as the parameter's CURRENT binding and rewrites it to 5, and the
//@ mechanism: substitution facts `y == x`, `x == 5` say the same. The encoder gives the entry and the current
//@ mechanism: value of a by-value parameter one name. A local copied the same way (`let mut a = n; let b = a;
//@ mechanism: a = 5;`) is bound to its value (`b -> n`) and refuted, and the postcondition lane refutes
//@ mechanism: `result@ == 5` for the parameter spelling. Found probing D-140's re-bind withdrawal sideways; no
//@ mechanism: precondition and no drop is involved, so withdrawing entry facts does not reach it.
//@ accept-means: a `proof_assert!` about a copy of a parameter is credited with the value the parameter was
//@ accept-means: re-bound to after the copy, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `y` holds the parameter's entry value, which the precondition (`true`) leaves
//@ WHY THE CONTRACT IS FALSE: arbitrary; `copy_then_rebind(0)` asserts `0 == 5`.
//@ fixed-by: D-241: a re-bound by-value parameter's entry value is read by its own symbol inside the substitution map's values, so the copy keeps the value it copied.
//@ teeth: LIVE at D-140's head: ACCEPTED, exit 0, `proof_assert in creusot_test::copy_then_rebind verified`
//@ teeth: and `copy_then_rebind verified`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
pub fn copy_then_rebind(mut x: u32) {
    let y = x;
    x = 5;
    proof_assert!(y@ == 5);
    let _ = x;
}
