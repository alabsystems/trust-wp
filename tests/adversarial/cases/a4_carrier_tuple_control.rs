//@ expect: verify
//@ mechanism: carrier-tuple lowering — over-refusal control for the Option<(&mut T, &mut U)> lane
//@ fixed-by: Fix B M2 carrier-tuple sort (#prophecy-slots)
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
//@
//@ The honest half of a4: the returned borrows ARE `x` and `y`, so their prophecies coincide with
//@ the parameters'. If this stops verifying, the carrier-tuple lowering has broken the
//@ prophecy plumbing for a shape that worked before it, or the fail-closed guard has grown teeth
//@ it should not have on tuple payloads.
//@ teeth: n/a — over-refusal control; verifies on the pre-M2 build (05e6373) and must keep
//@ teeth: verifying on the M2 build. Its value is that a4_carrier_tuple_inversion and this case
//@ teeth: are the SAME shape with opposite truth values: only a real prophecy separates them.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(match result {
    Some((a, b)) => ^a == ^x && ^b == ^y,
    None => true,
})]
pub fn pair_passthrough<'a>(
    x: &'a mut i32,
    y: &'a mut i32,
) -> Option<(&'a mut i32, &'a mut i32)> {
    Some((x, y))
}
