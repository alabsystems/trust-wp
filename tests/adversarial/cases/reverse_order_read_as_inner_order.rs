//@ expect: reject
//@ mechanism: `std::cmp::Reverse<T>` orders its values opposite to `T`: its `lt` is `other.0 < self.0`.
//@ mechanism: The builtin `PartialOrd` contracts (`result == (self@ < rhs@)`, and the same for `<=`, `>`,
//@ mechanism: `>=`) run for a comparison whose type has library behaviour (`call_runs_builtin_semantics`
//@ mechanism: admits `<Reverse<i32> as PartialOrd>::lt`: `Reverse` is a library type and its bound
//@ mechanism: `i32: PartialOrd` is discharged by a primitive), and the comparison is then read as the
//@ mechanism: order of the inner values, so `Reverse(x) < Reverse(y)` is read as `x < y`. Every
//@ mechanism: operator, a `Reverse` built in the body or taken as a parameter, and a panic guarded by
//@ mechanism: the (true) comparison are read so. Measured rejected: `!=`, `cmp`, `partial_cmp`, `max`
//@ mechanism: and `Option<Reverse<i32>>`'s `<` over the same values. Not a float defect: found probing
//@ mechanism: sideways from D-215's withdrawal of the same builtin contracts from float comparisons.
//@ accept-means: `rev_lt(1, 2)` returns `false`, `rev_ge(1, 2)` returns `true`,
//@ accept-means: `rev_param_le(Reverse(1), Reverse(2))` returns `false`, and `rev_gt_panics(1, 2)` panics;
//@ accept-means: an accept claims the opposite of each.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a builtin comparison contract runs
//@ fixed-by: only for a type whose comparison orders its view as the contract states (`Reverse` does not),
//@ fixed-by: or `Reverse`'s comparisons state the inverted order, as Creusot's `OrdLogic for Reverse` does.
//@ teeth: ACCEPTED when committed (`rev_lt`, `rev_ge`, `rev_param_le` and `rev_gt_panics` each verified), and on
//@ teeth: the campaign tip: it predates D-215, which withdraws these contracts from floats only.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::cmp::Reverse;

#[requires(x@ < y@)]
#[ensures(result)]
pub fn rev_lt(x: i32, y: i32) -> bool {
    Reverse(x) < Reverse(y)
}

#[requires(x@ < y@)]
#[ensures(!result)]
pub fn rev_ge(x: i32, y: i32) -> bool {
    Reverse(x) >= Reverse(y)
}

#[requires(a.0@ < b.0@)]
#[ensures(result)]
pub fn rev_param_le(a: Reverse<u8>, b: Reverse<u8>) -> bool {
    a <= b
}

#[requires(x@ < y@)]
pub fn rev_gt_panics(x: i64, y: i64) {
    if Reverse(x) > Reverse(y) {
        panic!();
    }
}
