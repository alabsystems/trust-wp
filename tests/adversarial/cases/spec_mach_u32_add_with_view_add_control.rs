//@ expect: verify
//@ mechanism: control: one clause applying `+` at `u32` and at `Int`. D-232 reads every operator of
//@ mechanism: one kind in a clause at one type, so the clause is refused, true as it is.
//@ WHY THE CONTRACT IS TRUE: *p < 100, so *p + 1 does not wrap, and its view is p@ + 1.
//@ xfail: the clause applies `+` to more than one type (Int, u32) and is refused (D-232).
//@ xfail-verdict: unknown
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*p < 100u32)]
#[ensures(^p == *p + 1u32 && (^p)@ == p@ + 1)]
pub fn inc_view(p: &mut u32) {
    *p += 1;
}
