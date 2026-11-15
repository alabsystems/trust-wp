//@ expect: reject
//@ mechanism: isolating twin of `impl_law_proved_control`: `v(false)` is -1, so the impl's law `a.v() >= 0` is false and must be neither credited nor left live
//@ accept-means: an impl law was credited without its postcondition being proved
//@ verdict: error
//@ refused-with: <bool as Tr>::nonneg postcondition FAILED (logic postcondition)
//@ teeth: the pair differs only in `0` / `-1`; the control's law verifies and this one is refuted
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self) -> Int;
    #[logic(law)]
    #[ensures(a.v() >= 0)]
    fn nonneg(a: Self);
}

impl Tr for bool {
    #[logic(open)]
    fn v(self) -> Int {
        if self { 1 } else { -1 }
    }
    // WRONG: v(false) is -1.
    #[logic(open, law)]
    #[ensures(a.v() >= 0)]
    fn nonneg(a: Self) {}
}
