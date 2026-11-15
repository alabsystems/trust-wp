//@ expect: verify
//@ mechanism: control: `f` returns 0, the imported `Z`'s `k()`, the function its contract names.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; refuted before D-198, verified with it)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(result == 10)]
    fn k() -> Int;
}

pub struct Z;
impl Z {
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 0 }
    }
}

#[ensures(result@ == W::k())]
pub fn f<W: Tr>() -> u32 {
    use crate::Z as W;
    0
}
