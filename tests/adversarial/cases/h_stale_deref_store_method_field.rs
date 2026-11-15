//@ expect: reject
//@ mechanism: prophecy-store — method-call receiver after a FIELD store through bor
//@ accept-means: self.0@ == 0 discharged although bor.0 is 5
//@ teeth: verified on wp-s30 aae5ef9
//@ also-verified: S::need
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S(pub i32);

impl S {
    #[requires(self.0@ == 0)]
    pub fn need(&self) {}
}

#[requires(bor.0@ == 0)]
pub fn method_field(bor: &mut S) {
    bor.0 = 5;
    bor.need();
}
