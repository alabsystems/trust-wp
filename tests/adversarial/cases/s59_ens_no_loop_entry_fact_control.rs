//@ expect: verify
//@ mechanism: control: no loop at all, so the entry fact about `*a` is exactly the current value and legitimately discharges the postcondition
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(a: &mut u32) -> u32 { *a }
