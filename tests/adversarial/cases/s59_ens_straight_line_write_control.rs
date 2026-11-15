//@ expect: verify
//@ mechanism: control: the loop is REMOVED, so the write to `*a` is straight-line and walked by the extraction; the entry fact `(*a)@ == 0` is still the value `r` holds and legitimately discharges the postcondition
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
#[ensures(result@ == 0)]
pub fn f(a: &mut u32) -> u32 { let r = *a; *a = 7; r }
