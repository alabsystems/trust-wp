//@ expect: verify
//@ mechanism: control: `old((*a)@)` is the ENTRY frame; a straight-line write to `*a` does not disturb it and the returned copy is genuinely that value
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == old((*a)@))]
pub fn f(a: &mut u32) -> u32 { let r = *a; *a = 7; r }
