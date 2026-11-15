// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `old(e)` over a parameter that is no `&mut`: the parameter is one value in
//! every state, so each clause below reads `v` itself.

#![allow(unused)]

use trust_wp::prelude::*;

// TRUE.
#[requires(v@ < 1000)]
#[ensures(result@ == old(v@) + 1)]
pub fn old_of_a_view(v: u32) -> u32 {
    v + 1
}

// TRUE.
#[requires(v@ < 1000)]
#[ensures(result@ == old(v@ + 1))]
pub fn old_of_a_sum(v: u32) -> u32 {
    v + 1
}

// TRUE.
#[requires(v@ < 1000)]
#[ensures(forall<i: Int> i == 1 ==> result@ == old(v@ + i))]
pub fn old_under_a_quantifier(v: u32) -> u32 {
    v + 1
}

// FALSE.
#[requires(v@ < 1000)]
#[ensures(forall<i: Int> i == 1 ==> result@ == old(v@ + i) + 1)]
pub fn old_under_a_quantifier_false(v: u32) -> u32 {
    v + 1
}

fn main() {}
