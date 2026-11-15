//@ expect: verify
//@ mechanism: control for loop_exit_condition_later_loop_rewrites_counter: two
//@ mechanism: loops in sequence, the second never touching the first loop's counter, so the first
//@ mechanism: loop's `!(i < 10u32)` holds at the return and `result >= 10u32` is TRUE. The function
//@ mechanism: continuation after several loops carried no loop's exit condition and refuted this
//@ mechanism: with a model whose `i` was still below 10.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result >= 10u32)]
pub fn f() -> u32 {
    let mut i: u32 = 0;
    #[invariant(i <= 10u32)]
    while i < 10 { i += 1; }
    let mut j: u32 = 0;
    #[invariant(j <= 5u32)]
    while j < 5 { j += 1; }
    i
}
