//@ expect: reject
//@ mechanism: the requires-only spelling of logic_fn_program_method_callee_builtin_name. D-119 credits a logic function with no `ensures` once the body goals the walk states are proved, and binds the body so that a construct the encoder refuses is refused here too; a program method spelled like an encoder built-in (`s.get(y)`) is neither refused by the encoder nor owed by the walk, so the credit stands on `needs_pos(1)` alone. Before D-119 a requires-only logic function was not examined at all; D-119 is what prints its `verified`.
//@ accept-means: a requires-only logic function that calls a program method outside its precondition is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 10` the body calls `s.get(10)`, and `S::get` requires `i@ < 10`; Creusot admits no program function in a logic body at all.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-119: `creusot_test::caller verified ✓` beside `S::get verified ✓`. The same body calling the aliased logic function `np(y)` in place of `s.get(y)` is refused (`logic callee precondition not proved`): the bound body does not encode.
//@ fixed-by: D-136
//@ also-verified: S::get
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

pub struct S {
    pub n: usize,
}

impl S {
    #[requires(i@ < 10)]
    #[ensures(result == i)]
    pub fn get(&self, i: usize) -> usize {
        i
    }
}

#[logic]
#[requires(true)]
pub fn caller(s: S, y: usize) -> Int {
    pearlite! { needs_pos(1) + s.get(y)@ }
}
