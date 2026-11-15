//@ expect: reject
//@ mechanism: the callee-precondition walk refuses a logic call that may denote a program function with a precondition only for a path call (`ProgramFnsWithRequires`), on the ground that the encoder refuses a METHOD it does not know (logic_fn_requires_only_program_method_callee.rs, `prog_get`). A program method spelled like a method the encoder has a built-in reading for is not refused there: `s.get(y)` is read as the encoder's own `get`, the walk owes nothing for it, and the ensures lane proves `true`. The same file with a program `len(&self)` requiring `self.n@ > 0`, called as `s.len()`, is ACCEPTED the same way.
//@ accept-means: a logic function that calls a program method outside its precondition is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 10` the body calls `s.get(10)`, and `S::get` requires `i@ < 10`; Creusot admits no program function in a logic body at all.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-119: `creusot_test::caller verified ✓` beside `S::get verified ✓`.
//@ fixed-by: D-136
//@ also-verified: S::get
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

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
#[ensures(true)]
pub fn caller(s: S, y: usize) -> usize {
    s.get(y)
}
