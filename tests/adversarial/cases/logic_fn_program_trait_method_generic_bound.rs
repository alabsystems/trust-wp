//@ expect: reject
//@ mechanism: the generic-bound spelling of logic_fn_program_method_callee_builtin_name: `t.get(y)` on `t: T` with `T: Tr`, where the trait's PROGRAM method `get` requires `i@ < 10`. The callee-precondition walk never checks a method call against the program functions (D-120), and the encoder reads `get` as its own builtin, so nothing owes or refuses the call. rustc resolves it to `Tr::get`. Found probing sideways from D-120.
//@ accept-means: a logic function that calls a program trait method through a generic bound outside its precondition is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 10` the body calls `t.get(10)`, and `Tr::get` requires `i@ < 10`; Creusot admits no program function in a logic body at all.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[requires(i@ < 10)]
    fn get(&self, i: usize) -> usize;
}

#[logic]
#[ensures(true)]
pub fn caller<T: Tr>(t: T, y: usize) -> usize {
    t.get(y)
}
