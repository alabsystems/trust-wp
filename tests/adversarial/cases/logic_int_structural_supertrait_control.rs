//@ expect: verify
//@ mechanism: the TRUE twin of logic_int_supertrait_arithmetic_in_program_context_panics: `Int` given
//@ mechanism: to a function bounded by a method-less trait whose supertraits are `Ord` and `Copy`, whose
//@ mechanism: run-time bodies on `Int` are exact. Only a supertrait that runs `Int` arithmetic, or another
//@ mechanism: body that is not the logical one, is refused.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — verified before and after a method-less trait's supertraits are read as asked.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Ordered: Ord + Copy {}
impl<T: Ord + Copy> Ordered for T {}

#[ensures(result == x)]
pub fn keep<T: Ordered>(x: T) -> T {
    x
}

#[ensures(result)]
pub fn caller() -> bool {
    let k = keep(Int(5));
    k == Int(5)
}
