//@ expect: verify
//@ mechanism: control: a `#[variant]` logic fn over a machine-integer parameter carries that parameter's range among its `requires` (discovery guards its definition with it), but a caller owes only the written `requires` (`LogicFnDef::written_requires`), as Creusot's vcgen does; the range holds of every `u32` argument.
//@ accept-means: n/a (control) — `3 >= 0` is the only precondition written on `g`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(n >= 0)]
#[variant(n)]
pub fn g(n: Int, k: u32) -> Int {
    pearlite! { n + k@ }
}

#[logic]
#[ensures(true)]
pub fn caller(k: u32) -> Int {
    g(3, k)
}
