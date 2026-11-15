//@ expect: reject
//@ mechanism: `resolve(e)` of an `e` whose type holds no borrow is `true` (Creusot's resolve, the
//@ mechanism: by-value reading of #2683). `encode_resolve` stripped the `*` of `resolve(*x)` and read
//@ mechanism: the resolve of the borrow `x` (`*x == ^x`), and read `resolve(x.a)` as
//@ mechanism: `(*x).a == (^x).a`: a claim STRONGER than `true`, harmless where it is proved and false
//@ mechanism: where it is negated. `!resolve(*x)` of a body writing a new value became `*x != ^x`.
//@ accept-means: a function is credited with `!true` (or `true ==> false`) about an integer.
//@ WHY THE CONTRACT IS FALSE: `*x` and `x.a` are integers; their resolve is `true` in every run,
//@ WHY THE CONTRACT IS FALSE: so `!resolve(..)` is `false` and `resolve(*x) ==> *x == 7` is
//@ WHY THE CONTRACT IS FALSE: `*x == 7`, which the precondition excludes.
//@ fixed-by: D-127 (`resolve` of a value held through a variable is refused, not read as its
//@ fixed-by: holder's)
//@ teeth: MEASURED (debug driver): before D-127 neg_deref, imp_deref and neg_field verified; D-127
//@ teeth: refuses each.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub a: i32,
    pub b: i32,
}

#[requires(*x != 5i32)]
#[ensures(!resolve(*x))]
pub fn neg_deref(x: &mut i32) {
    *x = 5;
}

#[requires(*x != 5i32 && *x != 7i32)]
#[ensures(resolve(*x) ==> *x == 7i32)]
pub fn imp_deref(x: &mut i32) {
    *x = 5;
}

#[requires(x.a != 5i32)]
#[ensures(!resolve(x.a))]
pub fn neg_field(x: &mut S) {
    x.a = 5;
}
