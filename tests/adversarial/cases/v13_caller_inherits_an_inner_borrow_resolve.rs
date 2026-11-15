//@ expect: reject
//@ mechanism: `resolve(x.m)` of `x: &mut M` was read as `(*x).m == (^x).m`, the claim that the outer
//@ mechanism: borrow left the field `m` (itself a borrow) unchanged, true of an empty body, where
//@ mechanism: `resolve(x.m)` states that the INNER borrow `x.m` is resolved. Its caller then wrote 5
//@ mechanism: through that borrow after the call, and the write, made through a borrow the struct
//@ mechanism: holds, never reached the borrowed local: the returned `a` kept its value 3.
//@ accept-means: `struct_inner` is credited with a claim about a borrow its caller keeps, and
//@ accept-means: `struct_exploit`, which writes 5 through that borrow after the call, is credited
//@ accept-means: with `result == 3`.
//@ WHY THE CONTRACT IS FALSE: `m.m` borrows `a`; after `struct_inner(&mut m)` the caller writes 5
//@ WHY THE CONTRACT IS FALSE: through it, so the inner borrow's final value is 5 while its value at
//@ WHY THE CONTRACT IS FALSE: the call is 3, and `struct_exploit` returns 5.
//@ fixed-by: D-127 (the resolve of a value held through a variable is refused; a read of a local a
//@ fixed-by: holder's borrow may have written is stale and fails closed)
//@ teeth: MEASURED (debug driver): before D-127 both functions verified; D-127 refuses both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

#[ensures(resolve(x.m))]
pub fn struct_inner(x: &mut M<'_>) {}

#[ensures(result == 3i32)]
pub fn struct_exploit() -> i32 {
    let mut a = 3i32;
    let mut m = M { m: &mut a };
    struct_inner(&mut m);
    *m.m = 5;
    a
}
