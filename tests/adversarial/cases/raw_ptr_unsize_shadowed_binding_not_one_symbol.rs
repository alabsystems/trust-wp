//@ expect: reject
//@ mechanism: why a raw-pointer unsizing is a function and not left untranslated: an untranslated
//@ mechanism: right-hand side is bound to its source name, which the shadowing `let a` shares, so
//@ mechanism: `x` (the first `a`) and the second `a` became one symbol and were proved equal.
//@ fixed-by: D-145
//@ accept-means: two unsizings of unrelated pointers bound to one shadowed name are read as one value.
//@ WHY THE CONTRACT IS FALSE: `x` has length 4 and the second `a` length 8.
//@ teeth: ACCEPTED under a draft that left raw-pointer unsizing untranslated; rejected at the merge
//@ teeth: base (the identity reads `x == a` as `p == q`, unproved).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn f(p: *const [u8; 4], q: *const [u8; 8]) -> bool {
    let a: *const [u8] = p;
    let x = a;
    let a: *const [u8] = q;
    x == a
}
