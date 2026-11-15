//@ expect: reject
//@ mechanism: a `PtrToPtr` cast to a custom unsized pointee (a struct with a slice tail) keeps the
//@ mechanism: length, which the classifier does not read as the identity or `thin`. Left
//@ mechanism: untranslated, each cast was bound to its source name, which the shadowing `let a`
//@ mechanism: shares, so `x` (the first `a`) and the second `a` were one symbol and equal. The
//@ mechanism: cast is its type pair's uninterpreted function of the operand instead.
//@ fixed-by: D-145
//@ accept-means: two casts of unrelated pointers bound to one shadowed name are read as one value.
//@ WHY THE CONTRACT IS FALSE: `f(p, q)` with `p` and `q` at different addresses compares two
//@ WHY THE CONTRACT IS FALSE: different pointers and returns false.
//@ teeth: ACCEPTED under the draft of D-145 that left a cast of neither kind untranslated (probe
//@ teeth: pK-draft), where raw_ptr_cast_to_custom_dst_congruence_control did not verify; rejected
//@ teeth: at the merge base (the identity reads `x == a` as `p == q`, unproved).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct D {
    pub n: u8,
    pub tail: [u8],
}

#[ensures(result)]
pub fn f(p: *const [u8], q: *const [u8]) -> bool {
    let a = p as *const D;
    let x = a;
    let a = q as *const D;
    x == a
}
