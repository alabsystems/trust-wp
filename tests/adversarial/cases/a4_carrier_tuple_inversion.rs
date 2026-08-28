//@ expect: reject
//@ mechanism: Final-collapse prophecy inversion on a CARRIER-TUPLE payload (Option<(&mut T, &mut U)>)
//@ fixed-by: 932a7de (Fix A); lowering by the Fix B M2 carrier-tuple sort (#prophecy-slots)
//@ accept-means: `^a`/`^b` were collapsed onto `*a`/`*b` for the tuple payload of an Option — the
//@ accept-means: sibling-binder shape `split_first_mut` returns. That is the take_first_mut
//@ accept-means: inversion class, reached through the tuple lane instead of the direct payload.
//@
//@ THE CLASS THIS COVERS: before Fix B M2 the tuple payload of an `Option` punned onto the single
//@ global `Uninterpreted("Tuple2")` sort and its positional getters ranged over `Int`, so the
//@ `&mut` elements had no prophecy slot at all. M2 lowers them at the mutref record sort; this
//@ case is the standing gate that the lowering did not also make the inversion PROVABLE.
//@
//@ WHY THE CONTRACT IS FALSE: `caller` writes 9 through the first returned borrow while `*a` is 7.
//@ teeth: VERIFIED PRE/POST. Rejected on the pre-M2 build (05e6373, `unknown (incomplete)`) and
//@ teeth: rejected on the M2 build — the lowering does not open an accept route. Shape gate for the
//@ teeth: carrier-tuple class, which had NO coverage in either corpus before this case.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(match result {
    Some((a, b)) => ^a == *a && ^b == *b,
    None => true,
})]
pub fn pair_inverted<'a>(x: &'a mut i32, y: &'a mut i32) -> Option<(&'a mut i32, &'a mut i32)> {
    *x = 7;
    Some((x, y))
}

// The refutation, in executable Rust: after this call `*a` is 7 and `^a` is 9.
pub fn caller() {
    let mut v = 0i32;
    let mut w = 1i32;
    if let Some((a, _b)) = pair_inverted(&mut v, &mut w) {
        *a = 9;
    }
}
