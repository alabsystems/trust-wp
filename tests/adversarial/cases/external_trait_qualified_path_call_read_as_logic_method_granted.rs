//@ expect: reject
//@ mechanism: `<u32 as From<S>>::from(s)` in `g`'s `ensures`, where the crate implements the standard
//@ mechanism: `From<S>` for `u32` as a PROGRAM function returning 0, beside a local logic method
//@ mechanism: `S::from` returning 10. `Resolver::resolve_qualified` places the trait path through the
//@ mechanism: module (`resolve_prefix`), finds no `From` there (the standard prelude is not a child of
//@ mechanism: the module) and answers "unresolved", which leaves the call under its written name; the
//@ mechanism: encoder dispatches it on `s`'s sort to `S::from` (10), whose per-member
//@ mechanism: `receiver_dispatch` counts methods only and never sees `From::from`. `g`, which returns
//@ mechanism: 10, is credited against a contract Rust reads as `result == 0`.
//@ fixed-by: OPEN — committed RED rather than hidden. Closes where a method-style qualified path call
//@ fixed-by: whose trait the resolver cannot place is refused, never left to the encoder's receiver
//@ fixed-by: dispatch.
//@ accept-means: `g` claims `result == <u32 as From<S>>::from(s)` (0 by Rust's reading), returns 10,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED at wp-s139 236a48a4 and at the campaign tip 2d7d2634: ACCEPTED, exit 0
//@ teeth: (`g verified ✓`); a `#[trusted]` callee's contract so spelled credits its caller at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;
impl S {
    #[logic(open)]
    pub fn from(self) -> u32 {
        pearlite! { 10u32 }
    }
}

impl From<S> for u32 {
    fn from(_x: S) -> u32 {
        0
    }
}

// WRONG: `<u32 as From<S>>::from(s)` is the program impl above, 0.
#[ensures(result == <u32 as From<S>>::from(s))]
pub fn g(s: S) -> u32 {
    let _ = s;
    10
}
