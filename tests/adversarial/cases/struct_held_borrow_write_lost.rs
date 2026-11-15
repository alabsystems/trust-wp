//@ expect: reject
//@ mechanism: a `&mut` stored in a struct field (`let h = H { p: &mut x }; *h.p = 7;`): moving the borrow into an aggregate records no borrow-chain edge, so the write through the field reaches neither `h.p` nor `x` and the borrowed place keeps its entry value. Any container that carries a `&mut` — not just a second local — breaks the write-back.
//@ fixed-by: 7bb3a696 — the resolver reads the borrow back out of the aggregate constructor.
//@ accept-means: a `&mut` handed to a data structure stops writing to its pointee as far as the verifier is concerned, which covers every borrow-holding wrapper type a user can write.
//@ WHY THE PROGRAM IS WRONG: `h.p` is `&mut x`; `*h.p = 7` sets `x` to 7, and the assertion claims 5.
//@ teeth: CLOSED. The case now rejects and its control verifies, so the borrow is followed into and out of the aggregate in both directions.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub struct H<'a> {
    pub p: &'a mut i32,
}

pub fn k() {
    let mut x = 5i32;
    let h = H { p: &mut x };
    *h.p = 7;
    proof_assert!(x == 5i32);
}
