//@ expect: reject
//@ mechanism: a `snapshot!` of a scalar local is read at the `proof_assert!` as the local's CURRENT
//@ mechanism: value, not its value when the snapshot was taken: after `let s = snapshot!(c); c = 5;`,
//@ mechanism: `proof_assert!(c == *s)` is proved and the true `proof_assert!(*s == 0u32)` is refuted.
//@ mechanism: The write may be a plain assignment, a write through a borrow, or drop glue: the snapshot
//@ mechanism: follows each. Found probing D-140's proof_assert spelling; not a drop defect.
//@ accept-means: a `proof_assert!` equating a local with its own snapshot is credited after the local
//@ accept-means: changed.
//@ WHY THE CONTRACT IS FALSE: at each assertion `c` is 5 and `*s` is 0.
//@ fixed-by: D-241: a `snapshot!` capture freezes the current value of the names it reads; D-129 still owns the drop-glue spelling.
//@ teeth: LIVE: ACCEPTED at D-140's head, all three assertions `verified`; with D-129 the
//@ teeth: `drop_glue` assertion is refused and `assign` and `write_through_borrow` stay `verified`.
//@ also-verified: <G<'_> as std::ops::Drop>::drop
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

pub fn assign() -> u32 {
    let mut c = 0u32;
    let s = snapshot!(c);
    c = 5;
    proof_assert!(c == *s);
    c
}

pub fn write_through_borrow() -> u32 {
    let mut c = 0u32;
    let s = snapshot!(c);
    {
        let r = &mut c;
        *r = 5;
    }
    proof_assert!(c == *s);
    c
}

pub fn drop_glue() -> u32 {
    let mut c = 0u32;
    let s = snapshot!(c);
    {
        let _g = G(&mut c);
    }
    proof_assert!(c == *s);
    c
}
