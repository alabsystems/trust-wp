//@ expect: reject
//@ mechanism: loop variant over a name a macro's `let mut $n` rebinds (D-239). The variant lane
//@ mechanism: resolves its names at the loop header (D-238), with the hygiene of the binding's
//@ mechanism: pattern span; `mut` carries the macro's hygiene, so the caller's `n` was read as the
//@ mechanism: parameter (5), under which `n@ - i@` decreases and stays non-negative.
//@ accept-means: a variant is checked about a binding the caller's `n` does not denote there.
//@ WHY THE CONTRACT IS FALSE: after bind_mut!(n), n is 0, so the variant `n@ - i@` is -1 after the
//@ WHY THE CONTRACT IS FALSE: first iteration: it is not bounded below.
//@ fixed-by: D-239
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): VERIFIED on 62994450 (D-238);
//@ teeth: FAILED with D-239.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

macro_rules! bind_mut {
    ($n:ident) => {
        let mut $n = 0u32;
        $n += 0;
    };
}

#[requires(n@ == 5)]
pub fn vm1(n: u32) {
    bind_mut!(n);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    #[variant(n@ - i@)]
    while i < 3 {
        i += 1;
    }
}
