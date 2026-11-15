//@ expect: verify
//@ mechanism: control for r31_loop_variant_macro_mut_ident.rs (D-239): the macro's `let mut $n`
//@ mechanism: binds the caller's `n` to 3, and the variant `n@ - i@` over that binding is
//@ mechanism: bounded and decreases.
//@ accept-means: n/a (control) - the variant decreases and stays non-negative.
//@ teeth: MEASURED: vacuous (error) on 62994450 (D-238), verified with D-239.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

macro_rules! bind_mut_to {
    ($n:ident, $e:expr) => {
        let mut $n = $e;
        $n += 0;
    };
}

#[requires(n@ == 5)]
pub fn vm2(n: u32) {
    bind_mut_to!(n, 3u32);
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    #[invariant(n@ == 3)]
    #[variant(n@ - i@)]
    while i < n {
        i += 1;
    }
}
