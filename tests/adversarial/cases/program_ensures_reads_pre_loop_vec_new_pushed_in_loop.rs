//@ expect: reject
//@ mechanism: `let mut v = Vec::new()` before an annotated loop whose body pushes onto `v` through the
//@ mechanism: two-phase `&mut` of `push`; the function returns `v` and claims it is empty. The block-slice
//@ mechanism: walker (`collect_call_effects_for_blocks`) states `Vec::new`'s postcondition `v@ == Seq::empty()`
//@ mechanism: about the bare name `v`, the function-level path reads the returned `v` as that same name after
//@ mechanism: the loop, and the loop's writes through the loan did not retire the premise. The `Vec` spelling of
//@ mechanism: program_ensures_reads_pre_loop_call_result_written_through_loan_in_loop.rs, found probing sideways.
//@ accept-means: a function that returns a vector of length `n` is credited with returning an empty one, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `go(1)` returns `[0]`, whose length is 1.
//@ teeth: MEASURED ACCEPTED, exit 0, before D-243; `unknown` with D-243.
//@ fixed-by: D-243 (a call's postcondition is not a premise of a slice that runs after a later loop that may
//@ fixed-by: change a name it speaks of, directly or through a loan).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ < 1000)]
#[ensures(result@.len() == 0)]
pub fn go(n: u32) -> Vec<u32> {
    let mut v = Vec::new();
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n {
        v.push(i);
        i += 1;
    }
    v
}
