//@ expect: reject
//@ mechanism: a BY-VALUE parameter pinned by its precondition and written inside a loop, then a
//@ mechanism: `proof_assert!` of its entry value after the loop (`#[requires(c == 0)]`, `while .. {
//@ mechanism: c = 5; .. } proof_assert!(c == 0)`), or inside the loop above the write. The
//@ mechanism: proof_assert lane reads the precondition, a fact about the ENTRY value under the same
//@ mechanism: name, beside the binding the loop leaves `c` with, and proves the assertion. Neither
//@ mechanism: withdrawal fires: D-140 counts a by-value parameter re-bound only when the assertion's
//@ mechanism: substitution names it by something other than itself, and D-38 asks only of a
//@ mechanism: by-reference parameter's pointee. The function's own lane injects a fail-closed
//@ mechanism: `false` for the same loop and stays unknown, so the credit and the obligation are judged
//@ mechanism: in two environments. The write may be direct, through a reborrow or through a tuple
//@ mechanism: holder; a callee handed `&mut c` is refused on the merge and on main. Found probing
//@ mechanism: D-140's withdrawal sideways while reviewing the merge of main's D-127..D-129.
//@ fixed-by: D-241: a write of the parameter's own storage that may run before the assertion (the loop's, by a back edge too) withdraws its entry facts.
//@ accept-means: an assertion about a parameter's entry value is credited `verified` after a loop
//@ accept-means: overwrote the parameter.
//@ WHY THE CONTRACT IS FALSE: every loop runs three times and stores 5 into `c`, so each assertion
//@ WHY THE CONTRACT IS FALSE: reads 5 (after the loop, or from the second iteration on).
//@ teeth: MEASURED on the debug driver of the merge of main's D-127..D-129 into the campaign and on
//@ teeth: both of its parents: each `proof_assert in creusot_test::<fn> verified` beside a function
//@ teeth: verdict of unknown, so the run is rejected with the assertion credited (TEETH LOST).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(c == 0i32)]
pub fn after_loop_direct(mut c: i32) {
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        c = 5i32;
        i += 1u32;
    }
    proof_assert!(c == 0i32);
}

#[requires(c == 0i32)]
pub fn after_loop_reborrow(mut c: i32) {
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        let r = &mut c;
        *r = 5i32;
        i += 1u32;
    }
    proof_assert!(c == 0i32);
}

#[requires(c == 0i32)]
pub fn after_loop_tuple_holder(mut c: i32) {
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        let t = (&mut c, 0i32);
        *t.0 = 5i32;
        i += 1u32;
    }
    proof_assert!(c == 0i32);
}

#[requires(c == 0i32)]
pub fn in_loop_above_the_write(mut c: i32) {
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        proof_assert!(c == 0i32);
        c = 5i32;
        i += 1u32;
    }
}
