//@ expect: reject
//@ mechanism: a `proof_assert!` inside a loop body, ABOVE a write to a local later in the same body:
//@ mechanism: `while i < 3 { proof_assert!(c == 0); c = 5; i += 1; }`. From the second iteration on
//@ mechanism: the assertion reads what the previous iteration wrote, but the proof_assert lane reads
//@ mechanism: `c` at its value from before the loop: a local the loop writes and the invariant does
//@ mechanism: not name is not re-bound at the loop head for an assertion in the body. Every loop
//@ mechanism: form is affected (an annotated `while`, an unannotated one, `loop` with `break`), in a
//@ mechanism: contracted host and a contract-free one, and so is a write through a tuple or struct
//@ mechanism: holder of `&mut c`: D-129 takes the lanes to follow a holder's store, which they do on
//@ mechanism: the straight path into the assertion but not across the back edge, so its stale-read
//@ mechanism: refusal never fires here. Found probing D-129's followed-holder exemption sideways; the
//@ mechanism: direct-write spelling shows the defect is the in-loop assertion's state, not the holder.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means an assertion inside a loop
//@ fixed-by: reads every local the loop body may write at a value the loop head leaves unconstrained
//@ fixed-by: except by the invariant, as the loop's own preservation check does.
//@ accept-means: an assertion that is false from the second iteration on is credited in every
//@ accept-means: function, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: every loop runs three times and writes `c` after the assertion, so the
//@ WHY THE CONTRACT IS FALSE: second iteration asserts `c == 0` (or `c == 0u32`) of a `c` that is 5,
//@ WHY THE CONTRACT IS FALSE: or 1 for `partner_written`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the debug driver of the merge of main's D-127..D-129 into the
//@ teeth: campaign and on both of its parents: each function `verified` and each
//@ teeth: `proof_assert in creusot_test::<fn> verified`. A write through a reborrow (`let r = &mut c;
//@ teeth: *r = 5`) or a `c += 1` in the same place leaves the assertion credited too, with the
//@ teeth: function refuted on another obligation. A write by a callee handed `&mut c` is refused on
//@ teeth: the merge and on main, and its assertion is credited on the campaign parent.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub fn direct_write() {
    let mut c = 0i32;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        proof_assert!(c == 0i32);
        c = 5i32;
        i += 1u32;
    }
}

#[requires(true)]
#[ensures(true)]
pub fn contracted_direct_write() {
    let mut c = 0i32;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        proof_assert!(c == 0i32);
        c = 5i32;
        i += 1u32;
    }
}

pub fn unannotated_loop() {
    let mut c = 0i32;
    let mut i = 0u32;
    while i < 3u32 {
        proof_assert!(c == 0i32);
        c = 5i32;
        i += 1u32;
    }
}

pub fn loop_with_break() {
    let mut c = 0i32;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    loop {
        proof_assert!(c == 0i32);
        c = 5i32;
        i += 1u32;
        if i >= 3u32 {
            break;
        }
    }
}

pub fn partner_written() {
    let mut c = 0u32;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        proof_assert!(c == 0u32);
        c = i + 1u32;
        i += 1u32;
    }
}

pub fn tuple_holder_write() {
    let mut c = 0i32;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        proof_assert!(c == 0i32);
        let t = (&mut c, 0i32);
        *t.0 = 5i32;
        i += 1u32;
    }
}

pub fn struct_holder_write() {
    let mut c = 0i32;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        proof_assert!(c == 0i32);
        let h = M { m: &mut c };
        *h.m = 5i32;
        i += 1u32;
    }
}
