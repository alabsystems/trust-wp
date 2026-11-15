//@ expect: reject
//@ mechanism: the relacq message-passing post-loop lane built the fact `x == 1`, which is the
//@ mechanism: assertion below itself, by matching substrings of the source text, falling back to
//@ mechanism: the whole file when the function's span did not match, so the substrings in the
//@ mechanism: comments after this header matched (the lane also needed the file's first assertion
//@ mechanism: macro to follow them, so this header does not spell one); the fact was added after
//@ mechanism: any loop with exit facts, with no program point, dominance or written-since check
//@ mechanism: (D-190).
//@ accept-means: an assertion is assumed by a fact synthesised from comment text.
//@ WHY THE CONTRACT IS FALSE: with v = 0, x = 0.
//@ fixed-by: D-190 (the lane is deleted)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on a3819cee relp's assertion VERIFIED and relp was credited verified; with D-190 it FAILED.
// LoadCommitter .load(ghost!{ State::Synchronisation( data_own.val().val()@ == 1
// if !*snapshot!(c.val()).into_ghost() { return }
// perm = Ghost::new(Some(
// let x = unsafe { p.get(ghost!{perm.as_ref().unwrap()}) };
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 1000u32)]
pub fn relp(n: u32, v: i32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let x = v;
    proof_assert!(x == 1i32);
}
