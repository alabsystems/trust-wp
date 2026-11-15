//@ expect: reject
//@ verdict: unknown
//@ refused-with: std call can panic under a condition its spec cannot state
//@ mechanism: `String::truncate` panics when the new length is not a char boundary, and so do
//@ mechanism: `String::insert`, `insert_str` and `remove` at a byte index off one. Their std specs
//@ mechanism: stated no precondition, and the char view cannot state a byte boundary, so each call
//@ mechanism: now refuses rather than being trusted.
//@ accept-means: a `String` edit at a byte index is trusted not to panic again.
//@ fixed-by: D-121 — a panic a std spec cannot state refuses the call.
//@ WHY THE CONTRACT IS FALSE: `"é"` is two bytes, and truncating it to one panics.
//@ teeth: rejected before the fix too, but by an ay solver panic while encoding `String::from`'s
//@ teeth: spec (TEETH LOST: a crash), MEASURED with the std spec tables reverted to the base; now a
//@ teeth: named refusal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f() -> usize {
    let mut s = String::from("é");
    s.truncate(1);
    s.len()
}
