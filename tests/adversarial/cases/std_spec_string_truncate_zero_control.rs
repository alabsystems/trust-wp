//@ expect: verify
//@ xfail: the price of refusing `String::truncate`: 0 is a char boundary of every string, but the
//@ xfail: char view cannot state which byte indices are, so every call refuses (D-121).
//@ mechanism: the TRUE twin of std_spec_string_truncate_char_boundary_unmodelled, truncating to 0.
//@ mechanism: An XPASS here while the twin still rejects means a boundary became statable.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — measured `unknown`, the refusal its twin carries.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f() -> usize {
    let mut s = String::from("é");
    s.truncate(0);
    s.len()
}
