//@ expect: verify
//@ mechanism: the TRUE twin of seq_eq_premise_equates_outside_range: identical except that the
//@ mechanism: claim is about the element INSIDE the equated prefix.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(s.len() == 2 && u.len() == 2 && s.subsequence(0, 1) == u.subsequence(0, 1))]
#[ensures(s[0] == u[0])]
pub fn f(s: Ghost<Seq<Int>>, u: Ghost<Seq<Int>>) {}
