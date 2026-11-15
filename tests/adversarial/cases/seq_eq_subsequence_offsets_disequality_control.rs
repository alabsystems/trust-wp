//@ expect: verify
//@ xfail: proof-trusted: ay answers UNSAT but produces no strictly certified proof, so the verdict
//@ xfail: is withheld. A fix that compares elements must make this TRUE twin verify.
//@ mechanism: the TRUE twin of seq_eq_subsequence_offsets_disequality: identical except that
//@ mechanism: the precondition makes the first elements differ, so the subsequences do.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(s.len() == 3 && s[0] != s[1])]
#[ensures(s.subsequence(1, 3) != s.subsequence(0, 2))]
pub fn f(s: Ghost<Seq<Int>>) {}
