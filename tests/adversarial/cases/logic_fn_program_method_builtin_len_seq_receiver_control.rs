//@ expect: verify
//@ mechanism: control for logic_fn_program_method_callee_builtin_len, differing in the receiver's type alone: the crate still has a program `S::len` with a precondition, and the logic body calls `len` on a `Seq`, which is the standard logic function. A fix that refuses every method spelled like a program function refuses this one; a fix that reads what rustc resolved the call to does not.
//@ accept-means: n/a (control) — `Seq::len` has no precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub n: usize,
}

impl S {
    #[requires(self.n@ > 0)]
    #[ensures(result == self.n)]
    pub fn len(&self) -> usize {
        self.n
    }
}

#[logic]
#[ensures(result == q.len())]
pub fn caller(q: Seq<Int>) -> Int {
    pearlite! { q.len() }
}
