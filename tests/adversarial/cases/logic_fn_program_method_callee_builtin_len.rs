//@ expect: reject
//@ mechanism: the `len` spelling of logic_fn_program_method_callee_builtin_name, which D-120 records inside that case's mechanism: a program `len(&self)` requiring `self.n@ > 0`, called `s.len()` in a logic body. The encoder reads `len` as its builtin length and the callee-precondition walk never checks a method call against the program functions, so nothing owes or refuses the call.
//@ accept-means: a logic function that calls a program method outside its precondition is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `s.n == 0` the body calls `s.len()`, and `S::len` requires `self.n@ > 0`; Creusot admits no program function in a logic body at all.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓` beside `S::len verified ✓`. The control is logic_fn_program_method_builtin_len_seq_receiver_control.rs.
//@ fixed-by: D-136
//@ also-verified: S::len
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
#[ensures(true)]
pub fn caller(s: S) -> usize {
    s.len()
}
