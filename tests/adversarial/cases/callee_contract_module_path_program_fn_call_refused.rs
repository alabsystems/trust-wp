//@ expect: reject
//@ mechanism: one-occurrence twin of callee_contract_repeated_module_path_program_fn_call_read_as_logic_method_granted.rs:
//@ mechanism: a `#[trusted]` callee's contract writes the module path `a::m(s)` once, where `a::m` is a
//@ mechanism: program function (0) and every local logic `m` is a method (`S::m`, 10). The scope
//@ mechanism: resolver refuses it (D-196) and the text carries the refusal marker to the caller, whose
//@ mechanism: `result == 10` is refused, never credited on `S::m`.
//@ fixed-by: D-196 — a path through a local module names that module's function, a logic one or
//@ fixed-by: nothing (`Resolver::resolve_call_name_unchecked`, the `PathTarget::Module` arm).
//@ accept-means: `caller` claims `result == 10` and returns `g(s)`, which Rust's reading of `g`'s
//@ accept-means: trusted contract makes 0; ACCEPTED means that credit is printed.
//@ teeth: MEASURED at wp-s139 236a48a4 and at the campaign tip 2d7d2634: refused (`caller error:
//@ teeth: ... __lfidU__m_N.._ was not resolved`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;
impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

pub mod a {
    pub fn m(_x: super::S) -> u32 {
        0
    }
}

#[trusted]
#[ensures(result == a::m(s))]
pub fn g(s: S) -> u32 {
    a::m(s)
}

// WRONG: `g(s)` is `a::m(s)`, 0.
#[ensures(result == 10u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}
