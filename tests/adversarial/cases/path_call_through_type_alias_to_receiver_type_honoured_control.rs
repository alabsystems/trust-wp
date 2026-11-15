//@ expect: verify
//@ xfail: D-209's price — a method-style path call through an alias is refused even where the alias
//@ xfail: names the receiver's own type and Rust reads the logic method.
//@ mechanism: TRUE twin of path_call_through_type_alias_to_program_assoc_fn_read_as_logic_method_granted.rs:
//@ mechanism: `type A = S;`, so `A::m(s)` is `S::m(s)` (10), and `g` returns 10. The scope resolver
//@ mechanism: does not place an alias, so the call is refused rather than read through it.
//@ teeth: over-refusal control. MEASURED at the campaign tip 2d7d2634 (before D-209): verified, the
//@ teeth: encoder's receiver dispatch reading `A::m(s)` as `S::m(s)`, which here is Rust's reading too.
//@ teeth: With D-209: refused (`__lfidU__m_N.._` not resolved).
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

pub type A = S;

#[ensures(result == A::m(s))]
pub fn g(s: S) -> u32 {
    let _ = s;
    10
}
