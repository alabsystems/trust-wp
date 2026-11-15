//@ expect: reject
//@ mechanism: path_call_through_type_alias_to_program_assoc_fn_read_as_logic_method_granted.rs in a
//@ mechanism: callee's contract TEXT: `g` is `#[trusted]` and claims `result == A::m(s)` with
//@ mechanism: `type A = U;`, which Rust reads as `U::m(s)`, `U`'s program function (0), the value
//@ mechanism: `g` returns. The text resolvers leave the call written (`qualified_path_rewrite`
//@ mechanism: answers `None` for a qualifier that is neither a trait nor a type, and the scope
//@ mechanism: resolver's `resolve_prefix` does not place an alias), and the caller's encoder
//@ mechanism: dispatches `A::m(s)` on `s`'s sort to `S::m` (10): `caller`, which returns `g(s)`,
//@ mechanism: is credited with `result == 10`.
//@ fixed-by: D-209 — the scope resolver refuses the alias prefix in `g`'s text too, and the marker replaces the call.
//@ accept-means: `caller` claims `result == 10` and returns `g(s)`, which Rust's reading of `g`'s
//@ accept-means: trusted contract makes 0; ACCEPTED means that credit is printed.
//@ teeth: MEASURED at wp-s139 236a48a4: `caller verified ✓` (`g` trusted). At the campaign tip
//@ teeth: 2d7d2634 refused (`__lfidU__m_N.._`): there the text resolver typed the call on `s` and
//@ teeth: rustc's confirmation of the written path refused it.
//@ teeth: With D-209: refused (`caller error: ... __lfidU__.._N.._ was not resolved`).
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

pub struct U;
impl U {
    pub fn m(_x: S) -> u32 {
        0
    }
}

pub type A = U;

#[trusted]
#[ensures(result == A::m(s))]
pub fn g(s: S) -> u32 {
    U::m(s)
}

// WRONG: `g(s)` is `U::m(s)`, 0.
#[ensures(result == 10u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}
