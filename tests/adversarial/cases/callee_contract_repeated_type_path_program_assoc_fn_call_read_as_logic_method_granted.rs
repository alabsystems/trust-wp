//@ expect: reject
//@ mechanism: callee_contract_repeated_module_path_program_fn_call_read_as_logic_method_granted.rs
//@ mechanism: through a local type's path: a `#[trusted]` callee's contract writes `U::m(s)` twice in
//@ mechanism: one clause, where `U::m(_x: S)` is `U`'s inherent PROGRAM associated function (0) and
//@ mechanism: every local logic `m` is a method (`S::m`, 10). `qualified_path_rewrite` leaves a local
//@ mechanism: type with an inherent item of the name to the scope resolver, which refuses each
//@ mechanism: occurrence (`resolve_on_adt_path`: the inherent item is not a logic definition) with
//@ mechanism: its own per-call marker; two markers are two outcomes, `resolve_clause_text_in_scope`
//@ mechanism: keeps `U::m(s)` as written, and the caller's encoder dispatches it on `s`'s sort to
//@ mechanism: `S::m` (10). The one-occurrence spelling is refused.
//@ fixed-by: D-209 — a spelling refused at one occurrence of a callee's text is refused at every one (`resolve_clause_text_in_scope`).
//@ accept-means: `caller` claims `result == 10` and returns `g(s)`, which Rust's reading of `g`'s
//@ accept-means: trusted contract makes 0; ACCEPTED means that credit is printed.
//@ teeth: MEASURED at wp-s139 236a48a4: `caller verified ✓` (`g` trusted). At the campaign tip
//@ teeth: 2d7d2634 refused (`__lfidU__m_N.._`): rustc's confirmation of the path refused it there.
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

#[trusted]
#[ensures(result == U::m(s) || result == U::m(s))]
pub fn g(s: S) -> u32 {
    U::m(s)
}

// WRONG: `g(s)` is `U::m(s)`, 0.
#[ensures(result == 10u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}
