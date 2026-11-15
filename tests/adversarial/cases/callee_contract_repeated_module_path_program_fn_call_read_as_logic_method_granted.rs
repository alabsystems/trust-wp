//@ expect: reject
//@ mechanism: a `#[trusted]` callee's contract writes the module path `a::m(s)` TWICE in one clause,
//@ mechanism: where `a::m` is a program function (0) and every local logic `m` is a method (`S::m`,
//@ mechanism: 10). The scope resolver refuses each occurrence (D-196: a local module's `m` is a logic
//@ mechanism: function or nothing), and D-208 (4) spells each refusal with its own per-call marker
//@ mechanism: (`refused_call_marker`). `resolve_clause_text_in_scope` rewrites a written name in the
//@ mechanism: callee's TEXT only when every occurrence of it resolved to ONE outcome; two distinct
//@ mechanism: markers are two outcomes, so the text keeps `a::m(s)` as written, and the caller's
//@ mechanism: encoder dispatches it on `s`'s sort to `S::m` (10). `caller`, which returns `g(s)`, is
//@ mechanism: credited with `result == 10`. With one occurrence the marker replaces the call and the
//@ mechanism: caller is refused (callee_contract_module_path_program_fn_call_refused.rs): the twins
//@ mechanism: differ in the repeated disjunct alone.
//@ fixed-by: D-209 — a spelling refused at one occurrence of a callee's text is refused at every one (`resolve_clause_text_in_scope`).
//@ accept-means: `caller` claims `result == 10` and returns `g(s)`, which Rust's reading of `g`'s
//@ accept-means: trusted contract makes 0; ACCEPTED means that credit is printed.
//@ teeth: MEASURED at wp-s139 236a48a4: `caller verified ✓` (`g` trusted); the one-occurrence twin is
//@ teeth: refused there (`__lfidU__m_N.._` not resolved). At the campaign tip 2d7d2634 both are
//@ teeth: refused: there the text resolver typed the call on `s` and rustc's confirmation of the
//@ teeth: written path refused each occurrence in the text itself.
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

pub mod a {
    pub fn m(_x: super::S) -> u32 {
        0
    }
}

#[trusted]
#[ensures(result == a::m(s) || result == a::m(s))]
pub fn g(s: S) -> u32 {
    a::m(s)
}

// WRONG: `g(s)` is `a::m(s)`, 0.
#[ensures(result == 10u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}
