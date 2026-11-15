//@ expect: reject
//@ mechanism: path_call_through_type_alias_to_program_assoc_fn_read_as_logic_method_granted.rs with
//@ mechanism: the alias declared in `host`'s block, around `inner` (D-195's block scopes): the block
//@ mechanism: lookup finds `type A = U;`, `path_target` maps the alias to no target, and the
//@ mechanism: unresolved prefix leaves `A::m(s)` under its written name for the encoder, which
//@ mechanism: dispatches it on `s`'s sort to `S::m` (10). Rust reads `U::m(s)`, `U`'s program
//@ mechanism: function.
//@ fixed-by: D-209 — the block alias is an unplaced prefix, refused (`resolve_call_name_unchecked`).
//@ accept-means: `inner` claims `result == A::m(s)` where Rust's `A::m` is `U`'s program function,
//@ accept-means: returns 10, and is credited on `S::m` (10); the crate exits 0.
//@ teeth: MEASURED at wp-s139 236a48a4 and at the campaign tip 2d7d2634: ACCEPTED, exit 0
//@ teeth: (`host::inner verified ✓`).
//@ teeth: With D-209: refused (`host::inner error: ... __lfidU__.._N.._ was not resolved`).
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

pub fn host() -> u32 {
    type A = U;
    // WRONG: `A::m` is `U`'s program function, not `S::m`.
    #[ensures(result == A::m(s))]
    fn inner(s: S) -> u32 {
        let _ = s;
        10
    }
    inner(S)
}
