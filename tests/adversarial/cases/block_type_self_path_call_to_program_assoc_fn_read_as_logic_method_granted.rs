//@ expect: reject
//@ mechanism: self_path_call_to_program_assoc_fn_read_as_logic_method_granted.rs with the type and its
//@ mechanism: impl declared in a function's block: `Self::m(s)` in `host::U::g`'s `ensures` is `U`'s PROGRAM
//@ mechanism: function `m` (0). D-195's block scopes are not consulted for a `Self` prefix (it names the
//@ mechanism: enclosing impl's type); `resolve_self_item` gets no logic id for `U::m` and answers
//@ mechanism: "unresolved", and the encoder dispatches the written call on `s`'s sort to `S::m` (10).
//@ fixed-by: D-210 — a method-style `Self::m` call `resolve_self_item` does not resolve to a logic
//@ fixed-by: definition is refused (`resolve_call_name_unchecked`).
//@ accept-means: `host::U::g` claims `result == Self::m(s)` (0 by Rust's reading), returns 10, and the
//@ accept-means: crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::U::g verified ✓`) with the block-scope resolver
//@ teeth: (D-195..D-209) and at the campaign tip it was built on alike. With D-210: refused
//@ teeth: (`host::U::g error: ... was not resolved to one definition by the driver`).
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

pub fn host() -> u32 {
    struct U;
    impl U {
        fn m(_x: S) -> u32 {
            0
        }
        // WRONG: `Self::m` is `U`'s program function (0).
        #[ensures(result == Self::m(s))]
        fn g(s: S) -> u32 {
            let _ = s;
            10
        }
    }
    U::g(S)
}
