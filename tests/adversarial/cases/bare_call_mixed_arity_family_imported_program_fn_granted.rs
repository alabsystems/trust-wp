//@ expect: reject
//@ mechanism: the module-scope spelling of bare_call_mixed_arity_family_block_program_fn_granted.rs:
//@ mechanism: the crate root imports the program function `prog::m` (0), so Rust reads the bare
//@ mechanism: `m(s)` in `f`'s contract as that function. The family holds the method `S::m` (10)
//@ mechanism: and the free logic function `other::m(a, b)`, so the resolver reads the call as a free
//@ mechanism: one, finds the import, which is no logic definition, and leaves the call under its
//@ mechanism: written name; the encoder dispatches it on `s`'s sort to `S::m` and `f`, which returns
//@ mechanism: 10, is credited.
//@ fixed-by: D-200 — REFUSED: a bare call is method-style exactly where every definition of its
//@ fixed-by: arity is a method (`identity::dispatches_on_receiver`, the predicate the encoder's
//@ fixed-by: receiver dispatch asks), so the program function's call is spelled with the refusal
//@ fixed-by: marker instead of being left for the dispatch.
//@ accept-means: `f` claims `result == m(s)` with Rust's `m` the imported program function (0),
//@ accept-means: returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-199 in force.
//@ teeth: With D-200: REFUSED (`unknown`): `f` errors on the unresolved marker `__lfidU__m`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;
impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

pub mod other {
    use crate::S;
    use creusot_std::prelude::*;

    #[logic(open)]
    pub fn m(_a: S, _b: S) -> u32 {
        pearlite! { 5u32 }
    }
}

pub mod prog {
    use crate::S;

    pub fn m(_x: S) -> u32 {
        0
    }
}
use prog::m;

#[ensures(result == m(s))]
pub fn f(s: S) -> u32 {
    let _ = s;
    10
}

pub fn use_it() -> u32 {
    m(S)
}
