//@ expect: reject
//@ also-verified: host
//@ mechanism: bare_call_block_program_fn_read_as_logic_method_granted.rs with a free logic function
//@ mechanism: `other::m(a, b)` of another arity in the family. `inner`'s contract writes the bare call
//@ mechanism: `m(s)`, which Rust resolves to the program function `m` of `host`'s block (0). The
//@ mechanism: resolver takes a bare call for a method-style one only when EVERY member of the family
//@ mechanism: is a method; with `other::m` in it, it reads `m(s)` as a free call, finds the block's
//@ mechanism: program function, which is no logic definition, and leaves the call under its written
//@ mechanism: name. The encoder's receiver dispatch asks only whether every member OF THE CALL'S
//@ mechanism: ARITY is a method, which holds (`S::m`), and reads `m(s)` as `S::m(s)` (10): `inner`,
//@ mechanism: which returns 10, is credited. `host` claims nothing.
//@ fixed-by: D-200 — REFUSED: a bare call is method-style exactly where every definition of its
//@ fixed-by: arity is a method (`identity::dispatches_on_receiver`, the predicate the encoder's
//@ fixed-by: receiver dispatch asks), so the program function's call is spelled with the refusal
//@ fixed-by: marker instead of being left for the dispatch.
//@ accept-means: `inner` claims `result == m(s)` with Rust's `m` the block's program function (0),
//@ accept-means: returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`) with D-199 in force.
//@ teeth: With D-200: REFUSED (`unknown`): `host::inner` errors on the unresolved marker `__lfidU__m`.
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

pub fn host() -> u32 {
    fn m(_x: S) -> u32 {
        0
    }
    #[ensures(result == m(s))]
    fn inner(s: S) -> u32 {
        let _ = s;
        10
    }
    let _ = m(S);
    inner(S)
}
