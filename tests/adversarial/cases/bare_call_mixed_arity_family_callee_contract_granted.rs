//@ expect: reject
//@ mechanism: bare_call_mixed_arity_family_imported_program_fn_granted.rs read at a CALL SITE. `g`'s
//@ mechanism: contract `result == m(s)` names the imported program function `prog::m` (0), and `g`
//@ mechanism: returns 0. A caller reads `g`'s contract as text resolved in `g`'s scope; the family
//@ mechanism: holds `S::m` (10) and the free `other::m(a, b)`, so the bare call is left under its
//@ mechanism: written name and the encoder dispatches it on `s`'s sort to `S::m`: `caller`, which
//@ mechanism: returns `g(s)` (0), is credited with `result == 10`. (`g` itself is refuted on the
//@ mechanism: same reading, which is why the crate does not exit 0.)
//@ fixed-by: D-200 — REFUSED: a bare call is method-style exactly where every definition of its
//@ fixed-by: arity is a method (`identity::dispatches_on_receiver`, the predicate the encoder's
//@ fixed-by: receiver dispatch asks), so the program function's call is spelled with the refusal
//@ fixed-by: marker instead of being left for the dispatch.
//@ accept-means: `caller` claims `result == 10` and returns 0; ACCEPTED means that credit is printed.
//@ teeth: MEASURED: `caller verified ✓` (and `g FAILED`) with D-199 in force.
//@ teeth: With D-200: REFUSED (`unknown`): `caller` errors on the unresolved marker `__lfidU__m`.
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
pub fn g(s: S) -> u32 {
    let _ = s;
    0
}

#[ensures(result == 10u32)]
pub fn caller(s: S) -> u32 {
    g(s)
}

pub fn use_it() -> u32 {
    m(S)
}
