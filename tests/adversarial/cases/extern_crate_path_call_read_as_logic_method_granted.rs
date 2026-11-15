//@ expect: reject
//@ mechanism: path_call_through_type_alias_to_program_assoc_fn_read_as_logic_method_granted.rs through
//@ mechanism: a path into another crate: `core::convert::identity(s)` in `g`'s `ensures`, beside a
//@ mechanism: local logic method `S::identity` returning `S(10)`. Rust reads the standard program
//@ mechanism: function, `s` itself (`s.0 == 0` by `g`'s precondition), so the claim
//@ mechanism: `core::convert::identity(s) == S(10u32)` is false. `resolve_prefix` places no path off
//@ mechanism: `core` (it is no child of the module), the call is left under its written name, and the
//@ mechanism: encoder dispatches it on `s`'s sort to `S::identity`.
//@ fixed-by: D-209 — a path off `core` is an unplaced prefix, refused (`resolve_call_name_unchecked`).
//@ accept-means: `g` is credited with `core::convert::identity(s) == S(10u32)` under `s.0 == 0`, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED at wp-s139 236a48a4 and at the campaign tip 2d7d2634: ACCEPTED, exit 0
//@ teeth: (`g verified ✓`).
//@ teeth: With D-209: refused (`g error: ... __lfidU__.._N.._ was not resolved`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S(pub u32);
impl S {
    #[logic(open)]
    pub fn identity(self) -> S {
        pearlite! { S(10u32) }
    }
}

// WRONG: `core::convert::identity(s)` is `s`, whose field is 0.
#[requires(s.0 == 0u32)]
#[ensures(core::convert::identity(s) == S(10u32))]
pub fn g(s: S) {
    let _ = s;
}
