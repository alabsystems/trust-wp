//@ expect: reject
//@ mechanism: the callee-contract spelling of imported_external_adt_path_call_read_as_logic_method_granted.rs:
//@ mechanism: a `#[trusted]` callee `g` claims `result == Option::from(s)` (`Some(s)` by Rust's reading,
//@ mechanism: with `Option` imported), and `caller` claims `result == None` for `g(s)`. Read in `g`'s scope
//@ mechanism: (`resolve_spec_clauses_in_scope`), the typed text resolver leaves a non-trait qualifier to the
//@ mechanism: scope resolver, whose `resolve_on_adt_path` answers a non-local type by `inherent_item`
//@ mechanism: alone, never a logic id; the spelling is left written, and the caller's encoder dispatches
//@ mechanism: it on `s`'s sort to the logic method `S::from` (`None`). At the campaign tip this branch was
//@ mechanism: built on the caller is refused (`__lfidU__from_N0_` was not resolved).
//@ fixed-by: D-212 — a method-style path call through a non-local type is refused
//@ fixed-by: (`resolve_on_adt_path`).
//@ accept-means: `caller` is credited with `result == None` for `g(s)`, which returns `Some(s)`.
//@ teeth: MEASURED: `caller verified ✓` beside `g trusted (skipped)` with the block-scope resolver
//@ teeth: (D-195..D-210), a per-function false credit; refused at the campaign tip. With D-212: refused
//@ teeth: (`caller error: ... was not resolved to one definition by the driver`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use core::option::Option;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct S;
impl S {
    #[logic(open)]
    pub fn from(self) -> Option<S> {
        pearlite! { None }
    }
}

#[trusted]
#[ensures(result == Option::from(s))]
pub fn g(s: S) -> Option<S> {
    Some(s)
}

// WRONG: `g` returns `Some(s)`.
#[ensures(result == None)]
pub fn caller(s: S) -> Option<S> {
    g(s)
}
