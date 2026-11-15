//@ expect: reject
//@ mechanism: `Option::from(s)` in `g`'s `ensures`, with `Option` imported explicitly
//@ mechanism: (`use core::option::Option;`), so `resolve_prefix` places it (`PathTarget::Adt`), beside a local
//@ mechanism: logic method `S::from` returning `None`. Rust reads the path as `<Option<S> as From<S>>::from`,
//@ mechanism: the standard library's PROGRAM function (`Some(s)`). `Resolver::resolve_on_adt_path` answers
//@ mechanism: a non-local type by `inherent_item` alone, whose `id_for_def` is `None` for every non-local
//@ mechanism: definition, so the call is "unresolved" and left under its written name; the encoder
//@ mechanism: dispatches it on `s`'s sort to `S::from` (`None`). Without the import the prefix is unplaced
//@ mechanism: and D-209 refuses the call.
//@ fixed-by: D-212 — a method-style path call through a non-local type is refused
//@ fixed-by: (`resolve_on_adt_path`).
//@ accept-means: `g` claims `result == Option::from(s)` (`Some(s)` by Rust's reading), returns `None`, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`g verified ✓`) with the block-scope resolver (D-195..D-209) and at
//@ teeth: the campaign tip it was built on alike. With D-212: refused (`g error: ... was not resolved to
//@ teeth: one definition by the driver`).
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

// WRONG: `Option::from(s)` is `Some(s)`.
#[ensures(result == Option::from(s))]
pub fn g(s: S) -> Option<S> {
    let _ = s;
    None
}
