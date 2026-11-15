//@ expect: reject
//@ mechanism: a trait's DEFAULT method `g` claims `result@ == Self::m(self)`, where `m` is a logic method
//@ mechanism: of the same trait with a visible default body (0), and returns 0. At an abstract `Self` the
//@ mechanism: claim does not hold: `S` overrides `m` (10) and inherits `g`. `resolve_self_item` finds the
//@ mechanism: declaration `Tr::m`; `Resolver::resolve_call_name` withholds a declaration whose default body
//@ mechanism: is visible (`decl_has_visible_body`: an impl may override it) by answering "unresolved", so the
//@ mechanism: call is left under its written name `Self::m`, and the encoder reads it as the declaration's
//@ mechanism: definition, default body included. `Tr::g` is verified against `m`'s default, and `caller`
//@ mechanism: is credited through `g`'s contract at `S` (`m` is 10 there) although `s.g()` returns 0. The
//@ mechanism: spellings `self.m()`, `Tr::m(self)` and `<Self as Tr>::m(self)` are refused. Sibling:
//@ mechanism: trait_default_contract_zero_arity_self_path_reads_sibling_default_body_granted.rs.
//@ fixed-by: OPEN — committed RED rather than hidden. Closes where a declaration the resolver withholds is
//@ fixed-by: refused, never left under its written name for the encoder to read.
//@ accept-means: a trait default method is verified against a sibling's default body that an impl
//@ accept-means: overrides, and a caller is credited with `result@ == 10` for a call that returns 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`Tr::g verified ✓`, `caller verified ✓`) with the block-scope
//@ teeth: resolver (D-195..D-209) and at the campaign tip it was built on alike.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic(open)]
    fn m(self) -> Int
    where
        Self: Sized,
    {
        pearlite! { 0 }
    }

    // WRONG for an impl that overrides `m`.
    #[ensures(result@ == Self::m(self))]
    fn g(self) -> u32
    where
        Self: Sized,
    {
        0
    }
}

pub struct S;
impl Tr for S {
    #[logic(open)]
    fn m(self) -> Int {
        pearlite! { 10 }
    }
}

// WRONG: `S::g` is the default (0).
#[ensures(result@ == 10)]
pub fn caller(s: S) -> u32 {
    s.g()
}
