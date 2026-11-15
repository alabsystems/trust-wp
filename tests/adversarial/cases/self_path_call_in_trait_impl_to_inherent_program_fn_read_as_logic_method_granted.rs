//@ expect: reject
//@ mechanism: self_path_call_to_program_assoc_fn_read_as_logic_method_granted.rs in a TRAIT impl: in
//@ mechanism: `impl Tr for U`, `Self::m(s)` is `U`'s inherent PROGRAM function `m` (0). `resolve_self_item`
//@ mechanism: looks only at the enclosing trait impl, finds no `m` there and answers "unresolved"; the
//@ mechanism: call is left under its written name and the encoder dispatches it on `s`'s sort to the
//@ mechanism: logic method `S::m` (10).
//@ fixed-by: D-210 — a method-style `Self::m` call `resolve_self_item` does not resolve to a logic
//@ fixed-by: definition is refused (`resolve_call_name_unchecked`).
//@ accept-means: `<U as Tr>::g` claims `result == Self::m(s)` (0 by Rust's reading), returns 10, and the
//@ accept-means: crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`<U as Tr>::g verified ✓`) with the block-scope resolver
//@ teeth: (D-195..D-209) and at the campaign tip it was built on alike. With D-210: refused
//@ teeth: (`<U as Tr>::g error: ... was not resolved to one definition by the driver`).
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

pub trait Tr {
    fn g(s: S) -> u32;
}

impl Tr for U {
    // WRONG: `Self::m` is `U`'s inherent program function (0).
    #[ensures(result == Self::m(s))]
    fn g(s: S) -> u32 {
        let _ = s;
        10
    }
}
