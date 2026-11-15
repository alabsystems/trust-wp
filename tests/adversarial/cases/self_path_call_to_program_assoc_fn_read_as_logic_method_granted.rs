//@ expect: reject
//@ mechanism: `Self::m(s)` in the `ensures` of `U::g`, an inherent method of `U`, whose `m` is a PROGRAM
//@ mechanism: associated function `m(_x: S) -> u32` (0). Every local logic `m` is a method (`S::m`, 10),
//@ mechanism: so the family dispatches on its receiver (`dispatches_on_receiver`). The `["Self", _]` arm of
//@ mechanism: `Resolver::resolve_call_name_unchecked` asks only `resolve_self_item`, which finds `U::m` in
//@ mechanism: the enclosing impl, gets no logic id for it (`id_for_def`) and answers "unresolved"; the call
//@ mechanism: is left under its written name, and the encoder dispatches it on `s`'s sort
//@ mechanism: (`resolve_family_by_receiver`) to `S::m` (10). D-209 refuses a method-style path call whose
//@ mechanism: prefix `resolve_prefix` cannot place; a `Self` prefix never reaches that check. Siblings:
//@ mechanism: self_path_call_in_trait_impl_to_inherent_program_fn_read_as_logic_method_granted.rs (in a
//@ mechanism: trait impl) and block_type_self_path_call_to_program_assoc_fn_read_as_logic_method_granted.rs
//@ mechanism: (a type declared in a block).
//@ fixed-by: D-210 — a method-style `Self::m` call `resolve_self_item` does not resolve to a logic
//@ fixed-by: definition is refused (`resolve_call_name_unchecked`).
//@ accept-means: `U::g` claims `result == Self::m(s)` (0 by Rust's reading, a program call Creusot refuses),
//@ accept-means: returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`U::g verified ✓`) with the block-scope resolver (D-195..D-209)
//@ teeth: and at the campaign tip it was built on alike. With D-210: refused (`U::g error: ... was not
//@ teeth: resolved to one definition by the driver`).
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
    // WRONG: `Self::m` is `U`'s program function (0).
    #[ensures(result == Self::m(s))]
    pub fn g(s: S) -> u32 {
        let _ = s;
        10
    }
}
