//@ expect: reject
//@ mechanism: `g<T: Tr, U: Tr>` requires `<T as Tr>::m(a@) == <U as Tr>::m(a@)`, and `caller` calls `g::<&'static S, &'static V>(3)`, where `Tr` is implemented for `&S` (`x + 1`) and `&V` (`x`). The callee's clause carries one generic marker per qualified call, and each is instantiated at the call's type arguments (`identity_typed::instantiate_generic_markers`). The typed lookup reads a reference type at its pointee and finds no implementation for `S` or `V`, so both instantiations are refused. Every refusal was spelled with the one marker of the short name, `__lfidU__m`, so the precondition `caller` owes became `__lfidU__m(a@) == __lfidU__m(a@)`: a reflexive equality, which the trivially-true check reads as `true` without encoding either side, so no encoder ever saw the marker it would have refused.
//@ accept-means: a caller was credited with a call whose precondition is false, because two refused calls of one name were one symbol.
//@ WHY IT IS FALSE: at `T = &S`, `U = &V` the precondition is `3 + 1 == 3`, which is false: `caller` violates `g`'s contract. Creusot's `vc_caller` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (`caller verified ✓`) with every refusal spelled `logic_fn_unresolved_marker(short)`; rejected (`unknown`) with each refused call given its own symbol, the encoder then refusing it (`logic function call `__lfidU__m_N<site>_` was not resolved to one definition by the driver`).
//@ fixed-by: D-164 — each call the identity resolver refuses has a symbol no other call shares (`identity::refused_call_marker`), so no equality between two refused calls is reflexive.
//@ also-verified: g
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn m(x: Int) -> Int;
}
pub struct S;
pub struct V;
impl Tr for &S {
    #[logic(open)]
    fn m(x: Int) -> Int {
        x + 1
    }
}
impl Tr for &V {
    #[logic(open)]
    fn m(x: Int) -> Int {
        x
    }
}

#[requires(<T as Tr>::m(a@) == <U as Tr>::m(a@))]
pub fn g<T: Tr, U: Tr>(a: u32) {}

pub fn caller() {
    g::<&'static S, &'static V>(3);
}
