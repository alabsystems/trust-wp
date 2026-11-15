//@ expect: reject
//@ mechanism: the `T::m` spelling of callee_requires_generic_qualified_refused_calls_share_no_symbol.rs: `g<T: Tr,
//@ mechanism: U: Tr>` requires `T::m(a@) == U::m(a@)`, and `caller` calls `g::<&'static S, &'static V>(3)`,
//@ mechanism: where `Tr` is implemented for `&S` (`x + 1`) and `&V` (`x`). Each call carries a generic marker,
//@ mechanism: and the typed lookup refuses both instantiations at the caller. Spelled with the one refusal
//@ mechanism: marker of the short name, the precondition `caller` owes was `__lfidU__m(a@) == __lfidU__m(a@)`,
//@ mechanism: which the reflexive check reads as `true` without encoding either side.
//@ accept-means: a caller was credited with a call whose precondition is false, because two refused calls of one name were one symbol.
//@ WHY IT IS FALSE: at `T = &S`, `U = &V` the precondition is `3 + 1 == 3`; Creusot's `vc_caller` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (`caller verified ✓`) at the campaign tip, and with `refused_call_marker`
//@ teeth: built to return the short name's one marker; rejected (`unknown`) with each refused call given its
//@ teeth: own symbol.
//@ fixed-by: D-164 — each call the identity resolver refuses has a symbol no other call shares (`identity::refused_call_marker`).
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

#[requires(T::m(a@) == U::m(a@))]
pub fn g<T: Tr, U: Tr>(a: u32) {}

pub fn caller() {
    g::<&'static S, &'static V>(3);
}
