//@ expect: reject
//@ mechanism: a CONST GENERIC PARAMETER shadows a unit struct of the same name in the value
//@ mechanism: namespace: rustc resolves the bare path `S` in a clause of `f<const S: i64>` to the
//@ mechanism: parameter (an `i64`), so `S.v()` is `<i64 as Tr>::v`. unit_struct_value_type
//@ mechanism: (logic/identity.rs) reads the name off the owner's MODULE only; its callers rule out
//@ mechanism: clause binders, parameters, `result` and body locals, but not the owner's generic
//@ mechanism: parameters, so the receiver is typed as the unit struct and `<S as Tr>::v` is used.
//@ accept-means: the receiver `S` was typed as the module's unit struct although the clause's
//@ accept-means: `S` is the const parameter.
//@ WHY THE CONTRACT IS FALSE: `S.v()` is `<i64 as Tr>::v(S)`, which is 2, not 1 (a plain rustc
//@ WHY THE CONTRACT IS FALSE: build of the same body prints the i64 impl's value).
//@ fixed-by: unit_struct_value_type refuses a name that is a generic parameter of the owner or
//@ fixed-by: of a generics parent (impl, trait, the function a closure is in).
//@ teeth: ACCEPTED (exit 0, `f verified`) at the head that introduced unit_struct_value_type;
//@ teeth: before it the receiver had no Rust type and the call was refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn v(self) -> Int { 1 }
}
impl Tr for i64 {
    #[logic(open)]
    fn v(self) -> Int { 2 }
}
#[ensures(S.v() == 1)]
pub fn f<const S: i64>() {}
