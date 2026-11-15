//@ expect: reject
//@ verdict: failed
//@ fn-failed: k
//@ also-verified: h
//@ mechanism: a callee contract travels to its call sites as clause TEXT, resolved once in the
//@ mechanism: callee's scope (identity_typed.rs resolve_family_calls_in_text). A unit struct
//@ mechanism: receiver there must select the same impl the callee's own verification used, or
//@ mechanism: the caller is granted a different postcondition than the one `h` proved.
//@ accept-means: the caller read `T.v` as some definition other than `T`'s impl.
//@ WHY THE CONTRACT IS FALSE: `h(1, 2)` returns 2 and `T.v(1, 2)` is 2; `k` claims 1.
//@ teeth: standing shape gate; not shown to accept on any build (before the fix the text lane
//@ teeth: refused the receiver, so the caller was never granted anything).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self, p: Int, q: Int) -> Int;
}
pub struct S;
pub struct T;
impl Tr for S {
    #[logic(open)]
    fn v(self, p: Int, _: Int) -> Int { p }
}
impl Tr for T {
    #[logic(open)]
    fn v(self, _: Int, q: Int) -> Int { q }
}
#[ensures(result@ == T.v(a@, b@))]
pub fn h(a: u32, b: u32) -> u32 { b }
#[ensures(result == 1u32)]
pub fn k() -> u32 { h(1, 2) }
