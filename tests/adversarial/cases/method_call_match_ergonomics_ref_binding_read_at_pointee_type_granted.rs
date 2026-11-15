//@ expect: reject
//@ mechanism: `match &o { Some(y) => y.m(), None => false }` with `o: Option<A>`: the default binding
//@ mechanism: mode binds `y` by reference, `y: &A`, and Rust's method lookup starts at `&A`, where the
//@ mechanism: local `impl Tr for &A` (`m` true) applies by value before the lookup derefs to `A`'s
//@ mechanism: inherent `m` (false). The claim is `result == o.is_some()`. The contract parser
//@ mechanism: keeps the scrutinee's borrow as its operand; were `y` typed as the payload `A`, `y.m()`
//@ mechanism: would be read as the inherent `A::m` (false) and `f`, which returns false, credited.
//@ fixed-by: n/a (never accepted: a sideways guard of D-201)
//@ accept-means: `f` claims `result == true` of every `Some` in Rust's reading, returns false, and the
//@ accept-means: crate exits 0.
//@ teeth: not shown: refused (`unknown`) with D-201 in force, where the resolver leaves
//@ teeth: `y.m()` untyped and the encoder's dispatch finds it ambiguous.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A;
impl A {
    #[logic(open)]
    pub fn m(self) -> bool {
        pearlite! { false }
    }
}

pub trait Tr {
    #[logic]
    fn m(self) -> bool;
}

impl Tr for &A {
    #[logic(open)]
    fn m(self) -> bool {
        pearlite! { true }
    }
}

#[ensures(result == match &o { Some(y) => y.m(), None => false })]
pub fn f(o: Option<A>) -> bool {
    let _ = o;
    false
}
