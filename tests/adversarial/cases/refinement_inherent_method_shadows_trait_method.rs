//@ expect: reject
//@ mechanism: an inherent `S::v` shadows the trait's `v` inside the impl's clause (Rust selects the inherent method), while the trait's clause read at `S` means `<S as Tr>::v`. The two clauses are the same TEXT and different definitions: `S::v` is 5, `<S as Tr>::v` is the field, which may be negative
//@ accept-means: the refinement compared the clauses as text, or bound the impl's call to the trait impl, and credited `get`'s refinement although `S(-1).get()` breaks the trait's promise to generic callers
//@ verdict: unknown
//@ refused-with: matches several impls
//@ teeth: prospective — the receiver-typed resolution sees two definitions of `v` at `S` (inherent and trait impl) and refuses, in `get`'s own contract and in both refinement sides; a rule that preferred either one, or compared the clauses as text, would verify this crate
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self) -> Int;
    #[ensures(self.v() >= 0)]
    fn get(&self) -> i32;
}

pub struct S(pub i32);

impl S {
    #[logic(open)]
    pub fn v(self) -> Int {
        5
    }
}

impl Tr for S {
    #[logic(open)]
    fn v(self) -> Int {
        pearlite! { self.0@ }
    }
    // Here `self.v()` is the inherent S::v (5): true for the body, but it
    // does not refine the trait's `<S as Tr>::v() >= 0`.
    #[ensures(self.v() >= 0)]
    fn get(&self) -> i32 {
        0
    }
}
