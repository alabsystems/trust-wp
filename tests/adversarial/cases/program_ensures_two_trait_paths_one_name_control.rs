//@ expect: verify
//@ mechanism: control for program_ensures_two_trait_paths_one_name.rs, differing in the `+ 1` alone: each trait path is read as its own trait's implementation at `S`, and `1 + 1 == 2` holds. Refused (`unknown`) where path calls are matched with rustc's by first argument; verified where each is matched by its written path.
//@ accept-means: n/a (control) — `<S as Tr>::m(x) + 1` is `<S as Other>::m(x)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn m(self) -> Int;
}
pub trait Other {
    #[logic]
    fn m(self) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn m(self) -> Int {
        1
    }
}
impl Other for S {
    #[logic(open)]
    fn m(self) -> Int {
        2
    }
}

#[ensures(Tr::m(x) + 1 == Other::m(x))]
pub fn prog(x: S) {}
