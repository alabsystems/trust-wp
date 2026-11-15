//@ expect: verify
//@ mechanism: logic-fn identity v2 — a SEALED default body binds on an abstract generic receiver (`x: T`, `T: Tr`); Creusot forbids overriding it and the driver enforces the seal
//@ fixed-by: s35 logic-fn identity v2 (sealed declaration bodies bind for a bound generic parameter)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr {
    #[logic]
    fn f(self, x: Int) -> Int;
    #[logic(open, sealed)]
    fn g(self, x: Int) -> Int {
        self.f(x) + 1
    }
}
#[ensures(x.g(y) == x.f(y) + 1)]
pub fn p<T: Tr>(x: T, y: Int) {}
