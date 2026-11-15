//@ expect: verify
//@ mechanism: `Self::f()` inside an impl that DOES define `f` is that impl's own `f` (2), never the trait default (1)
//@ teeth: control for `inherited_default_overridden_false`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Foo {
    #[logic(open)]
    fn f() -> Int {
        1
    }
    fn get(&self) -> i32;
}

impl Foo for () {
    #[logic(open)]
    fn f() -> Int {
        2
    }
    #[ensures(result@ == Self::f())]
    fn get(&self) -> i32 {
        2
    }
}
