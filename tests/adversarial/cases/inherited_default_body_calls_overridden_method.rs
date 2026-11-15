//@ expect: reject
//@ mechanism: an inherited default whose body CALLS another trait method: at `()` the default `f` is `h() + 1` with the impl's `h` (5), so 6. The declaration's definition reads `h` at an abstract `Self`; were that read through the trait's visible default (0), binding `Self::f()` to the declaration would say 1
//@ accept-means: an inherited default that calls another method was bound to the declaration's definition, which reads the overridden `h` through the trait's own default
//@ verdict: unknown
//@ refused-with: names one of several definitions
//@ teeth: prospective — only a default that calls nothing is bound (`is_self_contained_default`); widening that to this body, with its `Self::h` read through the trait default, would prove `get() == 1`, which is false
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Foo {
    #[logic(open)]
    fn h() -> Int {
        0
    }
    #[logic(open)]
    fn f() -> Int {
        Self::h() + 1
    }
    fn get(&self) -> i32;
}

impl Foo for () {
    #[logic(open)]
    fn h() -> Int {
        5
    }
    // WRONG: Self::f() at () is h() + 1 = 6; get() returns 1.
    #[ensures(result@ == Self::f())]
    fn get(&self) -> i32 {
        1
    }
}
