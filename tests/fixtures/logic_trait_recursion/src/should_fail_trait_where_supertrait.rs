// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED pin (creusot tests/should_fail/terminates/trait_where_supertrait.rs):
//! same as trait_where but the recursion goes through a supertrait — `P` is a
//! bound of `Q::f` and `Q` is a supertrait of `P`, closing the cycle. Must be
//! rejected as an illegal recursive trait.

use trust_wp::{ensures, logic};

pub trait Q<T>: Sized {
    #[logic]
    #[ensures(false)]
    fn f(self, x: T)
    where
        Self: P<Self>;
}

pub trait P<T>: Q<T> {}

impl<T> Q<i32> for T {
    #[logic]
    #[ensures(false)]
    fn f(self, _x: i32)
    where
        Self: P<Self>,
    {
        self.f(self)
    }
}

impl P<i32> for i32 {}

#[logic]
#[ensures(false)]
pub fn g() {
    0i32.f(0i32)
}

fn main() {}
