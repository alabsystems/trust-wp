// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED pin (creusot tests/should_fail/terminates/trait_where.rs): the trait
//! definition is recursive through a where clause of a method — `Tr` is a
//! bound of `Tr::f` (`where Self: Tr<Self>`), so `self.f(self)` dispatches
//! back into the definition. Must be rejected as an illegal recursive trait.

use trust_wp::{ensures, logic};

pub trait Tr<T>: Sized {
    #[logic]
    #[ensures(false)]
    fn f(&self, x: &T)
    where
        Self: Tr<Self>;
}

impl<U> Tr<i32> for U {
    #[logic]
    #[ensures(false)]
    fn f(&self, _x: &i32)
    where
        U: Tr<U>,
    {
        self.f(self)
    }
}

#[logic]
#[ensures(false)]
pub fn g() {
    1i32.f(&1i32)
}

fn main() {}
