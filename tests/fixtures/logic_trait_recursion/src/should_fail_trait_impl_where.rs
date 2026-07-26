// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED pin (creusot tests/should_fail/terminates/trait_impl_where.rs): the
//! where clause is only on the impl, so the trait itself is fine — but
//! `self.f()` inside `<i32 as Tr>::f` dispatches back into the same impl
//! method (an identity self-call the termination callgraph must thread even
//! though the short name `f` is ambiguous between the trait declaration and
//! the impl). Must be rejected as unconditional self-recursion.

use trust_wp::{ensures, logic};

pub trait Tr {
    #[logic]
    #[ensures(false)]
    fn f(&self);
}

impl Tr for i32 {
    // A too naive termination checker might accept this definition because it
    // just calls the `f` provided by the `i32: Tr` bound — which is this very
    // definition.
    #[logic]
    #[ensures(false)]
    fn f(&self)
    where
        i32: Tr,
    {
        self.f()
    }
}

#[logic]
#[ensures(false)]
pub fn g() {
    1i32.f()
}

fn main() {}
