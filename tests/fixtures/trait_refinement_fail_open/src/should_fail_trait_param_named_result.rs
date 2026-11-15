// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (review F2, t1c): a trait parameter named `result` was
//! captured by the postcondition's `result`, so `result == 0` over the
//! parameter was matched against the impl's `x == 0`.
//!
//! That exact shape no longer type-checks: an `#[ensures]` on a trait
//! signature binds `result` next to the parameters (Creusot's
//! `creusot-std-proc` `ensures` pushes `result: T` onto the signature, and
//! trust-wp's type-check vehicle does the same), so rustc stops it with E0415.
//! A trait parameter named `result` still reaches the refinement pass through
//! a precondition, and the positional renaming must refuse it there.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[requires(true)]
    fn m(result: u32) -> u32;
}

pub struct S;

impl Tr for S {
    #[requires(x@ == 0)]
    fn m(x: u32) -> u32 {
        0
    }
}

pub fn through<T: Tr>() -> u32 {
    T::m(5)
}

fn main() {}
