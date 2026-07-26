// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `ghost_let!` should produce a `Ghost<T>` binding.
#![allow(unexpected_cfgs)]

use trust_wp_macros::ghost_let;

extern crate self as trust_wp_std;

pub mod ghost {
    use core::marker::PhantomData;

    pub struct Ghost<T>(PhantomData<T>);

    impl<T> Ghost<T> {
        pub fn new(_value: T) -> Self {
            Self(PhantomData)
        }

        pub fn conjure() -> Self {
            Self(PhantomData)
        }
    }
}

fn ghost_let_value_has_ghost_type() {
    ghost_let!(g = 41 + 1);
    let _: trust_wp_std::ghost::Ghost<i32> = g;
}

fn ghost_let_mut_binding_has_ghost_type() {
    ghost_let!(mut g = 0usize);
    let _: trust_wp_std::ghost::Ghost<usize> = g;
}

fn main() {
    ghost_let_value_has_ghost_type();
    ghost_let_mut_binding_has_ghost_type();
}
