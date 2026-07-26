// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `ghost_let!` should preserve reborrowed reference shape
//! and wrap it as `Ghost<&mut FieldTy>`.
#![allow(unexpected_cfgs)]

use trust_wp_macros::ghost_let;

extern crate self as trust_wp_std;

pub mod ghost {
    pub struct Ghost<T>(Option<T>);

    impl<T> Ghost<T> {
        pub fn new(value: T) -> Self {
            Self(Some(value))
        }

        pub fn conjure() -> Self {
            Self(None)
        }

        pub fn into_inner(mut self) -> T {
            self.0.take().expect("ghost helper should contain value")
        }
    }
}

struct WithInv(i32);

fn ghost_let_reborrow_has_expected_ghost_type() {
    let mut v = WithInv(1);
    let g = trust_wp_std::ghost::Ghost::new(&mut v);

    ghost_let!(g2 = &mut g.into_inner().0);

    let _: trust_wp_std::ghost::Ghost<&mut i32> = g2;
}

fn main() {
    ghost_let_reborrow_has_expected_ghost_type();
}
