// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass regression test: `extern_spec!` accepts trait impl syntax.
//! Covers `impl Trait for Type` parsing and tuple self types.

use trust_wp_macros::extern_spec;

trait UseSelf {
    fn func(&self, rhs: &Self) -> bool;
}

impl UseSelf for () {
    fn func(&self, _: &()) -> bool {
        true
    }
}

impl UseSelf for i32 {
    fn func(&self, _: &Self) -> bool {
        true
    }
}

extern_spec! {
    impl UseSelf for () {
        fn func(&self, s: &Self) -> bool;
    }

    impl UseSelf for i32 {
        fn func(&self, s: &Self) -> bool;
    }

    impl<'a> core::ops::Add<&'a u16> for u16 {
        fn add(self, rhs: &'a u16) -> u16;
    }

    impl<U: PartialOrd<U>, T: PartialOrd<T>> core::cmp::PartialOrd for (U, T) {
        fn lt(&self, other: &(U, T)) -> bool;
    }
}

fn main() {}
