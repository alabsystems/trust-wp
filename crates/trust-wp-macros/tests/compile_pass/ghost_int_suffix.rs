// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `123int` Pearlite integer suffixes should be accepted
//! in ghost blocks and contract attributes.
//! Regression test for int-suffix support.

#![allow(unexpected_cfgs)]

use trust_wp_macros::{ensures, ghost, requires};

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

pub mod logic {
    #[derive(Clone, Copy)]
    pub struct Int(pub i128);

    impl From<i32> for Int {
        fn from(v: i32) -> Self {
            Int(v as i128)
        }
    }

    impl From<i128> for Int {
        fn from(v: i128) -> Self {
            Int(v)
        }
    }
}

#[requires(x > 0)]
#[ensures(result > 0)]
fn simple_contract(x: i32) -> i32 {
    x
}

fn main() {
    let _ = simple_contract(1);
    ghost!({
        let _x = ::trust_wp_std::logic::Int::from(1);
    });
}
