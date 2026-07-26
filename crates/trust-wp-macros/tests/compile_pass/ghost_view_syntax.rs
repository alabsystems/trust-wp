// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: Creusot `@` (view) and `^` (final) syntax should be
//! accepted in ghost! blocks after #2009 unified preprocessing.
//!
//! Previously `ghost! { let y = v@; }` failed because ghost! only applied
//! int-suffix transforms, not @ or ^ transforms.

#![allow(unexpected_cfgs, dead_code, unused_variables)]

use trust_wp_macros::ghost;

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

/// Stub for `view(expr)` — the @ postfix transform rewrites `v@` to `view(v)`.
fn view<T>(x: T) -> T {
    x
}

/// Stub for `final_value(expr)` — the ^ prefix transform rewrites `^v` to `final_value(v)`.
fn final_value<T>(x: T) -> T {
    x
}

fn main() {
    let v = 42i32;

    // AC2: ghost! { let y = v@; } should compile (@ transform applied)
    ghost!({
        let _y = v@;
    });

    // Also verify ^ works in ghost blocks
    ghost!({
        let _z = ^v;
    });
}
