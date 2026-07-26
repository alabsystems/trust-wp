// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `result` in extern_spec `#[requires]` is rejected
//!
//! The `result` keyword is only valid in postconditions (`#[ensures]`).
//! Before #810, extern_spec did not validate contract expressions at all.
//!
//! Issue: #810 (fix), #831 (test)

use trust_wp_macros::extern_spec;

extern_spec! {
    impl<T> core::option::Option::<T> {
        // ERROR: `result` is not valid in #[requires]
        #[requires(result > 0)]
        #[ensures(result == self)]
        fn unwrap(self) -> T;
    }
}

fn main() {}
