// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: bare `#[requires]` in `extern_spec!` is rejected
//!
//! Contract attributes must use the parenthesized form `#[requires(expr)]`.
//! A bare `#[requires]` (Meta::Path) was previously silently dropped.
//!
//! Issue: #810 (fix), #831 (test)

use trust_wp_macros::extern_spec;

extern_spec! {
    impl<T> core::option::Option::<T> {
        // ERROR: bare #[requires] without parenthesized expression
        #[requires]
        fn unwrap(self) -> T;
    }
}

fn main() {}
