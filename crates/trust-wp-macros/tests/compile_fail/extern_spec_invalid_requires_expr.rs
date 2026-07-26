// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: malformed extern_spec `#[requires]` expression is rejected
//!
//! This exercises the parse-failure path in `validate_contract_attr` used by
//! `extern_spec!` contract validation.
//!
//! Issue: #810 (fix), #831 (test)

use trust_wp_macros::extern_spec;

extern_spec! {
    impl<T> core::option::Option::<T> {
        // ERROR: malformed contract expression should fail validation
        #[requires(1 +)]
        fn unwrap(self) -> T;
    }
}

fn main() {}
