// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fixture for testing user-defined extern_spec! contracts.
//!
//! This project defines an extern_spec! for Option::unwrap and uses it
//! in a function that relies on the specified contract for verification.

use trust_wp::{ensures, extern_spec, requires};

// User-defined extern_spec for Option::unwrap
// This should be discovered by the driver and used during verification.
extern_spec! {
    impl<T> core::option::Option::<T> {
        /// unwrap requires that the Option is Some
        #[requires(self.is_some())]
        #[ensures(Some(result) == old(self))]
        fn unwrap(self) -> T;
    }
}

/// Function that relies on the extern_spec! for Option::unwrap.
///
/// The precondition `opt.is_some()` satisfies the extern_spec's requires clause.
/// The postcondition leverages the extern_spec's ensures clause.
#[requires(opt.is_some())]
#[ensures(result == old(opt).unwrap())]
pub fn get_value(opt: Option<i32>) -> i32 {
    opt.unwrap()
}

/// Simpler test: just verify the unwrap succeeds with a known Some value.
#[ensures(result == 42)]
pub fn get_known_value() -> i32 {
    let opt = Some(42);
    opt.unwrap()
}
