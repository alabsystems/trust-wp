// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-surface guard for `Clone` and `PartialEq` re-exports from
//! `trust_wp_std::prelude::*`.
//!
//! Uses `self::Clone` / `self::PartialEq` in bounds to prove the names come
//! from the prelude import, not the Rust standard prelude.
//!
//! `Default` is not tested with `self::` here because trust-wp-macros exports a
//! `Default` derive macro that shadows the trait in module-local resolution.
//! `Default` trait coverage lives in `prelude_model_default_surface.rs`.

use trust_wp_std::prelude::*;

#[derive(Debug, Clone, PartialEq)]
struct Wrapper(i32);

fn require_clone<T: self::Clone>(value: &T) -> T {
    value.clone()
}

fn require_partial_eq<T: self::PartialEq>(a: &T, b: &T) -> bool {
    a == b
}

#[test]
fn test_clone_resolves_from_prelude() {
    let w = Wrapper(42);
    let cloned = require_clone(&w);
    assert_eq!(cloned, Wrapper(42));
}

#[test]
fn test_partial_eq_resolves_from_prelude() {
    let a = Wrapper(1);
    let b = Wrapper(1);
    assert!(require_partial_eq(&a, &b));
    assert!(!require_partial_eq(&a, &Wrapper(2)));
}
