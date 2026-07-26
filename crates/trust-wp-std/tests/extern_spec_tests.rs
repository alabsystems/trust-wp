// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `extern_spec!` macro expansion.
//!
//! These tests verify that the macro generates correct stub functions with
//! doc markers that can be discovered by the driver.
//!
//! Note: Generic types must use turbofish syntax (`Type::<T>`) to avoid
//! parsing ambiguity where `<` could be interpreted as a comparison operator.

use trust_wp_std::extern_spec;

/// Test basic `extern_spec` for `Option::unwrap`.
/// Uses turbofish syntax to avoid parsing ambiguity.
#[test]
fn test_extern_spec_option_unwrap() {
    extern_spec! {
        impl<T> core::option::Option::<T> {
            #[requires(self.is_some())]
            #[ensures(Some(result) == old(self))]
            fn unwrap(self) -> T;
        }
    }

    // If we get here, the macro expanded successfully
}

/// Test `extern_spec` with multiple methods.
#[test]
fn test_extern_spec_multiple_methods() {
    extern_spec! {
        impl<T> core::option::Option::<T> {
            #[ensures(result == self.is_some())]
            fn is_some(&self) -> bool;

            #[ensures(result == !self.is_some())]
            fn is_none(&self) -> bool;
        }
    }
}

/// Test `extern_spec` for `Vec`.
#[test]
fn test_extern_spec_vec() {
    extern_spec! {
        impl<T> std::vec::Vec::<T> {
            #[ensures(result == self.len())]
            fn len(&self) -> usize;

            #[ensures((^self).len() == self.len() + 1)]
            fn push(&mut self, value: T);
        }
    }
}

/// Test `extern_spec` with no preconditions (ensures only).
#[test]
fn test_extern_spec_ensures_only() {
    extern_spec! {
        impl<T> std::vec::Vec::<T> {
            #[ensures(result.len() == 0)]
            fn new() -> std::vec::Vec::<T>;
        }
    }
}

/// Test that `extern_spec` doesn't interfere with runtime execution.
/// The specs are for verification only - runtime behavior should be unchanged.
#[test]
fn test_extern_spec_runtime_behavior() {
    extern_spec! {
        impl<T> core::option::Option::<T> {
            #[requires(self.is_some())]
            fn unwrap(self) -> T;
        }
    }

    // Runtime behavior should still work — unwrap is intentional (testing extern_spec doesn't interfere)
    let opt = Some(42);
    #[allow(clippy::unnecessary_literal_unwrap)]
    let val = opt.unwrap();
    assert_eq!(val, 42);

    let v = Vec::<i32>::new();
    assert_eq!(v.len(), 0);
}

/// Test `extern_spec` with Result type.
/// Note: `Result::unwrap` requires E: Debug bound.
#[test]
fn test_extern_spec_result() {
    extern_spec! {
        impl<T, E: std::fmt::Debug> core::result::Result::<T, E> {
            #[ensures(result == self.is_ok())]
            fn is_ok(&self) -> bool;

            #[requires(self.is_ok())]
            #[ensures(Ok(result) == self)]
            fn unwrap(self) -> T;
        }
    }

    let ok: Result<i32, &str> = Ok(42);
    assert_eq!(ok, Ok(42));
    // Intentionally calling unwrap() on known-Ok to exercise the extern_spec contract.
    #[allow(clippy::unnecessary_literal_unwrap)]
    let val = ok.unwrap();
    assert_eq!(val, 42);
}

/// Test `extern_spec` with concrete type (no generics needed).
#[test]
fn test_extern_spec_concrete_type() {
    extern_spec! {
        impl String {
            #[ensures(result == self.len())]
            fn len(&self) -> usize;
        }
    }

    let s = String::from("hello");
    assert_eq!(s.len(), 5);
}
