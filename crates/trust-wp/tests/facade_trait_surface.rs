// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-surface guard for `Clone` and `PartialEq` through both
//! `use trust_wp::*;` and `use trust_wp::prelude::*;` import paths.
//!
//! Uses `self::Clone` / `self::PartialEq` in bounds to prove the names come
//! from the facade import, not the Rust standard prelude.
//!
//! `Default` is not tested with `self::` here because trust-wp-macros exports a
//! `Default` derive macro that shadows the trait in module-local resolution.
//! `Default` trait coverage lives in `prelude_model_default_surface.rs`.

mod via_star {
    use trust_wp::*;

    #[derive(Debug, Clone, PartialEq)]
    struct Wrapper(i32);

    fn require_clone<T: self::Clone>(value: &T) -> T {
        value.clone()
    }

    fn require_partial_eq<T: self::PartialEq>(a: &T, b: &T) -> bool {
        a == b
    }

    #[test]
    fn test_star_clone() {
        let w = Wrapper(42);
        assert_eq!(require_clone(&w), Wrapper(42));
    }

    #[test]
    fn test_star_partial_eq() {
        assert!(require_partial_eq(&Wrapper(1), &Wrapper(1)));
        assert!(!require_partial_eq(&Wrapper(1), &Wrapper(2)));
    }
}

mod via_prelude {
    use trust_wp::prelude::*;

    #[derive(Debug, Clone, PartialEq)]
    struct Wrapper(i32);

    fn require_clone<T: self::Clone>(value: &T) -> T {
        value.clone()
    }

    fn require_partial_eq<T: self::PartialEq>(a: &T, b: &T) -> bool {
        a == b
    }

    #[test]
    fn test_prelude_clone() {
        let w = Wrapper(42);
        assert_eq!(require_clone(&w), Wrapper(42));
    }

    #[test]
    fn test_prelude_partial_eq() {
        assert!(require_partial_eq(&Wrapper(1), &Wrapper(1)));
        assert!(!require_partial_eq(&Wrapper(1), &Wrapper(2)));
    }
}
