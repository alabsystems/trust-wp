// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Specifications for `std::result::Result<T, E>`
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These specifications define the contract semantics for Result methods.
//! trust-wp-driver uses these specs when verifying code that uses Result.
//!
//! Reference: Creusot's `creusot-std/src/std/result.rs`

// Allow raw string hashes for spec string literals (consistency over optimization)
#![allow(clippy::needless_raw_string_hashes)]
// Allow doc_markdown pedantic warnings for contract notation
#![allow(clippy::doc_markdown)]

/// Specification trait for `Result<T, E>` methods (internal).
///
/// This trait documents the contracts for Result methods. **Users should
/// call standard `Result` methods directly** — trust-wp-driver resolves
/// these specs internally via the `std_specs` module. The `_spec()` methods
/// here are for testing trust-wp-std itself.
///
/// # Specifications
///
/// ## is_ok / is_err
/// ```text
/// #[ensures(result == matches!(*self, Ok(_)))]
/// fn is_ok(&self) -> bool;
///
/// #[ensures(result == matches!(*self, Err(_)))]
/// fn is_err(&self) -> bool;
/// ```
///
/// ## unwrap / unwrap_err
/// ```text
/// #[requires(matches!(*self, Ok(_)))]
/// #[ensures(Ok(result) == *self)]
/// fn unwrap(self) -> T;
///
/// #[requires(matches!(*self, Err(_)))]
/// #[ensures(Err(result) == *self)]
/// fn unwrap_err(self) -> E;
/// ```
///
/// ## unwrap_or
/// ```text
/// #[ensures(match *self {
///     Ok(v) => result == v,
///     Err(_) => result == default,
/// })]
/// fn unwrap_or(self, default: T) -> T;
/// ```
///
/// ## map / map_err
/// ```text
/// #[ensures(match *self {
///     Ok(v) => result == Ok(f(v)),
///     Err(e) => result == Err(e),
/// })]
/// fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Result<U, E>;
///
/// #[ensures(match *self {
///     Ok(v) => result == Ok(v),
///     Err(e) => result == Err(f(e)),
/// })]
/// fn map_err<U, F: FnOnce(E) -> U>(self, f: F) -> Result<T, U>;
/// ```
pub trait ResultSpec<T, E> {
    /// Specification: result == matches!(*self, Ok(_))
    fn is_ok_spec(&self) -> bool;

    /// Specification: result == matches!(*self, Err(_))
    fn is_err_spec(&self) -> bool;

    /// Specification: requires(is_ok), ensures(Ok(result) == *self)
    fn unwrap_spec(self) -> T;

    /// Specification: requires(is_err), ensures(Err(result) == *self)
    fn unwrap_err_spec(self) -> E;

    /// Specification: ensures(match *self { Ok(v) => v, Err(_) => default })
    fn unwrap_or_spec(self, default: T) -> T;

    /// Specification: ensures(match *self { Ok(v) => Some(v), Err(_) => None })
    fn ok_spec(self) -> Option<T>;

    /// Specification: ensures(match *self { Ok(_) => None, Err(e) => Some(e) })
    fn err_spec(self) -> Option<E>;

    /// Specification: ensures(match *self { Ok(v) => Ok(f(v)), Err(e) => Err(e) })
    fn map_spec<U, F: FnOnce(T) -> U>(self, f: F) -> Result<U, E>;

    /// Specification: ensures(match *self { Ok(v) => Ok(v), Err(e) => Err(f(e)) })
    fn map_err_spec<U, F: FnOnce(E) -> U>(self, f: F) -> Result<T, U>;

    /// Specification: ensures(match *self { Ok(v) => f(v), Err(e) => Err(e) })
    fn and_then_spec<U, F: FnOnce(T) -> Result<U, E>>(self, f: F) -> Result<U, E>;

    /// Specification for expect(): requires(is_ok), ensures(Ok(result) == *self)
    ///
    /// Same contract as unwrap, but panics with custom message.
    /// ```text
    /// #[requires(matches!(*self, Ok(_)))]
    /// #[ensures(Ok(result) == *self)]
    /// fn expect(self, msg: &str) -> T;
    /// ```
    fn expect_spec(self, msg: &str) -> T
    where
        E: std::fmt::Debug;

    /// Specification for unwrap_or_else(): lazy default evaluation
    ///
    /// ```text
    /// #[ensures(match *self {
    ///     Ok(v) => result == v,
    ///     Err(e) => result == f(e),
    /// })]
    /// fn unwrap_or_else<F: FnOnce(E) -> T>(self, f: F) -> T;
    /// ```
    fn unwrap_or_else_spec<F: FnOnce(E) -> T>(self, f: F) -> T;

    /// Specification for as_ref(): converts &Result<T, E> to Result<&T, &E>
    ///
    /// ```text
    /// #[ensures(match *self {
    ///     Ok(ref v) => result == Ok(v),
    ///     Err(ref e) => result == Err(e),
    /// })]
    /// fn as_ref(&self) -> Result<&T, &E>;
    /// ```
    fn as_ref_spec(&self) -> Result<&T, &E>;

    /// Specification for as_mut(): converts &mut Result<T, E> to Result<&mut T, &mut E>
    ///
    /// ```text
    /// #[ensures(match *self {
    ///     Ok(ref mut v) => result == Ok(v),
    ///     Err(ref mut e) => result == Err(e),
    /// })]
    /// fn as_mut(&mut self) -> Result<&mut T, &mut E>;
    /// ```
    fn as_mut_spec(&mut self) -> Result<&mut T, &mut E>;

    /// Specification for expect_err(): requires(is_err), ensures(Err(result) == *self)
    ///
    /// Same contract as unwrap_err, but panics with custom message.
    /// ```text
    /// #[requires(matches!(*self, Err(_)))]
    /// #[ensures(Err(result) == *self)]
    /// fn expect_err(self, msg: &str) -> E;
    /// ```
    fn expect_err_spec(self, msg: &str) -> E
    where
        T: std::fmt::Debug;

    /// Specification for unwrap_unchecked(): unsafe, requires(is_ok)
    ///
    /// ```text
    /// #[requires(matches!(*self, Ok(_)))]
    /// #[ensures(Ok(result) == *self)]
    /// fn unwrap_unchecked(self) -> T;
    /// ```
    fn unwrap_unchecked_spec(self) -> T;

    /// Specification for unwrap_err_unchecked(): unsafe, requires(is_err)
    ///
    /// ```text
    /// #[requires(matches!(*self, Err(_)))]
    /// #[ensures(Err(result) == *self)]
    /// fn unwrap_err_unchecked(self) -> E;
    /// ```
    fn unwrap_err_unchecked_spec(self) -> E;
}

impl<T, E> ResultSpec<T, E> for Result<T, E> {
    fn is_ok_spec(&self) -> bool {
        self.is_ok()
    }

    fn is_err_spec(&self) -> bool {
        self.is_err()
    }

    #[allow(clippy::wildcard_enum_match_arm)]
    fn unwrap_spec(self) -> T {
        match self {
            Ok(value) => value,
            Err(_) => panic!("called `Result::unwrap()` on an `Err` value"),
        }
    }

    fn unwrap_err_spec(self) -> E {
        match self {
            Ok(_) => panic!("called `Result::unwrap_err()` on an `Ok` value"),
            Err(value) => value,
        }
    }

    fn unwrap_or_spec(self, default: T) -> T {
        self.unwrap_or(default)
    }

    fn ok_spec(self) -> Option<T> {
        self.ok()
    }

    fn err_spec(self) -> Option<E> {
        self.err()
    }

    fn map_spec<U, F: FnOnce(T) -> U>(self, f: F) -> Result<U, E> {
        self.map(f)
    }

    fn map_err_spec<U, F: FnOnce(E) -> U>(self, f: F) -> Result<T, U> {
        self.map_err(f)
    }

    fn and_then_spec<U, F: FnOnce(T) -> Result<U, E>>(self, f: F) -> Result<U, E> {
        self.and_then(f)
    }

    fn expect_spec(self, msg: &str) -> T
    where
        E: std::fmt::Debug,
    {
        self.expect(msg)
    }

    fn unwrap_or_else_spec<F: FnOnce(E) -> T>(self, f: F) -> T {
        self.unwrap_or_else(f)
    }

    fn as_ref_spec(&self) -> Result<&T, &E> {
        self.as_ref()
    }

    fn as_mut_spec(&mut self) -> Result<&mut T, &mut E> {
        self.as_mut()
    }

    fn expect_err_spec(self, msg: &str) -> E
    where
        T: std::fmt::Debug,
    {
        self.expect_err(msg)
    }

    fn unwrap_unchecked_spec(self) -> T {
        match self {
            Ok(value) => value,
            // SAFETY: caller must ensure self is Ok — same as std's unwrap_unchecked
            Err(_) => panic!("called `Result::unwrap_unchecked()` on an `Err` value"),
        }
    }

    fn unwrap_err_unchecked_spec(self) -> E {
        match self {
            Ok(_) => panic!("called `Result::unwrap_err_unchecked()` on an `Ok` value"),
            // SAFETY: caller must ensure self is Err — same as std's unwrap_err_unchecked
            Err(value) => value,
        }
    }
}

/// Internal specification definitions used by the driver's hardcoded fallback
/// tables and local tests. Builtin registry loading happens separately.
///
/// These are structured as data that the driver can query.
#[doc(hidden)]
pub mod specs {
    /// Contract for `Result::is_ok`
    pub const IS_OK: &str = r#"
        ensures: result == match *self { Ok(_) => true, Err(_) => false, }
    "#;

    /// Contract for `Result::is_err`
    pub const IS_ERR: &str = r#"
        ensures: result == match *self { Ok(_) => false, Err(_) => true, }
    "#;

    /// Contract for `Result::unwrap`
    pub const UNWRAP: &str = r#"
        requires: match *self { Ok(_) => true, Err(_) => false, }
        ensures: Ok(result) == *self
    "#;

    /// Contract for `Result::unwrap_err`
    pub const UNWRAP_ERR: &str = r#"
        requires: match *self { Ok(_) => false, Err(_) => true, }
        ensures: Err(result) == *self
    "#;

    /// Contract for `Result::unwrap_or`
    pub const UNWRAP_OR: &str = r#"
        ensures: match *self {
            Ok(v) => result == v,
            Err(_) => result == default,
        }
    "#;

    /// Contract for `Result::map`
    pub const MAP: &str = r#"
        ensures: match *self {
            Ok(v) => result == Ok(f(v)),
            Err(e) => result == Err(e),
        }
    "#;

    /// Contract for `Result::map_err`
    pub const MAP_ERR: &str = r#"
        ensures: match *self {
            Ok(v) => result == Ok(v),
            Err(e) => result == Err(f(e)),
        }
    "#;

    /// Contract for `Result::and_then`
    pub const AND_THEN: &str = r#"
        ensures: match *self {
            Ok(v) => result == f(v),
            Err(e) => result == Err(e),
        }
    "#;

    /// Contract for `Result::ok`
    pub const OK: &str = r#"
        ensures: match *self {
            Ok(v) => result == Some(v),
            Err(_) => result == None,
        }
    "#;

    /// Contract for `Result::err`
    pub const ERR: &str = r#"
        ensures: match *self {
            Ok(_) => result == None,
            Err(e) => result == Some(e),
        }
    "#;

    /// Contract for `Result::expect`
    ///
    /// Same as unwrap, but with custom panic message.
    pub const EXPECT: &str = r#"
        requires: match *self { Ok(_) => true, Err(_) => false, }
        ensures: Ok(result) == *self
    "#;

    /// Contract for `Result::unwrap_or_else`
    pub const UNWRAP_OR_ELSE: &str = r#"
        ensures: match *self {
            Ok(v) => result == v,
            Err(e) => result == f(e),
        }
    "#;

    /// Contract for `Result::as_ref`
    ///
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const AS_REF: &str = r#"
        ensures: self.is_ok() ==> result.is_ok()
        ensures: self.is_ok() ==> result.unwrap() == self.unwrap()
        ensures: self.is_err() ==> result.is_err()
        ensures: self.is_err() ==> result.unwrap_err() == self.unwrap_err()
    "#;

    /// Contract for `Result::as_mut`
    ///
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const AS_MUT: &str = r#"
        ensures: self.is_ok() ==> result.is_ok()
        ensures: self.is_ok() ==> result.unwrap() == self.unwrap()
        ensures: self.is_err() ==> result.is_err()
        ensures: self.is_err() ==> result.unwrap_err() == self.unwrap_err()
    "#;

    /// Contract for `Result::and`
    ///
    /// Returns `res` if self is `Ok`, otherwise returns the `Err` value of self.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const AND: &str = r#"
        params: self, res
        ensures: self.is_ok() ==> result == res
        ensures: self.is_err() ==> result.is_err()
        ensures: self.is_err() ==> result.unwrap_err() == self.unwrap_err()
    "#;

    /// Contract for `Result::or`
    ///
    /// Returns self if it is `Ok`, otherwise returns `res`.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const OR: &str = r#"
        params: self, res
        ensures: self.is_ok() ==> result.is_ok()
        ensures: self.is_ok() ==> result.unwrap() == self.unwrap()
        ensures: self.is_err() ==> result == res
    "#;

    /// Contract for `Result::or_else`
    ///
    /// Calls `op` if self is `Err`, otherwise returns the `Ok` value of self.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const OR_ELSE: &str = r#"
        params: self, op
        ensures: self.is_ok() ==> result.is_ok()
        ensures: self.is_ok() ==> result.unwrap() == self.unwrap()
    "#;

    /// Contract for `Result::unwrap_or_default`
    ///
    /// Returns the contained `Ok` value or a default.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const UNWRAP_OR_DEFAULT: &str = r#"
        ensures: self.is_ok() ==> result == self.unwrap()
        ensures: self.is_err() ==> result@ == 0
    "#;

    /// Contract for `Result::copied` (for Result<&T, E>)
    ///
    /// Maps a `Result<&T, E>` to a `Result<T, E>` by copying the `Ok` value.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const COPIED: &str = r#"
        ensures: self.is_ok() ==> result.is_ok()
        ensures: self.is_err() ==> result.is_err()
    "#;

    /// Contract for `Result::cloned` (for Result<&T, E>)
    ///
    /// Maps a `Result<&T, E>` to a `Result<T, E>` by cloning the `Ok` value.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const CLONED: &str = r#"
        ensures: self.is_ok() ==> result.is_ok()
        ensures: self.is_err() ==> result.is_err()
    "#;

    /// Contract for `Result::transpose` (for Result<Option<T>, E>)
    ///
    /// Transposes a Result of an Option into an Option of a Result.
    /// Ok(None) -> None, Ok(Some(v)) -> Some(Ok(v)), Err(e) -> Some(Err(e)).
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const TRANSPOSE: &str = r#"
        ensures: self.is_err() ==> result.is_some()
        ensures: self.is_ok() ==> self.unwrap().is_none() ==> result.is_none()
        ensures: self.is_ok() ==> self.unwrap().is_some() ==> result.is_some()
    "#;

    /// Contract for `Result::inspect`
    ///
    /// Calls `f` with a reference to the Ok value (if any), then returns self.
    pub const INSPECT: &str = r#"
        ensures: result == *self
    "#;

    /// Contract for `Result::inspect_err`
    ///
    /// Calls `f` with a reference to the Err value (if any), then returns self.
    pub const INSPECT_ERR: &str = r#"
        ensures: result == *self
    "#;

    /// Contract for `Result::map_or`
    ///
    /// Returns the provided default (if Err), or applies a function to
    /// the contained value.
    pub const MAP_OR: &str = r#"
        params: self, default, f
        ensures: self.is_err() ==> result == default
    "#;

    /// Contract for `Result::map_or_else`
    ///
    /// Computes a default (if Err), or applies a function to the Ok value.
    pub const MAP_OR_ELSE: &str = r#"
        params: self, default, f
        ensures: self.is_err() ==> result == default(self.unwrap_err())
    "#;

    /// Contract for `Result::is_ok_and`
    ///
    /// Returns `true` if the result is `Ok` and the predicate returns `true`.
    pub const IS_OK_AND: &str = r#"
        params: self, f
        ensures: self.is_err() ==> result == false
    "#;

    /// Contract for `Result::is_err_and`
    ///
    /// Returns `true` if the result is `Err` and the predicate returns `true`.
    pub const IS_ERR_AND: &str = r#"
        params: self, f
        ensures: self.is_ok() ==> result == false
    "#;

    /// Contract for `Result::flatten` (for `Result<Result<T, E>, E>`)
    ///
    /// Converts `Result<Result<T, E>, E>` into `Result<T, E>`.
    /// Ok(Ok(v)) -> Ok(v), Ok(Err(e)) -> Err(e), Err(e) -> Err(e).
    pub const FLATTEN: &str = r#"
        ensures: self.is_err() ==> result.is_err()
    "#;

    /// Contract for `Result::expect_err`
    ///
    /// Same as unwrap_err, but panics with custom message.
    /// ```text
    /// #[requires(matches!(*self, Err(_)))]
    /// #[ensures(Err(result) == *self)]
    /// fn expect_err(self, msg: &str) -> E;
    /// ```
    pub const EXPECT_ERR: &str = r#"
        requires: match *self { Ok(_) => false, Err(_) => true, }
        ensures: Err(result) == *self
    "#;

    /// Contract for `Result::unwrap_unchecked`
    ///
    /// Unsafe: caller must ensure `self` is `Ok`.
    pub const UNWRAP_UNCHECKED: &str = r#"
        requires: match *self { Ok(_) => true, Err(_) => false, }
        ensures: Ok(result) == *self
    "#;

    /// Contract for `Result::unwrap_err_unchecked`
    ///
    /// Unsafe: caller must ensure `self` is `Err`.
    pub const UNWRAP_ERR_UNCHECKED: &str = r#"
        requires: match *self { Ok(_) => false, Err(_) => true, }
        ensures: Err(result) == *self
    "#;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_ok_spec() {
        let ok: Result<i32, &str> = Ok(42);
        let err: Result<i32, &str> = Err("error");
        assert!(ok.is_ok_spec());
        assert!(!err.is_ok_spec());
    }

    #[test]
    fn test_is_err_spec() {
        let ok: Result<i32, &str> = Ok(42);
        let err: Result<i32, &str> = Err("error");
        assert!(!ok.is_err_spec());
        assert!(err.is_err_spec());
    }

    #[test]
    fn test_unwrap_spec() {
        let ok: Result<i32, &str> = Ok(42);
        assert_eq!(ok.unwrap_spec(), 42);
    }

    #[test]
    #[should_panic(expected = "called `Result::unwrap()` on an `Err` value")]
    fn test_unwrap_spec_err_panics() {
        let err: Result<i32, &str> = Err("error");
        let _ = err.unwrap_spec();
    }

    #[test]
    fn test_unwrap_err_spec() {
        let err: Result<i32, &str> = Err("error");
        assert_eq!(err.unwrap_err_spec(), "error");
    }

    #[test]
    #[should_panic(expected = "called `Result::unwrap_err()` on an `Ok` value")]
    fn test_unwrap_err_spec_ok_panics() {
        let ok: Result<i32, &str> = Ok(42);
        let _ = ok.unwrap_err_spec();
    }

    #[test]
    fn test_unwrap_or_spec() {
        let ok: Result<i32, &str> = Ok(42);
        let err: Result<i32, &str> = Err("error");
        assert_eq!(ok.unwrap_or_spec(0), 42);
        assert_eq!(err.unwrap_or_spec(0), 0);
    }

    #[test]
    fn test_ok_spec() {
        let ok: Result<i32, &str> = Ok(42);
        let err: Result<i32, &str> = Err("error");
        assert_eq!(ok.ok_spec(), Some(42));
        assert_eq!(err.ok_spec(), None);
    }

    #[test]
    fn test_err_spec() {
        let ok: Result<i32, &str> = Ok(42);
        let err: Result<i32, &str> = Err("error");
        assert_eq!(ok.err_spec(), None);
        assert_eq!(err.err_spec(), Some("error"));
    }

    #[test]
    fn test_map_spec() {
        let ok: Result<i32, &str> = Ok(2);
        let err: Result<i32, &str> = Err("error");
        assert_eq!(ok.map_spec(|v| v * 2), Ok(4));
        assert_eq!(err.map_spec(|v| v * 2), Err("error"));
    }

    #[test]
    fn test_map_err_spec() {
        let ok: Result<i32, &str> = Ok(2);
        let err: Result<i32, &str> = Err("error");
        assert_eq!(ok.map_err_spec(|e| format!("{e}!")), Ok(2));
        assert_eq!(
            err.map_err_spec(|e| format!("{e}!")),
            Err("error!".to_string())
        );
    }

    #[test]
    fn test_and_then_spec() {
        let ok: Result<i32, &str> = Ok(2);
        let err: Result<i32, &str> = Err("error");
        assert_eq!(ok.and_then_spec(|v| Ok(v + 1)), Ok(3));
        assert_eq!(err.and_then_spec(|v| Ok(v + 1)), Err("error"));
    }

    #[test]
    fn test_expect_spec() {
        let ok: Result<i32, &str> = Ok(42);
        assert_eq!(ok.expect_spec("should have value"), 42);
    }

    #[test]
    fn test_unwrap_or_else_spec() {
        let ok: Result<i32, &str> = Ok(42);
        let err: Result<i32, &str> = Err("error");
        assert_eq!(ok.unwrap_or_else_spec(|_| 100), 42);
        assert_eq!(err.unwrap_or_else_spec(|_| 100), 100);
    }

    #[test]
    fn test_as_ref_spec() {
        let ok: Result<i32, &str> = Ok(42);
        let err: Result<i32, &str> = Err("error");
        assert_eq!(ok.as_ref_spec(), Ok(&42));
        assert_eq!(err.as_ref_spec(), Err(&"error"));
    }

    #[test]
    fn test_as_mut_spec() {
        let mut ok: Result<i32, &str> = Ok(42);
        let mut err: Result<i32, &str> = Err("error");
        if let Ok(v) = ok.as_mut_spec() {
            *v = 100;
        }
        assert_eq!(ok, Ok(100));
        assert_eq!(err.as_mut_spec(), Err(&mut "error"));
    }

    #[test]
    fn test_expect_err_spec() {
        let err: Result<i32, &str> = Err("error");
        assert_eq!(err.expect_err_spec("should be err"), "error");
    }

    #[test]
    fn test_unwrap_unchecked_spec() {
        let ok: Result<i32, &str> = Ok(42);
        assert_eq!(ok.unwrap_unchecked_spec(), 42);
    }

    #[test]
    #[should_panic(expected = "called `Result::unwrap_unchecked()` on an `Err` value")]
    fn test_unwrap_unchecked_spec_err_panics() {
        let err: Result<i32, &str> = Err("error");
        let _ = err.unwrap_unchecked_spec();
    }

    #[test]
    fn test_unwrap_err_unchecked_spec() {
        let err: Result<i32, &str> = Err("error");
        assert_eq!(err.unwrap_err_unchecked_spec(), "error");
    }

    #[test]
    #[should_panic(expected = "called `Result::unwrap_err_unchecked()` on an `Ok` value")]
    fn test_unwrap_err_unchecked_spec_ok_panics() {
        let ok: Result<i32, &str> = Ok(42);
        let _ = ok.unwrap_err_unchecked_spec();
    }
}
