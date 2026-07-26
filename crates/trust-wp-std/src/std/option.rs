// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Specifications for `std::option::Option<T>`
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These specifications define the contract semantics for Option methods.
//! trust-wp-driver uses these specs when verifying code that uses Option.
//!
//! Reference: Creusot's `creusot-std/src/std/option.rs`

// Allow raw string hashes for spec string literals (consistency over optimization)
#![allow(clippy::needless_raw_string_hashes)]
// Allow doc_markdown pedantic warnings for contract notation
#![allow(clippy::doc_markdown)]

use std::hash::Hash;

use crate::logic::{unreachable, Mapping};

/// Specification trait for `Option<T>` methods (internal).
///
/// This trait documents the contracts for Option methods. **Users should
/// call standard `Option` methods directly** — trust-wp-driver resolves
/// these specs internally via the `std_specs` module. The `_spec()` methods
/// here are for testing trust-wp-std itself.
///
/// # Specifications
///
/// ## is_some / is_none
/// ```text
/// #[ensures(result == (*self != None))]
/// fn is_some(&self) -> bool;
///
/// #[ensures(result == (*self == None))]
/// fn is_none(&self) -> bool;
/// ```
///
/// ## unwrap
/// ```text
/// #[requires(*self != None)]
/// #[ensures(Some(result) == *self)]
/// fn unwrap(self) -> T;
/// ```
///
/// ## unwrap_or
/// ```text
/// #[ensures(match *self {
///     Some(v) => result == v,
///     None => result == default,
/// })]
/// fn unwrap_or(self, default: T) -> T;
/// ```
///
/// ## map
/// ```text
/// #[ensures(match *self {
///     Some(v) => result == Some(f(v)),
///     None => result == None,
/// })]
/// fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U>;
/// ```
///
/// ## and_then
/// ```text
/// #[ensures(match *self {
///     Some(v) => result == f(v),
///     None => result == None,
/// })]
/// fn and_then<U, F: FnOnce(T) -> Option<U>>(self, f: F) -> Option<U>;
/// ```
///
/// ## or_else
/// ```text
/// #[ensures(match *self {
///     Some(_) => result == *self,
///     None => result == f(),
/// })]
/// fn or_else<F: FnOnce() -> Option<T>>(self, f: F) -> Option<T>;
/// ```
///
/// ## ok_or
/// ```text
/// #[ensures(self.is_some() ==> result.is_ok())]
/// #[ensures(self.is_some() ==> result.unwrap() == self.unwrap())]
/// #[ensures(self.is_none() ==> result.is_err())]
/// #[ensures(self.is_none() ==> result.unwrap_err() == err)]
/// fn ok_or<E>(self, err: E) -> Result<T, E>;
/// ```
///
/// ## ok_or_else
/// ```text
/// #[ensures(self.is_some() ==> result.is_ok())]
/// #[ensures(self.is_some() ==> result.unwrap() == self.unwrap())]
/// #[ensures(self.is_none() ==> result.is_err())]
/// #[ensures(self.is_none() ==> result.unwrap_err() == err())]
/// fn ok_or_else<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E>;
/// ```
pub trait OptionSpec<T> {
    /// Specification: result == (*self != None)
    fn is_some_spec(&self) -> bool;

    /// Specification: result == (*self == None)
    fn is_none_spec(&self) -> bool;

    /// Specification: requires(*self != None), ensures(Some(result) == *self)
    fn unwrap_spec(self) -> T;

    /// Specification: ensures(match *self { Some(v) => v, None => default })
    fn unwrap_or_spec(self, default: T) -> T;

    /// Specification: ensures(match *self { Some(v) => Some(f(v)), None => None })
    fn map_spec<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U>;

    /// Specification: ensures(match *self { Some(v) => f(v), None => None })
    fn and_then_spec<U, F: FnOnce(T) -> Option<U>>(self, f: F) -> Option<U>;

    /// Specification: ensures(match *self { Some(_) => *self, None => f() })
    fn or_else_spec<F: FnOnce() -> Option<T>>(self, f: F) -> Option<T>;

    /// Specification: ensures(match *self { Some(v) => Ok(v), None => Err(err) })
    fn ok_or_spec<E>(self, err: E) -> Result<T, E>;

    /// Specification: ensures(match *self { Some(v) => Ok(v), None => Err(err()) })
    fn ok_or_else_spec<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E>;

    /// Specification for take(): ensures(^self == None), ensures(result == old(*self))
    fn take_spec(&mut self) -> Option<T>;

    /// Specification for replace(): ensures(^self == Some(value)), ensures(result == old(*self))
    fn replace_spec(&mut self, value: T) -> Option<T>;

    /// Specification for expect(): requires(*self != None), ensures(Some(result) == *self)
    ///
    /// Same contract as unwrap, but panics with custom message.
    /// ```text
    /// #[requires(*self != None)]
    /// #[ensures(Some(result) == *self)]
    /// fn expect(self, msg: &str) -> T;
    /// ```
    fn expect_spec(self, msg: &str) -> T;

    /// Specification for unwrap_or_else(): lazy default evaluation
    ///
    /// ```text
    /// #[ensures(match *self {
    ///     Some(v) => result == v,
    ///     None => result == f(),
    /// })]
    /// fn unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T;
    /// ```
    fn unwrap_or_else_spec<F: FnOnce() -> T>(self, f: F) -> T;

    /// Specification for as_ref(): converts &Option<T> to Option<&T>
    ///
    /// ```text
    /// #[ensures(match *self {
    ///     Some(ref v) => result == Some(v),
    ///     None => result == None,
    /// })]
    /// fn as_ref(&self) -> Option<&T>;
    /// ```
    fn as_ref_spec(&self) -> Option<&T>;

    /// Specification for as_mut(): converts &mut Option<T> to Option<&mut T>
    ///
    /// ```text
    /// #[ensures(match *self {
    ///     Some(ref mut v) => result == Some(v),
    ///     None => result == None,
    /// })]
    /// fn as_mut(&mut self) -> Option<&mut T>;
    /// ```
    fn as_mut_spec(&mut self) -> Option<&mut T>;
}

impl<T> OptionSpec<T> for Option<T> {
    fn is_some_spec(&self) -> bool {
        self.is_some()
    }

    fn is_none_spec(&self) -> bool {
        self.is_none()
    }

    fn unwrap_spec(self) -> T {
        self.unwrap()
    }

    fn unwrap_or_spec(self, default: T) -> T {
        self.unwrap_or(default)
    }

    fn map_spec<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U> {
        self.map(f)
    }

    fn and_then_spec<U, F: FnOnce(T) -> Option<U>>(self, f: F) -> Option<U> {
        self.and_then(f)
    }

    fn or_else_spec<F: FnOnce() -> Option<T>>(self, f: F) -> Option<T> {
        self.or_else(f)
    }

    fn ok_or_spec<E>(self, err: E) -> Result<T, E> {
        self.ok_or(err)
    }

    fn ok_or_else_spec<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E> {
        self.ok_or_else(err)
    }

    fn take_spec(&mut self) -> Option<T> {
        self.take()
    }

    fn replace_spec(&mut self, value: T) -> Option<T> {
        self.replace(value)
    }

    fn expect_spec(self, msg: &str) -> T {
        self.expect(msg)
    }

    fn unwrap_or_else_spec<F: FnOnce() -> T>(self, f: F) -> T {
        self.unwrap_or_else(f)
    }

    fn as_ref_spec(&self) -> Option<&T> {
        self.as_ref()
    }

    fn as_mut_spec(&mut self) -> Option<&mut T> {
        self.as_mut()
    }
}

/// Stable logical helper methods for `Option<T>`.
pub trait OptionExt<T> {
    /// Same as [`Option::unwrap`], but on the logical helper surface.
    fn unwrap_logic(self) -> T;

    /// Same as [`Option::and_then`], but with a total mapping.
    fn and_then_logic<U: Clone>(self, f: Mapping<T, Option<U>>) -> Option<U>
    where
        T: Eq + Hash;

    /// Same as [`Option::map`], but with a total mapping.
    fn map_logic<U: Clone>(self, f: Mapping<T, U>) -> Option<U>
    where
        T: Eq + Hash;
}

impl<T> OptionExt<T> for Option<T> {
    fn unwrap_logic(self) -> T {
        match self {
            Some(value) => value,
            None => unreachable(),
        }
    }

    fn and_then_logic<U: Clone>(self, f: Mapping<T, Option<U>>) -> Option<U>
    where
        T: Eq + Hash,
    {
        match self {
            Some(value) => f.get(value),
            None => None,
        }
    }

    fn map_logic<U: Clone>(self, f: Mapping<T, U>) -> Option<U>
    where
        T: Eq + Hash,
    {
        self.map(|value| f.get(value))
    }
}

/// Internal specification definitions used by the driver's hardcoded fallback
/// tables and local tests. Builtin registry loading happens separately.
///
/// These are structured as data that the driver can query.
#[doc(hidden)]
pub mod specs {
    /// Contract for `Option::is_some`
    pub const IS_SOME: &str = r#"
        ensures: result == (*self != None)
    "#;

    /// Contract for `Option::is_none`
    pub const IS_NONE: &str = r#"
        ensures: result == (*self == None)
    "#;

    /// Contract for `Option::unwrap`
    pub const UNWRAP: &str = r#"
        requires: *self != None
        ensures: Some(result) == *self
    "#;

    /// Contract for `Option::unwrap_or`
    pub const UNWRAP_OR: &str = r#"
        ensures: match *self {
            Some(v) => result == v,
            None => result == default,
        }
    "#;

    /// Contract for `Option::map`
    pub const MAP: &str = r#"
        ensures: match *self {
            Some(v) => result == Some(f(v)),
            None => result == None,
        }
    "#;

    /// Contract for `Option::and_then`
    pub const AND_THEN: &str = r#"
        ensures: match *self {
            Some(v) => result == f(v),
            None => result == None,
        }
    "#;

    /// Contract for `Option::take`
    pub const TAKE: &str = r#"
        ensures: (^self) == None
        ensures: result == old(*self)
    "#;

    /// Contract for `Option::replace`
    pub const REPLACE: &str = r#"
        ensures: (^self) == Some(value)
        ensures: result == old(*self)
    "#;

    /// Contract for `Option::or_else`
    pub const OR_ELSE: &str = r#"
        ensures: match *self {
            Some(_) => result == *self,
            None => result == f(),
        }
    "#;

    /// Contract for `Option::expect`
    ///
    /// Same as unwrap, but with custom panic message.
    pub const EXPECT: &str = r#"
        requires: *self != None
        ensures: Some(result) == *self
    "#;

    /// Contract for `Option::unwrap_or_else`
    ///
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const UNWRAP_OR_ELSE: &str = r#"
        ensures: self.is_some() ==> result == self.unwrap()
        ensures: self.is_none() ==> result == f()
    "#;

    /// Contract for `Option::as_ref`
    ///
    /// Uses implication-style postconditions for solver tractability.
    /// as_ref preserves the Some/None status and inner value. (#1296)
    pub const AS_REF: &str = r#"
        ensures: self.is_some() ==> result.is_some()
        ensures: self.is_some() ==> result.unwrap() == self.unwrap()
        ensures: self.is_none() ==> result.is_none()
    "#;

    /// Contract for `Option::as_mut`
    ///
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const AS_MUT: &str = r#"
        ensures: self.is_some() ==> result.is_some()
        ensures: self.is_some() ==> result.unwrap() == self.unwrap()
        ensures: self.is_none() ==> result.is_none()
    "#;

    /// Contract for `Option::ok_or`
    ///
    /// Uses implication-style with tester/selector methods to avoid sort
    /// mismatches between Option<T> and Result<T, E> sorts. Direct
    /// constructor comparisons (`result == Ok(v)`) can fail when the
    /// encoder assigns different sorts to the Ok/Err constructors in the
    /// spec vs the assertion. Tester methods (is_ok/is_err) and selectors
    /// (unwrap/unwrap_err) operate within their own sort, avoiding the
    /// cross-type sort mismatch. (#2675)
    pub const OK_OR: &str = r#"
        params: self, err
        ensures: self.is_some() ==> result.is_ok()
        ensures: self.is_some() ==> result.unwrap() == self.unwrap()
        ensures: self.is_none() ==> result.is_err()
        ensures: self.is_none() ==> result.unwrap_err() == err
    "#;

    /// Contract for `Option::ok_or_else`
    ///
    /// Uses implication-style with tester/selector methods to avoid sort
    /// mismatches. See `OK_OR` for rationale. (#2675)
    pub const OK_OR_ELSE: &str = r#"
        params: self, err
        ensures: self.is_some() ==> result.is_ok()
        ensures: self.is_some() ==> result.unwrap() == self.unwrap()
        ensures: self.is_none() ==> result.is_err()
        ensures: self.is_none() ==> result.unwrap_err() == err()
    "#;

    /// Contract for `Option::unwrap_or_default`
    ///
    /// Returns the contained value or a default.
    /// Uses implication-style postconditions for solver tractability. (#1296)
    pub const UNWRAP_OR_DEFAULT: &str = r#"
        ensures: self.is_some() ==> result == self.unwrap()
        ensures: self.is_none() ==> result@ == 0
    "#;

    /// Contract for `Option::unwrap_unchecked`
    ///
    /// Unsafe: caller must ensure `self` is `Some`.
    pub const UNWRAP_UNCHECKED: &str = r#"
        requires: *self != None
        ensures: Some(result) == *self
    "#;

    /// Contract for `Option::inspect`
    ///
    /// Calls the closure on the contained value (if any), then returns self.
    pub const INSPECT: &str = r#"
        ensures: result == *self
    "#;

    /// Contract for `Option::map_or`
    ///
    /// Returns the provided default (if None), or applies a function to
    /// the contained value.
    pub const MAP_OR: &str = r#"
        params: self, default, f
        ensures: self.is_none() ==> result == default
    "#;

    /// Contract for `Option::map_or_else`
    ///
    /// Computes a default (if None), or applies a function to the contained value.
    pub const MAP_OR_ELSE: &str = r#"
        params: self, default, f
        ensures: self.is_none() ==> result == default()
    "#;

    /// Contract for `Option::and`
    ///
    /// Returns `None` if self is `None`, otherwise returns `optb`.
    pub const AND: &str = r#"
        params: self, optb
        ensures: self.is_none() ==> result == None
        ensures: self.is_some() ==> result == optb
    "#;

    /// Contract for `Option::or`
    ///
    /// Returns self if it is `Some`, otherwise returns `optb`.
    pub const OR: &str = r#"
        params: self, optb
        ensures: self.is_some() ==> result == *self
        ensures: self.is_none() ==> result == optb
    "#;

    /// Contract for `Option::xor`
    ///
    /// Returns `Some` if exactly one of self, optb is `Some`.
    pub const XOR: &str = r#"
        params: self, optb
        ensures: self.is_some() && optb.is_none() ==> result == *self
        ensures: self.is_none() && optb.is_some() ==> result == optb
        ensures: self.is_some() && optb.is_some() ==> result == None
        ensures: self.is_none() && optb.is_none() ==> result == None
    "#;

    /// Contract for `Option::filter`
    ///
    /// Returns `None` if self is `None`, otherwise calls `predicate`
    /// and returns `Some(v)` if predicate returns true, else `None`.
    pub const FILTER: &str = r#"
        ensures: self.is_none() ==> result == None
    "#;

    /// Contract for `Option::is_some_and`
    ///
    /// Returns true if self is `Some` and the predicate returns true.
    pub const IS_SOME_AND: &str = r#"
        ensures: self.is_none() ==> result == false
    "#;

    /// Contract for `Option::insert`
    ///
    /// Inserts a value, then returns a mutable reference to it.
    pub const INSERT: &str = r#"
        params: self, value
        ensures: (^self) == Some(value)
    "#;

    /// Contract for `Option::get_or_insert`
    ///
    /// Inserts `value` if self is `None`, then returns a mutable reference
    /// to the contained value.
    pub const GET_OR_INSERT: &str = r#"
        params: self, value
        ensures: self.is_some() ==> *result == old(*self).unwrap()
        ensures: self.is_none() ==> *result == value
    "#;

    /// Contract for `Option::get_or_insert_with`
    ///
    /// Inserts a value computed from `f` if self is `None`, then returns
    /// a mutable reference to the contained value.
    pub const GET_OR_INSERT_WITH: &str = r#"
        ensures: old(*self).is_some() ==> *result == old(*self).unwrap()
    "#;

    /// Contract for `Option::take_if`
    ///
    /// Takes the value out if the predicate returns true, replacing with `None`.
    pub const TAKE_IF: &str = r#"
        ensures: self.is_none() ==> result == None
    "#;

    /// Contract for `Option::copied` (for Option<&T>)
    ///
    /// Maps an `Option<&T>` to an `Option<T>` by copying the contents.
    pub const COPIED: &str = r#"
        ensures: self.is_none() ==> result == None
        ensures: self.is_some() ==> result == Some(*self.unwrap())
    "#;

    /// Contract for `Option::cloned` (for Option<&T>)
    ///
    /// Maps an `Option<&T>` to an `Option<T>` by cloning the contents.
    pub const CLONED: &str = r#"
        ensures: self.is_none() ==> result == None
        ensures: self.is_some() ==> result == Some(*self.unwrap())
    "#;

    /// Contract for `Option::zip`
    ///
    /// Zips self with another Option.
    pub const ZIP: &str = r#"
        params: self, other
        ensures: self.is_none() ==> result == None
        ensures: other.is_none() ==> result == None
    "#;

    /// Contract for `Option::unzip` (for Option<(A, B)>)
    ///
    /// Unzips an option containing a tuple into a tuple of options.
    pub const UNZIP: &str = r#"
        ensures: self.is_none() ==> result.0 == None && result.1 == None
    "#;

    /// Contract for `Option::transpose` (for Option<Result<T, E>>)
    ///
    /// Transposes an Option of a Result into a Result of an Option.
    /// Full specification: None -> Ok(None), Some(Ok(v)) -> Ok(Some(v)),
    /// Some(Err(e)) -> Err(e). Uses implication-style for solver
    /// tractability. (#1296)
    pub const TRANSPOSE: &str = r#"
        ensures: self.is_none() ==> result.is_ok()
        ensures: self.is_none() ==> result.unwrap().is_none()
        ensures: self.is_some() ==> result.is_ok() == self.unwrap().is_ok()
    "#;

    /// Contract for `Option::flatten` (for Option<Option<T>>)
    ///
    /// Converts from `Option<Option<T>>` to `Option<T>`.
    pub const FLATTEN: &str = r#"
        ensures: self.is_none() ==> result == None
    "#;

    /// Contract for `Option::iter` — returns an iterator over the contained value.
    ///
    /// Yields 0 elements for None, 1 element for Some(v).
    pub const ITER: &str = r#"
        params: self
    "#;

    /// Contract for `Option::as_deref` — converts `&Option<T>` to `Option<&T::Target>`.
    ///
    /// Preserves None/Some variant.
    pub const AS_DEREF: &str = r#"
        ensures: self.is_none() ==> result == None
        ensures: self.is_some() ==> result.is_some()
    "#;

    /// Contract for `Option::as_deref_mut` — converts `&mut Option<T>` to `Option<&mut T::Target>`.
    pub const AS_DEREF_MUT: &str = r#"
        ensures: self.is_none() ==> result == None
        ensures: self.is_some() ==> result.is_some()
    "#;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::Mapping;

    #[test]
    fn test_is_some_spec() {
        let some: Option<i32> = Some(42);
        let none: Option<i32> = None;
        assert!(some.is_some_spec());
        assert!(!none.is_some_spec());
    }

    #[test]
    fn test_is_none_spec() {
        let some: Option<i32> = Some(42);
        let none: Option<i32> = None;
        assert!(!some.is_none_spec());
        assert!(none.is_none_spec());
    }

    #[test]
    fn test_unwrap_spec() {
        let some: Option<i32> = Some(42);
        assert_eq!(some.unwrap_spec(), 42);
    }

    #[test]
    fn test_unwrap_or_spec() {
        let some: Option<i32> = Some(42);
        let none: Option<i32> = None;
        assert_eq!(some.unwrap_or_spec(0), 42);
        assert_eq!(none.unwrap_or_spec(0), 0);
    }

    #[test]
    fn test_map_spec() {
        let some: Option<i32> = Some(2);
        let none: Option<i32> = None;
        assert_eq!(some.map_spec(|v| v * 2), Some(4));
        assert_eq!(none.map_spec(|v| v * 2), None);
    }

    #[test]
    fn test_and_then_spec() {
        let some: Option<i32> = Some(3);
        let none: Option<i32> = None;
        assert_eq!(some.and_then_spec(|v| Some(v + 1)), Some(4));
        assert_eq!(none.and_then_spec(|v| Some(v + 1)), None);
    }

    #[test]
    fn test_or_else_spec() {
        let some: Option<i32> = Some(7);
        let none: Option<i32> = None;
        assert_eq!(some.or_else_spec(|| Some(1)), Some(7));
        assert_eq!(none.or_else_spec(|| Some(1)), Some(1));
    }

    #[test]
    fn test_take_spec() {
        let mut opt = Some(42);
        let taken = opt.take_spec();
        assert_eq!(taken, Some(42));
        assert!(opt.is_none());
    }

    #[test]
    fn test_take_spec_none() {
        let mut opt: Option<i32> = None;
        let taken = opt.take_spec();
        assert_eq!(taken, None);
        assert!(opt.is_none());
    }

    #[test]
    fn test_replace_spec() {
        let mut opt = Some(42);
        let old = opt.replace_spec(100);
        assert_eq!(old, Some(42));
        assert_eq!(opt, Some(100));
    }

    #[test]
    fn test_replace_spec_none() {
        let mut opt: Option<i32> = None;
        let old = opt.replace_spec(7);
        assert_eq!(old, None);
        assert_eq!(opt, Some(7));
    }

    #[test]
    fn test_expect_spec() {
        let some: Option<i32> = Some(42);
        assert_eq!(some.expect_spec("should have value"), 42);
    }

    #[test]
    fn test_unwrap_or_else_spec() {
        let some: Option<i32> = Some(42);
        let none: Option<i32> = None;
        assert_eq!(some.unwrap_or_else_spec(|| 100), 42);
        assert_eq!(none.unwrap_or_else_spec(|| 100), 100);
    }

    #[test]
    fn test_ok_or_spec() {
        let some: Option<i32> = Some(42);
        let none: Option<i32> = None;
        assert_eq!(some.ok_or_spec(false), Ok(42));
        assert_eq!(none.ok_or_spec(true), Err(true));
    }

    #[test]
    fn test_ok_or_else_spec() {
        let some: Option<i32> = Some(42);
        let none: Option<i32> = None;
        assert_eq!(some.ok_or_else_spec(|| false), Ok(42));
        assert_eq!(none.ok_or_else_spec(|| true), Err(true));
    }

    #[test]
    fn test_as_ref_spec() {
        let some: Option<i32> = Some(42);
        let none: Option<i32> = None;
        assert_eq!(some.as_ref_spec(), Some(&42));
        assert_eq!(none.as_ref_spec(), None);
    }

    #[test]
    fn test_as_mut_spec() {
        let mut some: Option<i32> = Some(42);
        let mut none: Option<i32> = None;
        if let Some(v) = some.as_mut_spec() {
            *v = 100;
        }
        assert_eq!(some, Some(100));
        assert_eq!(none.as_mut_spec(), None);
    }

    #[test]
    fn test_unwrap_logic() {
        assert_eq!(Some(42_i32).unwrap_logic(), 42);
    }

    #[test]
    fn test_map_logic() {
        let mapping = Mapping::cst(0_i32).set(1_i32, 10_i32);
        assert_eq!(Some(1_i32).map_logic(mapping), Some(10));
        assert_eq!(Option::<i32>::None.map_logic(Mapping::cst(5_i32)), None);
    }

    #[test]
    fn test_and_then_logic() {
        let mapping = Mapping::cst(None::<i32>).set(3_i32, Some(4_i32));
        assert_eq!(Some(3_i32).and_then_logic(mapping), Some(4));
        assert_eq!(
            Option::<i32>::None.and_then_logic(Mapping::cst(Some(1_i32))),
            None
        );
    }
}
