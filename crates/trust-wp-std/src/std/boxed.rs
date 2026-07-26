// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for `alloc::boxed::Box<T>`
//!
//! These specifications define the contract semantics for Box methods.
//! trust-wp-driver uses these specs when verifying code that uses Box.
//!
//! ## Design Notes
//!
//! `Box<T>` is logically transparent — it owns a `T` value and dereferencing
//! returns that value. At the verification level, `*box_val == inner_val`.
//! This matches the rustc MIR treatment where `Box::new` already has a
//! special `ResolvedCallKind::BoxNew` that treats it as identity.
//!
//! The specs here cover the remaining Box surface not handled by the
//! identity shortcut: Deref, DerefMut, into_inner, and as_ref/as_mut.

// Allow raw string hashes for spec string literals (consistency over optimization)
#![allow(clippy::needless_raw_string_hashes)]
// Allow doc_markdown pedantic warnings for contract notation
#![allow(clippy::doc_markdown)]

/// Specification trait for `Box<T>` methods (internal).
///
/// This trait documents the contracts for Box methods. **Users should
/// call standard `Box` methods directly** — trust-wp-driver resolves
/// these specs internally via the `std_specs` module. The `_spec()` methods
/// here are for testing trust-wp-std itself.
///
/// # Specifications
///
/// ## new
/// ```text
/// #[ensures(*result == value)]
/// fn new(value: T) -> Box<T>;
/// ```
///
/// ## into_inner (unstable, but modeled)
/// ```text
/// #[ensures(result == *self)]
/// fn into_inner(self) -> T;
/// ```
///
/// ## Deref
/// ```text
/// #[ensures(*result == *self)]
/// fn deref(&self) -> &T;
/// ```
///
/// ## DerefMut
/// ```text
/// #[ensures(*result == *self)]
/// #[ensures(^result == *(^self))]
/// fn deref_mut(&mut self) -> &mut T;
/// ```
///
/// ## leak
/// ```text
/// #[ensures(*result == *b)]
/// fn leak<'a>(b: Box<T>) -> &'a mut T;
/// ```
///
/// ## from_raw (unsafe — postulated unreachable)
/// ```text
/// #[requires(false)]
/// unsafe fn from_raw(raw: *mut T) -> Box<T>;
/// ```
///
/// ## into_raw / drop (opaque post-state)
/// `Box::into_raw` and `<Box<T> as Drop>::drop` have no observable
/// post-condition; they exist only so the verifier can recognise the call
/// sites and emit empty contracts. Resolution of any prophecy obligations
/// on the inner `T` is handled by `<Box<T> as Resolve>::resolve` returning
/// `true` (see `crate::resolve`).
pub trait BoxSpec<T> {
    /// Specification: ensures *result == value
    fn new_spec(value: T) -> Self
    where
        Self: Sized;

    /// Specification: ensures result == *self
    fn into_inner_spec(self) -> T
    where
        Self: Sized;

    /// Specification: ensures *result == *self
    fn deref_spec(&self) -> &T;

    /// Specification: ensures *result == *self, ensures ^result == *(^self)
    fn deref_mut_spec(&mut self) -> &mut T;

    /// Specification: ensures *result == *self
    fn as_ref_spec(&self) -> &T;

    /// Specification: ensures *result == *self, ensures ^result == *(^self)
    fn as_mut_spec(&mut self) -> &mut T;
}

impl<T> BoxSpec<T> for Box<T> {
    fn new_spec(value: T) -> Self {
        Box::new(value)
    }

    fn into_inner_spec(self) -> T {
        *self
    }

    fn deref_spec(&self) -> &T {
        self
    }

    fn deref_mut_spec(&mut self) -> &mut T {
        self
    }

    fn as_ref_spec(&self) -> &T {
        self.as_ref()
    }

    fn as_mut_spec(&mut self) -> &mut T {
        self.as_mut()
    }
}

/// Internal specification definitions used by the driver's hardcoded fallback
/// tables and local tests. Builtin registry loading happens separately.
#[doc(hidden)]
pub mod specs {
    /// Contract for `Box::new`
    ///
    /// Box is logically transparent: the result dereferences to the input value.
    pub const NEW: &str = r"
        ensures: *result == value
    ";

    /// Contract for `Box::into_inner` / `*box_val`
    ///
    /// Unwrapping a Box returns the contained value.
    pub const INTO_INNER: &str = r"
        ensures: result == *self
    ";

    /// Contract for `<Box<T> as Deref>::deref`
    ///
    /// Box deref is the identity on the inner value.
    pub const DEREF: &str = r"
        ensures: *result == *self
    ";

    /// Contract for `<Box<T> as DerefMut>::deref_mut`
    ///
    /// Box deref_mut provides a mutable reference to the inner value.
    /// The final-state postcondition connects the reference prophecy
    /// to the Box's final state.
    pub const DEREF_MUT: &str = r"
        ensures: *result == *self
        ensures: ^result == *(^self)
    ";

    /// Contract for `Box::as_ref`
    ///
    /// Returns a shared reference to the contained value.
    pub const AS_REF: &str = r"
        ensures: *result == *self
    ";

    /// Contract for `Box::as_mut`
    ///
    /// Returns a mutable reference to the contained value.
    pub const AS_MUT: &str = r"
        ensures: *result == *self
        ensures: ^result == *(^self)
    ";

    /// Contract for `Box::from_raw`
    ///
    /// `from_raw` rebuilds a `Box<T>` from a raw pointer. Creusot postulates
    /// `requires: false` because reasoning about raw-pointer construction
    /// requires invariants not expressible in the surface specification
    /// language; the proof obligation is to avoid calling it.
    ///
    /// Reference: Creusot `creusot-std/src/std/boxed.rs:62-64`.
    pub const FROM_RAW: &str = r"
        requires: false
    ";

    /// Contract for `Box::into_raw`
    ///
    /// Consumes the Box and returns a raw pointer to the contained value.
    /// No safety-relevant post-state is specified; Creusot leaves the
    /// post-state opaque so callers cannot reason about pointer identity.
    ///
    /// Reference: Creusot `creusot-std/src/std/boxed.rs:66-67`.
    pub const INTO_RAW: &str = "";

    /// Contract for `Box::leak`
    ///
    /// Leaks the Box, returning a `'a mut T` borrow. The returned reference
    /// dereferences to the same value as the Box did.
    ///
    /// Reference: Creusot `creusot-std/src/std/boxed.rs:80-84`.
    pub const LEAK: &str = r"
        ensures: *result == *b
    ";

    /// Contract for `<Box<T> as Drop>::drop`
    ///
    /// Box's drop is logically a no-op for verification: dropping does not
    /// expose any observable post-state to specifications. Resolving the
    /// Box (which discharges any prophecy obligations on the inner value)
    /// is handled by `<Box<T> as Resolve>::resolve` returning `true`.
    ///
    /// Reference: Creusot `creusot-std/src/std/boxed.rs:29-50,119-120` —
    /// Box's `Resolve` is trivially `true`, leaving `structural_resolve`
    /// to drive the inner obligation.
    pub const DROP: &str = "";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_box_new_spec() {
        let b = Box::new_spec(42);
        assert_eq!(*b, 42);
    }

    #[test]
    fn test_box_into_inner_spec() {
        let b = Box::new(42);
        let inner = b.into_inner_spec();
        assert_eq!(inner, 42);
    }

    #[test]
    fn test_box_deref_spec() {
        let b = Box::new(42);
        let r = b.deref_spec();
        assert_eq!(*r, 42);
    }

    #[test]
    fn test_box_deref_mut_spec() {
        let mut b = Box::new(42);
        let r = b.deref_mut_spec();
        *r = 99;
        assert_eq!(*b, 99);
    }

    #[test]
    fn test_box_as_ref_spec() {
        let b = Box::new(42);
        let r = b.as_ref_spec();
        assert_eq!(*r, 42);
    }

    #[test]
    fn test_box_as_mut_spec() {
        let mut b = Box::new(42);
        let r = b.as_mut_spec();
        *r = 99;
        assert_eq!(*b, 99);
    }

    #[test]
    fn test_new_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::NEW);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("*result == value"));
    }

    #[test]
    fn test_into_inner_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::INTO_INNER);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("result == *self"));
    }

    #[test]
    fn test_deref_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::DEREF);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("*result == *self"));
    }

    #[test]
    fn test_deref_mut_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::DEREF_MUT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.ensures[0].contains("*result == *self"));
        assert!(spec.ensures[1].contains("^result == *(^self)"));
    }

    #[test]
    fn test_as_ref_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::AS_REF);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("*result == *self"));
    }

    #[test]
    fn test_as_mut_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::AS_MUT);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec.ensures[0].contains("*result == *self"));
        assert!(spec.ensures[1].contains("^result == *(^self)"));
    }

    #[test]
    fn test_from_raw_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::FROM_RAW);
        assert_eq!(spec.requires.len(), 1);
        assert!(spec.requires[0].contains("false"));
        assert!(spec.ensures.is_empty());
    }

    #[test]
    fn test_into_raw_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::INTO_RAW);
        assert!(spec.requires.is_empty());
        assert!(spec.ensures.is_empty());
    }

    #[test]
    fn test_leak_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::LEAK);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("*result == *b"));
    }

    #[test]
    fn test_drop_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(specs::DROP);
        assert!(spec.requires.is_empty());
        assert!(spec.ensures.is_empty());
    }
}
