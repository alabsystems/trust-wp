// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The `resolve` predicate for borrow termination.
//!
//! In the RustHorn encoding, mutable references carry a "prophecy" variable
//! (`^x`, the final value) alongside the "current" variable (`*x`). When a
//! mutable borrow ends (is "resolved"), the current value equals the final
//! value:
//!
//! ```text
//! resolve(x) ≡ *x == ^x     (i.e., x_current == x_final)
//! ```
//!
//! For compound types:
//! ```text
//! resolve((a, b)) ≡ resolve(a) && resolve(b)
//! ```
//!
//! For shared references: `resolve(&x) ≡ true` (no prophecy variable).
//!
//! # Usage in contracts
//!
//! `resolve` appears in closure contracts when an `FnMut` closure is called
//! through `FnOnce`:
//!
//! ```text
//! postcondition_once(self, args, result) ≡
//!   exists<res_state> postcondition_mut(self, args, res_state, result)
//!                     && resolve(res_state)
//! ```
//!
//! This connects the three-level closure trait hierarchy: when you consume a
//! mutable closure (FnOnce), the post-state must resolve (the borrow ends).
//!
//! # Encoding
//!
//! The ay encoder recognizes `resolve(x)` as a built-in logic function and
//! expands it to `x_current == x_final` for simple (Int) types. For closure
//! environment types, it generates a conjunction of per-field resolve
//! predicates.

use crate::logic;

/// Trait for types whose borrows can be resolved (terminated).
///
/// In Creusot/trust-wp, `Resolve` is the specification-level trait that describes
/// what happens when a mutable borrow ends. For most types, resolving means
/// the current value equals the final (prophecy) value.
///
/// Types can implement `Resolve` to provide a custom resolve predicate for
/// opaque types. The `resolve_coherence` method serves as a proof obligation
/// showing that structural resolve implies the custom resolve predicate.
///
/// In trust-wp, the ay encoder handles resolve semantics as a built-in for
/// types that do not explicitly implement this trait. This trait exists for
/// source compatibility with Creusot tests that define custom resolve impls
/// (e.g., `hashmap_list.rs`).
///
/// Both methods are logic-mode (prophetic) in Creusot's design — implementers
/// override with `#[logic(prophetic)]` or `#[logic(prophetic, open)]`. The
/// trait/impl consistency checker enforces this.
///
/// Reference: Creusot `creusot-std/src/resolve.rs`
pub trait Resolve {
    /// The resolve predicate: `*self == ^self` (current equals final).
    ///
    /// Specification-only — panics if called at runtime.
    #[allow(unused_variables)]
    #[track_caller]
    #[logic(prophetic)]
    fn resolve(self) -> bool
    where
        Self: Sized,
    {
        panic!("resolve() is specification-only and cannot be called at runtime")
    }

    /// Proof obligation: structural resolve implies custom resolve.
    ///
    /// This method serves as a coherence proof that the structural
    /// decomposition (`structural_resolve(self)`) implies the custom
    /// `resolve` predicate. Creusot tests define this to demonstrate
    /// that their custom resolve is consistent with structural resolve.
    ///
    /// Specification-only — panics if called at runtime.
    ///
    /// Reference: Creusot `creusot-std/src/resolve.rs:29-32`
    #[allow(unused_variables)]
    #[track_caller]
    #[logic(prophetic)]
    fn resolve_coherence(self)
    where
        Self: Sized;
}

/// Resolve a value (specification-only function).
///
/// Asserts that the current value of `x` equals its final (prophecy) value,
/// meaning the borrow has ended.
///
/// This function works on all types (no `Resolve` bound required), matching
/// Creusot's `#[intrinsic("resolve")]` function which is not trait-gated.
/// The `Resolve` trait is a separate, opt-in mechanism for custom resolve
/// predicates on opaque types.
///
/// Reference: Creusot `creusot-std/src/resolve.rs:10-13`
#[must_use]
#[track_caller]
pub fn resolve<T>(_x: T) -> bool {
    panic!("resolve() is specification-only and cannot be called at runtime")
}

/// Structurally resolve a value (specification-only function).
///
/// Like `resolve`, but decomposes compound types field-by-field:
/// `structural_resolve((a, b))` ≡ `resolve(a) && resolve(b)`.
///
/// This function works on all types (no `Resolve` bound required), matching
/// Creusot's `#[intrinsic("structural_resolve")]` function.
///
/// Reference: Creusot `creusot-std/src/resolve.rs:35-39`
#[must_use]
#[track_caller]
pub fn structural_resolve<T>(_x: T) -> bool {
    panic!("structural_resolve() is specification-only and cannot be called at runtime")
}

// Implementations for fundamental reference types, matching Creusot's
// `creusot-std/src/resolve.rs:43-64`.

impl<T: ?Sized> Resolve for &T {
    #[cfg_attr(trust_wp, crate::logic(prophetic))]
    fn resolve(self) -> bool {
        true
    }

    #[cfg_attr(trust_wp, crate::logic(prophetic))]
    fn resolve_coherence(self) {}
}

impl<T: ?Sized> Resolve for &mut T {
    #[cfg_attr(trust_wp, crate::logic(prophetic))]
    fn resolve(self) -> bool {
        true
    }

    #[cfg_attr(trust_wp, crate::logic(prophetic))]
    fn resolve_coherence(self) {}
}

// `Box<T>` is logically transparent: resolving a Box is structurally equivalent
// to resolving the inner value. Creusot's nightly Box impl returns `true` and
// relies on `structural_resolve` to drive the per-field obligations; the
// non-nightly fallback uses the default `true` body via `impl<T: ?Sized>
// Resolve for Box<T> {}`. We mirror the non-nightly form so Box matches the
// blanket reference impls above.
//
// Reference: Creusot `creusot-std/src/std/boxed.rs:29-41,119-120`
impl<T: ?Sized> Resolve for Box<T> {
    #[cfg_attr(trust_wp, crate::logic(prophetic))]
    fn resolve(self) -> bool {
        true
    }

    #[cfg_attr(trust_wp, crate::logic(prophetic))]
    fn resolve_coherence(self) {}
}

/// Marker module for `resolve` predicate specification.
///
/// The actual `resolve` function is not callable at runtime — it exists only
/// in specification context. The ay encoder handles it as a built-in.
#[doc(hidden)]
pub mod specs {
    /// Specification text for `resolve` — used by trust-wp-driver for lookup.
    ///
    /// For simple types: `resolve(x)` means `*x == ^x` (current equals final).
    pub const RESOLVE_SIMPLE: &str = "resolve(x) == (*x == ^x)";
}
