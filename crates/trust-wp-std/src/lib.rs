// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub
)]
#![cfg_attr(
    test,
    allow(
        clippy::bool_assert_comparison,
        clippy::needless_borrows_for_generic_args,
        clippy::no_effect_underscore_binding,
        clippy::used_underscore_items,
        clippy::useless_vec
    )
)]

//! trust-wp Std - Verified standard library specifications
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This crate provides specifications for Rust standard library types:
//! - `Vec<T>` - Dynamic arrays
//! - `Option<T>` - Optional values
//! - `Result<T, E>` - Error handling
//! - `String` - Owned UTF-8 string type
//! - `Cell<T>` / `RefCell<T>` - Interior mutability
//! - `clone` - Clone trait specifications
//! - `cmp` - Comparison trait specifications (`Ord`, `PartialOrd`)
//! - `collections` - `HashMap`, `BTreeMap`, `VecDeque`
//! - `duration` - `Duration` specifications
//! - `instant` - `Instant` specifications
//! - `iter` - Iterator trait specifications
//! - `mem` - Memory operations (`swap`, `replace`, etc.)
//! - `ops` - Operator traits (`Index`, `Deref`, etc.)
//! - `primitives` - Primitive type specifications (`i32`, `u64`, etc.)
//! - `ptr` - Pointer operations
//! - `slice` - Slice specifications (`[T]`)
//! - `sync` - Synchronization primitives (`Arc`, `Mutex`, etc.)
//!
//! These specifications allow trust-wp to verify code that uses standard
//! library types without requiring the full standard library to be verified.
//!
//! # Usage
//!
//! ```rust
//! use trust_wp_std::prelude::*;
//!
//! // Logic types for specifications
//! let seq: Seq<i32> = Seq::empty();
//! let n: Int = Int::from(42);
//!
//! // Spec traits extend std types
//! let opt: Option<i32> = Some(42);
//! assert!(opt.is_some_spec());
//! ```
//!
//! # Trait Naming Convention
//!
//! Specification traits use two suffixes following Creusot conventions:
//!
//! - **`Spec`** — Behavioral contracts for methods that already exist on a
//!   standard library type. Each `Spec` trait provides `_spec()` counterparts
//!   (e.g., `is_some_spec()`, `len_spec()`) that the trust-wp-driver resolves
//!   internally. Examples: [`VecSpec`], [`OptionSpec`], [`StringSpec`].
//!
//! - **`Ext`** — New logical or ghost capabilities added to a type that have
//!   no runtime std counterpart. These provide specification-only operations
//!   such as pointer addresses, permission tokens, and invariant protocols.
//!   Examples: [`CharExt`], [`NumExt`], [`OptionExt`], [`SliceExt`],
//!   [`PointerExt`], [`PtrAddExt`], [`SlicePermExt`], [`SlicePointerExt`].
//!
//! Both suffixes are re-exported from [`prelude`].
//!
//! [`CharExt`]: crate::std::char::CharExt
//! [`NumExt`]: crate::std::num::NumExt
//! [`OptionExt`]: crate::std::option::OptionExt
//! [`SliceExt`]: crate::std::slice::SliceExt
//! [`VecSpec`]: crate::std::vec::VecSpec
//! [`OptionSpec`]: crate::std::option::OptionSpec
//! [`StringSpec`]: crate::std::string::StringSpec
//! [`PointerExt`]: crate::std::ptr::PointerExt
//! [`PtrAddExt`]: crate::std::ptr::PtrAddExt
//! [`SlicePermExt`]: crate::std::slice::SlicePermExt
//! [`SlicePointerExt`]: crate::std::ptr::SlicePointerExt
//!
//! # Architecture
//!
//! - `ghost` - Ghost code support (erased at compile time)
//! - `logic` - Logical types (Seq, Int, `FMap`, `FSet`) for specification reasoning
//! - `std` - Specifications for std types (Vec, Option, Result, String, etc.)
//! - `invariant` - Type invariants for verification
//! - `resolve` - Borrow termination resolve predicate
//! - `prelude` - Common re-exports

// Re-export macros for use in specifications
pub use trust_wp_macros::{
    assume, bitwise_proof, builtin, check, ensures, erasure, extern_spec, ghost, ghost_let,
    invariant, law, logic, maintains, opaque, open_inv_result, pearlite, predicate, proof_assert,
    requires, snapshot, terminates, trusted, variant, DeepModel, Default,
};

/// Ghost code support for specifications
///
/// Ghost code exists only for verification and is erased at compile time.
/// Use the [`ghost!`] macro to create ghost blocks and the [`Ghost<T>`](ghost::Ghost)
/// type for ghost values. Use [`snapshot!`] to capture values at specific program
/// points with [`Snapshot<T>`](ghost::Snapshot).
pub mod ghost;

/// Logical types for specifications
///
/// These types have no runtime representation but are used in contracts
/// to reason about program behavior without machine integer overflow concerns.
pub mod logic;

/// Specifications for Rust standard library types
///
/// Each submodule provides contracts for the corresponding std type.
/// Builtin `trust-wp-std` extern specs are registered with the driver directly.
/// Local `extern_spec!` definitions can override those entries, and hardcoded
/// `std_specs` tables remain as fallback and compatibility coverage.
#[allow(clippy::module_inception)]
pub mod std;

/// Type invariants for verification.
///
/// Types implementing [`Invariant`](invariant::Invariant) declare structural
/// properties that must hold at all program points.
pub mod invariant;

/// Peano integers for overflow-free incrementing.
///
/// Useful in data structures where the length only grows by one at a time
/// and overflow checking is impractical.
pub mod peano;

/// Sync view types for atomic invariant protocols.
///
/// Provides `SyncView`, `Timestamp`, and `AtView` for reasoning about
/// release-acquire and sequentially-consistent atomic operations.
pub mod sync_view;

/// The `resolve` predicate for borrow termination.
///
/// When a mutable borrow ends, `resolve(x)` asserts that the current value
/// equals the prophecy (final) value: `*x == ^x`.
pub mod resolve;

/// Interior mutability for verification.
///
/// Re-exports [`std::cell`] at the crate root for Creusot compatibility.
/// In Creusot, `creusot_std::cell::PermCell` is the primary import path;
/// trust-wp stores cell types under `trust_wp_std::std::cell` but re-exports
/// them here so that the Creusot path resolves. (#2682)
pub use crate::std::cell;

/// Prelude for convenient imports
///
/// ```rust
/// use trust_wp_std::prelude::*;
/// ```
pub mod prelude;
