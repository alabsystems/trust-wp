// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Prelude for trust-wp-std
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module re-exports commonly used types for convenience:
//!
//! - **Contract macros** — `requires`, `ensures`, `proof_assert`, `ghost`,
//!   `snapshot`, `invariant`, `logic`, `predicate`, `variant`, and more
//! - **Separation logic** — Resource algebras (`RA`, `Excl`, `Ag`, `Frac`),
//!   ghost permissions (`Perm`), resources (`Resource`), invariants
//!   (`NonAtomicInvariant`, `Protocol`)
//! - **Logic types** — `Seq`, `Int`, `FMap`, `FSet`, `Mapping`, `DeepModel`
//! - **Spec utilities** — `such_that`, `dead`, `unreachable`
//! - **Std trait re-exports** — `Clone`, `PartialEq`, `Default`
//! - **Std type specs** — `VecSpec`, `OptionSpec`, `ResultSpec`, etc.
//!
//! # Example
//!
//! ```text
//! use trust_wp_std::prelude::*;
//!
//! #[requires(x > 0)]
//! #[ensures(result == x + 1)]
//! fn increment(x: i32) -> i32 { x + 1 }
//! ```
//!
//! # Trait Naming Convention
//!
//! Both `Spec` and `Ext` traits are included in the prelude. Representative
//! helper-family `Ext` exports include `CharExt`, `NumExt`, `OptionExt`,
//! `SliceExt`, `PtrAddExt`, and `SlicePointerExt`. See the
//! [crate-level docs](crate) for the naming convention.
//!
//! # Sync Spec Traits
//!
//! Sync-related spec traits are re-exported here for discoverability.
//! The verification driver recognizes these specs via std_specs lookup,
//! but full pipeline integration (MIR extraction for sync types) is
//! not yet complete. See creusot-compatibility.md (repo root) for status.
//!
//! Guard model structs (MutexGuardSpec, RwLockReadGuardSpec, etc.) are
//! available via `trust_wp_std::std::sync` directly.
//!
//! # `view` Contract in `prelude::*`
//!
//! `prelude::*` re-exports the free `view(...)` function and borrowed
//! collection spec traits (`VecSpec`, `StringSpec`), so `v.view_spec()` and
//! `s.view_spec()` use borrowed receivers and do not consume values.
//!
//! The consuming [`View`](crate::logic::View) trait is intentionally not
//! re-exported from the prelude to avoid method-resolution surprises.
//! Import it explicitly when method-style consuming conversion is desired:
//!
//! ```rust
//! use trust_wp_std::logic::View;
//! ```

// Ghost code support
pub use crate::ghost::{Ghost, Snapshot};
// Type invariants
pub use crate::invariant::{inv, Invariant};
// Resource algebras for separation logic
pub use crate::logic::ra::{Ag, Excl, Frac, Id, UnitRA, RA};
// Logic types and spec utilities
pub use crate::logic::{
    dead, such_that, unreachable, view, DeepModel, FMap, FSet, Int, Mapping, OrdLogic, Seq,
    WellFounded,
};
// Borrow termination
pub use crate::resolve::{resolve, Resolve};
// Specification traits for std types
pub use crate::std::{
    char::CharExt,
    iter::{
        ClonedExt, CopiedExt, DoubleEndedIteratorSpec, EnumerateExt, FilterExt, FilterMapExt,
        FromIteratorSpec, FuseExt, IteratorSpec, MapExt, MapInv, RevExt, SkipExt, TakeExt, ZipExt,
    },
    num::NumExt,
    ops::{between, lower_bound, upper_bound, RangeBounds, RangeInclusiveExt},
    option::{OptionExt, OptionSpec},
    ptr::{PointerExt, PtrAddExt, SizedPointerExt, SlicePointerExt},
    result::ResultSpec,
    slice::{SliceExt, SliceMutExt, SlicePermExt},
    string::StringSpec,
    sync::{
        ArcSpec, CellSpec, Inv, JoinHandleSpec, MutexSpec, RcSpec, RefCellSpec, RwLockSpec, TrueInv,
    },
    vec::VecSpec,
};
// `Clone`, `PartialEq`, and `Default` are re-exported through their `std::`
// submodules so the prelude path matches Creusot's facade while Rust's standard
// prelude still provides the traits.
pub use crate::std::{clone::Clone, cmp::PartialEq, default::Default};
// Contract macros, separation logic types (Perm, Resource, NonAtomicInvariant, Protocol)
// `DeepModel` still needs an explicit macro export because it has no built-in counterpart.
pub use crate::{
    assume, bitwise_proof, check, ensures, erasure, extern_spec, ghost,
    ghost::{
        invariant::{AtomicInvariant, AtomicInvariantSC, NonAtomicInvariant, Protocol},
        perm::Perm,
        resource::{Authority, Fragment, Resource},
    },
    ghost_let, invariant, law, logic, maintains, opaque, open_inv_result, pearlite, predicate,
    proof_assert, requires, seq, snapshot, trusted, variant, DeepModel,
};
