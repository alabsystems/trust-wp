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

//! Creusot standard library compatibility shim for trust-wp.
//!
//! This crate re-exports trust-wp-std modules under the `creusot_std` namespace,
//! allowing Creusot test code to compile against trust-wp without source
//! modification.
//!
//! # Usage
//!
//! Creusot tests that use:
//! ```rust,ignore
//! use creusot_std::prelude::*;
//! ```
//! will get all trust-wp macros and types via this shim.
//!
//! Part of #459 (Creusot compat shim).

// Make `trust_wp_std` available as an extern crate so that proc macro expansions
// using `::trust_wp_std::...` paths resolve correctly in downstream crates.
// Without this, `ghost!`, `snapshot!`, `proof_assert!` etc. fail with
// "could not find `trust_wp_std` in the list of imported crates".
pub extern crate trust_wp_std;

// Re-export trust-wp-std modules to match creusot_std module paths.
// Note: we cannot re-export macros (ghost!, logic!, snapshot!) at crate root
// because their names conflict with the module re-exports. Creusot avoids
// this by defining modules inline rather than re-exporting. The macros are
// available via `creusot_std::macros::*` and `creusot_std::prelude::*`.
// Re-export commonly-used types at crate root (matching creusot_std patterns).
// These don't conflict because they're type names, not module names.
// Re-export the declare_namespace! macro from trust-wp-std.
// #[macro_export] places it at the trust_wp_std crate root; we re-export it here
// so that `creusot_std::declare_namespace!` works for Creusot compat tests
// (e.g., parallel_add.rs, message_passing_*.rs).
pub use trust_wp_std::{
    declare_namespace, ghost,
    ghost::{
        invariant::{
            AtomicInvariant, AtomicInvariantSC, NonAtomicInvariant, NonAtomicInvariantExt,
            Protocol, Tokens,
        },
        perm::Perm,
        resource::{Authority, Fragment, Resource},
        Ghost, Snapshot,
    },
    invariant,
    invariant::Invariant,
    logic,
    logic::{
        dead, such_that, unreachable, view, DeepModel, FMap, FSet, Int, Mapping, OrdLogic, Seq,
        View, WellFounded,
    },
    peano,
    peano::PeanoInt,
    resolve,
    resolve::Resolve,
    std,
    std::{cell, ptr::PointerExt},
    sync_view,
    sync_view::{AtView, SyncView},
};

/// Snapshot module, matching `creusot_std::snapshot::Snapshot`.
///
/// In Creusot, `Snapshot` is available both at `creusot_std::Snapshot` (re-export)
/// and `creusot_std::snapshot::Snapshot` (module path). This module provides the
/// latter path for diagnostic and import compatibility.
///
/// Part of #1804.
pub mod snapshot {
    pub use trust_wp_std::ghost::Snapshot;
}

/// Specification macros, matching `creusot_std::macros`.
pub mod macros {
    pub use trust_wp::{
        bitwise_proof, check, ensures, erasure, extern_spec, ghost, ghost_let, invariant, law,
        logic, maintains, opaque, open_inv_result, pearlite, predicate, proof_assert, requires,
        snapshot, trusted, variant, DeepModel, Default,
    };
}

/// Specification model traits (`View`, `DeepModel`).
pub mod model {
    pub use trust_wp_std::logic::{DeepModel, View};
}

/// Prelude matching `creusot_std::prelude::*`.
///
/// This re-exports all macros and commonly-used types, matching the
/// convention that Creusot tests use `use creusot_std::prelude::*;`.
pub mod prelude {
    // All proc macros
    // Re-export std::vec module so `use creusot_std::prelude::{vec, *}` resolves.
    // In Creusot, `vec` is a custom macro; here we re-export the std module
    // which provides `vec!` macro and `Vec` type.
    //
    // Do not glob-reexport Rust's prelude here. That would leak the built-in
    // `Default` derive back into this facade and defeat the compatibility
    // proc macro export below.
    // `PartialEq` follows Creusot's base_prelude export of `cmp::PartialEq`. (#2500)
    pub use std::{cmp::PartialEq, vec};

    pub use trust_wp::{
        bitwise_proof, builtin, check, ensures, erasure, extern_spec, ghost, ghost_let, invariant,
        law, logic, maintains, opaque, open_inv_result, pearlite, predicate, proof_assert,
        requires, snapshot, trusted, variant, DeepModel,
    };
    // Ghost and snapshot types
    pub use trust_wp_std::ghost::{
        invariant::{
            AtomicInvariant, AtomicInvariantSC, NonAtomicInvariant, NonAtomicInvariantExt,
            Protocol, Tokens,
        },
        perm::Perm,
        resource::{Authority, Fragment, Resource},
        Ghost, Snapshot,
    };
    // Type invariants and resolve
    pub use trust_wp_std::invariant::{inv, Invariant};
    // Logical indexing (matching upstream base_prelude logic::ops block).
    pub use trust_wp_std::logic::ops::IndexLogic as _;
    // Logic types and stubs
    pub use trust_wp_std::logic::{
        dead, view, FMap, FSet, Int, Mapping, OrdLogic, Seq, View, WellFounded,
    };
    // seq! macro for constructing Seq literals in ghost/snapshot contexts
    pub use trust_wp_std::seq;
    // `Clone` follows Creusot's facade path through `std::clone`.
    pub use trust_wp_std::std::clone::Clone;
    // `Default` follows Creusot's facade path through `std::default`.
    pub use trust_wp_std::std::default::Default;
    // Range-helper facade (matching upstream std::ops range surface).
    pub use trust_wp_std::std::ops::{
        between, lower_bound, upper_bound, RangeBounds, RangeInclusiveExt,
    };
    // Closure spec extension traits (matching upstream base_prelude ops block).
    pub use trust_wp_std::std::ops::{FnExt as _, FnMutExt as _, FnOnceExt as _};
    // Pointer and slice extension traits
    pub use trust_wp_std::std::ptr::{PointerExt, SizedPointerExt};
    // Export extension traits anonymously to match Creusot's base-prelude.
    pub use trust_wp_std::std::{
        char::CharExt as _,
        num::NumExt as _,
        option::OptionExt as _,
        ptr::{PtrAddExt as _, SlicePointerExt as _},
        slice::{SliceExt as _, SliceMutExt as _},
    };
    pub use trust_wp_std::{
        resolve::{resolve, Resolve},
        std::{
            iter::{
                ClonedExt, CopiedExt, DoubleEndedIteratorSpec, EnumerateExt, FilterExt,
                FilterMapExt, FromIteratorSpec, FuseExt, IteratorSpec, MapExt, MapInv, RevExt,
                SkipExt, TakeExt, ZipExt,
            },
            option::OptionSpec,
            result::ResultSpec,
            string::StringSpec,
            vec::VecSpec,
        },
    };
}
