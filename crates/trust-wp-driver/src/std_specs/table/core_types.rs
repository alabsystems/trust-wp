// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core type specs: ghost, option, result, vec.

use trust_wp_std::{
    ghost,
    std::{option, result, vec},
};

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = &[
    (
        &[
            "trust_wp_std::ghost::Ghost::new",
            "trust_wp_std::Ghost::new",
            "creusot_std::ghost::Ghost::new",
            "creusot_std::Ghost::new",
            "creusot_contracts::ghost::Ghost::new",
            "creusot_contracts::Ghost::new",
        ],
        ghost::specs::GHOST_NEW,
    ),
    (
        &[
            "trust_wp_std::ghost::Ghost::inner",
            "trust_wp_std::Ghost::inner",
            "creusot_std::ghost::Ghost::inner",
            "creusot_std::Ghost::inner",
            "creusot_contracts::ghost::Ghost::inner",
            "creusot_contracts::Ghost::inner",
        ],
        ghost::specs::GHOST_INNER,
    ),
    (
        &[
            "trust_wp_std::ghost::Ghost::inner_mut",
            "trust_wp_std::Ghost::inner_mut",
            "creusot_std::ghost::Ghost::inner_mut",
            "creusot_std::Ghost::inner_mut",
            "creusot_contracts::ghost::Ghost::inner_mut",
            "creusot_contracts::Ghost::inner_mut",
        ],
        ghost::specs::GHOST_INNER_MUT,
    ),
    (
        &[
            "trust_wp_std::ghost::Ghost::into_inner",
            "trust_wp_std::Ghost::into_inner",
            "creusot_std::ghost::Ghost::into_inner",
            "creusot_std::Ghost::into_inner",
            "creusot_contracts::ghost::Ghost::into_inner",
            "creusot_contracts::Ghost::into_inner",
        ],
        ghost::specs::GHOST_INTO_INNER,
    ),
    (
        &[
            "trust_wp_std::ghost::Snapshot::capture",
            "trust_wp_std::Snapshot::capture",
            "trust_wp::ghost::Snapshot::capture",
            "trust_wp::Snapshot::capture",
            "creusot_std::ghost::Snapshot::capture",
            "creusot_std::Snapshot::capture",
            "creusot_contracts::ghost::Snapshot::capture",
            "creusot_contracts::Snapshot::capture",
            // Type-directed `snapshot!` capture dispatch (bug/869): the SEMANTIC
            // capture is the free `snapshot_capture_select(&(expr))` — its inline
            // `&(expr)` argument is the sole captured reference (an anonymous
            // reborrow the pipelines collapse), so it is treated exactly like a
            // direct `Snapshot::capture`. The `.capture()` tail is a separate
            // identity (see `SNAPSHOT_CAPTURE_DISPATCH`).
            "trust_wp_std::ghost::snapshot_capture_select",
            "trust_wp_std::snapshot_capture_select",
        ],
        ghost::specs::SNAPSHOT_CAPTURE,
    ),
    // Type-directed `snapshot!` capture dispatch tail (bug/869). The
    // argument-less `.capture()` that consumes the selector is an identity
    // (`result == self`); the capture itself happened at
    // `snapshot_capture_select` above.
    (
        &[
            "trust_wp_std::ghost::SnapshotCaptureSelect::capture",
            "trust_wp_std::ghost::SnapshotCaptureFallback::capture",
            "trust_wp_std::SnapshotCaptureSelect::capture",
            "trust_wp_std::SnapshotCaptureFallback::capture",
            "<trust_wp_std::ghost::SnapshotCaptureSelect as trust_wp_std::ghost::SnapshotCaptureFallback>::capture",
            "<trust_wp_std::SnapshotCaptureSelect as trust_wp_std::SnapshotCaptureFallback>::capture",
        ],
        ghost::specs::SNAPSHOT_CAPTURE_DISPATCH,
    ),
    (
        &[
            "trust_wp_std::ghost::Snapshot::inner",
            "trust_wp_std::Snapshot::inner",
            "trust_wp::ghost::Snapshot::inner",
            "trust_wp::Snapshot::inner",
            "creusot_std::ghost::Snapshot::inner",
            "creusot_std::Snapshot::inner",
            "creusot_contracts::ghost::Snapshot::inner",
            "creusot_contracts::Snapshot::inner",
        ],
        ghost::specs::SNAPSHOT_INNER,
    ),
    (
        &[
            "trust_wp_std::ghost::Snapshot::into_inner",
            "trust_wp_std::Snapshot::into_inner",
            "trust_wp::ghost::Snapshot::into_inner",
            "trust_wp::Snapshot::into_inner",
            "creusot_std::ghost::Snapshot::into_inner",
            "creusot_std::Snapshot::into_inner",
            "creusot_contracts::ghost::Snapshot::into_inner",
            "creusot_contracts::Snapshot::into_inner",
        ],
        ghost::specs::SNAPSHOT_INTO_INNER,
    ),
    // Ghost::borrow — identity at logical level, &Ghost<T> -> Ghost<&T>. (#2671)
    (
        &[
            "trust_wp_std::ghost::Ghost::borrow",
            "trust_wp_std::Ghost::borrow",
            "creusot_std::ghost::Ghost::borrow",
            "creusot_std::Ghost::borrow",
            "creusot_contracts::ghost::Ghost::borrow",
            "creusot_contracts::Ghost::borrow",
        ],
        ghost::specs::GHOST_BORROW,
    ),
    // Ghost::borrow_mut — identity at logical level, &mut Ghost<T> -> Ghost<&mut T>. (#2671)
    (
        &[
            "trust_wp_std::ghost::Ghost::borrow_mut",
            "trust_wp_std::Ghost::borrow_mut",
            "creusot_std::ghost::Ghost::borrow_mut",
            "creusot_std::Ghost::borrow_mut",
            "creusot_contracts::ghost::Ghost::borrow_mut",
            "creusot_contracts::Ghost::borrow_mut",
        ],
        ghost::specs::GHOST_BORROW_MUT,
    ),
    // Ghost::conjure() — unconstrained ghost value, prevents opaque classification. (#2671)
    (
        &[
            "trust_wp_std::ghost::Ghost::conjure",
            "trust_wp_std::Ghost::conjure",
            "creusot_std::ghost::Ghost::conjure",
            "creusot_std::Ghost::conjure",
            "creusot_contracts::ghost::Ghost::conjure",
            "creusot_contracts::Ghost::conjure",
        ],
        ghost::specs::GHOST_CONJURE,
    ),
    // Ghost<(A, B)>::split — decompose a ghost pair, prevents opaque. (#2671)
    (
        &[
            "trust_wp_std::ghost::Ghost::split",
            "trust_wp_std::Ghost::split",
            "creusot_std::ghost::Ghost::split",
            "creusot_std::Ghost::split",
            "creusot_contracts::ghost::Ghost::split",
            "creusot_contracts::Ghost::split",
        ],
        ghost::specs::GHOST_SPLIT,
    ),
    // Ghost<T> implements Deref<Target = T>; at the logical level deref returns self. (#1572)
    (
        &[
            "<trust_wp_std::ghost::Ghost as core::ops::Deref>::deref",
            "<trust_wp_std::Ghost as core::ops::Deref>::deref",
            "<trust_wp_std::ghost::Ghost as std::ops::Deref>::deref",
            "<trust_wp_std::Ghost as std::ops::Deref>::deref",
            "trust_wp_std::ghost::Ghost::deref",
            "trust_wp_std::Ghost::deref",
            "<creusot_std::ghost::Ghost as core::ops::Deref>::deref",
            "<creusot_std::Ghost as core::ops::Deref>::deref",
            "<creusot_std::ghost::Ghost as std::ops::Deref>::deref",
            "<creusot_std::Ghost as std::ops::Deref>::deref",
            "creusot_std::ghost::Ghost::deref",
            "creusot_std::Ghost::deref",
            "<creusot_contracts::ghost::Ghost as core::ops::Deref>::deref",
            "<creusot_contracts::Ghost as core::ops::Deref>::deref",
            "creusot_contracts::ghost::Ghost::deref",
            "creusot_contracts::Ghost::deref",
        ],
        ghost::specs::GHOST_DEREF,
    ),
    // Ghost<T> implements DerefMut<Target = T>; deref_mut returns self. (#1572)
    (
        &[
            "<trust_wp_std::ghost::Ghost as core::ops::DerefMut>::deref_mut",
            "<trust_wp_std::Ghost as core::ops::DerefMut>::deref_mut",
            "<trust_wp_std::ghost::Ghost as std::ops::DerefMut>::deref_mut",
            "<trust_wp_std::Ghost as std::ops::DerefMut>::deref_mut",
            "trust_wp_std::ghost::Ghost::deref_mut",
            "trust_wp_std::Ghost::deref_mut",
            "<creusot_std::ghost::Ghost as core::ops::DerefMut>::deref_mut",
            "<creusot_std::Ghost as core::ops::DerefMut>::deref_mut",
            "<creusot_std::ghost::Ghost as std::ops::DerefMut>::deref_mut",
            "<creusot_std::Ghost as std::ops::DerefMut>::deref_mut",
            "creusot_std::ghost::Ghost::deref_mut",
            "creusot_std::Ghost::deref_mut",
            "<creusot_contracts::ghost::Ghost as core::ops::DerefMut>::deref_mut",
            "<creusot_contracts::Ghost as core::ops::DerefMut>::deref_mut",
            "creusot_contracts::ghost::Ghost::deref_mut",
            "creusot_contracts::Ghost::deref_mut",
        ],
        ghost::specs::GHOST_DEREF_MUT,
    ),
    // Snapshot::from_fn — deferred capture via closure, prevents opaque classification (#2675)
    (
        &[
            "trust_wp_std::ghost::Snapshot::from_fn",
            "trust_wp_std::Snapshot::from_fn",
            "trust_wp::ghost::Snapshot::from_fn",
            "trust_wp::Snapshot::from_fn",
            "creusot_std::ghost::Snapshot::from_fn",
            "creusot_std::Snapshot::from_fn",
            "creusot_contracts::ghost::Snapshot::from_fn",
            "creusot_contracts::Snapshot::from_fn",
        ],
        ghost::specs::SNAPSHOT_FROM_FN,
    ),
    // Snapshot::new_phantom — ghost placeholder, prevents opaque classification (#2299)
    (
        &[
            "trust_wp_std::ghost::Snapshot::new_phantom",
            "trust_wp_std::Snapshot::new_phantom",
            "trust_wp::ghost::Snapshot::new_phantom",
            "trust_wp::Snapshot::new_phantom",
            "creusot_std::ghost::Snapshot::new_phantom",
            "creusot_std::Snapshot::new_phantom",
            "creusot_contracts::ghost::Snapshot::new_phantom",
            "creusot_contracts::Snapshot::new_phantom",
        ],
        ghost::specs::SNAPSHOT_NEW_PHANTOM,
    ),
    // Snapshot<T> implements Deref<Target = T>; at the logical level deref returns self.
    (
        &[
            "<trust_wp_std::ghost::Snapshot as core::ops::Deref>::deref",
            "<trust_wp_std::Snapshot as core::ops::Deref>::deref",
            "<trust_wp_std::ghost::Snapshot as std::ops::Deref>::deref",
            "<trust_wp_std::Snapshot as std::ops::Deref>::deref",
            "trust_wp_std::ghost::Snapshot::deref",
            "trust_wp_std::Snapshot::deref",
            "<trust_wp::ghost::Snapshot as core::ops::Deref>::deref",
            "<trust_wp::Snapshot as core::ops::Deref>::deref",
            "<trust_wp::ghost::Snapshot as std::ops::Deref>::deref",
            "<trust_wp::Snapshot as std::ops::Deref>::deref",
            "trust_wp::ghost::Snapshot::deref",
            "trust_wp::Snapshot::deref",
            "<creusot_std::ghost::Snapshot as core::ops::Deref>::deref",
            "<creusot_std::Snapshot as core::ops::Deref>::deref",
            "<creusot_std::ghost::Snapshot as std::ops::Deref>::deref",
            "<creusot_std::Snapshot as std::ops::Deref>::deref",
            "creusot_std::ghost::Snapshot::deref",
            "creusot_std::Snapshot::deref",
            "<creusot_contracts::ghost::Snapshot as core::ops::Deref>::deref",
            "<creusot_contracts::Snapshot as core::ops::Deref>::deref",
            "creusot_contracts::ghost::Snapshot::deref",
            "creusot_contracts::Snapshot::deref",
        ],
        ghost::specs::SNAPSHOT_DEREF,
    ),
    // Snapshot::into_ghost — identity conversion, both transparent in SMT.
    (
        &[
            "trust_wp_std::ghost::Snapshot::into_ghost",
            "trust_wp_std::Snapshot::into_ghost",
            "trust_wp::ghost::Snapshot::into_ghost",
            "trust_wp::Snapshot::into_ghost",
            "creusot_std::ghost::Snapshot::into_ghost",
            "creusot_std::Snapshot::into_ghost",
            "creusot_contracts::ghost::Snapshot::into_ghost",
            "creusot_contracts::Snapshot::into_ghost",
        ],
        ghost::specs::SNAPSHOT_INTO_GHOST,
    ),
    // Snapshot<Seq<T>>::push_back — transparent Seq push_back through Snapshot.
    // Exists because Seq::push_back takes self by value but Snapshot::Deref
    // returns &Seq<T>, so auto-deref cannot bridge the gap.
    (
        &[
            "trust_wp_std::ghost::Snapshot::push_back",
            "trust_wp_std::Snapshot::push_back",
            "trust_wp::ghost::Snapshot::push_back",
            "trust_wp::Snapshot::push_back",
            "creusot_std::ghost::Snapshot::push_back",
            "creusot_std::Snapshot::push_back",
            "creusot_contracts::ghost::Snapshot::push_back",
            "creusot_contracts::Snapshot::push_back",
        ],
        ghost::specs::SNAPSHOT_SEQ_PUSH_BACK,
    ),
    // Snapshot<Seq<T>>::concat — transparent Seq concat through Snapshot.
    // Critical for iterator produces clauses: visited.concat(next@).
    (
        &[
            "trust_wp_std::ghost::Snapshot::concat",
            "trust_wp_std::Snapshot::concat",
            "trust_wp::ghost::Snapshot::concat",
            "trust_wp::Snapshot::concat",
            "creusot_std::ghost::Snapshot::concat",
            "creusot_std::Snapshot::concat",
            "creusot_contracts::ghost::Snapshot::concat",
            "creusot_contracts::Snapshot::concat",
        ],
        ghost::specs::SNAPSHOT_SEQ_CONCAT,
    ),
    // Snapshot<FMap<K,V>>::insert — transparent FMap insert through Snapshot.
    (
        &[
            "trust_wp_std::ghost::Snapshot::insert",
            "trust_wp_std::Snapshot::insert",
            "trust_wp::ghost::Snapshot::insert",
            "trust_wp::Snapshot::insert",
            "creusot_std::ghost::Snapshot::insert",
            "creusot_std::Snapshot::insert",
            "creusot_contracts::ghost::Snapshot::insert",
            "creusot_contracts::Snapshot::insert",
        ],
        ghost::specs::SNAPSHOT_FMAP_INSERT,
    ),
    // Perm<T>::disjoint_lemma — ghost lemma establishing permission disjointness (#1581)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::disjoint_lemma",
            "trust_wp_std::ghost::Perm::disjoint_lemma",
            "trust_wp_std::Perm::disjoint_lemma",
            "creusot_std::ghost::perm::Perm::disjoint_lemma",
            "creusot_std::Perm::disjoint_lemma",
        ],
        ghost::specs::PERM_DISJOINT_LEMMA,
    ),
    // Perm<T>::new — fresh allocation, pointer identity equals permission identity (#1581)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::new",
            "trust_wp_std::ghost::Perm::new",
            "trust_wp_std::Perm::new",
            "creusot_std::ghost::perm::Perm::new",
            "creusot_std::Perm::new",
        ],
        ghost::specs::PERM_NEW,
    ),
    // Perm::val — ghost logical value accessor (#2316)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::val",
            "trust_wp_std::ghost::Perm::val",
            "trust_wp_std::Perm::val",
            "creusot_std::ghost::perm::Perm::val",
            "creusot_std::Perm::val",
        ],
        ghost::specs::PERM_VAL,
    ),
    // Perm::ward — ghost container accessor (#2316)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::ward",
            "trust_wp_std::ghost::Perm::ward",
            "trust_wp_std::Perm::ward",
            "creusot_std::ghost::perm::Perm::ward",
            "creusot_std::Perm::ward",
        ],
        ghost::specs::PERM_WARD,
    ),
    // Perm::as_ref — ghost shared dereference through permission (#2315)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::as_ref",
            "trust_wp_std::ghost::Perm::as_ref",
            "trust_wp_std::Perm::as_ref",
            "creusot_std::ghost::perm::Perm::as_ref",
            "creusot_std::Perm::as_ref",
        ],
        ghost::specs::PERM_AS_REF,
    ),
    // Perm::as_mut — ghost mutable dereference through permission (#2315)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::as_mut",
            "trust_wp_std::ghost::Perm::as_mut",
            "trust_wp_std::Perm::as_mut",
            "creusot_std::ghost::perm::Perm::as_mut",
            "creusot_std::Perm::as_mut",
        ],
        ghost::specs::PERM_AS_MUT,
    ),
    // Perm::from_ref — decompose shared reference into raw pointer + ghost permission (#1804)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::from_ref",
            "trust_wp_std::ghost::Perm::from_ref",
            "trust_wp_std::Perm::from_ref",
            "creusot_std::ghost::perm::Perm::from_ref",
            "creusot_std::Perm::from_ref",
        ],
        ghost::specs::PERM_FROM_REF,
    ),
    // Perm::from_mut — decompose mutable reference into raw pointer + ghost permission (#1804)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::from_mut",
            "trust_wp_std::ghost::Perm::from_mut",
            "trust_wp_std::Perm::from_mut",
            "creusot_std::ghost::perm::Perm::from_mut",
            "creusot_std::Perm::from_mut",
        ],
        ghost::specs::PERM_FROM_MUT,
    ),
    // Perm::from_box — decompose box into raw pointer + ghost permission (#1804)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::from_box",
            "trust_wp_std::ghost::Perm::from_box",
            "trust_wp_std::Perm::from_box",
            "creusot_std::ghost::perm::Perm::from_box",
            "creusot_std::Perm::from_box",
        ],
        ghost::specs::PERM_FROM_BOX,
    ),
    // Perm::to_box — reconstruct Box from raw pointer + ghost permission (#2682)
    (
        &[
            "trust_wp_std::ghost::perm::Perm::to_box",
            "trust_wp_std::ghost::Perm::to_box",
            "trust_wp_std::Perm::to_box",
            "creusot_std::ghost::perm::Perm::to_box",
            "creusot_std::Perm::to_box",
        ],
        ghost::specs::PERM_TO_BOX,
    ),
    // Resource::val — ghost logical value accessor (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::val",
            "trust_wp_std::ghost::Resource::val",
            "trust_wp_std::Resource::val",
            "creusot_std::ghost::resource::Resource::val",
            "creusot_std::Resource::val",
        ],
        ghost::specs::RESOURCE_VAL,
    ),
    // Resource::alloc — allocate a fresh resource (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::alloc",
            "trust_wp_std::ghost::Resource::alloc",
            "trust_wp_std::Resource::alloc",
            "creusot_std::ghost::resource::Resource::alloc",
            "creusot_std::Resource::alloc",
        ],
        ghost::specs::RESOURCE_ALLOC,
    ),
    // Resource::split — split a resource into two parts (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::split",
            "trust_wp_std::ghost::Resource::split",
            "trust_wp_std::Resource::split",
            "creusot_std::ghost::resource::Resource::split",
            "creusot_std::Resource::split",
        ],
        ghost::specs::RESOURCE_SPLIT,
    ),
    // Resource::join — join two resources (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::join",
            "trust_wp_std::ghost::Resource::join",
            "trust_wp_std::Resource::join",
            "creusot_std::ghost::resource::Resource::join",
            "creusot_std::Resource::join",
        ],
        ghost::specs::RESOURCE_JOIN,
    ),
    // Resource::weaken — weaken a resource to a target value (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::weaken",
            "trust_wp_std::ghost::Resource::weaken",
            "trust_wp_std::Resource::weaken",
            "creusot_std::ghost::resource::Resource::weaken",
            "creusot_std::Resource::weaken",
        ],
        ghost::specs::RESOURCE_WEAKEN,
    ),
    // Resource::core — get maximal idempotent sub-resource (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::core",
            "trust_wp_std::ghost::Resource::core",
            "trust_wp_std::Resource::core",
            "creusot_std::ghost::resource::Resource::core",
            "creusot_std::Resource::core",
        ],
        ghost::specs::RESOURCE_CORE,
    ),
    // Resource::split_off — remove part from self, leaving remainder (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::split_off",
            "trust_wp_std::ghost::Resource::split_off",
            "trust_wp_std::Resource::split_off",
            "creusot_std::ghost::resource::Resource::split_off",
            "creusot_std::Resource::split_off",
        ],
        ghost::specs::RESOURCE_SPLIT_OFF,
    ),
    // Resource::split_mut — split into two mutable borrows (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::split_mut",
            "trust_wp_std::ghost::Resource::split_mut",
            "trust_wp_std::Resource::split_mut",
            "creusot_std::ghost::resource::Resource::split_mut",
            "creusot_std::Resource::split_mut",
        ],
        ghost::specs::RESOURCE_SPLIT_MUT,
    ),
    // Resource::join_in — join other into self (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::join_in",
            "trust_wp_std::ghost::Resource::join_in",
            "trust_wp_std::Resource::join_in",
            "creusot_std::ghost::resource::Resource::join_in",
            "creusot_std::Resource::join_in",
        ],
        ghost::specs::RESOURCE_JOIN_IN,
    ),
    // Resource::take — take value leaving unit (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::take",
            "trust_wp_std::ghost::Resource::take",
            "trust_wp_std::Resource::take",
            "creusot_std::ghost::resource::Resource::take",
            "creusot_std::Resource::take",
        ],
        ghost::specs::RESOURCE_TAKE,
    ),
    // Resource::update — apply frame-preserving update (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::update",
            "trust_wp_std::ghost::Resource::update",
            "trust_wp_std::Resource::update",
            "creusot_std::ghost::resource::Resource::update",
            "creusot_std::Resource::update",
        ],
        ghost::specs::RESOURCE_UPDATE,
    ),
    // Resource::new_unit — create unit resource for identity (#2316)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::new_unit",
            "trust_wp_std::ghost::Resource::new_unit",
            "trust_wp_std::Resource::new_unit",
            "creusot_std::ghost::resource::Resource::new_unit",
            "creusot_std::Resource::new_unit",
        ],
        ghost::specs::RESOURCE_NEW_UNIT,
    ),
    // Resource::id_ghost — ghost identity accessor (#2315)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::id_ghost",
            "trust_wp_std::ghost::Resource::id_ghost",
            "trust_wp_std::Resource::id_ghost",
            "creusot_std::ghost::resource::Resource::id_ghost",
            "creusot_std::Resource::id_ghost",
        ],
        ghost::specs::RESOURCE_ID_GHOST,
    ),
    // Resource::valid_op_lemma — composition validity lemma (#2315)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::valid_op_lemma",
            "trust_wp_std::ghost::Resource::valid_op_lemma",
            "trust_wp_std::Resource::valid_op_lemma",
            "creusot_std::ghost::resource::Resource::valid_op_lemma",
            "creusot_std::Resource::valid_op_lemma",
        ],
        ghost::specs::RESOURCE_VALID_OP_LEMMA,
    ),
    // Resource::join_shared — join shared references to the same resource (#2154)
    (
        &[
            "trust_wp_std::ghost::resource::Resource::join_shared",
            "trust_wp_std::ghost::Resource::join_shared",
            "trust_wp_std::Resource::join_shared",
            "creusot_std::ghost::resource::Resource::join_shared",
            "creusot_std::Resource::join_shared",
        ],
        ghost::specs::RESOURCE_JOIN_SHARED,
    ),
    // ── Authority methods (#2316) ─────────────────────────────────
    // Authority::alloc — allocate a fresh authority
    (
        &[
            "trust_wp_std::ghost::resource::Authority::alloc",
            "trust_wp_std::ghost::Authority::alloc",
            "trust_wp_std::Authority::alloc",
            "creusot_std::ghost::resource::Authority::alloc",
            "creusot_std::Authority::alloc",
        ],
        ghost::specs::AUTHORITY_ALLOC,
    ),
    // Authority::from_resource — create authority/fragment pair
    (
        &[
            "trust_wp_std::ghost::resource::Authority::from_resource",
            "trust_wp_std::ghost::Authority::from_resource",
            "trust_wp_std::Authority::from_resource",
            "creusot_std::ghost::resource::Authority::from_resource",
            "creusot_std::Authority::from_resource",
        ],
        ghost::specs::AUTHORITY_FROM_RESOURCE,
    ),
    // Authority::update — local update on authority/fragment pair
    (
        &[
            "trust_wp_std::ghost::resource::Authority::update",
            "trust_wp_std::ghost::Authority::update",
            "trust_wp_std::Authority::update",
            "creusot_std::ghost::resource::Authority::update",
            "creusot_std::Authority::update",
        ],
        ghost::specs::AUTHORITY_UPDATE,
    ),
    // Authority::add_fragment — add piece and return new fragment
    (
        &[
            "trust_wp_std::ghost::resource::Authority::add_fragment",
            "trust_wp_std::ghost::Authority::add_fragment",
            "trust_wp_std::Authority::add_fragment",
            "creusot_std::ghost::resource::Authority::add_fragment",
            "creusot_std::Authority::add_fragment",
        ],
        ghost::specs::AUTHORITY_ADD_FRAGMENT,
    ),
    // Authority::frag_lemma — assert fragment contained in authority
    (
        &[
            "trust_wp_std::ghost::resource::Authority::frag_lemma",
            "trust_wp_std::ghost::Authority::frag_lemma",
            "trust_wp_std::Authority::frag_lemma",
            "creusot_std::ghost::resource::Authority::frag_lemma",
            "creusot_std::Authority::frag_lemma",
        ],
        ghost::specs::AUTHORITY_FRAG_LEMMA,
    ),
    // Authority::id_ghost — ghost identity accessor
    (
        &[
            "trust_wp_std::ghost::resource::Authority::id_ghost",
            "trust_wp_std::ghost::Authority::id_ghost",
            "trust_wp_std::Authority::id_ghost",
            "creusot_std::ghost::resource::Authority::id_ghost",
            "creusot_std::Authority::id_ghost",
        ],
        ghost::specs::AUTHORITY_ID_GHOST,
    ),
    // ── Fragment methods (#2316) ──────────────────────────────────
    // Fragment::new_unit — create unit fragment
    (
        &[
            "trust_wp_std::ghost::resource::Fragment::new_unit",
            "trust_wp_std::ghost::Fragment::new_unit",
            "trust_wp_std::Fragment::new_unit",
            "creusot_std::ghost::resource::Fragment::new_unit",
            "creusot_std::Fragment::new_unit",
        ],
        ghost::specs::FRAGMENT_NEW_UNIT,
    ),
    // Fragment::core — duplicate the duplicable core
    (
        &[
            "trust_wp_std::ghost::resource::Fragment::core",
            "trust_wp_std::ghost::Fragment::core",
            "trust_wp_std::Fragment::core",
            "creusot_std::ghost::resource::Fragment::core",
            "creusot_std::Fragment::core",
        ],
        ghost::specs::FRAGMENT_CORE,
    ),
    // Fragment::split — split a fragment into two parts
    (
        &[
            "trust_wp_std::ghost::resource::Fragment::split",
            "trust_wp_std::ghost::Fragment::split",
            "trust_wp_std::Fragment::split",
            "creusot_std::ghost::resource::Fragment::split",
            "creusot_std::Fragment::split",
        ],
        ghost::specs::FRAGMENT_SPLIT,
    ),
    // Fragment::split_off — remove part from self, leaving remainder
    (
        &[
            "trust_wp_std::ghost::resource::Fragment::split_off",
            "trust_wp_std::ghost::Fragment::split_off",
            "trust_wp_std::Fragment::split_off",
            "creusot_std::ghost::resource::Fragment::split_off",
            "creusot_std::Fragment::split_off",
        ],
        ghost::specs::FRAGMENT_SPLIT_OFF,
    ),
    // Fragment::join — join two owned fragments
    (
        &[
            "trust_wp_std::ghost::resource::Fragment::join",
            "trust_wp_std::ghost::Fragment::join",
            "trust_wp_std::Fragment::join",
            "creusot_std::ghost::resource::Fragment::join",
            "creusot_std::Fragment::join",
        ],
        ghost::specs::FRAGMENT_JOIN,
    ),
    // Fragment::join_in — join other into self
    (
        &[
            "trust_wp_std::ghost::resource::Fragment::join_in",
            "trust_wp_std::ghost::Fragment::join_in",
            "trust_wp_std::Fragment::join_in",
            "creusot_std::ghost::resource::Fragment::join_in",
            "creusot_std::Fragment::join_in",
        ],
        ghost::specs::FRAGMENT_JOIN_IN,
    ),
    // Fragment::weaken — transform self into target
    (
        &[
            "trust_wp_std::ghost::resource::Fragment::weaken",
            "trust_wp_std::ghost::Fragment::weaken",
            "trust_wp_std::Fragment::weaken",
            "creusot_std::ghost::resource::Fragment::weaken",
            "creusot_std::Fragment::weaken",
        ],
        ghost::specs::FRAGMENT_WEAKEN,
    ),
    // Fragment::valid_op_lemma — composition validity lemma
    (
        &[
            "trust_wp_std::ghost::resource::Fragment::valid_op_lemma",
            "trust_wp_std::ghost::Fragment::valid_op_lemma",
            "trust_wp_std::Fragment::valid_op_lemma",
            "creusot_std::ghost::resource::Fragment::valid_op_lemma",
            "creusot_std::Fragment::valid_op_lemma",
        ],
        ghost::specs::FRAGMENT_VALID_OP_LEMMA,
    ),
    // Fragment::id_ghost — ghost identity accessor
    (
        &[
            "trust_wp_std::ghost::resource::Fragment::id_ghost",
            "trust_wp_std::ghost::Fragment::id_ghost",
            "trust_wp_std::Fragment::id_ghost",
            "creusot_std::ghost::resource::Fragment::id_ghost",
            "creusot_std::Fragment::id_ghost",
        ],
        ghost::specs::FRAGMENT_ID_GHOST,
    ),
    // NonAtomicInvariant::open / Ghost::open — bounded token precondition only. (#994)
    (
        &[
            "trust_wp_std::ghost::open",
            "trust_wp_std::ghost::Ghost::open",
            "trust_wp_std::Ghost::open",
            "trust_wp_std::ghost::invariant::open",
            "creusot_std::ghost::Ghost::open",
            "creusot_std::Ghost::open",
            "trust_wp_std::ghost::invariant::NonAtomicInvariant::open",
            "creusot_std::ghost::invariant::NonAtomicInvariant::open",
            "trust_wp_std::ghost::invariant::NonAtomicInvariantExt::open",
            "creusot_std::ghost::invariant::NonAtomicInvariantExt::open",
        ],
        ghost::specs::NON_ATOMIC_INVARIANT_OPEN,
    ),
    // AtomicInvariant::new — construct an atomic invariant
    (
        &[
            "trust_wp_std::ghost::invariant::AtomicInvariant::new",
            "creusot_std::ghost::invariant::AtomicInvariant::new",
        ],
        ghost::specs::ATOMIC_INVARIANT_NEW,
    ),
    // AtomicInvariant::open — open an atomic invariant
    (
        &[
            "trust_wp_std::ghost::invariant::AtomicInvariant::open",
            "creusot_std::ghost::invariant::AtomicInvariant::open",
        ],
        ghost::specs::ATOMIC_INVARIANT_OPEN,
    ),
    // AtomicInvariantSC::new — construct an SC atomic invariant
    (
        &[
            "trust_wp_std::ghost::invariant::AtomicInvariantSC::new",
            "creusot_std::ghost::invariant::AtomicInvariantSC::new",
        ],
        ghost::specs::ATOMIC_INVARIANT_SC_NEW,
    ),
    // AtomicInvariantSC::open — open an SC atomic invariant
    (
        &[
            "trust_wp_std::ghost::invariant::AtomicInvariantSC::open",
            "creusot_std::ghost::invariant::AtomicInvariantSC::open",
        ],
        ghost::specs::ATOMIC_INVARIANT_SC_OPEN,
    ),
    // Tokens::new — get all invariant namespace tokens
    (
        &[
            "trust_wp_std::ghost::invariant::Tokens::new",
            "trust_wp_std::Tokens::new",
            "creusot_std::ghost::invariant::Tokens::new",
            "creusot_std::Tokens::new",
        ],
        ghost::specs::TOKENS_NEW,
    ),
    // Tokens::reborrow — reborrow a token set
    (
        &[
            "trust_wp_std::ghost::invariant::Tokens::reborrow",
            "trust_wp_std::Tokens::reborrow",
            "creusot_std::ghost::invariant::Tokens::reborrow",
            "creusot_std::Tokens::reborrow",
        ],
        ghost::specs::TOKENS_REBORROW,
    ),
    // Tokens::contains — bounded all-token model for ghost namespace tokens
    (
        &[
            "trust_wp_std::ghost::invariant::Tokens::contains",
            "trust_wp_std::Tokens::contains",
            "creusot_std::ghost::invariant::Tokens::contains",
            "creusot_std::Tokens::contains",
        ],
        ghost::specs::TOKENS_CONTAINS,
    ),
    (
        &[
            "core::option::Option::is_some",
            "std::option::Option::is_some",
        ],
        option::specs::IS_SOME,
    ),
    (
        &[
            "core::option::Option::is_none",
            "std::option::Option::is_none",
        ],
        option::specs::IS_NONE,
    ),
    (
        &[
            "core::option::Option::unwrap",
            "std::option::Option::unwrap",
        ],
        option::specs::UNWRAP,
    ),
    (
        &[
            "core::option::Option::unwrap_or",
            "std::option::Option::unwrap_or",
        ],
        option::specs::UNWRAP_OR,
    ),
    (
        &["core::option::Option::map", "std::option::Option::map"],
        option::specs::MAP,
    ),
    (
        &[
            "core::option::Option::and_then",
            "std::option::Option::and_then",
        ],
        option::specs::AND_THEN,
    ),
    (
        &["core::option::Option::take", "std::option::Option::take"],
        option::specs::TAKE,
    ),
    (
        &[
            "core::option::Option::replace",
            "std::option::Option::replace",
        ],
        option::specs::REPLACE,
    ),
    (
        &[
            "core::option::Option::or_else",
            "std::option::Option::or_else",
        ],
        option::specs::OR_ELSE,
    ),
    (
        &[
            "core::option::Option::expect",
            "std::option::Option::expect",
        ],
        option::specs::EXPECT,
    ),
    (
        &[
            "core::option::Option::unwrap_or_else",
            "std::option::Option::unwrap_or_else",
        ],
        option::specs::UNWRAP_OR_ELSE,
    ),
    (
        &[
            "core::option::Option::as_ref",
            "std::option::Option::as_ref",
        ],
        option::specs::AS_REF,
    ),
    (
        &[
            "core::option::Option::as_mut",
            "std::option::Option::as_mut",
        ],
        option::specs::AS_MUT,
    ),
    (
        &["core::option::Option::ok_or", "std::option::Option::ok_or"],
        option::specs::OK_OR,
    ),
    (
        &[
            "core::option::Option::ok_or_else",
            "std::option::Option::ok_or_else",
        ],
        option::specs::OK_OR_ELSE,
    ),
    (
        &[
            "core::option::Option::unwrap_or_default",
            "std::option::Option::unwrap_or_default",
        ],
        option::specs::UNWRAP_OR_DEFAULT,
    ),
    (
        &[
            "core::option::Option::unwrap_unchecked",
            "std::option::Option::unwrap_unchecked",
        ],
        option::specs::UNWRAP_UNCHECKED,
    ),
    (
        &[
            "core::option::Option::inspect",
            "std::option::Option::inspect",
        ],
        option::specs::INSPECT,
    ),
    (
        &[
            "core::option::Option::map_or",
            "std::option::Option::map_or",
        ],
        option::specs::MAP_OR,
    ),
    (
        &[
            "core::option::Option::map_or_else",
            "std::option::Option::map_or_else",
        ],
        option::specs::MAP_OR_ELSE,
    ),
    (
        &["core::option::Option::and", "std::option::Option::and"],
        option::specs::AND,
    ),
    (
        &["core::option::Option::or", "std::option::Option::or"],
        option::specs::OR,
    ),
    (
        &["core::option::Option::xor", "std::option::Option::xor"],
        option::specs::XOR,
    ),
    (
        &[
            "core::option::Option::filter",
            "std::option::Option::filter",
        ],
        option::specs::FILTER,
    ),
    (
        &[
            "core::option::Option::is_some_and",
            "std::option::Option::is_some_and",
        ],
        option::specs::IS_SOME_AND,
    ),
    (
        &[
            "core::option::Option::insert",
            "std::option::Option::insert",
        ],
        option::specs::INSERT,
    ),
    (
        &[
            "core::option::Option::get_or_insert",
            "std::option::Option::get_or_insert",
        ],
        option::specs::GET_OR_INSERT,
    ),
    (
        &[
            "core::option::Option::get_or_insert_with",
            "std::option::Option::get_or_insert_with",
        ],
        option::specs::GET_OR_INSERT_WITH,
    ),
    (
        &[
            "core::option::Option::take_if",
            "std::option::Option::take_if",
        ],
        option::specs::TAKE_IF,
    ),
    (
        &[
            "core::option::Option::copied",
            "std::option::Option::copied",
        ],
        option::specs::COPIED,
    ),
    (
        &[
            "core::option::Option::cloned",
            "std::option::Option::cloned",
        ],
        option::specs::CLONED,
    ),
    (
        &["core::option::Option::zip", "std::option::Option::zip"],
        option::specs::ZIP,
    ),
    (
        &["core::option::Option::unzip", "std::option::Option::unzip"],
        option::specs::UNZIP,
    ),
    (
        &[
            "core::option::Option::transpose",
            "std::option::Option::transpose",
        ],
        option::specs::TRANSPOSE,
    ),
    (
        &[
            "core::option::Option::flatten",
            "std::option::Option::flatten",
        ],
        option::specs::FLATTEN,
    ),
    (
        &["core::option::Option::iter", "std::option::Option::iter"],
        option::specs::ITER,
    ),
    (
        &[
            "core::option::Option::as_deref",
            "std::option::Option::as_deref",
        ],
        option::specs::AS_DEREF,
    ),
    (
        &[
            "core::option::Option::as_deref_mut",
            "std::option::Option::as_deref_mut",
        ],
        option::specs::AS_DEREF_MUT,
    ),
    (
        &["core::result::Result::is_ok", "std::result::Result::is_ok"],
        result::specs::IS_OK,
    ),
    (
        &[
            "core::result::Result::is_err",
            "std::result::Result::is_err",
        ],
        result::specs::IS_ERR,
    ),
    (
        &[
            "core::result::Result::unwrap",
            "std::result::Result::unwrap",
        ],
        result::specs::UNWRAP,
    ),
    (
        &[
            "core::result::Result::unwrap_err",
            "std::result::Result::unwrap_err",
        ],
        result::specs::UNWRAP_ERR,
    ),
    (
        &[
            "core::result::Result::unwrap_or",
            "std::result::Result::unwrap_or",
        ],
        result::specs::UNWRAP_OR,
    ),
    (
        &["core::result::Result::map", "std::result::Result::map"],
        result::specs::MAP,
    ),
    (
        &[
            "core::result::Result::map_err",
            "std::result::Result::map_err",
        ],
        result::specs::MAP_ERR,
    ),
    (
        &[
            "core::result::Result::and_then",
            "std::result::Result::and_then",
        ],
        result::specs::AND_THEN,
    ),
    (
        &["core::result::Result::ok", "std::result::Result::ok"],
        result::specs::OK,
    ),
    (
        &["core::result::Result::err", "std::result::Result::err"],
        result::specs::ERR,
    ),
    (
        &[
            "core::result::Result::expect",
            "std::result::Result::expect",
        ],
        result::specs::EXPECT,
    ),
    (
        &[
            "core::result::Result::unwrap_or_else",
            "std::result::Result::unwrap_or_else",
        ],
        result::specs::UNWRAP_OR_ELSE,
    ),
    (
        &[
            "core::result::Result::as_ref",
            "std::result::Result::as_ref",
        ],
        result::specs::AS_REF,
    ),
    (
        &[
            "core::result::Result::as_mut",
            "std::result::Result::as_mut",
        ],
        result::specs::AS_MUT,
    ),
    (
        &["core::result::Result::and", "std::result::Result::and"],
        result::specs::AND,
    ),
    (
        &["core::result::Result::or", "std::result::Result::or"],
        result::specs::OR,
    ),
    (
        &[
            "core::result::Result::or_else",
            "std::result::Result::or_else",
        ],
        result::specs::OR_ELSE,
    ),
    (
        &[
            "core::result::Result::unwrap_or_default",
            "std::result::Result::unwrap_or_default",
        ],
        result::specs::UNWRAP_OR_DEFAULT,
    ),
    (
        &[
            "core::result::Result::copied",
            "std::result::Result::copied",
        ],
        result::specs::COPIED,
    ),
    (
        &[
            "core::result::Result::cloned",
            "std::result::Result::cloned",
        ],
        result::specs::CLONED,
    ),
    (
        &[
            "core::result::Result::transpose",
            "std::result::Result::transpose",
        ],
        result::specs::TRANSPOSE,
    ),
    (
        &[
            "core::result::Result::inspect",
            "std::result::Result::inspect",
        ],
        result::specs::INSPECT,
    ),
    (
        &[
            "core::result::Result::inspect_err",
            "std::result::Result::inspect_err",
        ],
        result::specs::INSPECT_ERR,
    ),
    (
        &[
            "core::result::Result::map_or",
            "std::result::Result::map_or",
        ],
        result::specs::MAP_OR,
    ),
    (
        &[
            "core::result::Result::map_or_else",
            "std::result::Result::map_or_else",
        ],
        result::specs::MAP_OR_ELSE,
    ),
    (
        &[
            "core::result::Result::is_ok_and",
            "std::result::Result::is_ok_and",
        ],
        result::specs::IS_OK_AND,
    ),
    (
        &[
            "core::result::Result::is_err_and",
            "std::result::Result::is_err_and",
        ],
        result::specs::IS_ERR_AND,
    ),
    (
        &[
            "core::result::Result::flatten",
            "std::result::Result::flatten",
        ],
        result::specs::FLATTEN,
    ),
    (
        &[
            "core::result::Result::expect_err",
            "std::result::Result::expect_err",
        ],
        result::specs::EXPECT_ERR,
    ),
    (
        &[
            "core::result::Result::unwrap_unchecked",
            "std::result::Result::unwrap_unchecked",
        ],
        result::specs::UNWRAP_UNCHECKED,
    ),
    (
        &[
            "core::result::Result::unwrap_err_unchecked",
            "std::result::Result::unwrap_err_unchecked",
        ],
        result::specs::UNWRAP_ERR_UNCHECKED,
    ),
    (
        &["alloc::vec::Vec::new", "std::vec::Vec::new"],
        vec::specs::NEW,
    ),
    (
        &["alloc::vec::Vec::len", "std::vec::Vec::len"],
        vec::specs::LEN,
    ),
    (
        &["alloc::vec::Vec::is_empty", "std::vec::Vec::is_empty"],
        vec::specs::IS_EMPTY,
    ),
    (
        &["alloc::vec::Vec::push", "std::vec::Vec::push"],
        vec::specs::PUSH,
    ),
    (
        &["alloc::vec::Vec::pop", "std::vec::Vec::pop"],
        vec::specs::POP,
    ),
    (
        &["alloc::vec::Vec::clear", "std::vec::Vec::clear"],
        vec::specs::CLEAR,
    ),
    (
        &["alloc::vec::Vec::first", "std::vec::Vec::first"],
        vec::specs::FIRST,
    ),
    (
        &["alloc::vec::Vec::last", "std::vec::Vec::last"],
        vec::specs::LAST,
    ),
    (
        &[
            "alloc::vec::Vec::get",
            "std::vec::Vec::get",
            "core::slice::get",
            "std::slice::get",
        ],
        vec::specs::GET_GENERIC,
    ),
    (
        &["alloc::vec::Vec::capacity", "std::vec::Vec::capacity"],
        vec::specs::CAPACITY,
    ),
    (
        &["alloc::vec::Vec::reserve", "std::vec::Vec::reserve"],
        vec::specs::RESERVE,
    ),
    (
        &[
            "alloc::vec::Vec::reserve_exact",
            "std::vec::Vec::reserve_exact",
        ],
        vec::specs::RESERVE_EXACT,
    ),
    (
        &[
            "alloc::vec::Vec::with_capacity",
            "std::vec::Vec::with_capacity",
        ],
        vec::specs::WITH_CAPACITY,
    ),
    (
        &["alloc::vec::Vec::truncate", "std::vec::Vec::truncate"],
        vec::specs::TRUNCATE,
    ),
    (
        &["alloc::vec::Vec::insert", "std::vec::Vec::insert"],
        vec::specs::INSERT,
    ),
    (
        &["alloc::vec::Vec::remove", "std::vec::Vec::remove"],
        vec::specs::REMOVE,
    ),
    (
        &[
            "alloc::vec::Vec::get_mut",
            "std::vec::Vec::get_mut",
            "core::slice::get_mut",
            "std::slice::get_mut",
        ],
        vec::specs::GET_MUT_GENERIC,
    ),
    (
        &[
            "alloc::vec::Vec::shrink_to_fit",
            "std::vec::Vec::shrink_to_fit",
        ],
        vec::specs::SHRINK_TO_FIT,
    ),
    (
        &["alloc::vec::Vec::shrink_to", "std::vec::Vec::shrink_to"],
        vec::specs::SHRINK_TO,
    ),
    (
        &["alloc::vec::Vec::resize", "std::vec::Vec::resize"],
        vec::specs::RESIZE,
    ),
    (
        &[
            "alloc::vec::Vec::swap",
            "std::vec::Vec::swap",
            "core::slice::swap",
            "std::slice::swap",
        ],
        vec::specs::SWAP,
    ),
    (
        &[
            "alloc::vec::Vec::contains",
            "std::vec::Vec::contains",
            "core::slice::contains",
            "std::slice::contains",
        ],
        vec::specs::CONTAINS,
    ),
    (
        &[
            "alloc::vec::Vec::extend_from_slice",
            "std::vec::Vec::extend_from_slice",
        ],
        vec::specs::EXTEND_FROM_SLICE,
    ),
    (
        &[
            "<alloc::vec::Vec as core::iter::Extend>::extend",
            "<std::vec::Vec as core::iter::Extend>::extend",
            "<alloc::vec::Vec as std::iter::Extend>::extend",
            "<std::vec::Vec as std::iter::Extend>::extend",
            "alloc::vec::Vec::extend",
            "std::vec::Vec::extend",
        ],
        vec::specs::EXTEND,
    ),
    // Index trait impl for Vec — concrete paths only (#980).
    // Generic trait paths (core::ops::Index::index) would match ANY Index
    // impl, not just Vec. Use trait-qualified UFCS paths for Vec instead.
    (
        &[
            "alloc::vec::Vec::index",
            "std::vec::Vec::index",
            "<alloc::vec::Vec as core::ops::Index>::index",
            "<std::vec::Vec as core::ops::Index>::index",
            "<alloc::vec::Vec as std::ops::Index>::index",
            "<std::vec::Vec as std::ops::Index>::index",
        ],
        vec::specs::INDEX_GENERIC,
    ),
    (
        &[
            "alloc::vec::Vec::index_mut",
            "std::vec::Vec::index_mut",
            "<alloc::vec::Vec as core::ops::IndexMut>::index_mut",
            "<std::vec::Vec as core::ops::IndexMut>::index_mut",
            "<alloc::vec::Vec as std::ops::IndexMut>::index_mut",
            "<std::vec::Vec as std::ops::IndexMut>::index_mut",
        ],
        vec::specs::INDEX_MUT_GENERIC,
    ),
    // ── Vec additional methods ─────────────────────────────────────
    (
        &["alloc::vec::Vec::append", "std::vec::Vec::append"],
        vec::specs::APPEND,
    ),
    (
        &["alloc::vec::Vec::split_off", "std::vec::Vec::split_off"],
        vec::specs::SPLIT_OFF,
    ),
    (
        &["alloc::vec::Vec::retain", "std::vec::Vec::retain"],
        vec::specs::RETAIN,
    ),
    (
        &[
            "alloc::vec::Vec::dedup",
            "std::vec::Vec::dedup",
            "core::slice::dedup",
            "std::slice::dedup",
        ],
        vec::specs::DEDUP,
    ),
    (
        &[
            "alloc::vec::Vec::reverse",
            "std::vec::Vec::reverse",
            "core::slice::reverse",
            "std::slice::reverse",
        ],
        vec::specs::REVERSE,
    ),
    (
        &[
            "alloc::vec::Vec::sort",
            "std::vec::Vec::sort",
            "core::slice::sort",
            "std::slice::sort",
        ],
        vec::specs::SORT,
    ),
    (
        &[
            "alloc::vec::Vec::sort_unstable",
            "std::vec::Vec::sort_unstable",
            "core::slice::sort_unstable",
            "std::slice::sort_unstable",
        ],
        vec::specs::SORT_UNSTABLE,
    ),
    (
        &[
            "alloc::vec::Vec::first_mut",
            "std::vec::Vec::first_mut",
            "core::slice::first_mut",
            "std::slice::first_mut",
        ],
        vec::specs::FIRST_MUT,
    ),
    (
        &[
            "alloc::vec::Vec::last_mut",
            "std::vec::Vec::last_mut",
            "core::slice::last_mut",
            "std::slice::last_mut",
        ],
        vec::specs::LAST_MUT,
    ),
    (
        &["alloc::vec::Vec::as_slice", "std::vec::Vec::as_slice"],
        vec::specs::AS_SLICE,
    ),
    (
        &[
            "alloc::vec::Vec::as_mut_slice",
            "std::vec::Vec::as_mut_slice",
        ],
        vec::specs::AS_MUT_SLICE,
    ),
    (
        &["alloc::vec::Vec::swap_remove", "std::vec::Vec::swap_remove"],
        vec::specs::SWAP_REMOVE,
    ),
    // binary_search — Vec deref path resolves to alloc::vec paths.
    // The [T]::binary_search path is in ptr_slice.rs via lookup_registry.
    (
        &[
            "alloc::vec::Vec::binary_search",
            "std::vec::Vec::binary_search",
        ],
        trust_wp_std::std::slice::specs::BINARY_SEARCH,
    ),
    // binary_search_by — Vec deref path
    (
        &[
            "alloc::vec::Vec::binary_search_by",
            "std::vec::Vec::binary_search_by",
        ],
        trust_wp_std::std::slice::specs::BINARY_SEARCH_BY,
    ),
    // binary_search_by_key — Vec deref path
    (
        &[
            "alloc::vec::Vec::binary_search_by_key",
            "std::vec::Vec::binary_search_by_key",
        ],
        trust_wp_std::std::slice::specs::BINARY_SEARCH_BY_KEY,
    ),
    // partition_point — Vec deref path
    (
        &[
            "alloc::vec::Vec::partition_point",
            "std::vec::Vec::partition_point",
        ],
        trust_wp_std::std::slice::specs::PARTITION_POINT,
    ),
    // split_at — Vec deref path (core::slice paths are in ptr_slice.rs via lookup_registry)
    (
        &["alloc::vec::Vec::split_at", "std::vec::Vec::split_at"],
        trust_wp_std::std::slice::specs::SPLIT_AT,
    ),
    // split_at_mut — Vec deref path
    (
        &[
            "alloc::vec::Vec::split_at_mut",
            "std::vec::Vec::split_at_mut",
        ],
        trust_wp_std::std::slice::specs::SPLIT_AT_MUT,
    ),
    // windows — Vec deref path
    (
        &["alloc::vec::Vec::windows", "std::vec::Vec::windows"],
        trust_wp_std::std::slice::specs::WINDOWS,
    ),
    // chunks — Vec deref path
    (
        &["alloc::vec::Vec::chunks", "std::vec::Vec::chunks"],
        trust_wp_std::std::slice::specs::CHUNKS,
    ),
    // split_first — Vec deref path
    (
        &["alloc::vec::Vec::split_first", "std::vec::Vec::split_first"],
        trust_wp_std::std::slice::specs::SPLIT_FIRST,
    ),
    // split_last — Vec deref path
    (
        &["alloc::vec::Vec::split_last", "std::vec::Vec::split_last"],
        trust_wp_std::std::slice::specs::SPLIT_LAST,
    ),
    // copy_from_slice — Vec deref path
    (
        &[
            "alloc::vec::Vec::copy_from_slice",
            "std::vec::Vec::copy_from_slice",
        ],
        trust_wp_std::std::slice::specs::COPY_FROM_SLICE,
    ),
    // sort_by — Vec deref path
    (
        &["alloc::vec::Vec::sort_by", "std::vec::Vec::sort_by"],
        vec::specs::SORT_BY,
    ),
    // sort_by_key — Vec deref path
    (
        &["alloc::vec::Vec::sort_by_key", "std::vec::Vec::sort_by_key"],
        vec::specs::SORT_BY_KEY,
    ),
    // sort_unstable_by — Vec deref path
    (
        &[
            "alloc::vec::Vec::sort_unstable_by",
            "std::vec::Vec::sort_unstable_by",
        ],
        vec::specs::SORT_UNSTABLE_BY,
    ),
    // sort_unstable_by_key — Vec deref path
    (
        &[
            "alloc::vec::Vec::sort_unstable_by_key",
            "std::vec::Vec::sort_unstable_by_key",
        ],
        vec::specs::SORT_UNSTABLE_BY_KEY,
    ),
    // from_elem — used by `vec![val; count]` macro
    (
        &["alloc::vec::from_elem", "std::vec::from_elem"],
        vec::specs::FROM_ELEM,
    ),
    // rotate_left — Vec deref path
    (
        &["alloc::vec::Vec::rotate_left", "std::vec::Vec::rotate_left"],
        trust_wp_std::std::slice::specs::ROTATE_LEFT,
    ),
    // rotate_right — Vec deref path
    (
        &[
            "alloc::vec::Vec::rotate_right",
            "std::vec::Vec::rotate_right",
        ],
        trust_wp_std::std::slice::specs::ROTATE_RIGHT,
    ),
    // fill — Vec deref path
    (
        &["alloc::vec::Vec::fill", "std::vec::Vec::fill"],
        trust_wp_std::std::slice::specs::FILL,
    ),
    // split_first_mut — Vec deref path
    (
        &[
            "alloc::vec::Vec::split_first_mut",
            "std::vec::Vec::split_first_mut",
        ],
        trust_wp_std::std::slice::specs::SPLIT_FIRST_MUT,
    ),
    // split_last_mut — Vec deref path
    (
        &[
            "alloc::vec::Vec::split_last_mut",
            "std::vec::Vec::split_last_mut",
        ],
        trust_wp_std::std::slice::specs::SPLIT_LAST_MUT,
    ),
    // drain — removes a range, returns Drain iterator
    (
        &["alloc::vec::Vec::drain", "std::vec::Vec::drain"],
        vec::specs::DRAIN,
    ),
    // retain_mut — like retain, with mutable references
    (
        &["alloc::vec::Vec::retain_mut", "std::vec::Vec::retain_mut"],
        vec::specs::RETAIN_MUT,
    ),
    // dedup_by — removes consecutive duplicates using custom comparison
    (
        &[
            "alloc::vec::Vec::dedup_by",
            "std::vec::Vec::dedup_by",
            "core::slice::dedup_by",
            "std::slice::dedup_by",
        ],
        vec::specs::DEDUP_BY,
    ),
    // dedup_by_key — removes consecutive duplicates using key extraction
    (
        &[
            "alloc::vec::Vec::dedup_by_key",
            "std::vec::Vec::dedup_by_key",
            "core::slice::dedup_by_key",
            "std::slice::dedup_by_key",
        ],
        vec::specs::DEDUP_BY_KEY,
    ),
];
