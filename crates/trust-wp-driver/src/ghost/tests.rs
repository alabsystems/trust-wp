// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for ghost type classification helpers.
//!
//! Integration tests for ghost block validation: `tests/ghost_move_validation.rs`.
//! Unit tests for `is_trust_wp_ghost_like_path` below (#1130).

use super::type_helpers::{
    is_known_interior_mutability_mutator_path, is_trust_wp_ghost_like_path,
    is_trust_wp_logic_type_path,
};

#[test]
fn test_trust_wp_std_full_path() {
    assert!(is_trust_wp_ghost_like_path(
        "trust_wp_std",
        "trust_wp_std::ghost::Ghost"
    ));
}

#[test]
fn test_trust_wp_std_short_path() {
    assert!(is_trust_wp_ghost_like_path("trust_wp_std", "ghost::Ghost"));
}

#[test]
fn test_trust_wp_std_snapshot_full_path() {
    assert!(is_trust_wp_ghost_like_path(
        "trust_wp_std",
        "trust_wp_std::ghost::Snapshot"
    ));
}

#[test]
fn test_trust_wp_reexport() {
    assert!(is_trust_wp_ghost_like_path("trust-wp", "trust_wp::Ghost"));
}

#[test]
fn test_trust_wp_reexport_def_path_from_trust_wp_std_crate() {
    assert!(is_trust_wp_ghost_like_path(
        "trust_wp_std",
        "trust_wp::Ghost"
    ));
}

#[test]
fn test_trust_wp_snapshot_reexport() {
    assert!(is_trust_wp_ghost_like_path(
        "trust-wp",
        "trust_wp::Snapshot"
    ));
}

#[test]
fn test_trust_wp_bare_name() {
    assert!(is_trust_wp_ghost_like_path("trust-wp", "Ghost"));
}

#[test]
fn test_trust_wp_snapshot_bare_name() {
    assert!(is_trust_wp_ghost_like_path("trust-wp", "Snapshot"));
}

#[test]
fn test_creusot_std_snapshot_path() {
    assert!(is_trust_wp_ghost_like_path(
        "creusot_std",
        "creusot_std::ghost::Snapshot"
    ));
}

#[test]
fn test_creusot_std_ghost_path() {
    assert!(is_trust_wp_ghost_like_path(
        "creusot_std",
        "creusot_std::ghost::Ghost"
    ));
}

#[test]
fn test_creusot_contracts_ghost_path() {
    assert!(is_trust_wp_ghost_like_path(
        "creusot_contracts",
        "creusot_contracts::Ghost"
    ));
}

#[test]
fn test_creusot_contracts_snapshot_path() {
    assert!(is_trust_wp_ghost_like_path(
        "creusot_contracts",
        "creusot_contracts::Snapshot"
    ));
}

/// Regression test for #1130: a bare "Ghost" name from a non-trust-wp
/// crate must NOT match.
#[test]
fn test_non_trust_wp_bare_ghost_rejected() {
    assert!(!is_trust_wp_ghost_like_path("user_crate", "Ghost"));
}

#[test]
fn test_non_trust_wp_bare_snapshot_rejected() {
    assert!(!is_trust_wp_ghost_like_path("user_crate", "Snapshot"));
}

#[test]
fn test_non_trust_wp_ghost_path_rejected() {
    assert!(!is_trust_wp_ghost_like_path(
        "user_crate",
        "user_crate::Ghost"
    ));
}

#[test]
fn test_non_trust_wp_nested_ghost_rejected() {
    assert!(!is_trust_wp_ghost_like_path(
        "other_lib",
        "other_lib::ghost::Ghost"
    ));
}

#[test]
fn test_non_trust_wp_nested_snapshot_rejected() {
    assert!(!is_trust_wp_ghost_like_path(
        "other_lib",
        "other_lib::ghost::Snapshot"
    ));
}

#[test]
fn test_known_interior_mutability_mutator_paths() {
    assert!(is_known_interior_mutability_mutator_path(
        "core::cell::Cell::set"
    ));
    assert!(is_known_interior_mutability_mutator_path(
        "std::cell::RefCell::replace_with"
    ));
    assert!(is_known_interior_mutability_mutator_path(
        "cell::Cell::swap"
    ));
    assert!(is_known_interior_mutability_mutator_path(
        "core::cell::RefCell::borrow_mut"
    ));
}

#[test]
fn test_non_mutator_paths_rejected() {
    assert!(!is_known_interior_mutability_mutator_path(
        "core::cell::Cell::get"
    ));
    assert!(!is_known_interior_mutability_mutator_path(
        "std::cell::RefCell::borrow"
    ));
    assert!(!is_known_interior_mutability_mutator_path(
        "user_crate::Cell::set"
    ));
}

#[test]
fn test_trust_wp_std_seq_is_logic_type() {
    assert!(is_trust_wp_logic_type_path(
        "trust_wp_std",
        "trust_wp_std::logic::seq::Seq"
    ));
}

#[test]
fn test_trust_wp_std_seq_short_path() {
    assert!(is_trust_wp_logic_type_path(
        "trust_wp_std",
        "trust_wp_std::logic::Seq"
    ));
}

#[test]
fn test_trust_wp_std_fmap_is_logic_type() {
    assert!(is_trust_wp_logic_type_path(
        "trust_wp_std",
        "trust_wp_std::logic::fmap::FMap"
    ));
}

#[test]
fn test_trust_wp_std_fset_is_logic_type() {
    assert!(is_trust_wp_logic_type_path(
        "trust_wp_std",
        "trust_wp_std::logic::fset::FSet"
    ));
}

#[test]
fn test_trust_wp_std_int_is_logic_type() {
    assert!(is_trust_wp_logic_type_path(
        "trust_wp_std",
        "trust_wp_std::logic::int::Int"
    ));
}

#[test]
fn test_creusot_std_seq_is_logic_type() {
    assert!(is_trust_wp_logic_type_path(
        "creusot_std",
        "creusot_std::logic::seq::Seq"
    ));
}

#[test]
fn test_trust_wp_std_mapping_is_logic_type() {
    assert!(is_trust_wp_logic_type_path(
        "trust_wp_std",
        "trust_wp_std::logic::Mapping"
    ));
}

#[test]
fn test_non_trust_wp_seq_rejected() {
    assert!(!is_trust_wp_logic_type_path(
        "user_crate",
        "user_crate::Seq"
    ));
}

#[test]
fn test_non_logic_trust_wp_type_rejected() {
    assert!(!is_trust_wp_logic_type_path(
        "trust_wp_std",
        "trust_wp_std::ghost::Ghost"
    ));
}
