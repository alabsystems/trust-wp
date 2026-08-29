// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_free_view_helper_aliases() {
    for path in [
        "creusot_std::view",
        "creusot_std::logic::view",
        "trust_wp_std::view",
        "trust_wp_std::logic::model::view",
        "trust_wp::view",
    ] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        assert_param_names(&spec, &["value"], path);
        assert_ensures_contains(&spec, "result == value@", path);
    }
}

#[test]
fn test_lookup_fmap_remove() {
    let spec = lookup_std_spec("trust_wp_std::logic::FMap::remove")
        .expect("FMap::remove spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "!result.contains(arg1)", "FMap::remove");
    assert_ensures_contains(
        &spec,
        "result.contains(k2) == self.contains(k2)",
        "FMap::remove",
    );
}

#[test]
fn test_lookup_fmap_index() {
    let spec =
        lookup_std_spec("trust_wp_std::logic::FMap::index").expect("FMap::index spec should exist");
    assert_requires_contains(&spec, "self.contains(arg1)", "FMap::index");
    assert_ensures_contains(&spec, "*result == self.lookup(arg1)", "FMap::index");
}

#[test]
fn test_lookup_fmap_index_trait_qualified() {
    let spec = lookup_std_spec("<trust_wp_std::logic::fmap::FMap as core::ops::Index>::index")
        .expect("trait-qualified FMap Index path should match");
    assert_requires_contains(&spec, "self.contains(arg1)", "FMap::index trait");
    assert_ensures_contains(&spec, "*result == self.lookup(arg1)", "FMap::index trait");
}

#[test]
fn test_lookup_fmap_singleton() {
    let spec = lookup_std_spec("trust_wp_std::logic::FMap::singleton")
        .expect("FMap::singleton spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.contains(arg0)", "FMap::singleton");
    assert_ensures_contains(&spec, "result.lookup(arg0) == arg1", "FMap::singleton");
    assert_ensures_contains(&spec, "result.len() == 1", "FMap::singleton");
}

#[test]
fn test_lookup_fmap_ext_eq() {
    let spec = lookup_std_spec("trust_wp_std::logic::FMap::ext_eq")
        .expect("FMap::ext_eq spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == (self.len() == arg1.len()", "FMap::ext_eq");
}

#[test]
fn test_lookup_fmap_disjoint() {
    let spec = lookup_std_spec("trust_wp_std::logic::FMap::disjoint")
        .expect("FMap::disjoint spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result == forall<k: _> !self.contains(k) || !arg1.contains(k)",
        "FMap::disjoint",
    );
}

#[test]
fn test_lookup_fmap_union() {
    let spec =
        lookup_std_spec("trust_wp_std::logic::FMap::union").expect("FMap::union spec should exist");
    assert_requires_contains(&spec, "self.disjoint(&arg1)", "FMap::union");
    assert_ensures_contains(
        &spec,
        "result.len() == self.len() + arg1.len()",
        "FMap::union",
    );
    assert_ensures_contains(
        &spec,
        "self.contains(k) ==> result.contains(k) && result.lookup(k) == self.lookup(k)",
        "FMap::union",
    );
    assert_ensures_contains(
        &spec,
        "arg1.contains(k) ==> result.contains(k) && result.lookup(k) == arg1.lookup(k)",
        "FMap::union",
    );
    assert_ensures_contains(
        &spec,
        "result.contains(k) ==> self.contains(k) || arg1.contains(k)",
        "FMap::union",
    );
}

#[test]
fn test_lookup_fmap_merge() {
    let spec =
        lookup_std_spec("trust_wp_std::logic::FMap::merge").expect("FMap::merge spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result.contains(k) == (self.contains(k) || arg1.contains(k))",
        "FMap::merge",
    );
    assert_ensures_contains(
        &spec,
        "self.contains(k) && !arg1.contains(k) ==> result.lookup(k) == self.lookup(k)",
        "FMap::merge",
    );
    assert_ensures_contains(
        &spec,
        "!self.contains(k) && arg1.contains(k) ==> result.lookup(k) == arg1.lookup(k)",
        "FMap::merge",
    );
}

// ── HashMap specs (#967) ────────────────────────────────────────

#[test]
fn test_lookup_fmap_split_mut_ghost() {
    let spec = lookup_std_spec("trust_wp_std::logic::FMap::split_mut_ghost")
        .expect("FMap::split_mut_ghost spec should exist");
    assert_requires_contains(&spec, "self.contains(*arg1)", "FMap::split_mut_ghost");
    assert_ensures_contains(
        &spec,
        "*result.0 == self.lookup(*arg1)",
        "FMap::split_mut_ghost",
    );
}

// ── FMap ghost premise trio (get_mut/split write-back campaign) ──

/// Every requires/ensures clause of the FMap ghost mutation specs MUST
/// parse: a clause that fails `parse_contract` at a call site is dropped
/// fail-closed into a synthetic `false` obligation (#1739), which would
/// wedge every proof_assert downstream of the call in the ghost block.
#[test]
fn test_fmap_ghost_mutation_spec_clauses_all_parse() {
    for path in [
        "trust_wp_std::logic::FMap::get_mut_ghost",
        "trust_wp_std::logic::FMap::split_mut_ghost",
        "trust_wp_std::logic::FMap::insert_ghost",
        "trust_wp_std::logic::FMap::remove_ghost",
        "trust_wp_std::logic::fmap::FMapGhostSplit::insert_ghost",
        "trust_wp_std::logic::fmap::FMapGhostSplit::remove_ghost",
    ] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        for clause in spec.requires.iter().chain(spec.ensures.iter()) {
            trust_wp_core::contract_parser::parse_contract(clause).unwrap_or_else(|e| {
                panic!("{path} clause must parse (fail-closed otherwise): `{clause}`: {e}")
            });
        }
    }
}

/// `get_mut_ghost` post-state clauses (Creusot creusot-std fmap.rs:351-367):
/// frame + len-preservation + post-containment. The `^self` mentions are
/// load-bearing — they advance the receiver's carrier at the call site.
/// The `^r` value write-back must stay ABSENT until the encoder can carry
/// an Option-payload prophecy (Final on a pattern binder currently
/// collapses to the binder — asserting it would pin the post-value to the
/// PRE-write payload, a false premise).
#[test]
fn test_lookup_fmap_get_mut_ghost_post_state() {
    let spec = lookup_std_spec("trust_wp_std::logic::FMap::get_mut_ghost")
        .expect("FMap::get_mut_ghost spec should exist");
    assert_ensures_contains(&spec, "(^self).contains(*arg1)", "FMap::get_mut_ghost");
    assert_ensures_contains(
        &spec,
        "!self.contains(*arg1) && !(^self).contains(*arg1)",
        "FMap::get_mut_ghost",
    );
    assert_ensures_contains(
        &spec,
        "k2 != *arg1 ==> (^self).contains(k2) == self.contains(k2)",
        "FMap::get_mut_ghost",
    );
    assert_ensures_contains(
        &spec,
        "k2 != *arg1 && self.contains(k2) ==> (^self).lookup(k2) == self.lookup(k2)",
        "FMap::get_mut_ghost",
    );
    assert_ensures_contains(&spec, "(^self).len() == self.len()", "FMap::get_mut_ghost");
    assert!(
        !spec.ensures.iter().any(|e| e.contains("^v")),
        "FMap::get_mut_ghost must NOT carry a `^v` payload write-back while \
         the encoder collapses Final on pattern binders (unsound): {:?}",
        spec.ensures
    );
}

/// `split_mut_ghost` seeds the split view from the pre-split map with the
/// GROUND consequences of `*result.1 == (*self).remove(*key)` (Creusot
/// fmap.rs:389-397) and mentions `^self` (via the ground write-back
/// consequence `(^self).contains(*arg1)`) so the parent's carrier advances
/// (havoc) at the split site — without a parent write-back equation (no
/// sound carrier for the split view's borrow-end generation exists at the
/// call site). The remove-model frame foralls must stay ABSENT: they have
/// no consumer until the parent write-back exists and their e-matching
/// load alone blew the whole-test budget (measured 2026-08-05).
#[test]
fn test_lookup_fmap_split_mut_ghost_seed_and_havoc() {
    let spec = lookup_std_spec("trust_wp_std::logic::FMap::split_mut_ghost")
        .expect("FMap::split_mut_ghost spec should exist");
    assert_ensures_contains(
        &spec,
        "!(*result.1).contains(*arg1)",
        "FMap::split_mut_ghost",
    );
    assert_ensures_contains(
        &spec,
        "(*result.1).len() == self.len() - 1",
        "FMap::split_mut_ghost",
    );
    assert_ensures_contains(&spec, "(^self).contains(*arg1)", "FMap::split_mut_ghost");
    assert!(
        !spec.ensures.iter().any(|e| e.contains("^result")),
        "FMap::split_mut_ghost must NOT equate the parent post-state with a \
         fixed-depth split-view generation (`^result.1` has no sound carrier \
         at the call site): {:?}",
        spec.ensures
    );
    assert!(
        !spec.ensures.iter().any(|e| e.contains("forall")),
        "FMap::split_mut_ghost must stay forall-free (no consumer until the \
         parent write-back exists; measured e-matching budget blowout): {:?}",
        spec.ensures
    );
}

// ── FMapGhostSplit spec lookups (#2671) ─────────────────────────

#[test]
fn test_lookup_fmap_ghost_split_insert() {
    let spec = lookup_std_spec("trust_wp_std::logic::fmap::FMapGhostSplit::insert_ghost")
        .expect("FMapGhostSplit::insert_ghost spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "(^self).contains(arg1)",
        "FMapGhostSplit::insert_ghost",
    );
    assert_ensures_contains(
        &spec,
        "(^self).lookup(arg1) == arg2",
        "FMapGhostSplit::insert_ghost",
    );
    // Split-view state semantics (Creusot: the split handle is a plain
    // `&mut FMap`): result binding + len laws mirror INSERT_GHOST.
    assert_ensures_contains(
        &spec,
        "Some(prev) => self.contains(arg1) && prev == self.lookup(arg1) && (^self).len() == self.len()",
        "FMapGhostSplit::insert_ghost",
    );
    assert_ensures_contains(
        &spec,
        "None => !self.contains(arg1) && (^self).len() == self.len() + 1",
        "FMapGhostSplit::insert_ghost",
    );
}

#[test]
fn test_lookup_fmap_ghost_split_remove() {
    let spec = lookup_std_spec("trust_wp_std::logic::fmap::FMapGhostSplit::remove_ghost")
        .expect("FMapGhostSplit::remove_ghost spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "!(^self).contains(*arg1)",
        "FMapGhostSplit::remove_ghost",
    );
}

// ── Seq Index spec lookups (#2671) ──────────────────────────────

#[test]
fn test_lookup_seq_index() {
    let spec =
        lookup_std_spec("trust_wp_std::logic::Seq::index").expect("Seq::index spec should exist");
    assert_requires_contains(&spec, "0 <= arg1", "Seq::index");
    assert_requires_contains(&spec, "arg1 < self.len()", "Seq::index");
    assert_ensures_contains(&spec, "*result == self[arg1]", "Seq::index");
}

#[test]
fn test_lookup_seq_index_trait_qualified() {
    // Verify trait-qualified path also works
    let spec = lookup_std_spec("<trust_wp_std::logic::Seq as core::ops::Index>::index")
        .expect("Seq Index trait spec should exist");
    assert_ensures_contains(&spec, "*result == self[arg1]", "Seq::index via trait");
}

// ── Resource Algebra spec lookups (#1126) ───────────────────────

#[test]
fn test_lookup_agree_op() {
    let spec =
        lookup_std_spec("trust_wp_std::logic::ra::Ag::op").expect("Ag::op spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self.0 == other.0", "Ag::op");
}

#[test]
fn test_lookup_agree_incl() {
    let spec = lookup_std_spec("trust_wp_std::logic::ra::agree::Ag::incl")
        .expect("Ag::incl spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self.0 == other.0", "Ag::incl");
}

#[test]
fn test_lookup_excl_op() {
    let spec =
        lookup_std_spec("trust_wp_std::logic::ra::Excl::op").expect("Excl::op spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == None", "Excl::op");
}

#[test]
fn test_lookup_excl_can_update() {
    let spec = lookup_std_spec("trust_wp_std::Excl::can_update")
        .expect("Excl::can_update spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == true", "Excl::can_update");
}

#[test]
fn test_lookup_frac_op() {
    let spec =
        lookup_std_spec("trust_wp_std::logic::ra::Frac::op").expect("Frac::op spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self.value == other.value", "Frac::op");
}

#[test]
fn test_lookup_frac_split() {
    let spec = lookup_std_spec("trust_wp_std::logic::ra::frac::Frac::split")
        .expect("Frac::split spec should exist");
    assert_requires_contains(&spec, "left_numer > 0", "Frac::split");
    assert_ensures_contains(&spec, "result.0.numer == left_numer", "Frac::split");
}

#[test]
fn test_lookup_frac_is_full() {
    let spec =
        lookup_std_spec("trust_wp_std::Frac::is_full").expect("Frac::is_full spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self.numer == FRAC_DENOM", "Frac::is_full");
}

// ── FSet set-theoretic spec lookups (#2239) ─────────────────────

#[test]
fn test_lookup_fset_singleton() {
    let spec = lookup_std_spec("trust_wp_std::logic::FSet::singleton")
        .expect("FSet::singleton spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.contains(arg1)", "FSet::singleton");
    assert_ensures_contains(&spec, "result.len() == 1", "FSet::singleton");
    assert_ensures_contains(
        &spec,
        "y != arg1 ==> !result.contains(y)",
        "FSet::singleton",
    );
}

#[test]
fn test_lookup_fset_singleton_param_names() {
    // FSet::singleton is an associated function (no self). Its params: line
    // declares "arg1" as the name for position 0. This differs from
    // Seq::singleton (arg0) and FMap::singleton (arg0, arg1) but is correct
    // because the params: line controls positional-to-named binding.
    let spec = lookup_std_spec("trust_wp_std::logic::FSet::singleton")
        .expect("FSet::singleton spec should exist");
    assert_param_names(&spec, &["arg1"], "FSet::singleton");
}

#[test]
fn test_lookup_fset_union() {
    let spec =
        lookup_std_spec("trust_wp_std::logic::FSet::union").expect("FSet::union spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result.contains(x) == (self.contains(x) || arg1.contains(x))",
        "FSet::union",
    );
}

#[test]
fn test_lookup_fset_intersection() {
    let spec = lookup_std_spec("trust_wp_std::logic::FSet::intersection")
        .expect("FSet::intersection spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result.contains(x) == (self.contains(x) && arg1.contains(x))",
        "FSet::intersection",
    );
}

#[test]
fn test_lookup_fset_difference() {
    let spec = lookup_std_spec("trust_wp_std::logic::FSet::difference")
        .expect("FSet::difference spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result.contains(x) == (self.contains(x) && !arg1.contains(x))",
        "FSet::difference",
    );
}

#[test]
fn test_lookup_fset_is_subset() {
    let spec = lookup_std_spec("trust_wp_std::logic::FSet::is_subset")
        .expect("FSet::is_subset spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result == (forall<x: _> self.contains(x) ==> arg1.contains(x))",
        "FSet::is_subset",
    );
}

#[test]
fn test_lookup_fset_is_superset() {
    let spec = lookup_std_spec("trust_wp_std::logic::FSet::is_superset")
        .expect("FSet::is_superset spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result == (forall<x: _> arg1.contains(x) ==> self.contains(x))",
        "FSet::is_superset",
    );
}

#[test]
fn test_lookup_fset_disjoint() {
    let spec = lookup_std_spec("trust_wp_std::logic::FSet::disjoint")
        .expect("FSet::disjoint spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result == (forall<x: _> !self.contains(x) || !arg1.contains(x))",
        "FSet::disjoint",
    );
}

#[test]
fn test_lookup_fset_ext_eq() {
    let spec = lookup_std_spec("trust_wp_std::logic::FSet::ext_eq")
        .expect("FSet::ext_eq spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(
        &spec,
        "result == (forall<x: _> self.contains(x) == arg1.contains(x))",
        "FSet::ext_eq",
    );
}

// ── FMap new spec lookups (#2239) ───────────────────────────────

#[test]
fn test_lookup_fmap_is_empty() {
    let spec = lookup_std_spec("trust_wp_std::logic::FMap::is_empty")
        .expect("FMap::is_empty spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == (self.len() == 0)", "FMap::is_empty");
}

#[test]
fn test_lookup_fmap_into_inner() {
    let spec = lookup_std_spec("trust_wp_std::logic::FMap::into_inner")
        .expect("FMap::into_inner spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == self", "FMap::into_inner");
}

// ── such_that spec lookups (#2245) ──────────────────────────────

#[test]
fn test_lookup_such_that() {
    let spec =
        lookup_std_spec("trust_wp_std::logic::such_that").expect("such_that spec should exist");
    assert!(
        spec.requires.is_empty(),
        "such_that should have no preconditions"
    );
    assert_ensures_contains(&spec, "arg0.get(result)", "such_that");
}

#[test]
fn test_lookup_such_that_module_qualified() {
    let spec = lookup_std_spec("trust_wp_std::logic::such_that::such_that")
        .expect("module-qualified such_that path should match");
    assert_ensures_contains(&spec, "arg0.get(result)", "such_that module path");
}
