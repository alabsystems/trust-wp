// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    super::*,
    helpers::{assert_ensures_contains, assert_param_names, assert_requires_contains},
};

#[test]
fn test_lookup_std_spec_ghost() {
    let ghost_new = lookup_std_spec("trust_wp_std::ghost::Ghost::<i32>::new")
        .expect("Ghost::new spec should exist");
    assert!(ghost_new.requires.is_empty());
    assert_eq!(ghost_new.ensures, vec!["result == value"]);
    assert_param_names(&ghost_new, &["value"], "Ghost::new");

    let ghost_inner = lookup_std_spec("trust_wp_std::ghost::Ghost::<i32>::inner")
        .expect("Ghost::inner spec should exist");
    assert!(ghost_inner.requires.is_empty());
    assert_eq!(ghost_inner.ensures, vec!["result == self"]);
    assert_param_names(&ghost_inner, &["self"], "Ghost::inner");

    let ghost_inner_mut = lookup_std_spec("trust_wp_std::ghost::Ghost::<i32>::inner_mut")
        .expect("Ghost::inner_mut spec should exist");
    assert!(ghost_inner_mut.requires.is_empty());
    assert_eq!(ghost_inner_mut.ensures, vec!["result == self"]);
    assert_param_names(&ghost_inner_mut, &["self"], "Ghost::inner_mut");

    let ghost_into_inner = lookup_std_spec("trust_wp_std::ghost::Ghost::<i32>::into_inner")
        .expect("Ghost::into_inner spec should exist");
    assert!(ghost_into_inner.requires.is_empty());
    assert_eq!(ghost_into_inner.ensures, vec!["result == self"]);
    assert_param_names(&ghost_into_inner, &["self"], "Ghost::into_inner");

    let snapshot_capture = lookup_std_spec("trust_wp_std::ghost::Snapshot::<i32>::capture")
        .expect("Snapshot::capture spec should exist");
    assert!(snapshot_capture.requires.is_empty());
    assert_eq!(snapshot_capture.ensures, vec!["result == value"]);
    assert_param_names(&snapshot_capture, &["value"], "Snapshot::capture");

    let snapshot_from_fn = lookup_std_spec("trust_wp_std::ghost::Snapshot::<i32>::from_fn")
        .expect("Snapshot::from_fn spec should exist");
    assert!(snapshot_from_fn.requires.is_empty());
    assert!(
        snapshot_from_fn.ensures.is_empty(),
        "from_fn is a deferred capture with no constraints"
    );

    let snapshot_new_phantom = lookup_std_spec("trust_wp_std::ghost::Snapshot::<i32>::new_phantom")
        .expect("Snapshot::new_phantom spec should exist");
    assert!(snapshot_new_phantom.requires.is_empty());
    assert!(
        snapshot_new_phantom.ensures.is_empty(),
        "new_phantom is a ghost placeholder with no constraints"
    );

    let snapshot_inner = lookup_std_spec("trust_wp_std::ghost::Snapshot::<i32>::inner")
        .expect("Snapshot::inner spec should exist");
    assert!(snapshot_inner.requires.is_empty());
    assert_eq!(snapshot_inner.ensures, vec!["result == self"]);
    assert_param_names(&snapshot_inner, &["self"], "Snapshot::inner");

    let snapshot_into_inner = lookup_std_spec("trust_wp_std::ghost::Snapshot::<i32>::into_inner")
        .expect("Snapshot::into_inner spec should exist");
    assert!(snapshot_into_inner.requires.is_empty());
    assert_eq!(snapshot_into_inner.ensures, vec!["result == self"]);
    assert_param_names(&snapshot_into_inner, &["self"], "Snapshot::into_inner");

    let ghost_deref = lookup_std_spec("<trust_wp_std::ghost::Ghost as core::ops::Deref>::deref")
        .expect("Ghost::deref spec should exist");
    assert!(ghost_deref.requires.is_empty());
    assert_eq!(ghost_deref.ensures, vec!["result == self"]);
    assert_param_names(&ghost_deref, &["self"], "Ghost::deref");

    let ghost_deref_mut =
        lookup_std_spec("<trust_wp_std::ghost::Ghost as core::ops::DerefMut>::deref_mut")
            .expect("Ghost::deref_mut spec should exist");
    assert!(ghost_deref_mut.requires.is_empty());
    assert_eq!(ghost_deref_mut.ensures, vec!["result == self"]);
    assert_param_names(&ghost_deref_mut, &["self"], "Ghost::deref_mut");
}

#[test]
fn test_lookup_std_spec_ghost_reexports() {
    let ghost_new = lookup_std_spec("trust_wp_std::Ghost::<i32>::new")
        .expect("Ghost::new re-export spec should exist");
    assert!(ghost_new.requires.is_empty());
    assert_eq!(ghost_new.ensures, vec!["result == value"]);
    assert_param_names(&ghost_new, &["value"], "Ghost::new re-export");

    let ghost_inner = lookup_std_spec("trust_wp_std::Ghost::<i32>::inner")
        .expect("Ghost::inner re-export spec should exist");
    assert!(ghost_inner.requires.is_empty());
    assert_eq!(ghost_inner.ensures, vec!["result == self"]);
    assert_param_names(&ghost_inner, &["self"], "Ghost::inner re-export");

    let ghost_inner_mut = lookup_std_spec("trust_wp_std::Ghost::<i32>::inner_mut")
        .expect("Ghost::inner_mut re-export spec should exist");
    assert!(ghost_inner_mut.requires.is_empty());
    assert_eq!(ghost_inner_mut.ensures, vec!["result == self"]);
    assert_param_names(&ghost_inner_mut, &["self"], "Ghost::inner_mut re-export");

    let ghost_into_inner = lookup_std_spec("trust_wp_std::Ghost::<i32>::into_inner")
        .expect("Ghost::into_inner re-export spec should exist");
    assert!(ghost_into_inner.requires.is_empty());
    assert_eq!(ghost_into_inner.ensures, vec!["result == self"]);
    assert_param_names(&ghost_into_inner, &["self"], "Ghost::into_inner re-export");

    let snapshot_capture = lookup_std_spec("trust_wp_std::Snapshot::<i32>::capture")
        .expect("Snapshot::capture re-export spec should exist");
    assert!(snapshot_capture.requires.is_empty());
    assert_eq!(snapshot_capture.ensures, vec!["result == value"]);
    assert_param_names(&snapshot_capture, &["value"], "Snapshot::capture re-export");

    let snapshot_from_fn = lookup_std_spec("trust_wp_std::Snapshot::<i32>::from_fn")
        .expect("Snapshot::from_fn re-export spec should exist");
    assert!(snapshot_from_fn.requires.is_empty());
    assert!(
        snapshot_from_fn.ensures.is_empty(),
        "from_fn re-export is a deferred capture with no constraints"
    );

    let snapshot_new_phantom = lookup_std_spec("trust_wp_std::Snapshot::<i32>::new_phantom")
        .expect("Snapshot::new_phantom re-export spec should exist");
    assert!(snapshot_new_phantom.requires.is_empty());
    assert!(
        snapshot_new_phantom.ensures.is_empty(),
        "new_phantom re-export is a ghost placeholder with no constraints"
    );

    let snapshot_inner = lookup_std_spec("trust_wp_std::Snapshot::<i32>::inner")
        .expect("Snapshot::inner re-export spec should exist");
    assert!(snapshot_inner.requires.is_empty());
    assert_eq!(snapshot_inner.ensures, vec!["result == self"]);
    assert_param_names(&snapshot_inner, &["self"], "Snapshot::inner re-export");

    let ghost_deref = lookup_std_spec("<trust_wp_std::Ghost as core::ops::Deref>::deref")
        .expect("Ghost::deref re-export spec should exist");
    assert!(ghost_deref.requires.is_empty());
    assert_eq!(ghost_deref.ensures, vec!["result == self"]);
    assert_param_names(&ghost_deref, &["self"], "Ghost::deref re-export");

    let ghost_deref_mut =
        lookup_std_spec("<trust_wp_std::Ghost as core::ops::DerefMut>::deref_mut")
            .expect("Ghost::deref_mut re-export spec should exist");
    assert!(ghost_deref_mut.requires.is_empty());
    assert_eq!(ghost_deref_mut.ensures, vec!["result == self"]);
    assert_param_names(&ghost_deref_mut, &["self"], "Ghost::deref_mut re-export");
}

#[test]
fn test_lookup_std_spec_snapshot_trust_wp_reexports() {
    let snapshot_capture = lookup_std_spec("trust_wp::Snapshot::<i32>::capture")
        .expect("Snapshot::capture trust-wp re-export spec should exist");
    assert!(snapshot_capture.requires.is_empty());
    assert_eq!(snapshot_capture.ensures, vec!["result == value"]);
    assert_param_names(
        &snapshot_capture,
        &["value"],
        "Snapshot::capture trust-wp re-export",
    );

    let snapshot_from_fn = lookup_std_spec("trust_wp::Snapshot::<i32>::from_fn")
        .expect("Snapshot::from_fn trust-wp re-export spec should exist");
    assert!(snapshot_from_fn.requires.is_empty());
    assert!(
        snapshot_from_fn.ensures.is_empty(),
        "from_fn trust-wp re-export is a deferred capture with no constraints"
    );

    let snapshot_new_phantom = lookup_std_spec("trust_wp::Snapshot::<i32>::new_phantom")
        .expect("Snapshot::new_phantom trust-wp re-export spec should exist");
    assert!(snapshot_new_phantom.requires.is_empty());
    assert!(
        snapshot_new_phantom.ensures.is_empty(),
        "new_phantom trust-wp re-export is a ghost placeholder with no constraints"
    );

    let snapshot_inner = lookup_std_spec("trust_wp::Snapshot::<i32>::inner")
        .expect("Snapshot::inner trust-wp re-export spec should exist");
    assert!(snapshot_inner.requires.is_empty());
    assert_eq!(snapshot_inner.ensures, vec!["result == self"]);
    assert_param_names(
        &snapshot_inner,
        &["self"],
        "Snapshot::inner trust-wp re-export",
    );

    let snapshot_into_inner = lookup_std_spec("trust_wp::Snapshot::<i32>::into_inner")
        .expect("Snapshot::into_inner trust-wp re-export spec should exist");
    assert!(snapshot_into_inner.requires.is_empty());
    assert_eq!(snapshot_into_inner.ensures, vec!["result == self"]);
    assert_param_names(
        &snapshot_into_inner,
        &["self"],
        "Snapshot::into_inner trust-wp re-export",
    );

    let snapshot_deref = lookup_std_spec("<trust_wp::Snapshot as core::ops::Deref>::deref")
        .expect("Snapshot::deref trust-wp re-export spec should exist");
    assert!(snapshot_deref.requires.is_empty());
    assert_eq!(snapshot_deref.ensures, vec!["result == self"]);
    assert_param_names(
        &snapshot_deref,
        &["self"],
        "Snapshot::deref trust-wp re-export",
    );
}

/// Facade-root `trust_wp::Ghost::*` paths resolve via normalization (#2335).
#[test]
fn test_lookup_std_spec_ghost_trust_wp_facade_reexports() {
    let ghost_new = lookup_std_spec("trust_wp::Ghost::<i32>::new")
        .expect("trust_wp::Ghost::new facade path should resolve via normalization");
    assert_eq!(ghost_new.ensures, vec!["result == value"]);
    assert_param_names(&ghost_new, &["value"], "Ghost::new facade");

    let ghost_inner = lookup_std_spec("trust_wp::Ghost::<i32>::inner")
        .expect("trust_wp::Ghost::inner facade path should resolve via normalization");
    assert_eq!(ghost_inner.ensures, vec!["result == self"]);
    assert_param_names(&ghost_inner, &["self"], "Ghost::inner facade");

    let ghost_into_inner = lookup_std_spec("trust_wp::Ghost::<i32>::into_inner")
        .expect("trust_wp::Ghost::into_inner facade path should resolve via normalization");
    assert_eq!(ghost_into_inner.ensures, vec!["result == self"]);
    assert_param_names(&ghost_into_inner, &["self"], "Ghost::into_inner facade");

    let ghost_deref = lookup_std_spec("<trust_wp::Ghost as core::ops::Deref>::deref")
        .expect("trust_wp::Ghost deref UFCS facade path should resolve via normalization");
    assert_eq!(ghost_deref.ensures, vec!["result == self"]);
    assert_param_names(&ghost_deref, &["self"], "Ghost::deref facade");
}

/// Module-qualified `trust_wp::ghost::*` paths resolve via prefix alias (#2335).
#[test]
fn test_lookup_std_spec_trust_wp_ghost_module_path() {
    let snap = lookup_std_spec("trust_wp::ghost::Snapshot::<i32>::capture")
        .expect("trust_wp::ghost::Snapshot path should resolve via trust_wp:: alias");
    assert_eq!(snap.ensures, vec!["result == value"]);
}

/// Facade-root `trust_wp::Perm::*` permission paths resolve via normalization (#2335).
#[test]
fn test_lookup_std_spec_trust_wp_facade_perm() {
    let perm_new = lookup_std_spec("trust_wp::Perm::<i32>::new")
        .expect("trust_wp::Perm::new facade path should resolve via normalization");
    assert_eq!(perm_new.ensures, vec!["result.0 == *result.1"]);
}

/// Facade-root `trust_wp::Seq::*` logic-type paths resolve via normalization (#2335).
#[test]
fn test_lookup_std_spec_trust_wp_facade_seq() {
    let seq_len = lookup_std_spec("trust_wp::Seq::<i32>::len_ghost")
        .expect("trust_wp::Seq::len_ghost facade path should resolve via normalization");
    assert_eq!(seq_len.ensures, vec!["result == self.len()"]);
    assert_param_names(&seq_len, &["self"], "Seq::len_ghost facade");
}

/// Internal `core` submodule paths from inherent `impl` blocks resolve
/// to canonical Seq spec paths after INTERNAL_SUBMODULES stripping (#2326).
#[test]
fn test_lookup_std_spec_seq_core_internal_submodule_push_back_ghost() {
    let spec = lookup_std_spec("trust_wp_std::logic::seq::core::<impl Seq<T>>::push_back_ghost")
        .expect("internal core submodule push_back_ghost path should resolve via normalization");
    assert!(
        spec.ensures
            .iter()
            .any(|e| e.contains("^self == self.push_back(arg1)")),
        "push_back_ghost spec should link post-state to push_back UF"
    );
}

#[test]
fn test_lookup_std_spec_seq_core_internal_submodule_len_ghost() {
    let spec = lookup_std_spec("trust_wp_std::logic::seq::core::<impl Seq<T>>::len_ghost")
        .expect("internal core submodule len_ghost path should resolve via normalization");
    assert_eq!(spec.ensures, vec!["result == self.len()"]);
    assert_param_names(&spec, &["self"], "Seq::len_ghost internal core submodule");
}

#[test]
fn test_lookup_std_spec_internal_logic_seq_alias() {
    let spec = lookup_std_spec("logic::seq::Seq::push_back_ghost")
        .expect("internal logic::seq::Seq path should resolve via crate-alias normalization");
    assert!(
        spec.ensures
            .iter()
            .any(|e| e.contains("^self == self.push_back(arg1)")),
        "Seq::push_back_ghost spec should link post-state to push_back UF"
    );
}

#[test]
fn test_lookup_std_spec_non_atomic_invariant_open_paths() {
    let ghost_open = lookup_std_spec("trust_wp_std::ghost::Ghost::open")
        .expect("Ghost::open invariant spec should exist");
    assert_requires_contains(
        &ghost_open,
        "tokens.contains(self.namespace())",
        "Ghost::open invariant precondition",
    );
    assert_ensures_contains(
        &ghost_open,
        "tokens.contains(self.namespace())",
        "Ghost::open invariant postcondition",
    );
    assert_param_names(&ghost_open, &["self", "tokens", "f"], "Ghost::open");

    let invariant_open =
        lookup_std_spec("trust_wp_std::ghost::invariant::NonAtomicInvariant::open")
            .expect("NonAtomicInvariant::open spec should exist");
    assert_requires_contains(
        &invariant_open,
        "tokens.contains(self.namespace())",
        "NonAtomicInvariant::open precondition",
    );
    assert_ensures_contains(
        &invariant_open,
        "tokens.contains(self.namespace())",
        "NonAtomicInvariant::open postcondition",
    );
    assert_param_names(
        &invariant_open,
        &["self", "tokens", "f"],
        "NonAtomicInvariant::open",
    );

    let collapsed_impl_open = lookup_std_spec("trust_wp_std::ghost::invariant::open")
        .expect("collapsed impl-path alias should resolve to the invariant open spec");
    assert_requires_contains(
        &collapsed_impl_open,
        "tokens.contains(self.namespace())",
        "collapsed impl-path precondition",
    );
    assert_ensures_contains(
        &collapsed_impl_open,
        "tokens.contains(self.namespace())",
        "collapsed impl-path postcondition",
    );
}

#[test]
fn test_lookup_std_spec_non_atomic_invariant_open_aliases() {
    let creusot_open = lookup_std_spec("creusot_std::ghost::Ghost::open")
        .expect("creusot_std Ghost::open should normalize to the invariant spec");
    assert_requires_contains(
        &creusot_open,
        "tokens.contains(self.namespace())",
        "creusot_std Ghost::open precondition",
    );
    assert_ensures_contains(
        &creusot_open,
        "tokens.contains(self.namespace())",
        "creusot_std Ghost::open postcondition",
    );

    let ext_open = lookup_std_spec("creusot_std::ghost::invariant::NonAtomicInvariantExt::open")
        .expect("NonAtomicInvariantExt::open alias should resolve");
    assert_requires_contains(
        &ext_open,
        "tokens.contains(self.namespace())",
        "NonAtomicInvariantExt::open precondition",
    );
    assert_ensures_contains(
        &ext_open,
        "tokens.contains(self.namespace())",
        "NonAtomicInvariantExt::open postcondition",
    );
    assert_param_names(
        &ext_open,
        &["self", "tokens", "f"],
        "NonAtomicInvariantExt::open",
    );
}

#[test]
fn test_lookup_std_spec_atomic_invariant_open_and_tokens_contains() {
    for path in [
        "trust_wp_std::ghost::invariant::AtomicInvariant::open",
        "creusot_std::ghost::invariant::AtomicInvariant::open",
        "trust_wp_std::ghost::invariant::AtomicInvariantSC::open",
        "creusot_std::ghost::invariant::AtomicInvariantSC::open",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert_requires_contains(
            &spec,
            "tokens.contains(self.namespace())",
            "atomic invariant open precondition",
        );
        assert_ensures_contains(
            &spec,
            "tokens.contains(self.namespace())",
            "atomic invariant open postcondition",
        );
        assert_param_names(&spec, &["self", "tokens", "f"], path);
    }

    for path in [
        "trust_wp_std::ghost::invariant::Tokens::contains",
        "trust_wp_std::Tokens::contains",
        "creusot_std::ghost::invariant::Tokens::contains",
        "creusot_std::Tokens::contains",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert_ensures_contains(&spec, "result == true", "Tokens::contains postcondition");
        assert_param_names(&spec, &["self", "namespace"], path);
    }

    for path in [
        "trust_wp_std::ghost::invariant::Tokens::new",
        "trust_wp_std::Tokens::new",
        "creusot_std::ghost::invariant::Tokens::new",
        "creusot_std::Tokens::new",
        "trust_wp_std::ghost::invariant::Tokens::reborrow",
        "trust_wp_std::Tokens::reborrow",
        "creusot_std::ghost::invariant::Tokens::reborrow",
        "creusot_std::Tokens::reborrow",
    ] {
        lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
    }
}

/// Snapshot::from_fn — deferred closure capture prevents opaque across all crate paths (#2675).
#[test]
fn test_lookup_std_spec_snapshot_from_fn() {
    for path in [
        "trust_wp_std::ghost::Snapshot::<i32>::from_fn",
        "trust_wp_std::Snapshot::<i32>::from_fn",
        "trust_wp::ghost::Snapshot::<i32>::from_fn",
        "trust_wp::Snapshot::<i32>::from_fn",
        "creusot_std::ghost::Snapshot::<i32>::from_fn",
        "creusot_std::Snapshot::<i32>::from_fn",
        "creusot_contracts::ghost::Snapshot::<i32>::from_fn",
        "creusot_contracts::Snapshot::<i32>::from_fn",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("Snapshot::from_fn should exist for path: {path}"));
        assert!(spec.requires.is_empty(), "from_fn has no preconditions");
        assert!(
            spec.ensures.is_empty(),
            "from_fn is a deferred capture with no constraints for path: {path}"
        );
    }
}

/// Snapshot<T>::into_ghost — identity conversion spec across all crate paths.
#[test]
fn test_lookup_std_spec_snapshot_into_ghost() {
    for path in [
        "trust_wp_std::ghost::Snapshot::<i32>::into_ghost",
        "trust_wp_std::Snapshot::<i32>::into_ghost",
        "trust_wp::ghost::Snapshot::<i32>::into_ghost",
        "trust_wp::Snapshot::<i32>::into_ghost",
        "creusot_std::ghost::Snapshot::<i32>::into_ghost",
        "creusot_std::Snapshot::<i32>::into_ghost",
        "creusot_contracts::ghost::Snapshot::<i32>::into_ghost",
        "creusot_contracts::Snapshot::<i32>::into_ghost",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("Snapshot::into_ghost should exist for path: {path}"));
        assert!(spec.requires.is_empty(), "into_ghost has no preconditions");
        assert_eq!(
            spec.ensures,
            vec!["result == self"],
            "into_ghost is identity for path: {path}"
        );
        assert_param_names(&spec, &["self"], &format!("into_ghost({path})"));
    }
}

/// Snapshot<Seq<T>>::concat — transparent Seq concat spec.
/// Critical for iterator produces clauses where visited is Snapshot<Seq<T>>.
#[test]
fn test_lookup_std_spec_snapshot_seq_concat() {
    for path in [
        "trust_wp_std::ghost::Snapshot::<Seq<i32>>::concat",
        "trust_wp_std::Snapshot::<Seq<i32>>::concat",
        "creusot_std::Snapshot::<Seq<i32>>::concat",
        "creusot_contracts::Snapshot::<Seq<i32>>::concat",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("Snapshot::concat should exist for path: {path}"));
        assert!(spec.requires.is_empty(), "concat has no preconditions");
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result.len() == self.len() + arg1.len()")),
            "concat spec should include length postcondition for path: {path}"
        );
        assert_param_names(&spec, &["self", "arg1"], &format!("concat({path})"));
    }
}

/// Snapshot<Seq<T>>::push_back — transparent Seq push_back spec.
#[test]
fn test_lookup_std_spec_snapshot_seq_push_back() {
    for path in [
        "trust_wp_std::ghost::Snapshot::<Seq<i32>>::push_back",
        "trust_wp_std::Snapshot::<Seq<i32>>::push_back",
        "creusot_std::Snapshot::<Seq<i32>>::push_back",
        "creusot_contracts::Snapshot::<Seq<i32>>::push_back",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("Snapshot::push_back should exist for path: {path}"));
        assert!(spec.requires.is_empty(), "push_back has no preconditions");
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result.len() == self.len() + 1")),
            "push_back spec should include length postcondition for path: {path}"
        );
        assert_param_names(&spec, &["self", "arg1"], &format!("push_back({path})"));
    }
}

/// Snapshot<FMap<K,V>>::insert — transparent FMap insert spec.
#[test]
fn test_lookup_std_spec_snapshot_fmap_insert() {
    for path in [
        "trust_wp_std::ghost::Snapshot::<FMap<i32, i32>>::insert",
        "trust_wp_std::Snapshot::<FMap<i32, i32>>::insert",
        "creusot_std::Snapshot::<FMap<i32, i32>>::insert",
        "creusot_contracts::Snapshot::<FMap<i32, i32>>::insert",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("Snapshot::insert should exist for path: {path}"));
        assert!(spec.requires.is_empty(), "insert has no preconditions");
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result.contains(arg1)")),
            "insert spec should include contains postcondition for path: {path}"
        );
        assert_param_names(&spec, &["self", "arg1", "arg2"], &format!("insert({path})"));
    }
}

/// Resource::alloc — the allocated resource's view is the snapshot payload.
///
/// Spec's own law: Creusot `creusot-std/src/ghost/resource.rs`
/// `Resource::alloc`: `#[ensures(result@ == *r)]`. Unfixed (empty spec) the
/// `result@` view is completely free and `Authority::new`-style wrappers get
/// fabricated counterexamples. (ce-census 2026-08-20,
/// resource_algebras/fmap_view_view.rs `new`)
#[test]
fn test_lookup_std_spec_resource_alloc_view_law() {
    for path in [
        "trust_wp_std::ghost::resource::Resource::alloc",
        "trust_wp_std::Resource::alloc",
        "creusot_std::Resource::alloc",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("Resource::alloc should exist for path: {path}"));
        assert!(spec.requires.is_empty(), "alloc has no preconditions");
        assert_eq!(
            spec.ensures,
            vec!["result@ == *arg0"],
            "alloc must carry the Creusot view law for path: {path}"
        );
        assert_param_names(&spec, &["arg0"], &format!("alloc({path})"));
    }
}
