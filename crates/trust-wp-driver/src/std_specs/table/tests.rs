// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::lookup_std_spec;

fn assert_param_names(spec: &super::super::StdSpec, expected: &[&str], context: &str) {
    let expected_vec: Vec<String> = expected.iter().map(|s| (*s).to_string()).collect();
    assert_eq!(
        spec.param_names.as_deref(),
        Some(expected_vec.as_slice()),
        "{context} param_names mismatch"
    );
}

#[test]
fn lookup_hashmap_iter_aliases() {
    let spec = lookup_std_spec("std::collections::HashMap::iter")
        .expect("HashMap::iter should resolve to a std spec");
    assert!(
        spec.ensures.iter().any(|e| e.contains("self@ == result@")),
        "HashMap::iter spec should preserve map view"
    );
}

#[test]
fn lookup_predcell_aliases_cover_required_surface() {
    for (path, required_fragment, ensured_fragment) in [
        (
            "trust_wp_std::std::cell::PredCell::new",
            Some("_pred[value]"),
            Some("result@ == *_pred"),
        ),
        (
            "creusot_std::cell::PredCell::get",
            None,
            Some("self@[result]"),
        ),
        (
            "creusot_std::std::cell::PredCell::set",
            Some("self@[value]"),
            None,
        ),
        (
            "trust_wp_std::std::cell::PredCell::replace",
            Some("self@[value]"),
            Some("self@[result]"),
        ),
        (
            "creusot_std::cell::PredCell::from_mut",
            Some("_pred[*t]"),
            Some("result@ == *_pred"),
        ),
        (
            "creusot_std::cell::PredCell::take",
            Some("Default::default.postcondition"),
            Some("self@[result]"),
        ),
        (
            "creusot_std::cell::PredCell::as_slice_of_cells",
            None,
            Some("result[i]@ == _pred[i]"),
        ),
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        if let Some(fragment) = required_fragment {
            assert!(
                spec.requires.iter().any(|clause| clause.contains(fragment)),
                "{path} requires should contain `{fragment}`: {:?}",
                spec.requires
            );
        }
        if let Some(fragment) = ensured_fragment {
            assert!(
                spec.ensures.iter().any(|clause| clause.contains(fragment)),
                "{path} ensures should contain `{fragment}`: {:?}",
                spec.ensures
            );
        }
    }
}

#[test]
fn lookup_permcell_aliases_cover_required_surface() {
    for (path, ensured_fragment) in [
        (
            "trust_wp_std::std::cell::PermCell::new",
            "result.0@ == value",
        ),
        ("creusot_std::cell::PermCell::get", "result == self@"),
        ("creusot_std::cell::PermCell::borrow", "*result == self@"),
        (
            "creusot_std::cell::PermCell::borrow_mut",
            "^result == (^self)@",
        ),
        (
            "trust_wp_std::std::cell::PermCell::replace",
            "(^self)@ == value",
        ),
        ("creusot_std::cell::PermCell::into_inner", "result == self@"),
        (
            "creusot_std::std::cell::PermCell::from_mut",
            "result.0@ == *t",
        ),
        (
            "creusot_std::cell::PermCell::take",
            "Default::default.postcondition",
        ),
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|clause| clause.contains(ensured_fragment)),
            "{path} ensures should contain `{ensured_fragment}`: {:?}",
            spec.ensures
        );
    }
}

#[test]
fn lookup_hashmap_into_iter_ref_alias() {
    let spec =
        lookup_std_spec("<&std::collections::HashMap as core::iter::IntoIterator>::into_iter")
            .expect("&HashMap IntoIterator::into_iter should resolve to a std spec");
    assert!(
        spec.ensures.iter().any(|e| e.contains("self@ == result@")),
        "&HashMap::into_iter spec should preserve map view"
    );
    assert_param_names(&spec, &["self"], "&HashMap::into_iter");
}

#[test]
fn lookup_hashset_into_iter_ref_alias_has_self_param_name() {
    let spec =
        lookup_std_spec("<&std::collections::HashSet as core::iter::IntoIterator>::into_iter")
            .expect("&HashSet IntoIterator::into_iter should resolve to a std spec");
    assert!(
        spec.ensures.iter().any(|e| e.contains("self@ == result@")),
        "&HashSet::into_iter spec should preserve set view"
    );
    assert_param_names(&spec, &["self"], "&HashSet::into_iter");
}

#[test]
fn lookup_hashset_intersection_spec() {
    let spec = lookup_std_spec("std::collections::HashSet::intersection")
        .expect("HashSet::intersection should resolve to a std spec");
    assert!(
        spec.ensures.iter().any(|e| e.contains("intersection")),
        "HashSet::intersection spec should mention set intersection"
    );
}

#[test]
fn lookup_seq_push_back_ghost_aliases() {
    for path in &[
        "trust_wp_std::logic::Seq::push_back_ghost",
        "trust_wp_std::logic::seq::Seq::push_back_ghost",
        "trust_wp_std::Seq::push_back_ghost",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("^self == self.push_back(arg1)")),
            "{path} spec should link post-state to push_back UF"
        );
    }
}

#[test]
fn lookup_seq_len_ghost() {
    let spec = lookup_std_spec("trust_wp_std::Seq::len_ghost")
        .expect("Seq::len_ghost should resolve to a spec");
    assert!(
        spec.ensures
            .iter()
            .any(|e| e.contains("result == self.len()")),
        "Seq::len_ghost spec should equate result to self.len()"
    );
}

#[test]
fn lookup_seq_logical_methods() {
    for (path, expected_fragment) in &[
        ("trust_wp_std::Seq::empty", "result.len() == 0"),
        ("trust_wp_std::Seq::singleton", "result.len() == 1"),
        (
            "trust_wp_std::Seq::push_back",
            "result.len() == self.len() + 1",
        ),
        ("trust_wp_std::Seq::get", "match result"),
        ("trust_wp_std::Seq::pop_back_ghost", "match result"),
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        let has_fragment = spec.ensures.iter().any(|e| e.contains(expected_fragment));
        assert!(
            has_fragment,
            "{path} spec should contain '{expected_fragment}'"
        );
    }
}

#[test]
fn lookup_clone_primitive_specs() {
    for ty in &[
        "bool", "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128",
        "usize",
    ] {
        let path = format!("<{ty} as core::clone::Clone>::clone");
        let spec = lookup_std_spec(&path)
            .unwrap_or_else(|| panic!("{path} should resolve to a clone spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("result == *self")),
            "{path} clone spec should ensure result == *self"
        );
    }
}

#[test]
fn lookup_default_primitive_specs() {
    for ty in &[
        "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "usize", "isize",
    ] {
        let path = format!("<{ty} as core::default::Default>::default");
        let spec = lookup_std_spec(&path)
            .unwrap_or_else(|| panic!("{path} should resolve to a default spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("result == 0")),
            "{path} default spec should ensure result == 0"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("Default::default.postcondition")),
            "{path} default spec should also retain the generic postcondition fact"
        );
    }
    // bool default is false, not 0
    let spec = lookup_std_spec("<bool as core::default::Default>::default")
        .expect("bool default spec should exist");
    assert!(
        spec.ensures.iter().any(|e| e.contains("result == false")),
        "bool default spec should ensure result == false"
    );
    assert!(
        spec.ensures
            .iter()
            .any(|e| e.contains("Default::default.postcondition")),
        "bool default spec should also retain the generic postcondition fact"
    );
}

#[test]
fn lookup_generic_default_postcondition_specs() {
    for path in &[
        "core::default::Default::default",
        "std::default::Default::default",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert_eq!(
            spec.ensures,
            vec!["core::default::Default::default.postcondition((), result)".to_string()],
            "{path} should only contribute the generic default postcondition fact"
        );
    }
}

#[test]
fn lookup_collection_default_specs() {
    // Vec::default() should get concrete postcondition (#2256)
    for path in &[
        "<alloc::vec::Vec as core::default::Default>::default",
        "<std::vec::Vec as core::default::Default>::default",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result@.len() == 0")),
            "{path} should have concrete view-empty postcondition, got: {:?}",
            spec.ensures,
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("Default::default.postcondition")),
            "{path} should also retain the generic postcondition fact",
        );
    }
    // String::default()
    for path in &[
        "<alloc::string::String as core::default::Default>::default",
        "<std::string::String as core::default::Default>::default",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result@.len() == 0")),
            "{path} should have concrete view-empty postcondition, got: {:?}",
            spec.ensures,
        );
    }
    // Option::default()
    for path in &[
        "<core::option::Option as core::default::Default>::default",
        "<std::option::Option as core::default::Default>::default",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("result == None()")),
            "{path} should have concrete None postcondition, got: {:?}",
            spec.ensures,
        );
    }
    // HashMap::default() (#2256)
    for path in &[
        "<std::collections::HashMap as core::default::Default>::default",
        "<std::collections::hash_map::HashMap as core::default::Default>::default",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result@.len() == 0")),
            "{path} should have concrete view-empty postcondition, got: {:?}",
            spec.ensures,
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("Default::default.postcondition")),
            "{path} should also retain the generic postcondition fact",
        );
    }
    // HashSet::default() (#2256)
    for path in &[
        "<std::collections::HashSet as core::default::Default>::default",
        "<std::collections::hash_set::HashSet as core::default::Default>::default",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result@.len() == 0")),
            "{path} should have concrete view-empty postcondition, got: {:?}",
            spec.ensures,
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("Default::default.postcondition")),
            "{path} should also retain the generic postcondition fact",
        );
    }
}

#[test]
fn lookup_generic_clone_postcondition_specs() {
    for path in &["core::clone::Clone::clone", "std::clone::Clone::clone"] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert_eq!(
            spec.ensures,
            vec![
                "T::clone.postcondition((self,), result)".to_string(),
                "T::clone.postcondition((self,), result) ==> result == *self".to_string(),
            ],
            "{path} should contribute the generic clone postcondition fact and equality law"
        );
        assert_param_names(&spec, &["self"], &format!("{path} generic clone"));
    }
}

#[test]
fn lookup_generic_partial_ord_specs() {
    for (path, op) in &[
        ("core::cmp::PartialOrd::le", "<="),
        ("core::cmp::PartialOrd::ge", ">="),
        ("core::cmp::PartialOrd::lt", "<"),
        ("core::cmp::PartialOrd::gt", ">"),
        ("std::cmp::PartialOrd::le", "<="),
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains(op)),
            "{path} spec should contain operator '{op}'"
        );
    }
}

#[test]
fn lookup_generic_partial_cmp_specs() {
    for path in &[
        "core::cmp::PartialOrd::partial_cmp",
        "std::cmp::PartialOrd::partial_cmp",
        "core::cmp::PartialOrd<Self>::partial_cmp",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("Ordering::Less")),
            "{path} spec should constrain Ordering results"
        );
    }
}

#[test]
fn lookup_generic_ord_cmp_specs() {
    for path in &["core::cmp::Ord::cmp", "std::cmp::Ord::cmp"] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("Ordering::Equal")),
            "{path} spec should constrain Ordering results"
        );
    }
}

#[test]
fn lookup_generic_partial_eq_specs() {
    for path in &[
        "core::cmp::PartialEq::eq",
        "std::cmp::PartialEq::eq",
        "core::cmp::PartialEq::ne",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            !spec.ensures.is_empty(),
            "{path} spec should have at least one ensures clause"
        );
    }
}

#[test]
fn duration_partial_ord_takes_precedence_over_generic() {
    // Type-specific Duration spec should be found via UFCS path,
    // NOT the generic PartialOrd spec. Verify the Duration spec
    // exists and has the same semantic content (both use self@).
    let duration_spec = lookup_std_spec("<core::time::Duration as core::cmp::PartialOrd>::le")
        .expect("Duration-specific PartialOrd::le should exist");
    assert!(
        duration_spec.ensures.iter().any(|e| e.contains("<=")),
        "Duration PartialOrd::le spec should contain '<=' operator"
    );
}

/// Ghost wrapper specs resolve for all alias variants. (#2315)
///
/// These specs prevent `OpaqueCallTrueAssumption` demotion for ghost methods
/// used in `specification/erasure` and `resource_algebras/excl` compat tests.
#[test]
fn lookup_ghost_perm_resource_specs() {
    for path in &[
        // Ghost::split (#2671)
        "trust_wp_std::ghost::Ghost::split",
        "creusot_std::ghost::Ghost::split",
        "creusot_contracts::Ghost::split",
        // Perm::as_ref
        "trust_wp_std::ghost::perm::Perm::as_ref",
        "creusot_std::ghost::perm::Perm::as_ref",
        "creusot_std::Perm::as_ref",
        // Perm::as_mut
        "trust_wp_std::ghost::perm::Perm::as_mut",
        "creusot_std::ghost::perm::Perm::as_mut",
        "creusot_std::Perm::as_mut",
        // Perm::from_ref (#1804)
        "trust_wp_std::ghost::perm::Perm::from_ref",
        "creusot_std::ghost::perm::Perm::from_ref",
        // Perm::from_mut (#1804)
        "trust_wp_std::ghost::perm::Perm::from_mut",
        "creusot_std::ghost::perm::Perm::from_mut",
        // Perm::from_box (#1804)
        "trust_wp_std::ghost::perm::Perm::from_box",
        "creusot_std::ghost::perm::Perm::from_box",
        // Resource::val (#2316)
        "trust_wp_std::ghost::resource::Resource::val",
        "creusot_std::ghost::resource::Resource::val",
        "creusot_std::Resource::val",
        // Resource::id_ghost
        "trust_wp_std::ghost::resource::Resource::id_ghost",
        "creusot_std::ghost::resource::Resource::id_ghost",
        "creusot_std::Resource::id_ghost",
        // Resource::valid_op_lemma
        "trust_wp_std::ghost::resource::Resource::valid_op_lemma",
        "creusot_std::ghost::resource::Resource::valid_op_lemma",
        "creusot_std::Resource::valid_op_lemma",
        // Resource::join_shared (#2154)
        "trust_wp_std::ghost::resource::Resource::join_shared",
        "creusot_std::ghost::resource::Resource::join_shared",
        "creusot_std::Resource::join_shared",
        // Resource::alloc (#2316)
        "trust_wp_std::ghost::resource::Resource::alloc",
        "creusot_std::ghost::resource::Resource::alloc",
        // Resource::split (#2316)
        "trust_wp_std::ghost::resource::Resource::split",
        "creusot_std::ghost::resource::Resource::split",
        // Resource::join (#2316)
        "trust_wp_std::ghost::resource::Resource::join",
        "creusot_std::ghost::resource::Resource::join",
        // Resource::weaken (#2316)
        "trust_wp_std::ghost::resource::Resource::weaken",
        "creusot_std::ghost::resource::Resource::weaken",
        // Resource::core (#2316)
        "trust_wp_std::ghost::resource::Resource::core",
        "creusot_std::ghost::resource::Resource::core",
        // Resource::split_off (#2316)
        "trust_wp_std::ghost::resource::Resource::split_off",
        "creusot_std::ghost::resource::Resource::split_off",
        // Resource::split_mut (#2316)
        "trust_wp_std::ghost::resource::Resource::split_mut",
        "creusot_std::ghost::resource::Resource::split_mut",
        // Resource::join_in (#2316)
        "trust_wp_std::ghost::resource::Resource::join_in",
        "creusot_std::ghost::resource::Resource::join_in",
        // Resource::take (#2316)
        "trust_wp_std::ghost::resource::Resource::take",
        "creusot_std::ghost::resource::Resource::take",
        // Resource::update (#2316)
        "trust_wp_std::ghost::resource::Resource::update",
        "creusot_std::ghost::resource::Resource::update",
        // Resource::new_unit (#2316)
        "trust_wp_std::ghost::resource::Resource::new_unit",
        "creusot_std::ghost::resource::Resource::new_unit",
    ] {
        assert!(
            lookup_std_spec(path).is_some(),
            "{path} should resolve to a spec (prevents opaque demotion)"
        );
    }
}

/// ★ SOUNDNESS PIN (#quantifier-frontier). `Resource::join_shared`
/// must NOT carry a committed, RA-generic `self@ == other@` postcondition.
///
/// Creusot's contract is `requires(self.id() == other.id())`,
/// `ensures(result.id() == self.id())` and
/// `ensures(self@.incl_eq(result@) && other@.incl_eq(result@))`
/// (`reference/creusot/creusot-std/src/ghost/resource.rs`). Since
/// `incl_eq(a, b) == a.eq(b) || a.incl(b)` (`…/logic/ra.rs`), the view equality
/// is NOT entailed for any RA with non-trivial inclusion (Frac, Auth/ViewRA) —
/// committing it generically is a premise STRENGTHENING, i.e. a trusted false
/// assumption. The unrenderable `incl_eq` conjunct is WITHHELD here; the
/// Ag-only collapse is injected by the gated driver specialization
/// `ag_join_shared_ensures`, never by this table.
#[test]
fn lookup_join_shared_spec_withholds_generic_view_equality() {
    let spec = lookup_std_spec("trust_wp_std::ghost::resource::Resource::join_shared")
        .expect("join_shared should resolve");
    assert!(
        !spec.ensures.iter().any(|e| e.contains("self@ == other@")),
        "join_shared must NOT commit an RA-generic `self@ == other@` ensures \
         (unsound for RAs with non-trivial inclusion): {:?}",
        spec.ensures
    );
    assert!(
        spec.ensures
            .iter()
            .any(|e| e.contains("result.id() == self.id()")),
        "join_shared should keep Creusot's renderable id-frame ensures: {:?}",
        spec.ensures
    );
    assert!(
        spec.requires
            .iter()
            .any(|r| r.contains("self.id() == other.id()")),
        "join_shared must emit Creusot's load-bearing same-identity requires: {:?}",
        spec.requires
    );
    assert!(
        spec.param_names.is_some(),
        "join_shared should have param names for positional substitution"
    );
    let names = spec.param_names.as_ref().unwrap();
    assert!(
        names.contains(&"self".to_string()) && names.contains(&"other".to_string()),
        "join_shared param names should include self and other: {:?}",
        names
    );
}

/// Raw-pointer permission dereference specs need explicit parameter names so
/// Creusot-style named contracts do not fall back to positional substitution.
#[test]
fn lookup_perm_pointer_specs_have_param_names() {
    for path in [
        "trust_wp_std::ghost::perm::Perm::as_ref",
        "creusot_std::ghost::perm::Perm::as_ref",
        "trust_wp_std::ghost::perm::Perm::as_mut",
        "creusot_std::ghost::perm::Perm::as_mut",
    ] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        assert_eq!(
            spec.param_names.as_deref(),
            Some(&["ptr".to_string(), "own".to_string()][..]),
            "{path} should expose ptr/own parameter names"
        );
    }
}

/// Authority/Fragment method specs prevent opaque demotion (#2316).
///
/// All Authority and Fragment methods must have spec table entries
/// to prevent OpaqueCallTrueAssumption fallback. These are the
/// resource algebra wrappers used in PermCell-based ghost protocols.
#[test]
fn lookup_authority_fragment_specs() {
    let update_spec = lookup_std_spec("trust_wp_std::ghost::resource::Authority::update")
        .expect("Authority::update should resolve to a spec");
    assert!(
        update_spec
            .requires
            .iter()
            .any(|r| r == "self.id() == frag.id()"),
        "Authority::update should require matching ids: {:?}",
        update_spec.requires
    );
    assert!(
        update_spec
            .requires
            .iter()
            .any(|r| r == "upd.premise(self@, frag@)"),
        "Authority::update should require the local-update premise: {:?}",
        update_spec.requires
    );
    assert!(
        update_spec
            .ensures
            .iter()
            .any(|e| e == "(^self)@ == upd.update(self@, frag@).0")
            && update_spec
                .ensures
                .iter()
                .any(|e| e == "(^frag)@ == upd.update(self@, frag@).1"),
        "Authority::update should connect final resources to upd.update: {:?}",
        update_spec.ensures
    );

    for path in &[
        // Authority methods
        "trust_wp_std::ghost::resource::Authority::alloc",
        "creusot_std::ghost::resource::Authority::alloc",
        "creusot_std::Authority::alloc",
        "trust_wp_std::ghost::resource::Authority::from_resource",
        "creusot_std::Authority::from_resource",
        "trust_wp_std::ghost::resource::Authority::update",
        "creusot_std::Authority::update",
        "trust_wp_std::ghost::resource::Authority::add_fragment",
        "creusot_std::Authority::add_fragment",
        "trust_wp_std::ghost::resource::Authority::frag_lemma",
        "creusot_std::Authority::frag_lemma",
        "trust_wp_std::ghost::resource::Authority::id_ghost",
        "creusot_std::Authority::id_ghost",
        // Fragment methods
        "trust_wp_std::ghost::resource::Fragment::new_unit",
        "creusot_std::ghost::resource::Fragment::new_unit",
        "creusot_std::Fragment::new_unit",
        "trust_wp_std::ghost::resource::Fragment::core",
        "creusot_std::Fragment::core",
        "trust_wp_std::ghost::resource::Fragment::split",
        "creusot_std::Fragment::split",
        "trust_wp_std::ghost::resource::Fragment::split_off",
        "creusot_std::Fragment::split_off",
        "trust_wp_std::ghost::resource::Fragment::join",
        "creusot_std::Fragment::join",
        "trust_wp_std::ghost::resource::Fragment::join_in",
        "creusot_std::Fragment::join_in",
        "trust_wp_std::ghost::resource::Fragment::weaken",
        "creusot_std::Fragment::weaken",
        "trust_wp_std::ghost::resource::Fragment::valid_op_lemma",
        "creusot_std::Fragment::valid_op_lemma",
        "trust_wp_std::ghost::resource::Fragment::id_ghost",
        "creusot_std::Fragment::id_ghost",
    ] {
        assert!(
            lookup_std_spec(path).is_some(),
            "{path} should resolve to a spec (prevents opaque demotion)"
        );
    }
}

/// FromIterator::from_iter specs close the collect() roundtrip gap. (#2116)
///
/// into_iter ensures self@ == result@ (map→iter), from_iter ensures
/// the result is related to the produced sequence, giving result@ == xs@
/// for roundtrip proofs through the type-specific bridge.
#[test]
fn lookup_hashmap_from_iter_spec() {
    for path in &[
        "<std::collections::HashMap as core::iter::FromIterator>::from_iter",
        "<std::collections::hash_map::HashMap as core::iter::FromIterator>::from_iter",
        "<std::collections::HashMap as core::iter::traits::collect::FromIterator>::from_iter",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("from_iter_post")),
            "{path} from_iter spec should use from_iter_post; got {:?}",
            spec.ensures
        );
    }
}

#[test]
fn lookup_hashset_from_iter_spec() {
    for path in &[
        "<std::collections::HashSet as core::iter::FromIterator>::from_iter",
        "<std::collections::hash_set::HashSet as core::iter::FromIterator>::from_iter",
        "<std::collections::HashSet as core::iter::traits::collect::FromIterator>::from_iter",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("result@ == iter@")),
            "{path} from_iter spec should close roundtrip: result@ == iter@; got {:?}",
            spec.ensures
        );
    }
}

/// Iterator::collect resolves to the generic entry, which carries NO result
/// clause: the roundtrip is appended only by the driver's type gate
/// (`mir_analysis/extract/collect_gate.rs`) for whitelisted `(Self, B)` pairs.
///
/// Post-borrowck MIR does NOT inline collect() to FromIterator::from_iter,
/// so the trait default method path is what appears at call sites.
#[test]
fn lookup_iterator_collect_spec() {
    for path in &[
        "core::iter::traits::iterator::Iterator::collect",
        "std::iter::traits::iterator::Iterator::collect",
        "std::iter::Iterator::collect",
        "core::iter::Iterator::collect",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.is_empty(),
            "{path} ungated collect spec must state nothing about the result; got {:?}",
            spec.ensures
        );
    }
}

/// Vec FromIterator::from_iter spec uses from_iter_post constraint. (#2217)
///
/// Direct from_iter calls get the richer FromIteratorSpec relation
/// instead of the simple roundtrip spec.
#[test]
fn lookup_vec_from_iter_spec() {
    for path in &[
        "<alloc::vec::Vec as core::iter::FromIterator>::from_iter",
        "<std::vec::Vec as core::iter::FromIterator>::from_iter",
        "<alloc::vec::Vec as core::iter::traits::collect::FromIterator>::from_iter",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("from_iter_post")),
            "{path} from_iter spec should use from_iter_post; got {:?}",
            spec.ensures
        );
    }
}

#[test]
fn lookup_vec_from_elem_spec_preserves_repeated_element() {
    for path in &["alloc::vec::from_elem", "std::vec::from_elem"] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result@.len() == count@")),
            "{path} from_elem spec should preserve length; got {:?}",
            spec.ensures
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result@.index_logic(i) == elem")),
            "{path} from_elem spec should expose repeated elements; got {:?}",
            spec.ensures
        );
        assert_param_names(&spec, &["elem", "count"], &format!("{path} from_elem"));
    }
}

/// Iterator::rev spec wraps the inner iterator. (#2217)
#[test]
fn lookup_iterator_rev_spec() {
    for path in &[
        "core::iter::traits::iterator::Iterator::rev",
        "std::iter::traits::iterator::Iterator::rev",
        "std::iter::Iterator::rev",
        "core::iter::Iterator::rev",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("result.iter()")),
            "{path} rev spec should reference result.iter(); got {:?}",
            spec.ensures
        );
    }
}

/// DoubleEndedIterator::next_back spec uses produces_back. (#2217)
#[test]
fn lookup_double_ended_next_back_spec() {
    for path in &[
        "core::iter::traits::double_ended::DoubleEndedIterator::next_back",
        "std::iter::DoubleEndedIterator::next_back",
        "core::iter::DoubleEndedIterator::next_back",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("produces_back")),
            "{path} next_back spec should reference produces_back; got {:?}",
            spec.ensures
        );
    }
}

/// Zero-arg logical constructors expose explicit empty parameter metadata. (#2569)
///
/// `params:` (empty) in the spec string produces `param_names: Some(vec![])`,
/// which suppresses the "no parameter names" warning in resolve_arg_names_or_warn.
#[test]
fn lookup_zero_arg_logical_constructors_have_empty_param_metadata() {
    for path in &[
        "creusot_std::FMap::new",
        "trust_wp_std::FMap::new",
        "creusot_std::FSet::new",
        "trust_wp_std::FSet::new",
        "trust_wp_std::Seq::new",
        "trust_wp_std::logic::Seq::new",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert_eq!(
            spec.param_names,
            Some(vec![]),
            "{path} should have explicit empty param_names (Some(vec![])), not None"
        );
    }
}

/// Guardrail: verify no alias path appears in more than one spec table.
///
/// Duplicate aliases would cause first-match precedence to silently shadow
/// a spec, depending on table iteration order.
#[test]
fn no_duplicate_aliases_across_tables() {
    use std::collections::HashSet;
    let mut seen = HashSet::new();
    for table in super::STD_SPEC_TABLES {
        for (paths, _spec) in *table {
            for path in *paths {
                assert!(
                    seen.insert(*path),
                    "duplicate alias found across spec tables: {path}"
                );
            }
        }
    }
}

// ── #2524: canonical and alias paths resolve through the shared registry ──

/// Verify mem_clone_default canonical AND alias paths resolve through
/// the imported shared registry. (#2524)
#[test]
fn migrated_mem_clone_default_canonical_and_alias_paths_resolve() {
    // mem::replace — canonical and alias
    let spec =
        lookup_std_spec("core::mem::replace").expect("canonical core::mem::replace should resolve");
    assert!(spec
        .ensures
        .iter()
        .any(|e| e.contains("result == old(*dest)")));
    let spec =
        lookup_std_spec("std::mem::replace").expect("alias std::mem::replace should resolve");
    assert!(spec
        .ensures
        .iter()
        .any(|e| e.contains("result == old(*dest)")));

    // Clone — canonical, std alias, and shorthand
    let spec = lookup_std_spec("<u32 as core::clone::Clone>::clone")
        .expect("canonical u32 clone should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("result == *self")));
    let spec = lookup_std_spec("<u32 as std::clone::Clone>::clone")
        .expect("std alias u32 clone should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("result == *self")));
    let spec = lookup_std_spec("u32::clone").expect("shorthand u32::clone should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("result == *self")));

    // Default — canonical, std alias, and shorthand
    let spec = lookup_std_spec("<i64 as core::default::Default>::default")
        .expect("canonical i64 default should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("result == 0")));
    let spec = lookup_std_spec("<i64 as std::default::Default>::default")
        .expect("std alias i64 default should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("result == 0")));
    let spec = lookup_std_spec("i64::default").expect("shorthand i64::default should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("result == 0")));
}

/// Verify ptr_slice canonical AND alias paths resolve through
/// the imported shared registry. (#2524)
#[test]
fn migrated_ptr_slice_canonical_and_alias_paths_resolve() {
    // Slice len — canonical and aliases
    let spec = lookup_std_spec("core::slice::<impl [T]>::len")
        .expect("canonical slice len should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("self@.len()")));
    let spec = lookup_std_spec("[T]::len").expect("alias [T]::len should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("self@.len()")));

    // Slice index — canonical, impl, and trait-qualified paths
    let spec =
        lookup_std_spec("core::slice::<impl [T]>::index").expect("impl slice index should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("ix")));
    let spec = lookup_std_spec("<[T] as core::ops::Index>::index")
        .expect("trait-qualified slice index should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("ix")));
    let spec = lookup_std_spec("<[T] as std::ops::Index>::index")
        .expect("std trait-qualified slice index should resolve");
    assert!(spec.ensures.iter().any(|e| e.contains("ix")));

    // Raw pointer is_null — alias paths that survive normalize_path.
    // The long-form `core::ptr::const_ptr::<impl *const T>::is_null` paths
    // normalize to `core::ptr::const_ptr::is_null` (generics stripped), which
    // doesn't match the table's raw entry. The short-form UFCS aliases are
    // what MIR paths actually resolve through.
    for path in &["<*const T>::is_null", "<*mut T>::is_null"] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("is_null_logic")),
            "{path} spec should contain is_null_logic"
        );
    }
}

/// Verify i128 and u128 Default entries are present after migration. (#2524)
///
/// These were missing from the driver's local table but present in the
/// builtin extern registry. The shared manifest includes them.
#[test]
fn migrated_default_includes_i128_u128() {
    for ty in &["i128", "u128"] {
        let canonical = format!("<{ty} as core::default::Default>::default");
        let spec = lookup_std_spec(&canonical)
            .unwrap_or_else(|| panic!("{canonical} should resolve after migration"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("result == 0")),
            "{canonical} default spec should ensure result == 0"
        );
        // std alias
        let std_alias = format!("<{ty} as std::default::Default>::default");
        let spec = lookup_std_spec(&std_alias)
            .unwrap_or_else(|| panic!("{std_alias} should resolve after migration"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("result == 0")),
            "{std_alias} default spec should ensure result == 0"
        );
        // shorthand
        let shorthand = format!("{ty}::default");
        let spec = lookup_std_spec(&shorthand)
            .unwrap_or_else(|| panic!("{shorthand} should resolve after migration"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("result == 0")),
            "{shorthand} default spec should ensure result == 0"
        );
    }
}

/// Verify that shared registry entries are type-compatible with the driver's
/// `SpecEntry` format and that their content is present in `STD_SPEC_TABLES`. (#2524)
#[test]
fn shared_registry_slices_are_directly_usable_as_spec_entries() {
    use trust_wp_std::std::lookup_registry;

    // Verify the slices are the same type as other tables in STD_SPEC_TABLES.
    let _: &[super::super::SpecEntry] = lookup_registry::MEM_CLONE_DEFAULT;
    let _: &[super::super::SpecEntry] = lookup_registry::PTR_SLICE;

    // Verify that every canonical path from the shared registries appears
    // in STD_SPEC_TABLES. This confirms the driver imports the shared data.
    let all_table_paths: std::collections::HashSet<&str> = super::STD_SPEC_TABLES
        .iter()
        .flat_map(|table| table.iter())
        .flat_map(|(paths, _)| paths.iter().copied())
        .collect();

    for (paths, _) in lookup_registry::MEM_CLONE_DEFAULT {
        assert!(
            all_table_paths.contains(paths[0]),
            "MEM_CLONE_DEFAULT canonical path {} should be in STD_SPEC_TABLES",
            paths[0]
        );
    }
    for (paths, _) in lookup_registry::PTR_SLICE {
        assert!(
            all_table_paths.contains(paths[0]),
            "PTR_SLICE canonical path {} should be in STD_SPEC_TABLES",
            paths[0]
        );
    }
}

/// All std spec string clauses must be parseable by the contract parser. (#1612)
///
/// Iterates every entry in `STD_SPEC_TABLES`, extracts requires/ensures clauses
/// via `StdSpec::from_spec_string`, and runs `parse_contract` on each. A parse
/// failure means the spec clause uses syntax the contract parser does not support,
/// which causes silent spec drops at verification time.
#[test]
fn all_std_spec_clauses_are_parseable() {
    use trust_wp_core::contract_parser::parse_contract;

    let mut failures = Vec::new();
    for table in super::STD_SPEC_TABLES {
        for (paths, spec_str) in *table {
            let spec = super::super::StdSpec::from_spec_string(spec_str);
            for (idx, clause) in spec.ensures.iter().enumerate() {
                if let Err(e) = parse_contract(clause) {
                    failures.push(format!(
                        "ensures[{idx}] of {:?} failed to parse: {e}\n  clause: {clause}",
                        paths
                    ));
                }
            }
            for (idx, clause) in spec.requires.iter().enumerate() {
                if let Err(e) = parse_contract(clause) {
                    failures.push(format!(
                        "requires[{idx}] of {:?} failed to parse: {e}\n  clause: {clause}",
                        paths
                    ));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "Unparseable spec clauses found (#1612):\n{}",
        failures.join("\n\n")
    );
}

/// Verify UFCS Deref/DerefMut paths for Arc, Rc, Vec, and String resolve
/// to the generic Deref/DerefMut specs. (#2689)
///
/// MIR auto-deref can produce UFCS paths like
/// `<alloc::sync::Arc as core::ops::Deref>::deref` instead of the plain
/// `core::ops::Deref::deref`. Without explicit UFCS entries, these fall
/// through to opaque treatment (OpaqueCallTrueAssumption).
#[test]
fn ufcs_deref_paths_resolve_for_smart_pointers() {
    // Arc Deref
    for path in &[
        "<alloc::sync::Arc as core::ops::Deref>::deref",
        "<std::sync::Arc as core::ops::Deref>::deref",
        "<alloc::sync::Arc as core::ops::deref::Deref>::deref",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should resolve to generic Deref spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("deref.postcondition")),
            "{path} should contain deref.postcondition"
        );
    }

    // Rc Deref
    for path in &[
        "<alloc::rc::Rc as core::ops::Deref>::deref",
        "<std::rc::Rc as core::ops::Deref>::deref",
        "<alloc::rc::Rc as core::ops::deref::Deref>::deref",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should resolve to generic Deref spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("deref.postcondition")),
            "{path} should contain deref.postcondition"
        );
    }

    // Vec Deref (Vec<T> -> &[T])
    for path in &[
        "<alloc::vec::Vec as core::ops::Deref>::deref",
        "<std::vec::Vec as core::ops::Deref>::deref",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should resolve to generic Deref spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("deref.postcondition")),
            "{path} should contain deref.postcondition"
        );
    }

    // String Deref (String -> &str)
    for path in &[
        "<alloc::string::String as core::ops::Deref>::deref",
        "<std::string::String as core::ops::Deref>::deref",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should resolve to generic Deref spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("deref.postcondition")),
            "{path} should contain deref.postcondition"
        );
    }
}

/// Verify UFCS DerefMut paths for Vec resolve to the generic DerefMut spec. (#2689)
#[test]
fn ufcs_deref_mut_paths_resolve_for_vec() {
    for path in &[
        "<alloc::vec::Vec as core::ops::DerefMut>::deref_mut",
        "<std::vec::Vec as core::ops::DerefMut>::deref_mut",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should resolve to generic DerefMut spec"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("deref_mut.postcondition")),
            "{path} should contain deref_mut.postcondition"
        );
    }
}

// ── NonZero type specs (#2669) ─────────────────────────────────────

/// Verify NonZero::new resolves for all 12 concrete types plus the generic form.
#[test]
fn lookup_nonzero_new_all_types() {
    let paths = [
        // Generic (Rust 1.79+)
        "core::num::NonZero::new",
        "std::num::NonZero::new",
        // Unsigned legacy
        "core::num::NonZeroU8::new",
        "core::num::NonZeroU16::new",
        "core::num::NonZeroU32::new",
        "core::num::NonZeroU64::new",
        "core::num::NonZeroU128::new",
        "core::num::NonZeroUsize::new",
        // Signed legacy
        "core::num::NonZeroI8::new",
        "core::num::NonZeroI16::new",
        "core::num::NonZeroI32::new",
        "core::num::NonZeroI64::new",
        "core::num::NonZeroI128::new",
        "core::num::NonZeroIsize::new",
        // std re-exports
        "std::num::NonZeroU32::new",
        "std::num::NonZeroI64::new",
    ];
    for path in &paths {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert_eq!(
            spec.ensures.len(),
            3,
            "{path} NonZero::new should have 3 ensures clauses, got: {:?}",
            spec.ensures
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result.is_some()")),
            "{path} should have is_some() clause"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result.is_none()")),
            "{path} should have is_none() clause"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result.unwrap()@ == value@")),
            "{path} should have unwrap equality clause"
        );
    }
}

/// Verify NonZero::get resolves and has the non-zero guarantee.
#[test]
fn lookup_nonzero_get_all_types() {
    let paths = [
        "core::num::NonZero::get",
        "core::num::NonZeroU32::get",
        "core::num::NonZeroI64::get",
        "std::num::NonZeroUsize::get",
        "std::num::NonZeroI128::get",
    ];
    for path in &paths {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert_eq!(
            spec.ensures.len(),
            2,
            "{path} NonZero::get should have 2 ensures clauses, got: {:?}",
            spec.ensures
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result@ == self@")),
            "{path} should have identity clause"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result@ != 0")),
            "{path} should have non-zero guarantee"
        );
    }
}

/// Verify NonZero::new_unchecked resolves with precondition.
#[test]
fn lookup_nonzero_new_unchecked() {
    let paths = [
        "core::num::NonZero::new_unchecked",
        "core::num::NonZeroU32::new_unchecked",
        "std::num::NonZeroI64::new_unchecked",
    ];
    for path in &paths {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve to a spec"));
        assert_eq!(
            spec.requires.len(),
            1,
            "{path} new_unchecked should have 1 requires clause"
        );
        assert!(
            spec.requires.iter().any(|e| e.contains("value@ != 0")),
            "{path} should require non-zero value"
        );
        assert_eq!(
            spec.ensures.len(),
            1,
            "{path} new_unchecked should have 1 ensures clause"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result@ == value@")),
            "{path} should ensure identity"
        );
    }
}

/// Verify NonZero::new with turbofish generics resolves (path normalization).
#[test]
fn lookup_nonzero_new_with_generics_normalized() {
    // `core::num::NonZero::<u32>::new` normalizes to `core::num::NonZero::new`
    let spec = lookup_std_spec("core::num::NonZero::<u32>::new")
        .expect("turbofish NonZero::new should resolve after path normalization");
    assert_eq!(
        spec.ensures.len(),
        3,
        "NonZero::new should have 3 ensures clauses"
    );
}

// ── Spec table completeness audit (#2689) ─────────────────────────────

/// Audit: verify the spec table has a minimum number of entries.
///
/// Entry count regression guard — consolidated with
/// `spec_table_entry_count_is_sufficient` (below) which checks both
/// entry count and alias count with tighter thresholds.
#[test]
fn audit_spec_table_entry_count_regression_guard() {
    let total: usize = super::STD_SPEC_TABLES.iter().map(|table| table.len()).sum();
    // The floor sits below the table's real size so ordinary churn never trips
    // it; a drop past it means a sub-table was emptied or removed.
    assert!(
        total >= 700,
        "Spec table entry count regressed: {total} < 700 (expected 700+). \
         Check if a table was accidentally emptied or removed."
    );
}

/// Audit: every path alias in a spec entry should resolve via lookup.
///
/// Each spec entry has multiple path aliases (e.g., `core::option::Option::unwrap`
/// and `std::option::Option::unwrap`). This test verifies that looking up ANY
/// alias succeeds, catching dead entries where normalize_path strips parts of
/// the path that prevent matching (e.g., `<impl *const T>` generics). (#2689)
///
/// Note: we only check that lookup succeeds (not that the spec contents match
/// exactly) because `lookup_std_spec` applies `resolve_self_type_constants_in_spec`
/// which replaces `Self::MIN`/`Self::MAX` with concrete type constants,
/// making direct comparison with the raw spec string misleading.
#[test]
fn audit_all_path_aliases_are_reachable() {
    let mut unreachable = Vec::new();
    for table in super::STD_SPEC_TABLES {
        for (paths, _spec_str) in *table {
            for path in *paths {
                if lookup_std_spec(path).is_none() {
                    unreachable.push(format!("  {path}"));
                }
            }
        }
    }
    assert!(
        unreachable.is_empty(),
        "Unreachable spec table entries found (#2689) — these paths fail \
         normalize_path and can never match:\n{}",
        unreachable.join("\n")
    );
}

/// Audit: creusot_std:: and creusot_contracts:: paths normalize correctly.
///
/// Verifies that `normalize_crate_aliases` correctly rewrites creusot
/// paths to trust_wp_std:: paths for lookup. These are the primary alias
/// patterns that the compat tests exercise. (#2689)
#[test]
fn audit_creusot_alias_normalization_coverage() {
    let test_cases = [
        // Basic creusot_std:: → trust_wp_std::
        (
            "creusot_std::logic::seq::Seq::push_back_ghost",
            "trust_wp_std::logic::seq::Seq::push_back_ghost",
        ),
        // creusot_contracts:: → trust_wp_std::
        (
            "creusot_contracts::logic::fmap::FMap::get",
            "trust_wp_std::logic::fmap::FMap::get",
        ),
        // UFCS paths with creusot_std in trait position
        (
            "<creusot_std::ghost::Ghost as creusot_std::Resolve>::resolve",
            "<trust_wp_std::ghost::Ghost as trust_wp_std::Resolve>::resolve",
        ),
        // trust_wp:: facade → trust_wp_std::
        (
            "trust_wp::logic::seq::Seq::len",
            "trust_wp_std::logic::seq::Seq::len",
        ),
        // std::cmp:: → core::cmp::
        ("std::cmp::PartialEq::eq", "core::cmp::PartialEq::eq"),
        // std::ops:: → core::ops::
        ("std::ops::Add::add", "core::ops::Add::add"),
        // Multiple replacements in one path
        (
            "<creusot_std::Vec as std::ops::Index>::index",
            "<trust_wp_std::Vec as core::ops::Index>::index",
        ),
    ];

    for (input, expected) in &test_cases {
        let result = super::super::normalize_crate_aliases(input);
        assert_eq!(
            &result, expected,
            "normalize_crate_aliases({input:?}) = {result:?}, expected {expected:?}"
        );
    }
}

// ══════════════════════════════════════════════════════════════════
// #2689 — Spec table completeness audit tests
// ══════════════════════════════════════════════════════════════════

/// Verify that all creusot_std/creusot_contracts alias prefixes
/// normalize correctly through `normalize_path` to `trust_wp_std::`.
/// This is the core path aliasing mechanism that makes spec lookup
/// work for Creusot compat tests. (#2689)
#[test]
fn path_normalization_resolves_all_crate_aliases() {
    let test_cases = [
        // creusot_std -> trust_wp_std
        (
            "creusot_std::logic::Seq::len",
            "trust_wp_std::logic::Seq::len",
        ),
        (
            "creusot_std::logic::fmap::FMap::insert",
            "trust_wp_std::logic::fmap::FMap::insert",
        ),
        (
            "creusot_std::logic::fset::FSet::contains",
            "trust_wp_std::logic::fset::FSet::contains",
        ),
        (
            "creusot_std::ghost::Ghost::new",
            "trust_wp_std::ghost::Ghost::new",
        ),
        // creusot_contracts -> trust_wp_std
        (
            "creusot_contracts::logic::Mapping::get",
            "trust_wp_std::logic::Mapping::get",
        ),
        (
            "creusot_contracts::Ghost::new",
            "trust_wp_std::ghost::Ghost::new",
        ),
        // trust_wp:: -> trust_wp_std::
        (
            "trust_wp::ghost::Snapshot::capture",
            "trust_wp_std::ghost::Snapshot::capture",
        ),
        // std::ops -> core::ops
        ("std::ops::Add::add", "core::ops::Add::add"),
        ("std::cmp::PartialOrd::le", "core::cmp::PartialOrd::le"),
    ];
    for (input, expected) in &test_cases {
        let normalized = super::super::normalize_path(input);
        assert_eq!(
            &normalized, expected,
            "normalize_path({input}) should produce {expected}, got {normalized}"
        );
    }
}

/// Audit: no duplicate path entries across tables.
///
/// Duplicate paths cause silent first-match shadowing where one spec is
/// unreachable. Detects cross-table path collisions. (#2689)
#[test]
fn audit_no_duplicate_paths_across_tables() {
    let mut seen: std::collections::HashMap<&str, usize> = std::collections::HashMap::new();
    let mut duplicates = Vec::new();

    for (table_idx, table) in super::STD_SPEC_TABLES.iter().enumerate() {
        for (paths, _) in *table {
            for path in *paths {
                if let Some(prev_table) = seen.insert(path, table_idx) {
                    if prev_table != table_idx {
                        duplicates.push(format!(
                            "  {path}: appears in table {prev_table} AND table {table_idx}"
                        ));
                    }
                }
            }
        }
    }
    assert!(
        duplicates.is_empty(),
        "Duplicate paths across spec tables (first-match shadowing risk):\n{}",
        duplicates.join("\n")
    );
}

/// Verify that every logical type method (Seq, FMap, FSet) resolves
/// through ALL known alias prefixes. This catches missing path aliases
/// that cause OpaqueCallTrueAssumption in compat tests. (#2689)
#[test]
fn logical_type_specs_resolve_through_all_alias_prefixes() {
    // For each logical type method, verify it resolves through every
    // alias prefix that can appear in compat tests.
    let seq_methods = [
        "len",
        "is_empty",
        "push_back",
        "push_front",
        "get",
        "pop_back",
        "tail",
        "concat",
        "set",
        "contains",
        "reverse",
        "ext_eq",
        "into_inner",
        "empty",
        "singleton",
        "subsequence",
        "len_ghost",
        "is_empty_ghost",
        "push_back_ghost",
        "push_front_ghost",
        "get_ghost",
        "get_mut_ghost",
        "pop_back_ghost",
        "pop_front_ghost",
        "index_logic",
        "to_owned_seq",
        "sorted",
        "sorted_range",
        "permutation_of",
        "count",
        "exchange",
    ];
    for method in &seq_methods {
        // Canonical trust_wp_std path
        let canonical = format!("trust_wp_std::logic::seq::Seq::{method}");
        assert!(
            lookup_std_spec(&canonical).is_some(),
            "Seq::{method} canonical path should resolve: {canonical}"
        );
        // creusot_std alias (resolves via normalization)
        let creusot = format!("creusot_std::logic::Seq::{method}");
        assert!(
            lookup_std_spec(&creusot).is_some(),
            "Seq::{method} creusot_std alias should resolve: {creusot}"
        );
        // Prelude shorthand
        let shorthand = format!("trust_wp_std::Seq::{method}");
        assert!(
            lookup_std_spec(&shorthand).is_some(),
            "Seq::{method} prelude shorthand should resolve: {shorthand}"
        );
    }

    let fmap_methods = [
        "empty",
        "insert",
        "get",
        "lookup",
        "contains",
        "len",
        "remove",
        "singleton",
        "ext_eq",
        "disjoint",
        "subset",
        "union",
        "merge",
        "is_empty",
        "into_inner",
        "insert_ghost",
        "remove_ghost",
        "get_ghost",
        "get_mut_ghost",
        "contains_ghost",
        "len_ghost",
        "is_empty_ghost",
        "split_mut_ghost",
        "incl",
        "unit",
    ];
    for method in &fmap_methods {
        let canonical = format!("trust_wp_std::logic::fmap::FMap::{method}");
        assert!(
            lookup_std_spec(&canonical).is_some(),
            "FMap::{method} canonical path should resolve: {canonical}"
        );
        let creusot = format!("creusot_std::logic::FMap::{method}");
        assert!(
            lookup_std_spec(&creusot).is_some(),
            "FMap::{method} creusot_std alias should resolve: {creusot}"
        );
    }

    let fset_methods = [
        "empty",
        "insert",
        "remove",
        "contains",
        "len",
        "peek",
        "is_empty",
        "singleton",
        "union",
        "intersection",
        "difference",
        "is_subset",
        "is_superset",
        "disjoint",
        "ext_eq",
        "insert_ghost",
        "remove_ghost",
        "contains_ghost",
        "len_ghost",
        "is_empty_ghost",
        "into_inner",
    ];
    for method in &fset_methods {
        let canonical = format!("trust_wp_std::logic::fset::FSet::{method}");
        assert!(
            lookup_std_spec(&canonical).is_some(),
            "FSet::{method} canonical path should resolve: {canonical}"
        );
        let creusot = format!("creusot_std::logic::FSet::{method}");
        assert!(
            lookup_std_spec(&creusot).is_some(),
            "FSet::{method} creusot_std alias should resolve: {creusot}"
        );
    }
}

/// Verify that Mapping specs resolve through creusot_contracts AND
/// creusot_std alias prefixes (both normalize to trust_wp_std). (#2689)
#[test]
fn mapping_specs_resolve_through_both_alias_prefixes() {
    let methods = ["get", "set", "cst", "ext_eq", "index"];
    for method in &methods {
        // creusot_contracts path (original Creusot)
        let contracts = format!("creusot_contracts::Mapping::{method}");
        assert!(
            lookup_std_spec(&contracts).is_some(),
            "Mapping::{method} should resolve through creusot_contracts: {contracts}"
        );
        // creusot_std path (also valid)
        let creusot_std = format!("creusot_std::logic::Mapping::{method}");
        assert!(
            lookup_std_spec(&creusot_std).is_some(),
            "Mapping::{method} should resolve through creusot_std: {creusot_std}"
        );
    }
}

/// Verify Hash trait specs exist for all required paths. (#2689)
///
/// Hash is called implicitly during HashMap/HashSet operations.
/// Missing Hash specs cause verification failures in any code that
/// uses hash-based collections.
#[test]
fn hash_trait_completeness() {
    let hash_paths = [
        // Hash::hash
        ("core::hash::Hash::hash", true),
        ("std::hash::Hash::hash", true),
        // Hash::hash_slice
        ("core::hash::Hash::hash_slice", true),
        ("std::hash::Hash::hash_slice", true),
        // Hasher methods
        ("core::hash::Hasher::finish", true),
        ("std::hash::Hasher::finish", true),
        ("core::hash::Hasher::write", true),
        ("std::hash::Hasher::write", true),
        ("core::hash::Hasher::write_u8", true),
        ("core::hash::Hasher::write_u16", true),
        ("core::hash::Hasher::write_u32", true),
        ("core::hash::Hasher::write_u64", true),
        ("core::hash::Hasher::write_usize", true),
        ("core::hash::Hasher::write_i8", true),
        ("core::hash::Hasher::write_i16", true),
        ("core::hash::Hasher::write_i32", true),
        ("core::hash::Hasher::write_i64", true),
        ("core::hash::Hasher::write_isize", true),
        // BuildHasher
        ("core::hash::BuildHasher::build_hasher", true),
        ("std::hash::BuildHasher::build_hasher", true),
    ];
    for (path, should_exist) in &hash_paths {
        let result = lookup_std_spec(path);
        if *should_exist {
            assert!(result.is_some(), "Hash trait spec missing: {path}");
        }
    }
}

/// Verify persistent data structure specs (BTreeMap, BTreeSet). (#2689)
///
/// BTreeMap/BTreeSet must have both std:: and alloc:: path aliases
/// since MIR can resolve to either depending on the import path.
#[test]
fn btree_completeness() {
    let btreemap_methods = [
        "new",
        "len",
        "is_empty",
        "insert",
        "remove",
        "get",
        "get_mut",
        "contains_key",
        "clear",
        "iter",
        "keys",
        "values",
        "iter_mut",
        "retain",
        "entry",
        "into_keys",
        "into_values",
        "values_mut",
    ];
    for method in &btreemap_methods {
        // std::collections path
        let std_path = format!("std::collections::BTreeMap::{method}");
        assert!(
            lookup_std_spec(&std_path).is_some(),
            "BTreeMap::{method} std path should resolve: {std_path}"
        );
        // alloc::collections path
        let alloc_path = format!("alloc::collections::btree_map::BTreeMap::{method}");
        assert!(
            lookup_std_spec(&alloc_path).is_some(),
            "BTreeMap::{method} alloc path should resolve: {alloc_path}"
        );
    }

    let btreeset_methods = [
        "new",
        "len",
        "is_empty",
        "insert",
        "remove",
        "contains",
        "clear",
        "iter",
        "retain",
        "intersection",
        "difference",
        "union",
        "is_subset",
        "is_superset",
        "is_disjoint",
    ];
    for method in &btreeset_methods {
        let std_path = format!("std::collections::BTreeSet::{method}");
        assert!(
            lookup_std_spec(&std_path).is_some(),
            "BTreeSet::{method} std path should resolve: {std_path}"
        );
        let alloc_path = format!("alloc::collections::btree_set::BTreeSet::{method}");
        assert!(
            lookup_std_spec(&alloc_path).is_some(),
            "BTreeSet::{method} alloc path should resolve: {alloc_path}"
        );
    }
}

/// Verify Iterator trait method specs are complete. (#2689)
///
/// Each Iterator adapter/terminal method must resolve so that
/// for-loop and iterator chain verification doesn't fall through
/// to OpaqueCallTrueAssumption.
#[test]
fn iterator_trait_completeness() {
    let core_iter_methods = [
        "next",
        "fuse",
        "cloned",
        "copied",
        "skip",
        "take",
        "enumerate",
        "zip",
        "map",
        "filter",
        "filter_map",
        "collect",
        "rev",
        "sum",
        "count",
        "for_each",
        "fold",
        "any",
        "all",
        "find",
        "position",
        "chain",
        "peekable",
        "flat_map",
        "inspect",
        "step_by",
        "take_while",
        "skip_while",
        "min",
        "max",
        "last",
        "nth",
        "flatten",
        "unzip",
        "min_by",
        "max_by",
        "min_by_key",
        "max_by_key",
        "product",
        "find_map",
        "reduce",
        "map_while",
        "scan",
        "try_fold",
        "try_for_each",
        "is_sorted",
        "partition",
        "eq",
        "size_hint",
        "by_ref",
        "cmp",
        "partial_cmp",
        "ne",
        "lt",
        "le",
        "gt",
        "ge",
    ];
    for method in &core_iter_methods {
        let path = format!("core::iter::traits::iterator::Iterator::{method}");
        assert!(
            lookup_std_spec(&path).is_some(),
            "Iterator::{method} core path should resolve: {path}"
        );
        let std_path = format!("std::iter::traits::iterator::Iterator::{method}");
        assert!(
            lookup_std_spec(&std_path).is_some(),
            "Iterator::{method} std path should resolve: {std_path}"
        );
    }
}

/// Plain Iterator aliases also appear at call sites for adapter builders. (#2689)
#[test]
fn iterator_plain_alias_completeness() {
    for path in &[
        "core::iter::Iterator::copied",
        "std::iter::Iterator::copied",
        "core::iter::Iterator::filter",
        "std::iter::Iterator::filter",
        "core::iter::Iterator::filter_map",
        "std::iter::Iterator::filter_map",
    ] {
        assert!(
            lookup_std_spec(path).is_some(),
            "plain Iterator alias should resolve: {path}"
        );
    }
}

/// Verify generic Index/IndexMut trait fallback specs exist. (#2689)
///
/// Without these, any type implementing Index/IndexMut that isn't
/// explicitly listed (Vec, HashMap, slice) falls through to opaque.
#[test]
fn index_trait_fallback_completeness() {
    // Generic Index::index fallback
    for path in &[
        "core::ops::Index::index",
        "core::ops::index::Index::index",
        "std::ops::Index::index",
        "std::ops::index::Index::index",
    ] {
        assert!(
            lookup_std_spec(path).is_some(),
            "Generic Index::index fallback should resolve: {path}"
        );
    }
    // Generic IndexMut::index_mut fallback
    for path in &[
        "core::ops::IndexMut::index_mut",
        "core::ops::index::IndexMut::index_mut",
        "std::ops::IndexMut::index_mut",
        "std::ops::index::IndexMut::index_mut",
    ] {
        assert!(
            lookup_std_spec(path).is_some(),
            "Generic IndexMut::index_mut fallback should resolve: {path}"
        );
    }
}

/// Verify arithmetic operator trait fallback specs exist. (#2689)
///
/// These prevent opaque classification for any type implementing
/// arithmetic operators (Add, Sub, Mul, etc.).
#[test]
fn arithmetic_operator_trait_completeness() {
    let operators = [
        ("core::ops::Add::add", "Add"),
        ("core::ops::Sub::sub", "Sub"),
        ("core::ops::Mul::mul", "Mul"),
        ("core::ops::Rem::rem", "Rem"),
        ("core::ops::Neg::neg", "Neg"),
        ("core::ops::BitAnd::bitand", "BitAnd"),
        ("core::ops::BitOr::bitor", "BitOr"),
        ("core::ops::BitXor::bitxor", "BitXor"),
        ("core::ops::Not::not", "Not"),
        ("core::ops::Shl::shl", "Shl"),
        ("core::ops::Shr::shr", "Shr"),
    ];
    for (path, name) in &operators {
        assert!(
            lookup_std_spec(path).is_some(),
            "{name} operator trait fallback should resolve: {path}"
        );
    }
}

/// Verify assignment operator trait fallback specs exist. (#2689)
///
/// Covers AddAssign through ShrAssign — all must resolve to prevent
/// opaque classification for `+=`, `-=`, etc.
#[test]
fn assignment_operator_trait_completeness() {
    let operators = [
        "core::ops::AddAssign::add_assign",
        "core::ops::SubAssign::sub_assign",
        "core::ops::MulAssign::mul_assign",
        "core::ops::DivAssign::div_assign",
        "core::ops::RemAssign::rem_assign",
        "core::ops::BitAndAssign::bitand_assign",
        "core::ops::BitOrAssign::bitor_assign",
        "core::ops::BitXorAssign::bitxor_assign",
        "core::ops::ShlAssign::shl_assign",
        "core::ops::ShrAssign::shr_assign",
    ];
    for path in &operators {
        assert!(
            lookup_std_spec(path).is_some(),
            "Assignment operator trait fallback should resolve: {path}"
        );
    }
}

/// Verify conversion trait fallback specs exist (From, Into, etc.). (#2689)
#[test]
fn conversion_trait_completeness() {
    let paths = [
        "core::convert::From::from",
        "core::convert::Into::into",
        "core::convert::AsRef::as_ref",
        "core::convert::AsMut::as_mut",
        "core::convert::TryFrom::try_from",
        "core::convert::TryInto::try_into",
        "core::convert::identity",
    ];
    for path in &paths {
        assert!(
            lookup_std_spec(path).is_some(),
            "Conversion trait fallback should resolve: {path}"
        );
    }
}

/// Verify comparison trait specs exist for all methods. (#2689)
#[test]
fn comparison_trait_completeness() {
    let paths = [
        // PartialEq
        "core::cmp::PartialEq::eq",
        "core::cmp::PartialEq::ne",
        // PartialOrd
        "core::cmp::PartialOrd::partial_cmp",
        "core::cmp::PartialOrd::le",
        "core::cmp::PartialOrd::ge",
        "core::cmp::PartialOrd::lt",
        "core::cmp::PartialOrd::gt",
        // Ord
        "core::cmp::Ord::cmp",
        "core::cmp::Ord::max",
        "core::cmp::Ord::min",
        "core::cmp::Ord::clamp",
        // Ordering methods
        "core::cmp::Ordering::then",
        "core::cmp::Ordering::then_with",
        "core::cmp::Ordering::reverse",
        "core::cmp::Ordering::is_eq",
        "core::cmp::Ordering::is_lt",
        "core::cmp::Ordering::is_gt",
        "core::cmp::Ordering::is_le",
        "core::cmp::Ordering::is_ge",
        // Free functions
        "core::cmp::min",
        "core::cmp::max",
        "core::cmp::min_by_key",
        "core::cmp::max_by_key",
    ];
    for path in &paths {
        assert!(
            lookup_std_spec(path).is_some(),
            "Comparison trait spec should resolve: {path}"
        );
    }
}

/// Verify DoubleEndedIterator::next_back resolves for all required
/// UFCS paths (concrete iterator types + adapters). (#2689)
#[test]
fn double_ended_iterator_completeness() {
    let paths = [
        // Trait method
        "core::iter::traits::double_ended::DoubleEndedIterator::next_back",
        // Concrete types
        "<alloc::vec::into_iter::IntoIter as core::iter::DoubleEndedIterator>::next_back",
        "<core::slice::iter::Iter as core::iter::DoubleEndedIterator>::next_back",
        // Adapter types
        "<core::iter::adapters::rev::Rev as core::iter::DoubleEndedIterator>::next_back",
        "<core::iter::adapters::chain::Chain as core::iter::DoubleEndedIterator>::next_back",
    ];
    for path in &paths {
        assert!(
            lookup_std_spec(path).is_some(),
            "DoubleEndedIterator::next_back UFCS path should resolve: {path}"
        );
    }
}

/// Verify formatting trait specs prevent opaque classification. (#2689)
///
/// Display::fmt, Debug::fmt, and formatting machinery (write_str, etc.)
/// must resolve to prevent opaque fallback in any code that prints.
#[test]
fn formatting_trait_completeness() {
    let paths = [
        "core::fmt::Display::fmt",
        "std::fmt::Display::fmt",
        "core::fmt::Debug::fmt",
        "std::fmt::Debug::fmt",
        "core::fmt::Write::write_str",
        "core::fmt::Write::write_fmt",
        "core::fmt::Formatter::write_str",
        "core::fmt::Formatter::write_fmt",
    ];
    for path in &paths {
        assert!(
            lookup_std_spec(path).is_some(),
            "Formatting trait spec should resolve: {path}"
        );
    }
}

/// Verify generic trait fallback specs for IntoIterator, Extend,
/// Deref/DerefMut, Drop, and Borrow. (#2689)
#[test]
fn generic_trait_fallback_completeness() {
    let paths = [
        // IntoIterator (generic fallback — after type-specific)
        "core::iter::IntoIterator::into_iter",
        // Extend (generic fallback)
        "core::iter::Extend::extend",
        // Deref / DerefMut
        "core::ops::Deref::deref",
        "core::ops::DerefMut::deref_mut",
        // Drop
        "core::ops::Drop::drop",
        "core::mem::drop",
        "core::ptr::drop_in_place",
        // Borrow / BorrowMut
        "core::borrow::Borrow::borrow",
        "core::borrow::BorrowMut::borrow_mut",
        // Fn traits
        "core::ops::Fn::call",
        "core::ops::FnOnce::call_once",
        "core::ops::FnMut::call_mut",
    ];
    for path in &paths {
        assert!(
            lookup_std_spec(path).is_some(),
            "Generic trait fallback should resolve: {path}"
        );
    }
}

/// Verify Resource Algebra specs resolve through creusot_std aliases. (#2689)
///
/// RA types (Ag, Excl, Frac) are used in ghost protocols and must
/// resolve to prevent opaque classification.
#[test]
fn resource_algebra_completeness() {
    let ag_methods = ["op", "can_update", "core", "incl"];
    for method in &ag_methods {
        let canonical = format!("trust_wp_std::logic::ra::agree::Ag::{method}");
        assert!(
            lookup_std_spec(&canonical).is_some(),
            "Ag::{method} canonical should resolve: {canonical}"
        );
        let creusot = format!("creusot_std::logic::ra::Ag::{method}");
        assert!(
            lookup_std_spec(&creusot).is_some(),
            "Ag::{method} creusot_std alias should resolve: {creusot}"
        );
    }

    let excl_methods = ["op", "can_update", "core", "incl"];
    for method in &excl_methods {
        let canonical = format!("trust_wp_std::logic::ra::excl::Excl::{method}");
        assert!(
            lookup_std_spec(&canonical).is_some(),
            "Excl::{method} canonical should resolve: {canonical}"
        );
        let creusot = format!("creusot_std::logic::ra::Excl::{method}");
        assert!(
            lookup_std_spec(&creusot).is_some(),
            "Excl::{method} creusot_std alias should resolve: {creusot}"
        );
    }

    let frac_methods = ["op", "split", "is_full"];
    for method in &frac_methods {
        let canonical = format!("trust_wp_std::logic::ra::frac::Frac::{method}");
        assert!(
            lookup_std_spec(&canonical).is_some(),
            "Frac::{method} canonical should resolve: {canonical}"
        );
        let creusot = format!("creusot_std::logic::ra::Frac::{method}");
        assert!(
            lookup_std_spec(&creusot).is_some(),
            "Frac::{method} creusot_std alias should resolve: {creusot}"
        );
    }
}

/// Verify VecDeque specs are complete with all path variants. (#2689)
#[test]
fn vecdeque_completeness() {
    let methods = [
        "new",
        "with_capacity",
        "len",
        "is_empty",
        "push_back",
        "push_front",
        "pop_back",
        "pop_front",
        "clear",
        "contains",
        "get",
        "iter",
        "drain",
    ];
    for method in &methods {
        let std_path = format!("std::collections::VecDeque::{method}");
        assert!(
            lookup_std_spec(&std_path).is_some(),
            "VecDeque::{method} std path should resolve: {std_path}"
        );
        let alloc_path = format!("alloc::collections::vec_deque::VecDeque::{method}");
        assert!(
            lookup_std_spec(&alloc_path).is_some(),
            "VecDeque::{method} alloc path should resolve: {alloc_path}"
        );
    }
}

/// Verify Box<T> specs resolve for all UFCS Deref/DerefMut paths. (#2689)
#[test]
fn box_completeness() {
    let paths = [
        "alloc::boxed::Box::new",
        "alloc::boxed::Box::into_inner",
        "<alloc::boxed::Box as core::ops::Deref>::deref",
        "<alloc::boxed::Box as core::ops::DerefMut>::deref_mut",
        "alloc::boxed::Box::as_ref",
        "alloc::boxed::Box::as_mut",
    ];
    for path in &paths {
        assert!(
            lookup_std_spec(path).is_some(),
            "Box spec should resolve: {path}"
        );
    }
}

/// Verify Iterator::next resolves for ALL concrete iterator adapter
/// UFCS paths that post-borrowck MIR can produce. (#2689)
///
/// This is the most critical iterator spec — when MIR resolves `next()`
/// on an adapter like Map or Filter, it produces the concrete UFCS path
/// rather than the trait method path.
#[test]
fn iterator_next_ufcs_adapter_completeness() {
    let adapter_paths = [
        // Map
        "<core::iter::adapters::map::Map as core::iter::Iterator>::next",
        // Filter
        "<core::iter::adapters::filter::Filter as core::iter::Iterator>::next",
        // FilterMap
        "<core::iter::adapters::filter_map::FilterMap as core::iter::Iterator>::next",
        // Enumerate
        "<core::iter::adapters::enumerate::Enumerate as core::iter::Iterator>::next",
        // Skip
        "<core::iter::adapters::skip::Skip as core::iter::Iterator>::next",
        // Take
        "<core::iter::adapters::take::Take as core::iter::Iterator>::next",
        // Zip
        "<core::iter::adapters::zip::Zip as core::iter::Iterator>::next",
        // Chain
        "<core::iter::adapters::chain::Chain as core::iter::Iterator>::next",
        // Fuse
        "<core::iter::adapters::fuse::Fuse as core::iter::Iterator>::next",
        // Cloned
        "<core::iter::adapters::cloned::Cloned as core::iter::Iterator>::next",
        // Copied
        "<core::iter::adapters::copied::Copied as core::iter::Iterator>::next",
        // Rev
        "<core::iter::adapters::rev::Rev as core::iter::Iterator>::next",
        // Peekable
        "<core::iter::adapters::peekable::Peekable as core::iter::Iterator>::next",
        // Concrete types
        "<core::slice::iter::Iter as core::iter::Iterator>::next",
        "<core::slice::iter::IterMut as core::iter::Iterator>::next",
        "<alloc::vec::into_iter::IntoIter as core::iter::Iterator>::next",
        // Range
        "<core::ops::range::Range as core::iter::Iterator>::next",
    ];
    for path in &adapter_paths {
        assert!(
            lookup_std_spec(path).is_some(),
            "Iterator::next UFCS adapter path should resolve: {path}"
        );
    }
}

/// Verify such_that (Hilbert epsilon) resolves through all aliases. (#2689)
#[test]
fn such_that_completeness() {
    for path in &[
        "trust_wp_std::logic::such_that",
        "trust_wp_std::logic::such_that::such_that",
        "trust_wp_std::such_that",
        "creusot_contracts::logic::such_that",
        "creusot_contracts::such_that",
        "creusot_std::logic::such_that",
        "creusot_std::such_that",
    ] {
        assert!(
            lookup_std_spec(path).is_some(),
            "such_that should resolve: {path}"
        );
    }
}

/// Verify RangeInclusive IntoIterator resolves. (#2689)
#[test]
fn range_inclusive_into_iter_completeness() {
    for path in &[
        "<core::ops::range::RangeInclusive as core::iter::IntoIterator>::into_iter",
        "<std::ops::RangeInclusive as core::iter::IntoIterator>::into_iter",
    ] {
        assert!(
            lookup_std_spec(path).is_some(),
            "RangeInclusive IntoIterator should resolve: {path}"
        );
    }
}

/// Verify RangeInclusive::new resolves without an opaque-call fallback.
#[test]
fn range_inclusive_new_resolves() {
    for path in &[
        "core::ops::range::RangeInclusive::new",
        "core::ops::RangeInclusive::new",
        "std::ops::range::RangeInclusive::new",
        "std::ops::RangeInclusive::new",
        "core::ops::range::RangeInclusive::<i32>::new",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("RangeInclusive::new should resolve: {path}"));
        let expected_params = vec!["start".to_string(), "end".to_string()];
        assert_eq!(
            spec.param_names.as_deref(),
            Some(expected_params.as_slice())
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e == "result.start_log() == start"),
            "missing start_log postcondition for {path}: {:?}",
            spec.ensures
        );
        assert!(
            spec.ensures.iter().any(|e| e == "result.end_log() == end"),
            "missing end_log postcondition for {path}: {:?}",
            spec.ensures
        );
    }
}

/// Atomic operation specs prevent opaque demotion (#2697).
///
/// All atomic types (AtomicBool, AtomicUsize, AtomicI32, AtomicU32, AtomicU64)
/// must have spec table entries for new, into_inner, load, store, swap, and
/// fetch_add to prevent OpaqueCallTrueAssumption fallback in Creusot compat
/// tests that use concurrent ghost protocols.
#[test]
fn lookup_atomic_operation_specs() {
    for path in &[
        // SC variant — AtomicBool
        "trust_wp_std::std::sync::atomic_sc::AtomicBool::new",
        "trust_wp_std::std::sync::atomic_sc::AtomicBool::load",
        "trust_wp_std::std::sync::atomic_sc::AtomicBool::store",
        "trust_wp_std::std::sync::atomic_sc::AtomicBool::swap",
        "trust_wp_std::std::sync::atomic_sc::AtomicBool::into_inner",
        // SC variant — AtomicU32
        "trust_wp_std::std::sync::atomic_sc::AtomicU32::new",
        "trust_wp_std::std::sync::atomic_sc::AtomicU32::load",
        "trust_wp_std::std::sync::atomic_sc::AtomicU32::store",
        "trust_wp_std::std::sync::atomic_sc::AtomicU32::swap",
        "trust_wp_std::std::sync::atomic_sc::AtomicU32::fetch_add",
        // SC variant — AtomicU64
        "trust_wp_std::std::sync::atomic_sc::AtomicU64::new",
        "trust_wp_std::std::sync::atomic_sc::AtomicU64::load",
        "trust_wp_std::std::sync::atomic_sc::AtomicU64::store",
        "trust_wp_std::std::sync::atomic_sc::AtomicU64::swap",
        "trust_wp_std::std::sync::atomic_sc::AtomicU64::fetch_add",
        // RelAcq variant — AtomicBool
        "trust_wp_std::std::sync::atomic_relacq::AtomicBool::new",
        "trust_wp_std::std::sync::atomic_relacq::AtomicBool::load",
        "trust_wp_std::std::sync::atomic_relacq::AtomicBool::store",
        "trust_wp_std::std::sync::atomic_relacq::AtomicBool::swap",
        // RelAcq variant — AtomicU32
        "trust_wp_std::std::sync::atomic_relacq::AtomicU32::new",
        "trust_wp_std::std::sync::atomic_relacq::AtomicU32::load",
        "trust_wp_std::std::sync::atomic_relacq::AtomicU32::swap",
        "trust_wp_std::std::sync::atomic_relacq::AtomicU32::fetch_add",
        // SC committer methods
        "trust_wp_std::std::sync::atomic_sc::LoadCommitter::val",
        "trust_wp_std::std::sync::atomic_sc::StoreCommitter::shoot",
        "trust_wp_std::std::sync::atomic_sc::UpdateCommitter::old_val",
        // RelAcq committer methods
        "trust_wp_std::std::sync::atomic_relacq::LoadCommitter::val",
        "trust_wp_std::std::sync::atomic_relacq::StoreCommitter::shoot",
        "trust_wp_std::std::sync::atomic_relacq::UpdateCommitter::old_val",
    ] {
        assert!(
            lookup_std_spec(path).is_some(),
            "{path} should resolve to a spec (prevents opaque demotion)"
        );
    }
}

/// Spec table coverage floor — a regression test against accidental
/// entry removal. (#2689)
///
/// The thresholds sit roughly a tenth below the table's actual entry and
/// alias counts: far enough to survive minor refactoring, close enough
/// that an emptied sub-table or a stripped alias list trips them.
#[test]
fn spec_table_entry_count_is_sufficient() {
    let total_entries: usize = super::STD_SPEC_TABLES.iter().map(|table| table.len()).sum();
    let total_aliases: usize = super::STD_SPEC_TABLES
        .iter()
        .flat_map(|table| table.iter())
        .map(|(paths, _)| paths.len())
        .sum();
    // Adjust the floors upward when entries are added, never decrease them.
    assert!(
        total_entries >= 630,
        "Spec table should have at least 630 entries, found {total_entries}. \
         Check if a table was accidentally emptied or removed."
    );
    assert!(
        total_aliases >= 2700,
        "Spec table should have at least 2700 total alias paths, found {total_aliases}. \
         Check if path aliases were accidentally stripped."
    );
}

/// Verify that all 16 sub-tables are loaded in STD_SPEC_TABLES. (#2689)
///
/// Guards against accidentally commenting out or removing a sub-table
/// from the ordered table-of-tables in mod.rs.
#[test]
fn all_subtables_loaded() {
    assert!(
        super::STD_SPEC_TABLES.len() >= 16,
        "Expected at least 16 sub-tables in STD_SPEC_TABLES, found {}. \
         A sub-table may have been accidentally removed from mod.rs.",
        super::STD_SPEC_TABLES.len()
    );
}

/// Verify that normalization handles all crate alias patterns needed
/// by compat tests, ensuring creusot_std paths don't require explicit
/// table entries. (#2689)
///
/// This test documents that trust_wp_std paths without explicit
/// creusot_std counterparts in the table are still reachable, because
/// `normalize_crate_aliases` rewrites `creusot_std::` -> `trust_wp_std::`
/// before lookup.
#[test]
fn normalization_covers_all_creusot_std_paths() {
    // Sample of trust_wp_std paths that exist in the table — verify their
    // creusot_std equivalents resolve via normalization (not explicit entries).
    let trust_wp_paths = [
        "trust_wp_std::cell::PermCell::new",
        "trust_wp_std::cell::PredCell::get",
        "trust_wp_std::ghost::Authority::alloc",
        "trust_wp_std::ghost::Ghost::new",
        "trust_wp_std::ghost::Snapshot::capture",
    ];

    for trust_wp_path in &trust_wp_paths {
        // The trust_wp_std:: path should resolve directly.
        assert!(
            lookup_std_spec(trust_wp_path).is_some(),
            "Canonical path should resolve: {trust_wp_path}"
        );

        // The creusot_std:: equivalent should also resolve via normalization.
        let creusot_path = trust_wp_path.replace("trust_wp_std::", "creusot_std::");
        assert!(
            lookup_std_spec(&creusot_path).is_some(),
            "creusot_std alias should resolve via normalization: {creusot_path}"
        );
    }
}

/// Primitive `Div::div` / `Rem::rem` specs bind ONLY primitive-integer Self
/// types. The bare trait path is what call resolution's trait-method
/// fallback looks up for every impl, so it must not carry the integer spec:
/// a user `impl Div for S` returning `S(0)` otherwise verified
/// `S(8).div(S(2))@ == 4`.
#[test]
fn primitive_div_rem_specs_are_integer_self_typed_only() {
    for path in [
        "core::ops::Div::div",
        "core::ops::arith::Div::div",
        "std::ops::Div::div",
    ] {
        assert!(
            lookup_std_spec(path).is_none(),
            "bare Div trait path must not resolve to the integer spec: {path}"
        );
    }
    for path in [
        "<i32 as core::ops::Div>::div",
        "<u64 as std::ops::Div>::div",
        "<isize as core::ops::arith::Div>::div",
        "i128::div",
    ] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("self@ / rhs@")),
            "{path} should carry the integer division spec: {:?}",
            spec.ensures
        );
    }
    for path in [
        "<i32 as core::ops::Rem>::rem",
        "<i64 as std::ops::Rem>::rem",
        "<u8 as core::ops::arith::Rem>::rem",
        "usize::rem",
    ] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        assert!(
            spec.ensures.iter().any(|e| e.contains("self@ % rhs@")),
            "{path} should carry the truncating integer remainder spec: {:?}",
            spec.ensures
        );
        assert!(
            spec.requires.iter().any(|r| r.contains("rhs@ != 0")),
            "{path} must keep the nonzero-divisor precondition"
        );
    }
    // The bare Rem trait path keeps the generic opaque fallback.
    let generic = lookup_std_spec("core::ops::Rem::rem").expect("generic Rem fallback");
    assert!(
        generic
            .ensures
            .iter()
            .any(|e| e.contains("T::rem.postcondition")),
        "bare Rem path must stay the generic fallback: {:?}",
        generic.ensures
    );
}

/// Primitive `rem_euclid` / `div_euclid` resolve to their Euclidean specs.
#[test]
fn primitive_euclid_specs_resolve() {
    for path in [
        "core::num::rem_euclid",
        "i32::rem_euclid",
        "core::num::u8::rem_euclid",
    ] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("self@.rem_euclid(rhs@)")));
    }
    for path in ["core::num::div_euclid", "i64::div_euclid"] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        assert!(spec
            .ensures
            .iter()
            .any(|e| e.contains("rem_euclid(rhs@)) / rhs@")));
    }
}

/// Signed `MIN / -1` overflow: every panicking primitive div/rem spec carries
/// creusot-std's `!(self@ == MIN@ && rhs@ == -1)` precondition, resolved to the
/// concrete integer type.
#[test]
fn primitive_div_rem_specs_require_no_signed_overflow() {
    for (path, ty) in [
        ("<i8 as core::ops::Div>::div", "i8"),
        ("core::num::<impl i8>::div", "i8"),
        ("<i32 as core::ops::Rem>::rem", "i32"),
        ("core::num::<impl i32>::rem", "i32"),
        ("core::num::<impl i64>::rem_euclid", "i64"),
        ("core::num::<impl i8>::div_euclid", "i8"),
        ("u32::rem_euclid", "u32"),
    ] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        let want = format!("!(self@ == {ty}::MIN@ && rhs@ == -1)");
        assert!(
            spec.requires.iter().any(|r| r.contains(&want)),
            "{path} must require {want}: {:?}",
            spec.requires
        );
    }
    for path in ["i8::checked_div", "i8::checked_rem"] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("result.is_none()") && e.contains("i8::MIN@ && rhs@ == -1")),
            "{path} must return None on MIN / -1: {:?}",
            spec.ensures
        );
    }
    let sat = lookup_std_spec("i8::saturating_div").expect("saturating_div");
    assert!(sat
        .ensures
        .iter()
        .any(|e| e.contains("result@ == i8::MAX@")));
    let wrap = lookup_std_spec("i8::wrapping_div").expect("wrapping_div");
    assert!(wrap
        .ensures
        .iter()
        .any(|e| e.contains("result@ == i8::MIN@")));
}

/// The generic `Rem`/`RemAssign`/`DivAssign` fallbacks cannot know the
/// callee's precondition, so they carry an undischargeable obligation instead
/// of assuming the call is panic-free.
#[test]
fn generic_rem_div_fallbacks_carry_precondition_obligation() {
    for (path, pre) in [
        ("core::ops::Rem::rem", "T::rem.precondition"),
        (
            "core::ops::RemAssign::rem_assign",
            "T::rem_assign.precondition",
        ),
        (
            "core::ops::DivAssign::div_assign",
            "T::div_assign.precondition",
        ),
    ] {
        let spec = lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should resolve"));
        assert!(
            spec.requires.iter().any(|r| r.contains(pre)),
            "{path} must require {pre}: {:?}",
            spec.requires
        );
    }
}
