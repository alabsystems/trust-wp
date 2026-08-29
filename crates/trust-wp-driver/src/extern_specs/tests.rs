// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parse_extern_spec_docs() {
    let docs = [
        "trust-wp:extern_spec:target=Option::unwrap",
        "trust-wp:extern_spec:requires=self.is_some()",
        "trust-wp:extern_spec:ensures=Some(result) == old(self)",
    ];

    let entry = parse_extern_spec_docs(docs.iter().copied())
        .expect("should not error")
        .expect("should find entry");
    assert_eq!(entry.target_path, "Option::unwrap");
    assert_eq!(entry.requires, vec!["self.is_some()"]);
    assert_eq!(entry.ensures, vec!["Some(result) == old(self)"]);
}

#[test]
fn test_parse_extern_spec_docs_multiple() {
    let docs = [
        "trust-wp:extern_spec:target=Vec::insert",
        "trust-wp:extern_spec:requires=index <= self.len(); value != 0",
        "trust-wp:extern_spec:ensures=(^self).len() == self.len() + 1",
    ];

    let entry = parse_extern_spec_docs(docs.iter().copied())
        .expect("should not error")
        .expect("should find entry");
    assert_eq!(entry.target_path, "Vec::insert");
    assert_eq!(entry.requires.len(), 2);
    assert_eq!(entry.ensures.len(), 1);
}

#[test]
fn test_parse_extern_spec_docs_empty_contracts() {
    let docs = [
        "trust-wp:extern_spec:target=Vec::new",
        "trust-wp:extern_spec:requires=",
        "trust-wp:extern_spec:ensures=result.len() == 0",
    ];

    let entry = parse_extern_spec_docs(docs.iter().copied())
        .expect("should not error")
        .expect("should find entry");
    assert_eq!(entry.target_path, "Vec::new");
    assert!(entry.requires.is_empty());
    assert_eq!(entry.ensures, vec!["result.len() == 0"]);
}

#[test]
fn test_parse_extern_spec_docs_not_extern_spec() {
    let docs = ["Some random doc comment", "Another doc line"];

    let result = parse_extern_spec_docs(docs.iter().copied()).expect("should not error");
    assert!(result.is_none());
}

#[test]
fn test_parse_extern_spec_docs_requires_without_target() {
    let docs = ["trust-wp:extern_spec:requires=x > 0"];

    let err = parse_extern_spec_docs(docs.iter().copied()).expect_err("should error");
    assert!(
        matches!(
            err,
            ParseExternSpecError::MissingTarget {
                marker_kind: "requires"
            }
        ),
        "expected MissingTarget(requires), got: {err}"
    );
}

#[test]
fn test_parse_extern_spec_docs_ensures_without_target() {
    let docs = ["trust-wp:extern_spec:ensures=result > 0"];

    let err = parse_extern_spec_docs(docs.iter().copied()).expect_err("should error");
    assert!(
        matches!(
            err,
            ParseExternSpecError::MissingTarget {
                marker_kind: "ensures"
            }
        ),
        "expected MissingTarget(ensures), got: {err}"
    );
}

#[test]
fn test_parse_extern_spec_docs_both_without_target() {
    let docs = [
        "trust-wp:extern_spec:requires=x > 0",
        "trust-wp:extern_spec:ensures=result > 0",
    ];

    let err = parse_extern_spec_docs(docs.iter().copied()).expect_err("should error");
    assert!(
        matches!(
            err,
            ParseExternSpecError::MissingTarget {
                marker_kind: "requires and ensures"
            }
        ),
        "expected MissingTarget(requires and ensures), got: {err}"
    );
}

#[test]
fn test_normalize_extern_spec_path() {
    assert_eq!(
        normalize_extern_spec_path("Option::unwrap"),
        "core::option::Option::unwrap"
    );
    assert_eq!(
        normalize_extern_spec_path("Vec::push"),
        "alloc::vec::Vec::push"
    );
    assert_eq!(
        normalize_extern_spec_path("Result::is_ok"),
        "core::result::Result::is_ok"
    );
    // Already qualified paths pass through
    assert_eq!(
        normalize_extern_spec_path("core::option::Option::unwrap"),
        "core::option::Option::unwrap"
    );
    assert_eq!(
        normalize_extern_spec_path("::core::option::Option::unwrap"),
        "core::option::Option::unwrap"
    );
    // Slice type mappings
    assert_eq!(
        normalize_extern_spec_path("[T]::first"),
        "core::slice::<impl [T]>::first"
    );
    assert_eq!(
        normalize_extern_spec_path("slice::get"),
        "core::slice::<impl [T]>::get"
    );
    // str primitive type
    assert_eq!(normalize_extern_spec_path("str::len"), "str::len");
}

#[test]
fn test_normalize_path_for_lookup() {
    assert_eq!(
        normalize_path_for_lookup("core::option::Option::<i32>::unwrap"),
        "core::option::Option::unwrap"
    );
    assert_eq!(
        normalize_path_for_lookup("alloc::vec::Vec::<T>::push"),
        "alloc::vec::Vec::push"
    );
}

#[test]
fn test_lookup_extern_spec() {
    let mut specs = HashMap::new();
    specs.insert(
        "core::option::Option::unwrap".to_string(),
        StdSpec {
            requires: vec!["self.is_some()".to_string()],
            ensures: vec!["Some(result) == old(self)".to_string()],
            param_names: None,
        },
    );

    // Exact match
    let found = lookup_extern_spec(&specs, "core::option::Option::unwrap").unwrap();
    assert_eq!(found.requires, vec!["self.is_some()"]);

    // With generics (normalized)
    let found = lookup_extern_spec(&specs, "core::option::Option::<i32>::unwrap").unwrap();
    assert_eq!(found.requires, vec!["self.is_some()"]);

    // std -> core remapping
    let found = lookup_extern_spec(&specs, "std::option::Option::unwrap").unwrap();
    assert_eq!(found.requires, vec!["self.is_some()"]);

    // std -> core remapping with generics (both remapping AND normalization needed)
    let found = lookup_extern_spec(&specs, "std::option::Option::<i32>::unwrap").unwrap();
    assert_eq!(found.requires, vec!["self.is_some()"]);

    // Not found
    assert!(lookup_extern_spec(&specs, "Vec::push").is_none());
}

#[test]
fn test_extern_specs_are_compatible_ignores_whitespace_and_clause_order() {
    let left = StdSpec {
        requires: vec!["self.is_some()".to_string(), "x > 0".to_string()],
        ensures: vec!["Some(result) == old(self)".to_string()],
        param_names: Some(vec!["self".to_string()]),
    };
    let right = StdSpec {
        requires: vec!["x>0".to_string(), "self . is_some ( )".to_string()],
        ensures: vec!["Some( result )==old( self )".to_string()],
        param_names: Some(vec!["self".to_string()]),
    };

    assert!(extern_specs_are_compatible(&left, &right));
}

#[test]
fn test_extern_specs_are_not_compatible_when_contract_differs() {
    let builtin = StdSpec {
        requires: vec!["self.is_some()".to_string()],
        ensures: vec!["Some(result) == old(self)".to_string()],
        param_names: None,
    };
    let local = StdSpec {
        requires: vec!["true".to_string()],
        ensures: vec!["Some(result) == old(self)".to_string()],
        param_names: None,
    };

    assert!(!extern_specs_are_compatible(&builtin, &local));
}

#[test]
fn test_merge_local_extern_specs_dedupes_compatible_builtin_duplicate() {
    let mut specs = HashMap::new();
    specs.insert(
        "core::option::Option::unwrap".to_string(),
        StdSpec {
            requires: vec!["self.is_some()".to_string()],
            ensures: vec!["Some(result) == old(self)".to_string()],
            param_names: None,
        },
    );

    let mut local = HashMap::new();
    local.insert(
        "core::option::Option::unwrap".to_string(),
        StdSpec {
            requires: vec!["self . is_some ( )".to_string()],
            ensures: vec!["Some( result ) == old( self )".to_string()],
            param_names: None,
        },
    );

    let report = merge_local_extern_specs(&mut specs, local);

    assert_eq!(report.compatible_builtin_duplicates, 1);
    assert!(report.incompatible_builtin_conflicts.is_empty());
    assert_eq!(specs.len(), 1);
    assert_eq!(
        specs["core::option::Option::unwrap"].requires,
        vec!["self.is_some()"]
    );
}

#[test]
fn test_merge_local_extern_specs_reports_incompatible_builtin_conflict() {
    let mut specs = HashMap::new();
    specs.insert(
        "core::option::Option::unwrap".to_string(),
        StdSpec {
            requires: vec!["self.is_some()".to_string()],
            ensures: vec!["Some(result) == old(self)".to_string()],
            param_names: None,
        },
    );

    let mut local = HashMap::new();
    local.insert(
        "core::option::Option::unwrap".to_string(),
        StdSpec {
            requires: vec!["true".to_string()],
            ensures: vec!["Some(result) == old(self)".to_string()],
            param_names: None,
        },
    );

    let report = merge_local_extern_specs(&mut specs, local);

    assert_eq!(report.compatible_builtin_duplicates, 0);
    assert_eq!(
        report.incompatible_builtin_conflicts,
        vec!["core::option::Option::unwrap"]
    );
    assert_eq!(
        specs["core::option::Option::unwrap"].requires,
        vec!["self.is_some()"]
    );
}

#[test]
fn test_merge_local_extern_specs_preserves_builtin_param_names() {
    let mut specs = HashMap::new();
    specs.insert(
        "alloc::vec::Vec::push".to_string(),
        StdSpec {
            requires: vec![],
            ensures: vec!["(^self)@ == self@.push_back(value)".to_string()],
            param_names: Some(vec!["self".to_string(), "value".to_string()]),
        },
    );

    let mut local = HashMap::new();
    local.insert(
        "alloc::vec::Vec::push".to_string(),
        StdSpec {
            requires: vec![],
            ensures: vec!["(^self)@==self@.push_back(value)".to_string()],
            param_names: None,
        },
    );

    let report = merge_local_extern_specs(&mut specs, local);

    assert_eq!(report.compatible_builtin_duplicates, 1);
    assert_eq!(
        specs["alloc::vec::Vec::push"].param_names,
        Some(vec!["self".to_string(), "value".to_string()])
    );
}

// Built-in registry bridge tests (#1672).

#[test]
fn test_builtin_registry_loads_nonempty() {
    let specs = builtin_trust_wp_std_specs();
    // Must include Vec, Option, Result, Clone, Default, String entries
    assert!(
        specs.len() > 50,
        "expected >50 entries (with aliases), got {}",
        specs.len()
    );
}

#[test]
fn test_builtin_registry_vec_new_canonical_path() {
    let specs = builtin_trust_wp_std_specs();
    let spec = specs
        .get("std::vec::Vec::new")
        .expect("missing std::vec::Vec::new");
    assert!(
        !spec.ensures.is_empty(),
        "Vec::new should have an ensures clause"
    );
}

#[test]
fn test_builtin_registry_vec_alias_alloc() {
    let specs = builtin_trust_wp_std_specs();
    let spec = specs
        .get("alloc::vec::Vec::push")
        .expect("missing alloc::vec::Vec::push alias");
    assert!(
        !spec.ensures.is_empty(),
        "Vec::push alias should have ensures"
    );
    assert_eq!(
        spec.param_names.as_deref(),
        Some(
            ["self", "value"]
                .as_slice()
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .as_slice()
        ),
        "Vec::push should have param_names for self and value"
    );
}

#[test]
fn test_builtin_registry_vec_get_uses_generic_slice_index_surface() {
    let specs = builtin_trust_wp_std_specs();
    let spec = specs
        .get("alloc::vec::Vec::get")
        .expect("missing alloc::vec::Vec::get alias");
    assert!(
        spec.ensures
            .iter()
            .any(|e| e.contains("ix.in_bounds(self@) ==> exists<r> result == Some(r)")),
        "Vec::get should use the generic SliceIndexSpec ensures surface: {:?}",
        spec.ensures
    );
    assert_eq!(
        spec.param_names.as_deref(),
        Some(
            ["self", "ix"]
                .as_slice()
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .as_slice()
        ),
        "Vec::get should expose self/ix param_names"
    );
}

#[test]
fn test_builtin_registry_vec_index_mut_uses_generic_slice_index_surface() {
    let specs = builtin_trust_wp_std_specs();
    let spec = specs
        .get("<alloc::vec::Vec as core::ops::IndexMut>::index_mut")
        .expect("missing alloc::vec::Vec IndexMut alias");
    assert!(
        spec.requires
            .iter()
            .any(|r| r.contains("ix.in_bounds(self@)")),
        "Vec::index_mut should require ix.in_bounds(self@): {:?}",
        spec.requires
    );
    assert!(
        spec.ensures
            .iter()
            .any(|e| e.contains("ix.resolve_elsewhere(self@, (^self)@)")),
        "Vec::index_mut should preserve the generic frame condition: {:?}",
        spec.ensures
    );
}

#[test]
fn test_builtin_registry_string_alias_alloc() {
    let specs = builtin_trust_wp_std_specs();
    assert!(
        specs.contains_key("alloc::string::String::len"),
        "missing alloc::string::String::len alias"
    );
}

#[test]
fn test_builtin_registry_option_alias_std() {
    let specs = builtin_trust_wp_std_specs();
    // Option uses core:: canonically; should have std:: alias too
    assert!(
        specs.contains_key("std::option::Option::unwrap"),
        "missing std::option::Option::unwrap alias"
    );
}

#[test]
fn test_builtin_registry_clone_shorthand() {
    let specs = builtin_trust_wp_std_specs();
    // UFCS trait-qualified path
    assert!(
        specs.contains_key("<bool as core::clone::Clone>::clone"),
        "missing canonical clone path"
    );
    // std:: trait alias
    assert!(
        specs.contains_key("<bool as std::clone::Clone>::clone"),
        "missing std clone alias"
    );
    // Shorthand inherent-style path
    assert!(
        specs.contains_key("bool::clone"),
        "missing shorthand bool::clone"
    );
}

#[test]
fn test_builtin_registry_default_bool() {
    let specs = builtin_trust_wp_std_specs();
    let spec = specs
        .get("<bool as core::default::Default>::default")
        .expect("missing bool Default spec");
    assert!(
        spec.ensures.iter().any(|e| e.contains("false")),
        "bool Default should ensure result == false"
    );
}

#[test]
fn test_expand_aliases_vec_inherent() {
    let aliases = super::builtin_registry::expand_builtin_path_aliases("std::vec::Vec::push");
    assert!(
        aliases.contains(&"alloc::vec::Vec::push".to_string()),
        "should expand std::vec to alloc::vec"
    );
}

#[test]
fn test_expand_aliases_ufcs_trait() {
    let aliases = super::builtin_registry::expand_builtin_path_aliases(
        "<std::vec::Vec as core::ops::Index>::index",
    );
    // Should produce std::ops alias
    assert!(
        aliases.iter().any(|a| a.contains("std::ops::Index")),
        "should expand core::ops to std::ops"
    );
    // Should produce alloc::vec alias
    assert!(
        aliases.iter().any(|a| a.contains("alloc::vec::Vec")),
        "should expand std::vec to alloc::vec in UFCS"
    );
}

#[test]
fn test_expand_aliases_primitive_clone_shorthand() {
    let aliases =
        super::builtin_registry::expand_builtin_path_aliases("<i32 as core::clone::Clone>::clone");
    assert!(
        aliases.contains(&"i32::clone".to_string()),
        "should produce shorthand i32::clone"
    );
    assert!(
        aliases.iter().any(|a| a.contains("std::clone::Clone")),
        "should produce std:: trait alias"
    );
}

// param_names preservation tests (#2298).

#[test]
fn test_parse_extern_spec_docs_with_params() {
    let docs = [
        "trust-wp:extern_spec:target=Vec::push",
        "trust-wp:extern_spec:params=self, value",
        "trust-wp:extern_spec:requires=true",
        "trust-wp:extern_spec:ensures=(^self)@.len() == self@.len() + 1",
    ];

    let entry = parse_extern_spec_docs(docs.iter().copied())
        .expect("should not error")
        .expect("should find entry");
    assert_eq!(entry.target_path, "Vec::push");
    assert_eq!(
        entry.param_names.as_deref(),
        Some(vec!["self".to_string(), "value".to_string()].as_slice()),
        "param_names should be parsed from params= marker"
    );
}

#[test]
fn test_parse_extern_spec_docs_without_params_is_none() {
    let docs = [
        "trust-wp:extern_spec:target=Vec::new",
        "trust-wp:extern_spec:ensures=result@.len() == 0",
    ];

    let entry = parse_extern_spec_docs(docs.iter().copied())
        .expect("should not error")
        .expect("should find entry");
    assert_eq!(entry.param_names, None, "no params= marker -> None");
}

#[test]
fn test_extern_spec_entry_to_std_spec_carries_param_names() {
    let entry = ExternSpecEntry {
        target_path: "Option::ok_or".to_string(),
        requires: vec![],
        ensures: vec!["result == Ok(self.unwrap())".to_string()],
        param_names: Some(vec!["self".to_string(), "err".to_string()]),
    };
    let spec: StdSpec = entry.into();
    assert_eq!(
        spec.param_names.as_deref(),
        Some(vec!["self".to_string(), "err".to_string()].as_slice()),
        "From<ExternSpecEntry> should carry param_names into StdSpec"
    );
}

#[test]
fn test_extern_spec_entry_to_std_spec_none_param_names() {
    let entry = ExternSpecEntry {
        target_path: "Vec::new".to_string(),
        requires: vec![],
        ensures: vec!["result@.len() == 0".to_string()],
        param_names: None,
    };
    let spec: StdSpec = entry.into();
    assert_eq!(
        spec.param_names, None,
        "None param_names should pass through"
    );
}

#[test]
fn test_parse_extern_spec_docs_params_empty_string() {
    let docs = [
        "trust-wp:extern_spec:target=Vec::new",
        "trust-wp:extern_spec:params=",
        "trust-wp:extern_spec:ensures=result@.len() == 0",
    ];

    let entry = parse_extern_spec_docs(docs.iter().copied())
        .expect("should not error")
        .expect("should find entry");
    assert_eq!(
        entry.param_names, None,
        "empty params= should be treated as None"
    );
}

/// Regression test (#2298): verify that param_names survive the full
/// extern_spec pipeline: parse doc markers -> ExternSpecEntry -> StdSpec ->
/// lookup_extern_spec. This exercises the bodyless/extern call path where
/// HIR/MIR names are unavailable and the spec-owned names must be used.
#[test]
fn test_param_names_survive_full_lookup_roundtrip() {
    // Simulate what the driver does: parse extern_spec markers, convert
    // to StdSpec, insert into the lookup table, then look up by path.
    let docs = [
        "trust-wp:extern_spec:target=Option::ok_or",
        "trust-wp:extern_spec:params=self, err",
        "trust-wp:extern_spec:ensures=self.is_some() ==> result == Ok(self.unwrap())",
    ];
    let entry = parse_extern_spec_docs(docs.iter().copied())
        .expect("should not error")
        .expect("should find entry");

    let normalized_path = normalize_extern_spec_path(&entry.target_path);
    let spec: StdSpec = entry.into();

    let mut table = HashMap::new();
    table.insert(normalized_path, spec);

    // Look up via the normalized path (as the MIR extraction would)
    let found = lookup_extern_spec(&table, "core::option::Option::ok_or")
        .expect("should find spec for Option::ok_or");
    assert_eq!(
        found.param_names,
        Some(vec!["self".to_string(), "err".to_string()]),
        "param_names must survive the full parse->convert->lookup pipeline"
    );
}
