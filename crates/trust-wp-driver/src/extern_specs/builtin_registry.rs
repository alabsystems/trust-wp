// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use crate::std_specs::StdSpec;

/// Load the built-in extern-spec registry from `trust-wp-std`.
///
/// Converts each `BuiltinExternSpec` entry into the driver's `StdSpec` format
/// and generates path aliases so that lookups by `alloc::vec::Vec::push`,
/// `std::vec::Vec::push`, or trait-qualified UFCS paths all find the spec.
///
/// For domains migrated to the shared lookup registry (#2524), aliases are
/// sourced from `trust_wp_std::std::lookup_registry` instead of from
/// `expand_builtin_path_aliases()`. This eliminates independent alias
/// maintenance for those domains.
///
/// See: `designs/2026-03-12-1672-extern-spec-registry-bridge.md`
/// See: `designs/2026-03-19-2524-std-spec-path-authority-unification.md`
pub fn builtin_trust_wp_std_specs() -> HashMap<String, StdSpec> {
    use trust_wp_std::std::{builtin_registry::BUILTIN_EXTERN_SPECS, lookup_registry};

    let mut specs = HashMap::new();
    for entry in BUILTIN_EXTERN_SPECS {
        let spec = StdSpec::from_spec_string(entry.spec);
        // Insert with the canonical target path.
        specs.insert(entry.target_path.to_string(), spec.clone());
        // For migrated domains, use shared manifest aliases.
        // For non-migrated domains, use local alias expansion.
        if let Some(aliases) = lookup_registry::migrated_builtin_extern_aliases(entry.target_path) {
            for &alias in aliases {
                specs
                    .entry(alias.to_string())
                    .or_insert_with(|| spec.clone());
            }
        } else {
            for alias in expand_builtin_path_aliases(entry.target_path) {
                specs.entry(alias).or_insert_with(|| spec.clone());
            }
        }
    }
    specs
}

/// Generate alias-expanded paths for a built-in extern-spec target path.
///
/// The driver sees paths from MIR in various forms depending on how the
/// compiler resolves re-exports. This function expands the canonical path
/// to cover the common alternatives:
/// - `std::vec::Vec::*` ↔ `alloc::vec::Vec::*`
/// - `std::string::String::*` ↔ `alloc::string::String::*`
/// - `std::option::*` ↔ `core::option::*`
/// - `std::result::*` ↔ `core::result::*`
/// - `core::clone::Clone` ↔ `std::clone::Clone` (trait-qualified UFCS)
/// - `core::default::Default` ↔ `std::default::Default` (trait-qualified UFCS)
/// - `core::ops::*` ↔ `std::ops::*` (trait-qualified UFCS)
pub(super) fn expand_builtin_path_aliases(path: &str) -> Vec<String> {
    let mut aliases = Vec::new();

    // Inherent method aliases: std ↔ alloc/core
    const INHERENT_ALIASES: &[(&str, &str)] = &[
        ("std::vec::Vec::", "alloc::vec::Vec::"),
        ("std::string::String::", "alloc::string::String::"),
        ("core::option::Option::", "std::option::Option::"),
        ("core::result::Result::", "std::result::Result::"),
    ];
    for &(from, to) in INHERENT_ALIASES {
        if let Some(rest) = path.strip_prefix(from) {
            aliases.push(format!("{to}{rest}"));
        }
    }

    // UFCS trait aliases: core:: ↔ std:: inside `<Type as Trait>` paths
    const UFCS_TRAIT_ALIASES: &[(&str, &str)] = &[
        ("core::clone::Clone", "std::clone::Clone"),
        ("core::default::Default", "std::default::Default"),
        ("core::ops::Index", "std::ops::Index"),
        ("core::ops::IndexMut", "std::ops::IndexMut"),
    ];
    for &(from, to) in UFCS_TRAIT_ALIASES {
        if path.contains(from) {
            aliases.push(path.replace(from, to));
        }
    }

    // UFCS type aliases: std::vec::Vec ↔ alloc::vec::Vec inside `<Type as Trait>` paths
    if path.contains("std::vec::Vec") {
        aliases.push(path.replace("std::vec::Vec", "alloc::vec::Vec"));
    }

    // Shorthand inherent paths for primitives (e.g., "bool::clone")
    if path.starts_with('<') {
        // Extract the type from `<TYPE as TRAIT>::method`
        if let Some(type_end) = path.find(" as ") {
            let inner_type = &path[1..type_end];
            if let Some(method_start) = path.rfind(">::") {
                let method = &path[method_start + 3..];
                aliases.push(format!("{inner_type}::{method}"));
            }
        }
    }

    aliases
}
