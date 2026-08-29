// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! External specification discovery and lookup for user-defined external specifications.
//!
//! This module provides discovery of `extern_spec!` macro expansions.
//! The macro emits stub functions with doc markers that this module parses.
//!
//! # Doc Marker Format
//!
//! The extern_spec! macro emits functions with these doc attributes:
//! - `trust-wp:extern_spec:target=<path>` - Target function path
//! - `trust-wp:extern_spec:requires=<exprs>` - Semicolon-separated preconditions
//! - `trust-wp:extern_spec:ensures=<exprs>` - Semicolon-separated postconditions
//!
//! # Integration with std_specs
//!
//! The effective lookup stack is:
//! 1. Local `extern_spec!` discoveries from this module
//! 2. Builtin `trust-wp-std` registry entries imported through
//!    `builtin_trust_wp_std_specs()`
//! 3. Hardcoded `std_specs` fallback
//!
//! This module handles only step 1. Builtin `trust-wp-std` specs are bridged in
//! separately instead of being discovered through local doc-marker parsing.
//!
//! # Design
//!
//! See `designs/2026-02-01-extern-spec.md` for the full design document.
//! Related: Issue #160

#![allow(clippy::doc_markdown)]

use std::collections::{BTreeMap, HashMap};

use crate::std_specs::StdSpec;

mod builtin_registry;

pub use builtin_registry::builtin_trust_wp_std_specs;

#[cfg(test)]
mod tests;

/// Error from parsing malformed extern spec doc markers.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ParseExternSpecError {
    /// Found requires/ensures markers but no target path.
    #[error("extern spec has {marker_kind} but no target path")]
    MissingTarget {
        /// Which kind of marker was found ("requires", "ensures", or "requires and ensures").
        marker_kind: &'static str,
    },
}

/// Parsed extern spec entry from doc markers.
#[derive(Debug, Clone)]
pub struct ExternSpecEntry {
    /// Target function path (e.g., "core::option::Option::unwrap")
    pub target_path: String,
    /// Preconditions
    pub requires: Vec<String>,
    /// Postconditions
    pub ensures: Vec<String>,
    /// Parameter names from the extern_spec signature (#2298).
    pub param_names: Option<Vec<String>>,
}

/// Parse extern spec doc markers from a function's doc attributes.
///
/// # Arguments
/// * `docs` - Iterator of doc string lines
///
/// # Returns
/// * `Ok(Some(entry))` - valid extern spec markers found
/// * `Ok(None)` - no extern spec markers present (normal function)
/// * `Err(e)` - incomplete/malformed markers (e.g., requires without target)
pub fn parse_extern_spec_docs<'a>(
    docs: impl Iterator<Item = &'a str>,
) -> Result<Option<ExternSpecEntry>, ParseExternSpecError> {
    let mut target_path = None;
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut param_names = None;

    for doc in docs {
        let doc = doc.trim();

        if let Some(path) = doc.strip_prefix("trust-wp:extern_spec:target=") {
            target_path = Some(path.to_string());
        } else if let Some(params) = doc.strip_prefix("trust-wp:extern_spec:params=") {
            let names: Vec<String> = params
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            if !names.is_empty() {
                param_names = Some(names);
            }
        } else if let Some(req) = doc.strip_prefix("trust-wp:extern_spec:requires=") {
            // Handle multiple semicolon-separated requires
            for r in req.split(';').map(str::trim) {
                if !r.is_empty() {
                    requires.push(r.to_string());
                }
            }
        } else if let Some(ens) = doc.strip_prefix("trust-wp:extern_spec:ensures=") {
            // Handle multiple semicolon-separated ensures
            for e in ens.split(';').map(str::trim) {
                if !e.is_empty() {
                    ensures.push(e.to_string());
                }
            }
        }
    }

    match (target_path, requires.is_empty(), ensures.is_empty()) {
        (Some(target_path), _, _) => Ok(Some(ExternSpecEntry {
            target_path,
            requires,
            ensures,
            param_names,
        })),
        (None, false, false) => Err(ParseExternSpecError::MissingTarget {
            marker_kind: "requires and ensures",
        }),
        (None, false, true) => Err(ParseExternSpecError::MissingTarget {
            marker_kind: "requires",
        }),
        (None, true, false) => Err(ParseExternSpecError::MissingTarget {
            marker_kind: "ensures",
        }),
        (None, true, true) => Ok(None),
    }
}

/// Normalize an extern_spec path to match std_specs lookup format.
///
/// The macro generates paths like `Option::unwrap` which need to be
/// expanded to `core::option::Option::unwrap` for lookup.
pub fn normalize_extern_spec_path(path: &str) -> String {
    let path = path.strip_prefix("::").unwrap_or(path);
    // If already fully qualified (starts with a known root module), return as-is
    if path.starts_with("core::") || path.starts_with("std::") || path.starts_with("alloc::") {
        return path.to_string();
    }

    // Map common type prefixes to their canonical paths
    let path_parts: Vec<&str> = path.split("::").collect();
    if path_parts.is_empty() {
        return path.to_string();
    }

    let type_name = path_parts[0];
    let canonical_prefix = match type_name {
        "Option" => "core::option::Option",
        "Result" => "core::result::Result",
        "Vec" => "alloc::vec::Vec",
        "String" => "alloc::string::String",
        "Box" => "alloc::boxed::Box",
        "Rc" => "alloc::rc::Rc",
        "Arc" => "alloc::sync::Arc",
        "HashMap" => "std::collections::HashMap",
        "HashSet" => "std::collections::HashSet",
        "BTreeMap" => "alloc::collections::BTreeMap",
        "BTreeSet" => "alloc::collections::BTreeSet",
        // Slice types keep their impl form so slice-specific lookup stays
        // separate from Vec fallback aliases.
        "[T]" | "slice" => "core::slice::<impl [T]>",
        // String slice primitive
        "str" => "str",
        _ => return path.to_string(), // Unknown type, return as-is
    };

    if path_parts.len() == 1 {
        canonical_prefix.to_string()
    } else {
        format!("{}::{}", canonical_prefix, path_parts[1..].join("::"))
    }
}

/// Look up an extern spec by path from a pre-built table.
///
/// This function checks the discovered extern specs table.
/// Returns None if no extern spec is found for the path.
pub(crate) fn lookup_extern_spec(specs: &HashMap<String, StdSpec>, path: &str) -> Option<StdSpec> {
    // First try exact match
    if let Some(spec) = specs.get(path) {
        return Some(spec.clone());
    }

    // Try normalized path (removes generics)
    let normalized = normalize_path_for_lookup(path);
    if let Some(spec) = specs.get(&normalized) {
        return Some(spec.clone());
    }

    // Try std -> core remapping (also normalize the remapped path)
    let core_path = path.replace("std::option::", "core::option::");
    let core_path = core_path.replace("std::result::", "core::result::");
    if let Some(spec) = specs.get(&core_path) {
        return Some(spec.clone());
    }
    // Also try normalized version of the remapped path (for paths with generics)
    let normalized_core = normalize_path_for_lookup(&core_path);
    if normalized_core != core_path {
        if let Some(spec) = specs.get(&normalized_core) {
            return Some(spec.clone());
        }
    }

    None
}

/// Result of merging local `extern_spec!` declarations into a base table.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ExternSpecMergeReport {
    /// Local specs that target a built-in path but are not syntactically
    /// compatible with the built-in contract.
    pub incompatible_builtin_conflicts: Vec<String>,
    /// Local specs equivalent to a built-in spec and therefore deduplicated.
    pub compatible_builtin_duplicates: usize,
}

/// Merge local extern specs into a base extern-spec table.
///
/// Equivalent local declarations are accepted as duplicates of built-in specs.
/// Incompatible declarations are reported and not inserted, so real conflicts
/// remain fatal at the call site.
pub fn merge_local_extern_specs(
    base_specs: &mut HashMap<String, StdSpec>,
    local_specs: HashMap<String, StdSpec>,
) -> ExternSpecMergeReport {
    let mut report = ExternSpecMergeReport::default();

    for (path, local_spec) in local_specs {
        if let Some(base_spec) = base_specs.get_mut(&path) {
            if extern_specs_are_compatible(base_spec, &local_spec) {
                *base_spec = merge_compatible_extern_spec(base_spec.clone(), local_spec);
                report.compatible_builtin_duplicates += 1;
            } else {
                report.incompatible_builtin_conflicts.push(path);
            }
        } else {
            base_specs.insert(path, local_spec);
        }
    }

    report
}

/// Conservative compatibility check for duplicate extern specs.
///
/// This intentionally recognizes only syntactically equivalent contracts after
/// whitespace normalization and clause reordering. It does not try to prove
/// logical implication, so incompatible overrides still fail closed.
pub fn extern_specs_are_compatible(left: &StdSpec, right: &StdSpec) -> bool {
    normalized_clause_multiset(&left.requires) == normalized_clause_multiset(&right.requires)
        && normalized_clause_multiset(&left.ensures) == normalized_clause_multiset(&right.ensures)
        && param_names_compatible(left.param_names.as_deref(), right.param_names.as_deref())
}

fn merge_compatible_extern_spec(base_spec: StdSpec, local_spec: StdSpec) -> StdSpec {
    StdSpec {
        requires: base_spec.requires,
        ensures: base_spec.ensures,
        param_names: base_spec.param_names.or(local_spec.param_names),
    }
}

fn param_names_compatible(left: Option<&[String]>, right: Option<&[String]>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => left == right,
        _ => true,
    }
}

fn normalized_clause_multiset(clauses: &[String]) -> BTreeMap<String, usize> {
    let mut normalized = BTreeMap::new();
    for clause in clauses {
        *normalized
            .entry(normalize_contract_clause(clause))
            .or_insert(0) += 1;
    }
    normalized
}

fn normalize_contract_clause(clause: &str) -> String {
    clause.chars().filter(|c| !c.is_whitespace()).collect()
}

/// Normalize a lookup path by removing generic parameters.
/// Delegates to `std_specs::normalize_path` to avoid duplication (#981).
fn normalize_path_for_lookup(path: &str) -> String {
    crate::std_specs::normalize_path(path)
}

/// Convert an ExternSpecEntry to a StdSpec.
impl From<ExternSpecEntry> for StdSpec {
    fn from(entry: ExternSpecEntry) -> Self {
        StdSpec {
            requires: entry.requires,
            ensures: entry.ensures,
            param_names: entry.param_names,
        }
    }
}
