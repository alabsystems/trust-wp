// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Allow doc_markdown for technical terms and code in documentation
#![allow(clippy::doc_markdown)]
// Allow wildcard patterns in match arms for clarity
#![allow(clippy::match_same_arms)]

//! Standard library spec lookup for trust-wp-driver
//!
//! This module provides spec lookup for Rust standard library types.
//! When the driver encounters calls to std methods (Option::unwrap, Vec::push, etc.),
//! it looks up specs here to inject into the verification conditions.
//!
//! # Phase 1 Approach
//!
//! In Phase 1, specs are looked up by path string matching. This is simple but
//! requires careful path normalization. Future phases may use DefId matching.
//!
//! # Integration Points
//!
//! This module is called from `mir_analysis/` during MIR extraction:
//! 1. When analyzing a function call in MIR
//! 2. Path is extracted from DefId
//! 3. Specs are looked up here
//! 4. Preconditions are added to the current verification obligation
//! 5. Postconditions are used to model the return value

use trust_wp_core::{closure::CaptureInvariant, formula::PureExpr};

/// Contract specs for a standard library function
#[derive(Debug, Clone)]
pub struct StdSpec {
    /// Preconditions that must hold before the call
    pub requires: Vec<String>,
    /// Postconditions that hold after the call
    pub ensures: Vec<String>,
    /// Synthesized type-invariant preconditions for this callee's own
    /// parameters, as structured expressions over the parameter names.
    ///
    /// WHY IT LIVES ON THE CALLEE'S SPEC: the same clause is a PREMISE when
    /// this function's own body is verified and an OBLIGATION at every call
    /// site. Computing it twice lets the grant and the obligation drift apart
    /// the moment either computation's inputs differ, which is the free grant
    /// this field exists to close. Both consumers read THIS vector.
    ///
    /// Empty for std and extern-spec entries: their invariants have no
    /// interpretable body here, so nothing is granted and nothing is owed.
    pub inv_requires: Vec<PureExpr>,
    /// Synthesized type invariants for a CLOSURE's captures, one entry per
    /// invariant-bearing capture.
    ///
    /// WHY IT LIVES ON THE CLOSURE'S SPEC: the closure's body is verified
    /// holding `inv(capture)` for each of these, and the site that BUILDS the
    /// closure is the hand-over that owes them — the same relation
    /// `inv_requires` has to a call site. Both consumers read THIS vector, so
    /// a capture cannot be granted a premise the construction site does not
    /// pay for.
    ///
    /// Empty for everything that is not a local closure.
    pub capture_inv_requires: Vec<CaptureInvariant>,
    /// Parameter names for positional-to-named substitution.
    ///
    /// Standard library functions are not local to the crate, so `arg_names_for_def_id`
    /// returns `None` for them. When a spec references parameter names (e.g., `err`
    /// in `Option::ok_or`), this field provides the names so the substitution map
    /// correctly resolves them to call-site arguments.
    pub param_names: Option<Vec<String>>,
}

impl StdSpec {
    /// Parse a spec string from trust-wp-std into a StdSpec.
    ///
    /// The spec string format is multi-line with `params:`, `requires:`, and
    /// `ensures:` prefixes:
    /// ```text
    /// params: self, err
    /// requires: condition1
    /// ensures: condition2
    /// ```
    ///
    /// The `params:` line provides parameter names for positional-to-named
    /// substitution at call sites. This is needed for standard library functions
    /// where `arg_names_for_def_id` returns `None` (external DefIds).
    ///
    /// Multi-line ensures (match expressions) are collected until the next keyword.
    pub(crate) fn from_spec_string(spec: &str) -> Self {
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut param_names: Option<Vec<String>> = None;

        let mut current_section: Option<&str> = None;
        let mut current_content = String::new();

        let mut block_comment_depth = 0u32;
        for line in spec.lines() {
            let line = strip_spec_comment(line, &mut block_comment_depth);
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }

            if trimmed.starts_with("params:") {
                // Save previous section if any
                if let Some(section) = current_section {
                    let content = current_content.trim().to_string();
                    if !content.is_empty() {
                        if section == "requires" {
                            requires.push(content);
                        } else if section == "ensures" {
                            ensures.push(content);
                        }
                    }
                }
                // Parse comma-separated parameter names
                let names_str = trimmed.trim_start_matches("params:").trim();
                param_names = Some(
                    names_str
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty())
                        .collect(),
                );
                current_section = None;
                current_content = String::new();
            } else if trimmed.starts_with("requires:") {
                // Save previous section if any
                if let Some(section) = current_section {
                    let content = current_content.trim().to_string();
                    if !content.is_empty() {
                        if section == "requires" {
                            requires.push(content);
                        } else if section == "ensures" {
                            ensures.push(content);
                        }
                    }
                }
                current_section = Some("requires");
                current_content = trimmed.trim_start_matches("requires:").trim().to_string();
            } else if trimmed.starts_with("ensures:") {
                // Save previous section if any
                if let Some(section) = current_section {
                    let content = current_content.trim().to_string();
                    if !content.is_empty() {
                        if section == "requires" {
                            requires.push(content);
                        } else if section == "ensures" {
                            ensures.push(content);
                        }
                    }
                }
                current_section = Some("ensures");
                current_content = trimmed.trim_start_matches("ensures:").trim().to_string();
            } else if current_section.is_some() {
                // Continue previous section (for multi-line expressions)
                if !current_content.is_empty() {
                    current_content.push(' ');
                }
                current_content.push_str(trimmed);
            }
        }

        // Save final section
        if let Some(section) = current_section {
            let content = current_content.trim().to_string();
            if !content.is_empty() {
                if section == "requires" {
                    requires.push(content);
                } else if section == "ensures" {
                    ensures.push(content);
                }
            }
        }

        Self {
            requires,
            ensures,
            inv_requires: Vec::new(),
            capture_inv_requires: Vec::new(),
            param_names,
        }
    }
}

/// Strip inline `//` and `/* */` comments from spec strings.
///
/// Specs are plain text (no string literals), so removing comment content
/// avoids parse errors from inline documentation.
fn strip_spec_comment(line: &str, block_comment_depth: &mut u32) -> String {
    let mut output = String::with_capacity(line.len());
    let mut chars = line.chars().peekable();

    while let Some(ch) = chars.next() {
        if *block_comment_depth > 0 {
            if ch == '/' && matches!(chars.peek(), Some('*')) {
                chars.next();
                *block_comment_depth += 1;
                continue;
            }
            if ch == '*' && matches!(chars.peek(), Some('/')) {
                chars.next();
                *block_comment_depth = block_comment_depth.saturating_sub(1);
            }
            continue;
        }

        if ch == '/' {
            match chars.peek() {
                Some('/') => {
                    if output.chars().last().is_some_and(|c| !c.is_whitespace()) {
                        output.push(' ');
                    }
                    break;
                }
                Some('*') => {
                    chars.next();
                    *block_comment_depth = block_comment_depth.saturating_add(1);
                    if output.chars().last().is_some_and(|c| !c.is_whitespace()) {
                        output.push(' ');
                    }
                    continue;
                }
                _ => {}
            }
        }

        output.push(ch);
    }

    output
}

/// Spec table entry: list of path aliases and the spec constant.
type SpecEntry = (&'static [&'static str], &'static str);

mod table;

use table::STD_SPEC_TABLES;

/// Look up specs for a standard library function by its path.
///
/// # Arguments
/// * `path` - The full path of the function (e.g., `core::option::Option::<T>::unwrap`)
///
/// # Returns
/// * `Some(StdSpec)` if specs are found
/// * `None` if the function is not a known std function or has no specs
fn lookup_std_spec(path: &str) -> Option<StdSpec> {
    let normalized = normalize_path(path);
    for table in STD_SPEC_TABLES {
        for (paths, spec) in *table {
            if paths.contains(&normalized.as_str()) {
                let mut result = StdSpec::from_spec_string(spec);
                // Resolve `Self::MIN`/`Self::MAX` to qualified constants (e.g., `u8::MIN`)
                // at lookup time so they are concrete when propagated as call-site
                // assumptions into user functions. (#967)
                resolve_self_type_constants_in_spec(path, &mut result);
                return Some(result);
            }
        }
    }
    None
}

/// Replace `Self::MIN`/`Self::MAX` with qualified integer constants in a spec.
///
/// When a spec for e.g. `u8::wrapping_add` references `Self::MIN@`, this
/// replaces it with `u8::MIN@` so the encoder's `resolve_qualified_int_constant`
/// can resolve it to a concrete value — even when `type_constants` is not set
/// (which happens when verifying user functions that call integer methods).
fn resolve_self_type_constants_in_spec(callee_path: &str, spec: &mut StdSpec) {
    // Extract integer type from the callee path.
    let int_type = INT_TYPES.iter().find(|&&ty| {
        callee_path
            .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
            .any(|segment| segment == ty)
    });

    let Some(int_type) = int_type else {
        return;
    };

    let has_self_constants = spec
        .ensures
        .iter()
        .chain(spec.requires.iter())
        .any(|s| s.contains("Self::MIN") || s.contains("Self::MAX"));

    if !has_self_constants {
        return;
    }

    for s in spec.ensures.iter_mut().chain(spec.requires.iter_mut()) {
        *s = self_constants_at(s, int_type);
    }
}

/// The integer types whose `MIN`/`MAX` a table clause's `Self::MIN`/`Self::MAX`
/// can be spelled at.
const INT_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
];

/// `clause` with `Self::MIN`/`Self::MAX` spelled at `int_type`.
fn self_constants_at(clause: &str, int_type: &str) -> String {
    clause
        .replace("Self::MIN", &format!("{int_type}::MIN"))
        .replace("Self::MAX", &format!("{int_type}::MAX"))
}

/// Every clause text the built-in tables can hand the contract parser: each
/// clause of the std tables and of trust-wp-std's built-in extern specs, and
/// each with `Self::MIN`/`Self::MAX` spelled at every integer type, as a
/// lookup resolves it. No type check of the crate being verified reads one,
/// so none may take the reading a type check gives a clause spelled the same
/// (`callbacks::spec_arith`).
pub fn builtin_clause_texts() -> std::collections::BTreeSet<String> {
    let mut texts = std::collections::BTreeSet::new();
    let specs = STD_SPEC_TABLES
        .iter()
        .flat_map(|table| table.iter())
        .map(|(_, spec)| StdSpec::from_spec_string(spec))
        .chain(crate::extern_specs::builtin_trust_wp_std_specs().into_values());
    for spec in specs {
        for clause in spec.requires.iter().chain(spec.ensures.iter()) {
            if clause.contains("Self::MIN") || clause.contains("Self::MAX") {
                for int_type in INT_TYPES {
                    texts.insert(self_constants_at(clause, int_type));
                }
            }
            texts.insert(clause.clone());
        }
    }
    texts
}

/// Normalize a path by removing generic parameters and the `::` before them.
///
/// Trait-qualified paths (`<Type as Trait>::method`) are preserved because they
/// appear as literal keys in the `STD_SPECS` table. Generic parameters inside
/// the trait qualification are still stripped.
///
/// Examples:
/// - `"core::option::Option::<i32>::unwrap"` -> `"core::option::Option::unwrap"`
/// - `"std::vec::Vec::<T>::push"` -> `"std::vec::Vec::push"`
/// - `"<core::time::Duration as core::ops::Add>::add"` -> `"<core::time::Duration as core::ops::Add>::add"`
pub(crate) fn normalize_path(path: &str) -> String {
    // Slice inherent-method paths need to keep their `::<impl [T]>` form so
    // they continue to route to the slice table instead of collapsing to the
    // Vec-deref aliases that also use `core::slice::first` / `last`.
    if let Some(normalized) = normalize_slice_impl_path(path) {
        return normalized;
    }

    let mut result = String::with_capacity(path.len());
    let mut in_generics: u32 = 0;
    // Track depth of the leading trait-qualified `<T as Trait>` bracket so we
    // preserve its content while still stripping nested generics inside it.
    let mut in_trait_qual: u32 = 0;
    let chars: Vec<char> = path.chars().collect();
    let len = chars.len();
    let mut i = 0;

    // Detect leading `<` which signals a trait-qualified path (UFCS), not a
    // generic parameter.
    let leading_trait_qual = !chars.is_empty() && chars[0] == '<';

    while i < len {
        let c = chars[i];

        // Inside the leading trait-qualification bracket, preserve content
        // but still strip nested generics (e.g. `<Vec<T> as Trait>`).
        if leading_trait_qual && in_trait_qual > 0 {
            match c {
                '<' => {
                    // Nested generic inside trait-qual — strip it.
                    in_generics += 1;
                    i += 1;
                }
                '>' if in_generics > 0 => {
                    in_generics -= 1;
                    i += 1;
                }
                '>' => {
                    // Closing the trait-qualification bracket.
                    in_trait_qual -= 1;
                    result.push(c);
                    i += 1;
                }
                _ if in_generics > 0 => {
                    i += 1;
                }
                _ => {
                    result.push(c);
                    i += 1;
                }
            }
            continue;
        }

        match c {
            '<' if leading_trait_qual && i == 0 => {
                // Opening the trait-qualification bracket — preserve it.
                in_trait_qual += 1;
                result.push(c);
                i += 1;
            }
            ':' if i + 2 < len && chars[i + 1] == ':' && chars[i + 2] == '<' => {
                // Skip `::` before `<` (generic turbofish).
                i += 2;
            }
            '<' => {
                in_generics += 1;
                i += 1;
            }
            '>' => {
                in_generics = in_generics.saturating_sub(1);
                i += 1;
            }
            _ if in_generics > 0 => {
                // Skip characters inside generics
                i += 1;
            }
            _ => {
                result.push(c);
                i += 1;
            }
        }
    }

    // Normalize compatibility shim crate paths to their canonical trust_wp_std
    // equivalents. `creusot_std` and `creusot_contracts` are pure re-export
    // crates — `pub use trust_wp_std::*` — so their def_path_str output should
    // match trust_wp_std table entries. (#967)
    normalize_crate_aliases(&result)
}

fn normalize_slice_impl_path(path: &str) -> Option<String> {
    let rest = path
        .strip_prefix("core::slice::<impl [")
        .or_else(|| path.strip_prefix("std::slice::<impl ["))?;
    let suffix_start = rest.find("]>::")?;
    let suffix = &rest[suffix_start + "]>::".len()..];
    Some(format!("core::slice::<impl [T]>::{suffix}"))
}

/// Replace known re-export crate prefixes with their canonical crate name.
///
/// `creusot_std::X` and `creusot_contracts::X` both resolve to `trust_wp_std::X`
/// because those crates are pure re-export shims (`pub use trust_wp_std::*`).
/// `tcx.def_path_str()` may return either the re-export path or the definition
/// path depending on visibility resolution, so we normalize here.
///
/// Also normalizes `std::` re-exports of `core::` modules within UFCS trait
/// paths: `std::cmp::PartialOrd` → `core::cmp::PartialOrd`, etc. (#967)
/// Slice inherent-method paths keep their `<impl [T]>` form so lookup stays
/// stable for both `core::slice` and `std::slice` MIR forms while preserving
/// the slice-specific table entries.
/// The STD_SPECS table uses `core::` paths canonically, but `tcx.def_path_str()`
/// may produce `std::` paths for traits defined in core but re-exported via std.
fn normalize_crate_aliases(path: &str) -> String {
    const ALIASES: &[(&str, &str)] = &[
        ("creusot_std::", "trust_wp_std::"),
        ("creusot_contracts::", "trust_wp_std::"),
        // Facade crate re-exports (#2335): `trust_wp::ghost::Snapshot::*`
        // and `trust_wp::logic::seq::Seq::*` normalize via this prefix.
        ("trust_wp::", "trust_wp_std::"),
        // std re-exports of core trait modules (#967): MIR paths may use
        // either `std::cmp` or `core::cmp` for the same trait. Normalize
        // to `core::` which the STD_SPECS table uses canonically.
        ("std::cmp::", "core::cmp::"),
        ("std::ops::", "core::ops::"),
        ("std::slice::", "core::slice::"),
    ];
    // Handle both plain paths and UFCS `<Type as Trait>` paths
    let mut result = path.to_string();
    for &(alias, canonical) in ALIASES {
        result = result.replace(alias, canonical);
    }

    // Paths originating inside `trust_wp_std` can surface without an explicit crate
    // prefix (for example `logic::seq::Seq::push_back_ghost`). Normalize those
    // internal paths to the canonical `trust_wp_std::`-prefixed form used in
    // `STD_SPECS` so lookup remains stable across crate contexts. (#1572)
    if let Some(rest) = result.strip_prefix("logic::") {
        return format!("trust_wp_std::logic::{rest}");
    }
    if let Some(rest) = result.strip_prefix("<logic::") {
        return format!("<trust_wp_std::logic::{rest}");
    }
    if let Some(rest) = result.strip_prefix("ghost::") {
        return format!("trust_wp_std::ghost::{rest}");
    }
    if let Some(rest) = result.strip_prefix("<ghost::") {
        return format!("<trust_wp_std::ghost::{rest}");
    }

    // Internal implementation submodule stripping (#2326): inherent `impl`
    // blocks in private submodules (e.g. `trust_wp_std::logic::seq::core`) produce
    // MIR paths like `trust_wp_std::logic::seq::core::push_back_ghost` after the
    // `<impl Type>` generic is stripped by `normalize_path`. The STD_SPECS table
    // uses the parent module path (`trust_wp_std::logic::seq::Seq::push_back_ghost`).
    // Strip known internal submodules to align with the canonical lookup paths.
    const INTERNAL_SUBMODULES: &[(&str, &str)] = &[
        (
            "trust_wp_std::logic::seq::core::",
            "trust_wp_std::logic::seq::Seq::",
        ),
        (
            "trust_wp_std::logic::fmap::core::",
            "trust_wp_std::logic::fmap::FMap::",
        ),
        (
            "trust_wp_std::logic::fset::core::",
            "trust_wp_std::logic::fset::FSet::",
        ),
        (
            "trust_wp_std::ghost::core::",
            "trust_wp_std::ghost::Ghost::",
        ),
    ];
    for &(internal, canonical) in INTERNAL_SUBMODULES {
        if let Some(rest) = result.strip_prefix(internal) {
            return format!("{canonical}{rest}");
        }
    }

    // Facade prelude re-exports (#2335): `use trust_wp::*;` exposes types at
    // the crate root (e.g., `trust_wp::Snapshot::capture`), which after the
    // alias pass becomes `trust_wp_std::Snapshot::capture`. The lookup table
    // uses definition-site paths (`trust_wp_std::ghost::Snapshot::capture`),
    // so insert the missing module prefix for known prelude types.
    const PRELUDE_TYPES: &[(&str, &str)] = &[
        ("Ghost", "ghost"),
        ("Snapshot", "ghost"),
        ("Perm", "ghost::perm"),
        ("Resource", "ghost::resource"),
        ("Seq", "logic::seq"),
        ("FMap", "logic::fmap"),
        ("FSet", "logic::fset"),
        ("Int", "logic"),
        ("Mapping", "logic"),
    ];
    for &(type_name, module) in PRELUDE_TYPES {
        let flat = format!("trust_wp_std::{type_name}::");
        if result.starts_with(&flat) {
            return format!(
                "trust_wp_std::{module}::{}",
                &result["trust_wp_std::".len()..]
            );
        }
        // UFCS: `<trust_wp_std::Type as Trait>::method`
        let ufcs = format!("<trust_wp_std::{type_name} ");
        if result.starts_with(&ufcs) {
            return result.replacen(
                &format!("trust_wp_std::{type_name}"),
                &format!("trust_wp_std::{module}::{type_name}"),
                1,
            );
        }
    }

    result
}

/// Parse a spec string into a PureExpr (test-only convenience).
#[cfg(test)]
fn parse_spec(spec: &str) -> Option<PureExpr> {
    trust_wp_core::contract_parser::parse_contract(spec).ok()
}

/// Combined lookup: extern_specs first, then std_specs.
///
/// This implements the spec lookup priority:
/// 1. User-defined extern_spec! (highest priority)
/// 2. trust-wp-std extern_spec!
/// 3. Hardcoded std_specs (lowest priority)
///
/// # Arguments
/// * `extern_specs` - Optional map of discovered extern_spec! entries
/// * `path` - The full path of the function
///
/// # Returns
/// * `Some(StdSpec)` if specs are found from either source
/// * `None` if no specs are found
pub fn lookup_spec_with_extern(
    extern_specs: Option<&std::collections::HashMap<String, StdSpec>>,
    path: &str,
) -> Option<StdSpec> {
    // Check extern_specs first if provided
    if let Some(specs) = extern_specs {
        if let Some(spec) = crate::extern_specs::lookup_extern_spec(specs, path) {
            return Some(spec);
        }
    }

    // Fall back to hardcoded std_specs
    lookup_std_spec(path)
}

/// Look up ONLY the discovered `extern_spec!` table (no builtin std tables).
///
/// Used for callees from foreign crates that are neither std nor a spec
/// library: user extern specs may describe them, the builtin tables never do.
pub fn lookup_extern_spec_only(
    extern_specs: &std::collections::HashMap<String, StdSpec>,
    path: &str,
) -> Option<StdSpec> {
    crate::extern_specs::lookup_extern_spec(extern_specs, path)
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod tests_ok_or_else;
