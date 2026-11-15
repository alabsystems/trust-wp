// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure-struct sort registration, constructor/selector declaration, and
//! capture-projection assertions.
//!
//! This subsystem models concrete closure environments as ay algebraic datatypes
//! with built-in constructor/selector semantics. It supports:
//!
//! - [`StructuredSortContext::ClosureStruct`]: Registration via enum dispatch
//! - [`AYEncoder::register_closure_struct_sort`]: Lazy, idempotent sort declaration
//! - [`AYEncoder::assert_capture_projection`]: Layer 2 capture field projection
//! - [`AYEncoder::build_closure_constructor`]: Constructor term assembly
//!
//! # Design (#2151)
//!
//! Closure environments are ay native algebraic datatypes (`Sort::Datatype`)
//! rather than uninterpreted sorts with UF constructor/accessor declarations:
//! the datatype definition carries the round-trip semantics itself, where the
//! UF encoding needs one quantified round-trip axiom per capture field — O(N)
//! quantifiers per closure that dominate solver time.

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort, Term};
use trust_wp_core::closure::CaptureField;

use super::AYEncoder;
use crate::{error::EncodingError, shared_types::CaptureKind};

#[cfg(test)]
mod tests;

/// Structured sort registrations for encoder-level ADT-like modeling.
///
/// Unlike [`super::sort_context::ExprSort`], these carry explicit sort metadata and trigger
/// declaration + axiom emission when registered.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg(test)]
pub(crate) enum StructuredSortContext {
    /// Concrete closure environment sort keyed by a stable closure identity.
    ///
    /// `captures` preserves field order because constructor/selector signatures
    /// are positional (`capture_0`, `capture_1`, ...).
    ClosureStruct {
        def_id: String,
        captures: Vec<CaptureField>,
    },
}

/// Registered closure-struct sort metadata.
///
/// Stored in `SortResolverState` so closure-specific sorts/functions are declared
/// exactly once and can be reused across all VC encodings.
#[derive(Debug, Clone)]
pub(crate) struct RegisteredClosureStructSort {
    pub(crate) sort: Sort,
    pub(crate) captures: Vec<(String, Sort, CaptureKind)>,
    /// The full datatype definition, retained for constructor/selector calls.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) datatype: DatatypeSort,
}

/// Stable symbol suffix for closure-sort declarations.
///
/// Uses FNV-1a over `def_id` to avoid leaking punctuation-heavy identifiers into
/// SMT symbol names while remaining deterministic across runs.
pub(crate) fn closure_symbol_suffix(def_id: &str) -> String {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    for byte in def_id.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{hash:016x}")
}

/// Extract the `ClosureEnv_*` name from a sort, handling both `Sort::Datatype`
/// and `Sort::Uninterpreted` representations (#2151).
///
/// Closure sorts are `Sort::Datatype` at registration time but may appear as
/// `Sort::Uninterpreted` in axiom code
/// (e.g., tag-based `"c..."` decoding in the UF fallback path). This helper
/// normalizes both representations to the underlying name.
pub(crate) fn closure_env_sort_name(sort: &Sort) -> Option<&str> {
    match sort {
        Sort::Uninterpreted(name) if name.starts_with("ClosureEnv_") => Some(name.as_str()),
        Sort::Datatype(dt) if dt.name.starts_with("ClosureEnv_") => Some(dt.name.as_str()),
        _ => None,
    }
}

/// Build a `DatatypeSort` for a closure environment.
fn build_closure_datatype(suffix: &str, captures: &[(String, Sort, CaptureKind)]) -> DatatypeSort {
    let sort_name = format!("ClosureEnv_{suffix}");
    let constructor_name = format!("mk_closure_env_{suffix}");
    let fields: Vec<DatatypeField> = captures
        .iter()
        .enumerate()
        .map(|(index, (_, capture_sort, _))| {
            DatatypeField::new(
                format!("closure_capture_{suffix}_{index}"),
                capture_sort.clone(),
            )
        })
        .collect();
    DatatypeSort::new(
        sort_name,
        vec![DatatypeConstructor::new(constructor_name, fields)],
    )
}

impl AYEncoder {
    /// Register a structured sort in the encoder context.
    ///
    /// Registration is lazy and idempotent: declarations are emitted
    /// only the first time a sort is requested.
    #[cfg(test)]
    pub(crate) fn register_structured_sort(
        &mut self,
        sort: StructuredSortContext,
    ) -> Result<Sort, EncodingError> {
        match sort {
            StructuredSortContext::ClosureStruct { def_id, captures } => {
                self.register_closure_struct_sort(&def_id, &captures)
            }
        }
    }

    /// Register a concrete closure-environment sort as a ay algebraic datatype.
    ///
    /// Declares a single-constructor datatype:
    /// - `ClosureEnv_<hash>` datatype sort
    /// - `mk_closure_env_<hash>(captures...)` constructor
    /// - `closure_capture_<hash>_<i>` selectors (field accessors)
    ///
    /// Round-trip semantics (`selector(constructor(x0, ..., xn)) == xi`) are
    /// built into the datatype definition — no quantified axioms needed (#2151).
    pub(crate) fn register_closure_struct_sort(
        &mut self,
        def_id: &str,
        captures: &[CaptureField],
    ) -> Result<Sort, EncodingError> {
        let ay_captures: Vec<(String, Sort, CaptureKind)> = captures
            .iter()
            .map(|field| {
                (
                    field.name().to_string(),
                    self.sort_from_expr_sort(field.sort().clone()),
                    field.kind(),
                )
            })
            .collect();

        if let Some(existing) = self.closure_struct_sort_cloned(def_id) {
            let existing_cmp: Vec<_> = existing
                .captures
                .iter()
                .map(|(n, s, k)| (n.as_str(), s, *k))
                .collect();
            let new_cmp: Vec<_> = ay_captures
                .iter()
                .map(|(n, s, k)| (n.as_str(), s, *k))
                .collect();
            if existing_cmp != new_cmp {
                return Err(EncodingError::unsupported(format!(
                    "closure sort registration for def_id '{def_id}' changed capture \
                     signature: existing={:?}, new={:?} (#1485)",
                    existing.captures, ay_captures,
                )));
            }
            return Ok(existing.sort.clone());
        }

        let suffix = closure_symbol_suffix(def_id);
        let dt = build_closure_datatype(&suffix, &ay_captures);

        // Declare the datatype with the solver. This registers the constructor
        // and all selectors atomically.
        self.solver.try_declare_datatype(&dt).map_err(|e| {
            EncodingError::unsupported(format!("closure datatype declaration: {e}"))
        })?;

        let sort = Sort::Datatype(dt.clone());

        self.store_closure_struct_sort(
            def_id.to_string(),
            RegisteredClosureStructSort {
                sort: sort.clone(),
                captures: ay_captures,
                datatype: dt,
            },
        );

        Ok(sort)
    }

    /// Build a selector (field access) term for a closure capture field.
    ///
    /// Uses `try_datatype_selector` instead of UF function application.
    pub(crate) fn closure_capture_selector(
        &mut self,
        closure_def_id: &str,
        field_index: usize,
        env_term: Term,
    ) -> Result<Term, EncodingError> {
        let registered = self
            .closure_struct_sort_cloned(closure_def_id)
            .ok_or_else(|| {
                EncodingError::unsupported(format!(
                    "closure struct sort not registered for def_id '{closure_def_id}'"
                ))
            })?;

        if field_index >= registered.captures.len() {
            return Err(EncodingError::unsupported(format!(
                "capture field index {field_index} out of bounds for closure '{closure_def_id}' \
                 with {} captures",
                registered.captures.len()
            )));
        }

        let suffix = closure_symbol_suffix(closure_def_id);
        let selector_name = format!("closure_capture_{suffix}_{field_index}");
        let (_, ref capture_sort, _) = registered.captures[field_index];

        self.solver
            .try_datatype_selector(&selector_name, env_term, capture_sort.clone())
            .map_err(|e| {
                EncodingError::unsupported(format!(
                    "closure capture selector '{selector_name}': {e}"
                ))
            })
    }

    /// Assert capture projection bindings for a registered closure struct sort.
    ///
    /// After a closure call that produces a post-state `post_state_var`, this
    /// method projects each capture field back to a caller-side variable:
    ///
    /// ```text
    /// assert capture_i(post_state) == caller_var_i
    /// ```
    ///
    /// This is the core Layer 2 operation: connecting the closure's mutated
    /// capture fields back to the caller's local variable bindings. (#1489)
    ///
    /// # Arguments
    /// * `closure_def_id` - DefId string identifying which closure struct sort
    /// * `post_state_var` - Name of the SMT variable holding the closure's post-state
    /// * `capture_bindings` - List of `(field_index, caller_var_name)` pairs
    ///
    /// # Errors
    /// Returns `EncodingError` if the closure sort was not registered or if
    /// a requested field index is out of bounds.
    pub(crate) fn assert_capture_projection(
        &mut self,
        closure_def_id: &str,
        post_state_var: &str,
        capture_bindings: &[(usize, String)],
    ) -> Result<(), EncodingError> {
        let registered = self
            .closure_struct_sort_cloned(closure_def_id)
            .ok_or_else(|| {
                EncodingError::unsupported(format!(
                    "closure struct sort not registered for def_id '{closure_def_id}'"
                ))
            })?;

        let post_state_term = self.get_or_declare_var(post_state_var, registered.sort.clone())?;

        let mut projected_terms = vec![None; registered.captures.len()];

        for &(field_index, ref caller_var_name) in capture_bindings {
            let projected_term =
                self.closure_capture_selector(closure_def_id, field_index, post_state_term)?;

            let (_, ref capture_sort, _) = registered.captures[field_index];
            let caller_term = self.get_or_declare_var(caller_var_name, capture_sort.clone())?;
            projected_terms[field_index] = Some(caller_term);

            let eq_term = self.eq_term(projected_term, caller_term);
            self.assert_solver_term("closure_capture_projection", eq_term);
        }

        if projected_terms.iter().all(Option::is_some) {
            let suffix = closure_symbol_suffix(closure_def_id);
            let constructor_name = format!("mk_closure_env_{suffix}");
            let constructor_args: Vec<Term> = projected_terms.into_iter().flatten().collect();
            let reconstructed = self
                .solver
                .try_datatype_constructor(
                    &registered.datatype,
                    &constructor_name,
                    &constructor_args,
                )
                .map_err(|e| {
                    EncodingError::unsupported(format!(
                        "closure constructor '{constructor_name}' for projection: {e}"
                    ))
                })?;
            let reconstruction_eq = self.eq_term(post_state_term, reconstructed);
            self.assert_solver_term(
                "closure_capture_projection_reconstruction",
                reconstruction_eq,
            );
        }

        Ok(())
    }

    /// Build a closure constructor term `mk_closure_env(captures...)`.
    ///
    /// Looks up the registered closure sort and its datatype, then applies
    /// the constructor to the given capture variable terms. Useful for setting
    /// up the initial closure environment in caller verification. (#1489)
    #[cfg(test)]
    pub(crate) fn build_closure_constructor(
        &mut self,
        closure_def_id: &str,
        capture_var_names: &[&str],
    ) -> Result<Term, EncodingError> {
        let registered = self
            .closure_struct_sort_cloned(closure_def_id)
            .ok_or_else(|| {
                EncodingError::unsupported(format!(
                    "closure struct sort not registered for def_id '{closure_def_id}'"
                ))
            })?;

        if capture_var_names.len() != registered.captures.len() {
            return Err(EncodingError::unsupported(format!(
                "expected {} capture vars for closure '{}', got {}",
                registered.captures.len(),
                closure_def_id,
                capture_var_names.len()
            )));
        }

        let suffix = closure_symbol_suffix(closure_def_id);
        let constructor_name = format!("mk_closure_env_{suffix}");

        let mut capture_terms = Vec::with_capacity(capture_var_names.len());
        for (i, var_name) in capture_var_names.iter().enumerate() {
            let (_, ref sort, _) = registered.captures[i];
            let term = self.get_or_declare_var(var_name, sort.clone())?;
            capture_terms.push(term);
        }

        self.safe_datatype_constructor(
            "closure environment constructor",
            &registered.datatype,
            &constructor_name,
            &capture_terms,
        )
        .map_err(|e| {
            EncodingError::unsupported(format!("closure constructor '{constructor_name}': {e}"))
        })
    }
}
