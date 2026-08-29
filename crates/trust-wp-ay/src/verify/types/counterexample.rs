// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample types for failed verification results.
//!
//! When verification fails (SAT model found for the negated VC), the SMT
//! solver provides concrete variable assignments that witness the failure.
//! These types represent that information with source-level origin tracking.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::Model;
use num_traits::ToPrimitive;

use crate::{encoder::AYEncoder, span::SourceSpan};

/// Origin of a variable in counterexample output.
///
/// When verification fails, trust-wp extracts counterexample values that
/// witness the failure. This enum tracks where each variable originated
/// from, enabling meaningful error messages that reference source locations.
///
/// # Example Usage
///
/// When a postcondition fails, the counterexample might include:
/// - `Parameter { name: "x", .. }` - the function argument
/// - `ReturnValue` - the computed return value
/// - `Internal` - intermediate values from the encoding
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum VarOrigin {
    /// Function parameter from the signature.
    ///
    /// The `name` matches the parameter name in source code.
    Parameter {
        name: String,
        span: Option<SourceSpan>,
    },
    /// Variable from a `#[requires(...)]` precondition expression.
    ///
    /// The `contract_idx` identifies which requires clause (0-indexed).
    Precondition {
        contract_idx: usize,
        span: Option<SourceSpan>,
    },
    /// Variable from a `#[ensures(...)]` postcondition expression.
    ///
    /// The `contract_idx` identifies which ensures clause (0-indexed).
    Postcondition {
        contract_idx: usize,
        span: Option<SourceSpan>,
    },
    /// Variable from a `#[invariant(...)]` loop invariant.
    Invariant { span: Option<SourceSpan> },
    /// MIR local variable (internal to rustc).
    ///
    /// The `local` is the MIR local index (e.g., `_0` for return, `_1` for first arg).
    MirLocal {
        local: u32,
        span: Option<SourceSpan>,
    },
    /// Return value of the function (corresponds to MIR `_0`).
    ReturnValue,
    /// Internal variable created during SMT encoding.
    ///
    /// These don't map directly to source code (e.g., intermediate
    /// arithmetic results, heap abstractions).
    Internal,
}

/// Information about a violated postcondition.
#[derive(Debug, Clone)]
pub struct PostconditionInfo {
    /// Which ensures clause was violated (0-indexed)
    pub clause_idx: usize,
    /// The contract text (original string from attribute)
    pub contract_text: String,
    /// Source span of the ensures attribute
    pub span: Option<SourceSpan>,
}

/// A single value in a counterexample, paired with its origin.
///
/// When verification fails, the SMT solver provides a model (set of
/// variable assignments) that witnesses the failure. Each assignment
/// is represented as a `CounterexampleValue` with:
/// - The variable name as it appears in the SMT encoding
/// - The concrete value from the model
/// - Optional origin information for error reporting
///
/// # Example
///
/// For a failed postcondition `result > x`, the counterexample might show:
/// - `CounterexampleValue { name: "x", value: CounterexampleType::Int(5.into()), origin: Some(Parameter { .. }) }`
/// - `CounterexampleValue { name: "result", value: CounterexampleType::Int(3.into()), origin: Some(ReturnValue) }`
#[derive(Debug, Clone)]
pub struct CounterexampleValue {
    /// Variable name from the SMT encoding.
    ///
    /// May include prefixes like `old_`, `_current`, `_final` depending
    /// on the encoding context.
    pub name: String,
    /// Concrete value from the SMT model.
    pub value: CounterexampleType,
    /// Origin of this variable for error reporting.
    ///
    /// `None` for internal variables that don't map to source code.
    pub origin: Option<VarOrigin>,
}

/// Type of counterexample value.
///
/// When verification fails with a SAT result, the SMT solver provides
/// concrete values for variables that witness the failure. trust-wp reuses the
/// solver-native recursive model value surface so counterexamples stay lossless
/// across integers, bitvectors, sequences, arrays, datatypes, and scalars.
pub use ay_dpll::api::ModelValue as CounterexampleType;

/// Counterexample extracted from SAT model
#[derive(Debug, Clone)]
pub struct Counterexample {
    /// Structured counterexample values with origin info
    pub values: Vec<CounterexampleValue>,
    /// The postcondition that was violated (if known)
    pub violated_postcondition: Option<PostconditionInfo>,
}

impl Counterexample {
    /// Create from a ay model.
    ///
    /// This creates a basic counterexample without origin information.
    /// Use `with_origins` to add variable origin tracking.
    pub(in crate::verify) fn from_model(model: Option<Model>) -> Self {
        Self::from_model_impl(model, None)
    }

    /// Create a counterexample using the encoder shell's active source
    /// bindings. Stale constants left behind by sort upgrades are omitted;
    /// the active declaration is projected back to its source spelling.
    pub(in crate::verify) fn from_model_with_active_source_identities(
        model: Option<Model>,
        active_source_identities: &HashMap<String, Vec<String>>,
    ) -> Self {
        let active_source_names = active_source_identities
            .values()
            .flatten()
            .cloned()
            .collect::<HashSet<_>>();
        Self::from_model_impl(
            model,
            Some((active_source_identities, &active_source_names)),
        )
    }

    pub(in crate::verify) fn from_encoder_model(encoder: &AYEncoder, model: Option<Model>) -> Self {
        let (active_source_identities, active_source_names) = encoder.active_source_projection();
        Self::from_model_impl(
            model,
            Some((&active_source_identities, &active_source_names)),
        )
    }

    fn from_model_impl(
        model: Option<Model>,
        active_projection: Option<(&HashMap<String, Vec<String>>, &HashSet<String>)>,
    ) -> Self {
        let mut values = Vec::new();

        if let Some(m) = model {
            let (encoded_base_sources, encoded_derived_sources) =
                model_source_identity_inventory(&m);
            for (name, value) in m.iter_ints() {
                push_value(
                    &mut values,
                    name,
                    CounterexampleType::Int(value.clone()),
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
            for (name, value) in m.iter_bools() {
                push_value(
                    &mut values,
                    name,
                    CounterexampleType::Bool(value),
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
            for (name, value) in m.iter_reals() {
                push_value(
                    &mut values,
                    name,
                    CounterexampleType::Real(value.clone()),
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
            for (name, (value, width)) in m.iter_bvs() {
                push_value(
                    &mut values,
                    name,
                    CounterexampleType::BitVec {
                        value: value.clone(),
                        width: *width,
                    },
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
            for (name, value) in m.iter_strings() {
                push_value(
                    &mut values,
                    name,
                    CounterexampleType::String(value.to_string()),
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
            for (name, value) in m.iter_fps() {
                push_value(
                    &mut values,
                    name,
                    value.clone(),
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
            for (name, value) in m.iter_seqs() {
                push_value(
                    &mut values,
                    name,
                    value.clone(),
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
            for (name, value) in m.iter_arrays() {
                push_value(
                    &mut values,
                    name,
                    value.clone(),
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
            for (name, value) in m.iter_datatypes() {
                push_value(
                    &mut values,
                    name,
                    value.clone(),
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
            for (name, value) in m.iter_uninterpreteds() {
                push_value(
                    &mut values,
                    name,
                    CounterexampleType::Uninterpreted(value.to_string()),
                    active_projection,
                    &encoded_base_sources,
                    &encoded_derived_sources,
                );
            }
        }

        values.sort_by(|left, right| left.name.cmp(&right.name));

        Counterexample {
            values,
            violated_postcondition: None,
        }
    }

    /// Create an empty counterexample (no variable assignments).
    pub fn empty() -> Self {
        Counterexample {
            values: Vec::new(),
            violated_postcondition: None,
        }
    }

    /// Add origin information for a variable.
    ///
    /// Call this after `from_model` to annotate variables with their origins.
    pub fn set_origin(&mut self, var_name: &str, origin: VarOrigin) {
        for val in &mut self.values {
            if val.name == var_name {
                val.origin = Some(origin);
                return;
            }
        }
    }

    /// Set the violated postcondition information.
    pub fn set_violated_postcondition(&mut self, info: PostconditionInfo) {
        self.violated_postcondition = Some(info);
    }

    /// Iterate over integer variable assignments.
    pub fn int_assignments(&self) -> impl Iterator<Item = (&str, i64)> {
        self.values.iter().filter_map(|v| match &v.value {
            CounterexampleType::Int(n) => Some((v.name.as_str(), n.to_i64().unwrap_or(i64::MAX))),
            _ => None,
        })
    }

    /// Iterate over boolean variable assignments.
    pub fn bool_assignments(&self) -> impl Iterator<Item = (&str, bool)> {
        self.values.iter().filter_map(|v| match &v.value {
            CounterexampleType::Bool(b) => Some((v.name.as_str(), *b)),
            _ => None,
        })
    }
}

fn push_value(
    values: &mut Vec<CounterexampleValue>,
    name: &str,
    value: CounterexampleType,
    active_projection: Option<(&HashMap<String, Vec<String>>, &HashSet<String>)>,
    encoded_base_sources: &HashSet<String>,
    encoded_derived_sources: &HashSet<String>,
) {
    if let Some((active, active_source_names)) = active_projection {
        if let Some(sources) = active.get(name) {
            for source in sources {
                values.push(CounterexampleValue {
                    name: source.clone(),
                    value: value.clone(),
                    origin: None,
                });
            }
            return;
        }
        if let Some(decoded) = crate::source_symbol::decode_identity(name) {
            match decoded {
                crate::source_symbol::DecodedSourceIdentity::Base { source }
                    if !active_source_names.contains(&source)
                        && !encoded_derived_sources.contains(&source) =>
                {
                    // Some verification paths intentionally remove a source
                    // shell binding before extraction. A base declaration is
                    // still the authoritative model value when no replacement
                    // binding for that source exists.
                    values.push(CounterexampleValue {
                        name: source,
                        value,
                        origin: None,
                    });
                }
                crate::source_symbol::DecodedSourceIdentity::Base { .. }
                | crate::source_symbol::DecodedSourceIdentity::Derived { .. } => {
                    // The source has another active identity, or this is an
                    // inactive derived auxiliary: omit the stale phantom.
                }
            }
            return;
        }
        if active_source_names.contains(name)
            || encoded_base_sources.contains(name)
            || encoded_derived_sources.contains(name)
        {
            // Source variables are always declared under solver-private
            // identities. A raw constant with the same spelling is therefore
            // an encoder-internal symbol, not a second source assignment.
            // Suppress it instead of emitting two indistinguishable values
            // whose types or assignments may disagree.
            return;
        }
    }
    let projected_name = active_projection.map_or_else(
        || crate::source_symbol::source_name(name).into_owned(),
        |_| name.to_string(),
    );
    values.push(CounterexampleValue {
        name: projected_name,
        value,
        origin: None,
    });
}

fn model_source_identity_inventory(model: &Model) -> (HashSet<String>, HashSet<String>) {
    let mut base_sources = HashSet::new();
    let mut derived_sources = HashSet::new();
    macro_rules! record_names {
        ($values:expr) => {
            for (name, _) in $values {
                match crate::source_symbol::decode_identity(name) {
                    Some(crate::source_symbol::DecodedSourceIdentity::Base { source }) => {
                        base_sources.insert(source);
                    }
                    Some(crate::source_symbol::DecodedSourceIdentity::Derived {
                        source, ..
                    }) => {
                        derived_sources.insert(source);
                    }
                    None => {}
                }
            }
        };
    }
    record_names!(model.iter_ints());
    record_names!(model.iter_bools());
    record_names!(model.iter_reals());
    record_names!(model.iter_bvs());
    record_names!(model.iter_strings());
    record_names!(model.iter_fps());
    record_names!(model.iter_seqs());
    record_names!(model.iter_arrays());
    record_names!(model.iter_datatypes());
    record_names!(model.iter_uninterpreteds());
    (base_sources, derived_sources)
}
