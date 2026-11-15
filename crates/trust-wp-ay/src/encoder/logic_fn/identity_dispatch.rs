// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Encoder side of logic-function identity (see
//! `trust_wp_core::logic::identity`): a call that still spells a colliding
//! short name is resolved on the encoded receiver, or refused.

use std::sync::atomic::{AtomicUsize, Ordering};

use ay_dpll::api::{Sort, Term};
use trust_wp_core::{
    formula::{resolve_sort_name, ExprSort, PureExpr},
    logic::identity::{
        is_refused_logic_fn_marker, logic_fn_identity_registry, resolve_family_by_receiver,
        LOGIC_FN_EXTERN_DECL_PREFIX, LOGIC_FN_ID_PREFIX,
    },
};

use crate::{encoder::AYEncoder, error::EncodingError};

static PLACEHOLDERS_TOTAL: AtomicUsize = AtomicUsize::new(0);
static PLACEHOLDERS_FOR_IDS: AtomicUsize = AtomicUsize::new(0);

/// The exact name of a nominal solver sort (no path or generic stripping: two
/// types that merely share a last segment must never match).
fn nominal_sort_name(sort: &Sort) -> Option<String> {
    match sort {
        Sort::Datatype(dt) => Some(dt.name.clone()),
        Sort::Uninterpreted(name) => Some(name.clone()),
        _ => None,
    }
}

/// The driver-provided type annotation of a method receiver, looking through
/// `old`, `*`/`^` and outer references (method-call autoderef).
fn receiver_annotation(expr: &PureExpr) -> Option<ExprSort> {
    let sort = match expr {
        PureExpr::Var(_, sort) => sort.clone()?,
        PureExpr::Old(inner) => return receiver_annotation(inner),
        PureExpr::Deref(inner) | PureExpr::Final(inner) => receiver_annotation(inner)?,
        _ => return None,
    };
    let mut sort = sort;
    while let ExprSort::Ref(inner) | ExprSort::MutRef(inner) = sort {
        sort = *inner;
    }
    Some(sort)
}

/// Record an unconstrained placeholder UF created for `name`.
///
/// With `TRUST_WP_LOGIC_PLACEHOLDER_REPORT` set, every placeholder is reported
/// on stderr so corpus runs can count them before/after.
pub(crate) fn note_logic_fn_placeholder(name: &str) {
    let total = PLACEHOLDERS_TOTAL.fetch_add(1, Ordering::Relaxed) + 1;
    let for_id =
        name.starts_with(LOGIC_FN_ID_PREFIX) && !name.starts_with(LOGIC_FN_EXTERN_DECL_PREFIX);
    let ids = if for_id {
        PLACEHOLDERS_FOR_IDS.fetch_add(1, Ordering::Relaxed) + 1
    } else {
        PLACEHOLDERS_FOR_IDS.load(Ordering::Relaxed)
    };
    if std::env::var_os("TRUST_WP_LOGIC_PLACEHOLDER_REPORT").is_some() {
        eprintln!(
            "trust-wp: logic-placeholder name={name} unique_id={for_id} total={total} ids={ids}"
        );
    }
}

/// How a call name relates to the logic-function identity registry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::encoder) enum FamilyResolution {
    /// Not a colliding short name (or already a unique id): no identity decision.
    NotFamily,
    /// The one definition the call denotes.
    Resolved(String),
    /// A colliding name (or a refusal marker) no rule resolves; the message
    /// says why. Callers must refuse (never pick a member).
    Unresolved(String),
}

impl AYEncoder {
    /// Decide which definition a logic-function call NAME denotes, WITHOUT
    /// constructing an error (constructing an `EncodingError` counts an
    /// unsupported-construct skip, so callers that have a sound alternative
    /// route query this first).
    pub(in crate::encoder) fn logic_fn_family_resolution(
        &self,
        name: &str,
        arg_terms: &[Term],
        arg_exprs: Option<&[PureExpr]>,
    ) -> FamilyResolution {
        if is_refused_logic_fn_marker(name) {
            return FamilyResolution::Unresolved(format!(
                "logic function call `{name}` was not resolved to one definition by the driver"
            ));
        }
        if name.starts_with(LOGIC_FN_ID_PREFIX) && !name.starts_with(LOGIC_FN_EXTERN_DECL_PREFIX) {
            return FamilyResolution::NotFamily;
        }
        let Some(registry) = logic_fn_identity_registry() else {
            return FamilyResolution::NotFamily;
        };
        let Some(family) = registry.unresolved_family_for_call(name) else {
            return FamilyResolution::NotFamily;
        };
        let Some(receiver) = arg_terms.first() else {
            return FamilyResolution::Unresolved(format!(
                "logic function call `{name}` names one of several definitions ({}) and was not \
                 resolved to one of them",
                family
                    .iter()
                    .map(|member| member.full_path.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        };
        // The ENCODED term must carry the nominal sort; a driver annotation
        // alone (e.g. a newtype erased to `Int`) never selects an impl, and a
        // disagreeing annotation refuses.
        let term_name = nominal_sort_name(&self.solver.get_sort(*receiver));
        let annotation_name = arg_exprs
            .and_then(|exprs| exprs.first())
            .and_then(receiver_annotation)
            .and_then(|sort| match sort {
                ExprSort::Datatype(id) => Some(resolve_sort_name(id)),
                _ => None,
            });
        let receiver_name = match (term_name, annotation_name) {
            (Some(term), Some(annotation)) if term != annotation => None,
            (Some(term), _) => Some(term),
            (None, _) => None,
        };
        let outcome = resolve_family_by_receiver(family, arg_terms.len(), |sort| {
            match (sort, receiver_name.as_deref()) {
                (ExprSort::Datatype(id), Some(receiver_name)) => {
                    resolve_sort_name(*id) == receiver_name
                }
                _ => false,
            }
        });
        if std::env::var_os("TRUST_WP_LOGIC_IDENTITY_TRACE").is_some() {
            eprintln!(
                "trust-wp: logic-identity encoder call={name} receiver={receiver_name:?} outcome={outcome:?}"
            );
        }
        match outcome {
            Ok(id) => FamilyResolution::Resolved(id),
            Err(message) => {
                FamilyResolution::Unresolved(format!("logic function call `{name}`: {message}"))
            }
        }
    }

    /// Resolve a logic-function call NAME that spells a colliding short name.
    ///
    /// Returns `Ok(None)` when `name` is not a colliding name (or already a
    /// unique id), `Ok(Some(id))` for the one definition it denotes, and an
    /// encoding error when it cannot be resolved — never the first match.
    pub(in crate::encoder) fn resolve_logic_fn_family_call(
        &self,
        name: &str,
        arg_terms: &[Term],
        arg_exprs: Option<&[PureExpr]>,
    ) -> Result<Option<String>, EncodingError> {
        match self.logic_fn_family_resolution(name, arg_terms, arg_exprs) {
            FamilyResolution::NotFamily => Ok(None),
            FamilyResolution::Resolved(id) => Ok(Some(id)),
            FamilyResolution::Unresolved(message) => Err(EncodingError::unsupported(message)),
        }
    }
}
