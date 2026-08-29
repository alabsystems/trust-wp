// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost substitution derivation helpers.
//!
//! Derives missing `^*name` substitutions from stable `*name = ^^name` patterns
//! produced during ghost context extraction.

use std::collections::HashMap;

use trust_wp_core::formula::PureExpr;

/// Derive missing `^*name` substitutions from stable `*name = ^^name` patterns.
///
/// Ghost context extraction often produces deref substitutions such as
/// `*g2 -> ^^g2` after writes through `Ghost<&mut T>`. Postconditions that use
/// `^*g2` encode to `Final(Deref(Var("g2")))`, so we also need a corresponding
/// substitution key `^*g2` to connect that symbol to the extracted state.
///
/// To stay conservative, only derive when RHS is exactly `Final(Final(Var(name)))`
/// for the same base name as the `*name` key.
pub(in crate::callbacks) fn derive_final_deref_ghost_substitutions(
    substitutions: &mut HashMap<String, PureExpr>,
) {
    fn is_simple_ident(name: &str) -> bool {
        let mut chars = name.chars();
        let Some(first) = chars.next() else {
            return false;
        };
        (first == '_' || first.is_ascii_alphabetic())
            && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    }

    let mut derived = Vec::new();
    for (lhs, rhs) in substitutions.iter() {
        let Some(base) = lhs.strip_prefix('*') else {
            continue;
        };
        if !is_simple_ident(base) {
            continue;
        }
        let final_deref_key = format!("^*{base}");
        if substitutions.contains_key(&final_deref_key) {
            continue;
        }

        let matches_double_final_same_base = match rhs {
            PureExpr::Final(inner) => match inner.as_ref() {
                PureExpr::Final(inner2) => {
                    matches!(inner2.as_ref(), PureExpr::Var(name, _) if name == base)
                }
                _ => false,
            },
            _ => false,
        };
        if matches_double_final_same_base {
            derived.push((final_deref_key, rhs.clone()));
            continue;
        }

        // Ghost block writes: when `*base` maps to a concrete value (e.g.,
        // `*g2 → Int(1)` from `**g2 = 1` inside a ghost block), derive
        // `^*base → value`. Ghost writes constrain the final state of the
        // inner reference, so the deref substitution directly determines
        // the final-deref value used in postconditions like `(^*g2) == 1`.
        // (#2671)
        let is_concrete_write = !matches!(rhs, PureExpr::Var(name, _) if name == base)
            && !matches!(rhs, PureExpr::Final(_));
        if is_concrete_write {
            derived.push((final_deref_key, rhs.clone()));
        }
    }

    for (key, value) in derived {
        substitutions.insert(key, value);
    }
}
