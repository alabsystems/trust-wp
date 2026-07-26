// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT encoding context and pattern binding helpers.

use std::collections::HashSet;

use crate::formula::Pattern;

/// Extract variable bindings from a match pattern into a set.
///
/// Used to exclude pattern-bound variables from free variable collection.
/// For example, in `match opt { Some(x) => x + 1, ... }`, the variable `x`
/// is bound by the pattern and should not be treated as a free variable.
pub(super) fn extract_pattern_bindings(pattern: &Pattern, bindings: &mut HashSet<String>) {
    match pattern {
        Pattern::Wildcard | Pattern::Literal(_) => {}
        Pattern::Binding(name) => {
            bindings.insert(name.clone());
        }
        Pattern::Alias { alias, pattern } => {
            bindings.insert(alias.clone());
            extract_pattern_bindings(pattern, bindings);
        }
        Pattern::Constructor { inner, .. } => {
            if let Some(inner_pat) = inner {
                extract_pattern_bindings(inner_pat, bindings);
            }
        }
        Pattern::Tuple(elements) => {
            for elem in elements {
                extract_pattern_bindings(elem, bindings);
            }
        }
    }
}

/// Context for SMT encoding — tracks whether we're in an "old" context
/// (evaluating pre-state values in a postcondition).
///
/// Used by both SMT-LIB2 text generation and variable sort collection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SmtContext {
    /// Normal context - variables use their current names
    Normal,
    /// Old context - variables get "old_" prefix for pre-state values
    Old,
}
