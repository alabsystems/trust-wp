// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, NAMED_FIELD_LOGIC_FN_PREFIX},
    parse_named_struct_ctor, Pattern, PureExpr,
};

use super::ParsedContract;

/// Rewrite named struct field access expressions to positional tuple-get calls.
///
/// The contract parser lowers `x.inner` to `LogicFnCall("__trust_wp_field_inner", [x])`,
/// while MIR extraction lowers struct field projections to
/// `LogicFnCall("__trust_wp_tuple_get_0", [x])`. These are two unrelated uninterpreted
/// functions in SMT, so the postcondition can never be proved.
///
/// This pass rewrites `__trust_wp_field_<name>` -> `__trust_wp_tuple_get_<index>` using
/// type information from `tcx` to map field names to positional indices.
pub(in crate::callbacks) fn rewrite_named_field_access_expr(
    expr: &PureExpr,
    field_map: &HashMap<String, usize>,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args } => {
            if let Some(field_name) = name.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX) {
                if let Some(&index) = field_map.get(field_name) {
                    return PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(index),
                        args,
                    };
                }
            }

            if let Some((type_name, field_names)) = parse_named_struct_ctor(&name) {
                let reordered = reorder_named_fields_to_positional(&field_names, &args, field_map);
                return PureExpr::LogicFnCall {
                    name: type_name.to_string(),
                    args: reordered,
                };
            }

            PureExpr::LogicFnCall { name, args }
        }
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: rewrite_named_struct_pattern(&arm.pattern, field_map),
                    body: arm.body,
                })
                .collect(),
        },
        other => other,
    })
}

/// Reorder named struct constructor arguments to canonical (definition-order)
/// positions using the field map.
///
/// Given field names `["y", "x"]` and args `[val_y, val_x]`, and a field_map
/// `{"x": 0, "y": 1}`, produces `[val_x, val_y]` (index 0 first, then index 1).
///
/// If any field name is not in the map, falls back to source order (no reordering)
/// to avoid silently corrupting the expression. (#1819)
pub(super) fn reorder_named_fields_to_positional(
    field_names: &[&str],
    args: &[PureExpr],
    field_map: &HashMap<String, usize>,
) -> Vec<PureExpr> {
    if field_names.len() != args.len() {
        // Mismatched lengths - cannot safely reorder, return as-is.
        return args.to_vec();
    }

    // Look up the canonical index for each field name.
    let mut indexed: Vec<Option<(usize, &PureExpr)>> = Vec::with_capacity(field_names.len());
    for (i, fname) in field_names.iter().enumerate() {
        match field_map.get(*fname) {
            Some(&idx) => indexed.push(Some((idx, &args[i]))),
            None => {
                // Unknown field - fall back to source order.
                return args.to_vec();
            }
        }
    }

    // Sort by canonical index and extract the reordered args.
    let mut pairs: Vec<(usize, &PureExpr)> = indexed.into_iter().flatten().collect();
    pairs.sort_by_key(|(idx, _)| *idx);
    pairs.into_iter().map(|(_, expr)| expr.clone()).collect()
}

/// Rewrite named struct constructor patterns to canonical field order.
///
/// For `Constructor { name: "TypeName{y,x}", inner: Tuple([pat_y, pat_x]) }`,
/// rewrites to `Constructor { name: "TypeName", inner: Tuple([pat_x, pat_y]) }`
/// using the field map to determine canonical order. (#1819)
pub(super) fn rewrite_named_struct_pattern(
    pattern: &Pattern,
    field_map: &HashMap<String, usize>,
) -> Pattern {
    match pattern {
        Pattern::Wildcard | Pattern::Binding(_) | Pattern::Literal(_) => pattern.clone(),
        Pattern::Alias { alias, pattern } => Pattern::Alias {
            alias: alias.clone(),
            pattern: Box::new(rewrite_named_struct_pattern(pattern, field_map)),
        },
        Pattern::Tuple(elements) => Pattern::Tuple(
            elements
                .iter()
                .map(|p| rewrite_named_struct_pattern(p, field_map))
                .collect(),
        ),
        Pattern::Constructor { name, inner } => {
            if let Some((type_name, field_names)) = parse_named_struct_ctor(name) {
                // Rewrite named struct pattern to canonical order.
                let rewritten_inner = inner
                    .as_ref()
                    .map(|p| rewrite_named_struct_pattern(p, field_map));
                let reordered_inner =
                    reorder_named_pattern_fields(&field_names, rewritten_inner.as_ref(), field_map);
                Pattern::Constructor {
                    name: type_name.to_string(),
                    inner: reordered_inner.map(Box::new),
                }
            } else {
                Pattern::Constructor {
                    name: name.clone(),
                    inner: inner
                        .as_ref()
                        .map(|p| Box::new(rewrite_named_struct_pattern(p, field_map))),
                }
            }
        }
        // Pattern is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
        _ => pattern.clone(),
    }
}

/// Reorder pattern fields to canonical positional order.
///
/// For a multi-field struct pattern stored as `Tuple([pat_y, pat_x])` with
/// field names `["y", "x"]`, reorders to `Tuple([pat_x, pat_y])` using field_map.
/// Single-field patterns are returned unchanged. (#1819)
fn reorder_named_pattern_fields(
    field_names: &[&str],
    inner: Option<&Pattern>,
    field_map: &HashMap<String, usize>,
) -> Option<Pattern> {
    let inner = inner?;

    match inner {
        Pattern::Tuple(elements) if elements.len() == field_names.len() => {
            // Multi-field: reorder elements by canonical index.
            let mut indexed: Vec<(usize, &Pattern)> = Vec::with_capacity(field_names.len());
            for (i, fname) in field_names.iter().enumerate() {
                match field_map.get(*fname) {
                    Some(&idx) => indexed.push((idx, &elements[i])),
                    None => return Some(inner.clone()), // Unknown field - no reorder.
                }
            }
            indexed.sort_by_key(|(idx, _)| *idx);
            let reordered: Vec<Pattern> = indexed.into_iter().map(|(_, p)| p.clone()).collect();
            if reordered.len() == 1 {
                Some(reordered.into_iter().next().expect("len == 1"))
            } else {
                Some(Pattern::Tuple(reordered))
            }
        }
        _ if field_names.len() == 1 => {
            // Single-field struct: no reordering needed (always index 0).
            Some(inner.clone())
        }
        _ => Some(inner.clone()),
    }
}

/// Apply named field access rewriting to all expressions in a parsed contract.
pub(super) fn rewrite_named_field_access_in_contract(
    parsed: &mut ParsedContract,
    field_map: &HashMap<String, usize>,
) {
    if field_map.is_empty() {
        return;
    }
    parsed.rewrite_all_exprs(|expr| rewrite_named_field_access_expr(expr, field_map));
}
