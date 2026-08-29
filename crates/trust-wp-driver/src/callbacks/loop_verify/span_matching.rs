// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Span-based per-loop invariant and variant selection.

use trust_wp_ay::EncodingError;
use trust_wp_core::formula::PureExpr;

/// Find the expressions for a specific MIR loop by matching its header
/// position against HIR loop expression spans.
///
/// Uses span containment: a MIR loop header at byte position P matches a per-loop
/// entry (start, end, exprs) if start ≤ P < end. When multiple entries
/// contain P (nested loops), the tightest span wins (smallest end - start).
///
/// Prevents false inheritance: if there is a loop (from `all_loop_spans`) that
/// contains the header position and is tighter than the best expression-bearing
/// loop, the MIR loop is nested inside a non-annotated loop — return empty.
///
/// Returns empty if no containing span is found.
fn find_loop_scoped_exprs<'a>(
    per_loop_exprs: &'a [(u32, u32, Vec<PureExpr>)],
    all_loop_spans: &[(u32, u32)],
    header_byte_pos: u32,
) -> &'a [PureExpr] {
    let mut best_exprs: Option<(u32, &'a [PureExpr])> = None;
    for (start, end, exprs) in per_loop_exprs {
        if *start <= header_byte_pos && header_byte_pos < *end {
            let span_size = end - start;
            match best_exprs {
                None => best_exprs = Some((span_size, exprs.as_slice())),
                Some((best_size, _)) if span_size < best_size => {
                    best_exprs = Some((span_size, exprs.as_slice()));
                }
                _ => {}
            }
        }
    }

    let Some((expr_span_size, exprs)) = best_exprs else {
        return &[];
    };

    let mut tightest_loop_size = u32::MAX;
    for (start, end) in all_loop_spans {
        if *start <= header_byte_pos && header_byte_pos < *end {
            let span_size = end - start;
            if span_size < tightest_loop_size {
                tightest_loop_size = span_size;
            }
        }
    }

    if tightest_loop_size < expr_span_size {
        return &[];
    }

    exprs
}

/// Find the invariants for a specific MIR loop by matching its header position
/// against HIR loop expression spans.
pub(super) fn find_loop_invariants(
    per_loop_invariants: &[(u32, u32, Vec<PureExpr>)],
    all_loop_spans: &[(u32, u32)],
    header_byte_pos: u32,
) -> Vec<PureExpr> {
    find_loop_scoped_exprs(per_loop_invariants, all_loop_spans, header_byte_pos).to_vec()
}

fn select_single_loop_variant<'a>(
    variants: &'a [PureExpr],
    context: &str,
) -> Result<Option<&'a PureExpr>, EncodingError> {
    match variants {
        [] => Ok(None),
        [variant] => Ok(Some(variant)),
        _ => Err(EncodingError::Unsupported {
            message: format!(
                "multiple #[variant(...)] clauses on the same {context} are not yet supported"
            ),
            span: None,
            contract_text: None,
        }),
    }
}

pub(super) fn select_loop_variant<'a>(
    flat_variants: &'a [PureExpr],
    per_loop_variants: &'a [(u32, u32, Vec<PureExpr>)],
    all_loop_spans: &[(u32, u32)],
    loop_count: usize,
    header_byte_pos: Option<u32>,
) -> Result<Option<&'a PureExpr>, EncodingError> {
    if let (false, Some(header_pos)) = (per_loop_variants.is_empty(), header_byte_pos) {
        return select_single_loop_variant(
            find_loop_scoped_exprs(per_loop_variants, all_loop_spans, header_pos),
            "loop",
        );
    }

    if loop_count > 1 && !flat_variants.is_empty() {
        return Err(EncodingError::Unsupported {
            message: "multi-loop termination variants require per-loop loop-span mapping; reusing the first parsed variant across loops is no longer allowed (#752)".to_string(),
            span: None,
            contract_text: None,
        });
    }

    select_single_loop_variant(flat_variants, "loop")
}
