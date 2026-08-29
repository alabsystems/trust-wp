// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Span utility helpers for ghost block location analysis.
//!
//! Provides span-ordering predicates and conversion from rustc `Span` to the
//! encoder's `SourceSpan`, used by ghost context extraction and verification
//! error enrichment.

use rustc_span::Span;
use trust_wp_ay::SourceSpan;

pub(in crate::callbacks) fn ghost_block_precedes_cutoff(
    block_span: Span,
    cutoff_span: Span,
) -> bool {
    let block = block_span.source_callsite();
    let cutoff = cutoff_span.source_callsite();
    if block.is_dummy() || cutoff.is_dummy() {
        return true;
    }
    block.hi() <= cutoff.lo()
}

/// Check if a ghost block *contains* the cutoff span.
///
/// When a `proof_assert!` is inside a `ghost! { ... }` block, the ghost block's
/// span encloses the proof_assert span. In this case, the ghost block's method
/// calls (e.g., `insert_ghost`, `len_ghost`) that precede the proof_assert need
/// to be captured as ghost context. The extraction `stop_span` should be the
/// cutoff (proof_assert) span, not the ghost block's end. (#1581)
pub(in crate::callbacks) fn ghost_block_contains_cutoff(
    block_span: Span,
    cutoff_span: Span,
) -> bool {
    let block = block_span.source_callsite();
    let cutoff = cutoff_span.source_callsite();
    if block.is_dummy() || cutoff.is_dummy() {
        return false;
    }
    block.lo() <= cutoff.lo() && cutoff.hi() <= block.hi()
}

/// Convert a rustc `Span` to a `SourceSpan` for embedding in `EncodingError`.
pub(in crate::callbacks) fn rustc_span_to_source_span(
    source_map: &rustc_span::source_map::SourceMap,
    span: Span,
) -> Option<SourceSpan> {
    if span.is_dummy() {
        return None;
    }
    let loc = source_map.lookup_char_pos(span.lo());
    let file_name = match &loc.file.name {
        rustc_span::FileName::Real(real) => real.local_path().map(|p| p.display().to_string()),
        _ => None,
    };
    // Source line/column values are always small enough for u32.
    #[allow(clippy::cast_possible_truncation)]
    let (line, col) = (loc.line as u32, loc.col_display as u32 + 1);
    Some(SourceSpan::with_location(
        file_name.as_deref().unwrap_or("<unknown>"),
        line,
        col, // 1-indexed
    ))
}
