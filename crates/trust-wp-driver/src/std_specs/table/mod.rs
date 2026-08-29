// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Static std-spec lookup table, decomposed by domain.

use super::SpecEntry;

mod boxed;
mod cell;
mod cmp;
mod collections;
mod core_types;
mod hash;
mod iter;
mod logical_map_set;
mod logical_seq_ra;
mod mem_clone_default;
mod nonzero;
mod primitives_checked;
mod primitives_overflow;
mod ptr_slice;
mod string_sync;
mod time;

#[cfg(test)]
mod tests;

/// Ordered table-of-tables for spec lookup.
///
/// First-match precedence is preserved by iterating tables in declaration
/// order. Each domain slice maintains its own internal ordering.
pub(super) static STD_SPEC_TABLES: &[&[SpecEntry]] = &[
    core_types::SPECS,
    boxed::SPECS,
    cell::SPECS,
    iter::SPECS,
    string_sync::SPECS,
    primitives_checked::SPECS,
    primitives_overflow::SPECS,
    nonzero::SPECS,
    time::SPECS,
    ptr_slice::SPECS,
    logical_map_set::SPECS,
    logical_seq_ra::SPECS,
    collections::SPECS,
    mem_clone_default::SPECS,
    // Generic trait specs — MUST be last so type-specific UFCS specs
    // (e.g., Duration's PartialOrd) take first-match precedence.
    cmp::SPECS,
    hash::SPECS,
];
