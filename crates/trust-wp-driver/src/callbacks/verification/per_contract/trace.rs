// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Diagnostic tracing for a parsed per-contract verification unit.

use tracing::{debug, trace};

use crate::callbacks::parsing::ParsedContract;

pub(super) fn trace_parsed_contract_state(parsed: &ParsedContract, def_path: &str, loc: &str) {
    debug!(def_path = %def_path, loc = %loc, "verifying function");
    if let Some(ref mut_borrow) = parsed.mut_borrow.mut_borrow_body {
        trace!(
            "mutable borrow function, final_values: {:?}",
            mut_borrow.final_values
        );
        if !mut_borrow.indexed_writes.is_empty() {
            trace!("indexed_writes: {:?}", mut_borrow.indexed_writes);
        }
    }
    if let Some(ref loop_analysis) = parsed.loop_fields.loop_analysis {
        if loop_analysis.has_loops {
            debug!(loops = loop_analysis.loops.len(), "function has loops");
            for (i, loop_info) in loop_analysis.loops.iter().enumerate() {
                trace!(
                    loop_idx = i,
                    header = loop_info.header.as_u32(),
                    body_blocks = loop_info.body_blocks.len(),
                    "loop info"
                );
            }
        }
    }
    if !parsed.loop_fields.invariants.is_empty() {
        debug!(
            count = parsed.loop_fields.invariants.len(),
            "invariant(s) specified"
        );
    }
    if !parsed.loop_fields.variants.is_empty() {
        debug!(
            count = parsed.loop_fields.variants.len(),
            "variant(s) specified (termination proof)"
        );
    }
}
