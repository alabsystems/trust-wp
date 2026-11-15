// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-loop final-value integration for function-level mut-borrow verification.

use std::collections::{HashMap, HashSet};

use tracing::trace;
use trust_wp_core::formula::PureExpr;

use super::super::{
    super::mir_analysis::{resolver::ResolveResults, MutBorrowBody},
    parsing::ParsedContract,
};

pub(super) fn inject_post_loop_final_values(
    parsed: &mut ParsedContract,
    loop_final_values: HashMap<String, PureExpr>,
) {
    if let Some(mut_borrow_body) = parsed.mut_borrow.mut_borrow_body.as_mut() {
        merge_into_existing_body(mut_borrow_body, loop_final_values);
        return;
    }

    let mut_ref_param_count = parsed.mut_borrow.mut_ref_param_names.len();
    parsed.mut_borrow.mut_borrow_body = Some(MutBorrowBody {
        final_values: loop_final_values,
        indexed_writes: vec![],
        resolve_results: synthesized_resolve_results(&parsed.mut_borrow.mut_ref_param_names),
        finality: HashMap::new(),
        borrow_id_origins: HashMap::new(),
        delayed_writeback_assumptions: vec![],
        mutation_continued_params: HashSet::new(),
        nested_slot_resolutions: vec![],
        nested_transfer_params: HashSet::new(),
        lent_path_resolutions: vec![],
    });
    trace!(
        "injected post-loop deref final values into mut_borrow_body for \
         function-level verification (resolve_results synthesized for {} &mut params)",
        mut_ref_param_count,
    );
}

fn merge_into_existing_body(
    mut_borrow_body: &mut MutBorrowBody,
    loop_final_values: HashMap<String, PureExpr>,
) {
    let written_names: Vec<_> = loop_final_values.keys().cloned().collect();
    mut_borrow_body.final_values.extend(loop_final_values);

    let resolve_results = mut_borrow_body
        .resolve_results
        .get_or_insert_with(|| ResolveResults {
            writebacks: vec![],
            has_precise_resolve: HashMap::new(),
        });
    for name in written_names {
        resolve_results.has_precise_resolve.insert(name, true);
    }
    trace!(
        "merged post-loop deref final values into existing mut_borrow_body for \
         function-level verification"
    );
}

fn synthesized_resolve_results(mut_ref_param_names: &HashSet<String>) -> Option<ResolveResults> {
    (!mut_ref_param_names.is_empty()).then(|| ResolveResults {
        writebacks: vec![],
        has_precise_resolve: mut_ref_param_names
            .iter()
            .map(|name| (name.clone(), true))
            .collect(),
    })
}
