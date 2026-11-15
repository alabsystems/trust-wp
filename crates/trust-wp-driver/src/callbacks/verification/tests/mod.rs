// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod clause_enrichment;
mod closure_enrichment;
mod contract_transform;
mod contract_transform_prepass;
mod fail_closed_axioms;
mod fail_fast;
mod loc_budget;
mod logic_fn_skip;
mod logic_fn_verify;
mod loop_exit_assumptions;
mod loop_obligations;
mod mir_retention_contracts;
mod proof_assert_pipeline;
mod recursive_variant;
mod reporting;
mod rustc_callback_harness;
mod skip_decision;
mod ssa_rename;
mod struct_field_map;
mod thir_retention;
mod thir_shadow;
mod type_constants;
