// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for trust-wp-ay SMT encoding.
//!
//! Test modules:
//! - `basic`: Basic encoding tests for primitives, arithmetic, and boolean operations
//! - `sep_logic`: Separation logic encoding tests (magic wand, points-to, etc.)
//! - `borrow`: Mutable borrow verification tests
//! - `borrow_finality_soundness`: Borrow finality prophecy propagation soundness tests (#2181)
//! - `loops`: Loop invariant verification tests
//! - `loops_compositional`: Compositional loop + post-loop verification tests (#2085)
//! - `loops_compositional_creusot`: Real Creusot compat pattern tests for compositional loops (#2085)
//! - `loops_initialization_proofs`: Initialization VC and loop entry reachability tests (#2133)
//! - `loops_logic_fn`: Loop + logic function axiom integration tests (#739)
//! - `encoding`: Error display, deref/final, view, and Vec verification tests
//! - `error_formatting`: Direct `EncodingError` display formatting tests (#1481)
//! - `quantifiers`: Quantifier and match expression encoding tests
//! - `seq_encoding`: Sequence (Seq) encoding tests (view, len, `push_back`, axioms)
//! - `heap_encoding`: Heap operation encoding tests (alloc, dealloc, permissions)
//! - `logic_fn`: Logic function call and registration tests
//! - `verification`: End-to-end verification tests
//! - `verification_closure`: Closure verification regression tests (#568)
//! - `match_encoding`: Pattern match encoding tests
//! - `match_soundness_audit`: Match encoding and capture projection soundness tests (#1560)
//! - `match_tuple_sort`: Tuple element range-sort inference tests (#994)
//! - `solver_axiom_scaling`: Solver refinement loop scaling and axiom witness binding scaling (#901)
//! - `sort_context`: Sort inference walker tests (`collect_seq_view_names`, `collect_bool_hints`)
//! - `resolve_var_sort`: Direct tests for `AYEncoder::resolve_var_sort` fallback chain (#1319)
//! - `performance_proofs`: Algorithmic complexity bounds and performance regression tests (#564)
//! - `performance_hotspot_proofs`: Focused #901 hotspot scaling proofs
//! - `loop_sort_inference`: Loop-context sort inference regression tests
//! - `loops_parameter_coverage`: Focused loop-parameter path coverage tests (#864)
//! - `memory_model_safety`: Memory model safety boundary tests (constrained-init, frame isolation)
//! - `memory_model_strengthening`: Focused memory-model assertion-strengthening tests
//! - `memory_model_dealloc_soundness`: Store-after-dealloc soundness and permission boundary tests
//! - `memory_model_edge_cases`: Memory model edge-case boundary tests (store-at-unallocated, double-alloc)
//! - `memory_model_points_to_boundaries`: points-to permission boundary strengthening tests
//! - `memory_model_symbolic`: Symbolic address memory-model regressions for ROW behavior (#1633, #1733)
//! - `memory_verification`: Memory verification: pipeline growth, model scaling, pool bounds (#901)
//! - `memory_lifecycle_proofs`: Memory lifecycle, panic isolation, and resource release proofs (#901)
//! - `memory_raii_guards`: RAII guard state invariants, encoder state isolation, scaling bounds (#901)
//! - `option_result_shared_spec_regressions`: Option/Result shared spec regression tests
//! - `param_sort_infer_nesting`: Seq sort inference through PureExpr nesting variants (#1552)
//! - `produces_transitivity`: semantic regression for `produces` transitivity (#934)
//! - `proof_assert_path_conditions`: Regression tests for proof_assert path condition propagation (#1457)
//! - `proof_coverage_1667`: focused proof-coverage tests for #1667 fallback/quantifier paths
//! - `proof_coverage_gaps`: Tests for zero-coverage functions identified in #901 audit
//! - `quantifier_sort_regressions`: Quantifier sort inference regression tests (#544, #560, #579)
//! - `coverage_gaps`: Tests for functions with zero direct coverage (#711)
//! - `encoding_error_paths`: Error-path coverage for LetAssume/LetObligation encoding (#904)
//! - `ghost_flatten_proofs`: Tests for `flatten_ghost_implications` and constant substitution (#901)
//! - `let_assume_obligation`: LetAssume/LetObligation encoding and scoping regression tests (#815)
//! - `div_mod_zero`: Regression tests for implicit divisor!=0 obligations on Div/Mod (#931)
//! - `de_morgan_proofs`: Formal verification of De Morgan existential negation (#970)
//! - `trigger_synthesis`: Trigger synthesis unit tests (extracted from encoder/trigger.rs, #1669)
//! - `trigger_synthesis_audit`: Trigger synthesis edge case audit (#1018)
//! - `body_break_audit`: Body-break `condition_is_body_break` algorithm audit tests (#1385, #1386)
//! - `container_element_invariant`: Container element invariant axiom tests (#P1-433)
//! - `closure_body_inline`: Closure body inlining tests for postcondition_once/mut (#2151)
//! - `closure_ensures_fallback`: ensures_exprs UF-fallback and result-param collision tests (#2124)
//! - `closure_fnonce_edge_cases`: FnOnce/Box capture edge cases, nested mut-ref captures, closure law chain (#2668)
//! - `closure_layer2`: Closure Layer-2 capture projection tests (#1489)
//! - `closure_layer3`: Closure Layer-3 tests for sort-aware witness + structural resolve (#1495)
//! - `closure_e2e`: End-to-end closure verification tests (#758 AC3, AC4)
//! - `closure_capture_error_paths`: Error-path coverage for closure capture registration (#1485)
//! - `closure_capture_type_invariants`: End-to-end closure capture type invariant injection tests (#2257)
//! - `type_constants`: Type constant resolution and encoder integration tests (#904 proof_coverage)
//! - `unsoundness_pipeline`: Demotion pipeline integration tests — thread isolation, partition invariants (#2106, #2202)
//! - `verify_scaling_proofs`: Verify-side algorithmic hotspot scaling proofs (#901)
//! - `proof_coverage_skolemize`: Skolemize_negated_universal proof coverage tests (#2202, #2106)
//! - `mut_ref_variable_measurement`: MutRefVarNames variable count measurement tests (#2150)
//! - `logic_fn_filter_indices`: Production `filter_logic_fn_indices_for_goal` tests (spec axiom reverse inclusion #1296)
//! - `sort_context_free_fns`: Free helper function tests for `sort_context::mod` (is_collection_expr_sort, extract_inner_var_annotation, apply_name_prefix, mapping_expr_sort)
//! - `quantified_var_usage_tests`: `collect_quantified_var_usage` per-variable coverage and `merge_pre_verification_and_post_bootstrap_snapshots` soundness
//! - `sort_hint_registration_tests`: Sort hint collection composition tests (Bool/Seq/FMap detection, multiple expressions)
//! - `trait_dispatch_regression`: Regression tests for trait dispatch patterns (#2670)
//! - `helpers`: Concise constructors for `PureExpr` and `Formula` in tests

mod algorithm_audit;
mod basic;
mod body_break_audit;
mod borrow;
mod borrow_finality_soundness;
mod ce_census_20260820;
mod closure_body_inline;
mod closure_capture_error_paths;
mod closure_capture_type_invariants;
mod closure_e2e;
mod closure_ensures_fallback;
mod closure_fnonce_edge_cases;
mod closure_layer2;
mod closure_layer3;
mod closure_sorts_tests;
mod container_element_invariant;
mod coverage_gaps;
mod creusot_07_validation;
mod de_morgan_proofs;
mod deref_final_regressions;
mod derived_kind;
mod div_mod_zero;
mod eager_instantiation_audit;
mod encoding;
mod encoding_error_paths;
mod eq_or_iff_proofs;
mod error_formatting;
mod expr_analysis_tests;
mod expr_seq_tests;
mod formula_quantifier_tests;
mod ghost_flatten_proofs;
#[cfg(feature = "unsafe-heap")]
mod heap_encoding;
pub(crate) mod helpers;
mod let_assume_actual_sort_guards;
mod let_assume_obligation;
mod logic_fn;
mod logic_fn_filter_indices;
mod loop_sort_inference;
mod loops;
mod loops_compositional;
mod loops_compositional_creusot;
mod loops_initialization_proofs;
mod loops_logic_fn;
mod loops_parameter_coverage;
mod loops_postcondition_proofs;
mod match_encoding;
mod match_soundness_audit;
mod match_tuple_sort;
mod memory_lifecycle_proofs;
mod memory_model_dealloc_soundness;
mod memory_model_edge_cases;
mod memory_model_points_to_boundaries;
mod memory_model_safety;
mod memory_model_strengthening;
mod memory_model_symbolic;
mod memory_raii_guards;
mod memory_safety;
mod memory_verification;
mod memory_walker_depth_proofs;
mod method_sort_parity;
mod mut_ref_variable_measurement;
mod option_result_shared_spec_regressions;
mod param_sort_infer_nesting;
#[cfg(feature = "performance-tests")]
mod performance_hotspot_proofs;
#[cfg(feature = "performance-tests")]
mod performance_proofs;
mod predcell_permcell_encoding;
mod produces_transitivity;
mod produces_unsoundness;
mod proof_assert_path_conditions;
mod proof_coverage_1667;
mod proof_coverage_2202;
mod proof_coverage_gaps;
mod proof_coverage_skolemize;
mod quantified_var_usage_tests;
mod quantifier_kind_tests;
mod quantifier_sort_regressions;
mod quantifiers;
mod resolve_var_sort;
mod sep_logic;
mod seq_classification_tests;
mod seq_encoding;
mod shift_amount_range;
mod solver_axiom_scaling;
mod solver_quantified_scaling;
mod sort_context;
mod sort_context_free_fns;
mod sort_hint_registration_tests;
mod sort_resolution_cascade_tests;
mod soundness_lock;
mod soundness_strategic_audit;
mod state_adt_tests;
mod state_closure_tests;
mod switch_target_tests;
mod trait_dispatch_regression;
mod trigger_synthesis;
mod trigger_synthesis_audit;
mod type_constants;
mod unknown_reason;
mod unsoundness_pipeline;
mod verification;
mod verification_closure;
mod verify_scaling_proofs;
