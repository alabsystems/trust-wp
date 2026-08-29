// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for encoder functions with zero direct unit test coverage (#711).

use ntest::timeout;

use super::{super::*, helpers::*};

// Existing named modules
mod algorithm_audit_axiom_tests;
mod bool_context_operand_tests;
mod bool_method_predicate_tests;
mod bool_view_identity_tests;
mod closure_axiom_tests;
mod deep_model_axiom_tests;
mod deref_final_nesting_tests;
mod fmap_axiom_tests;
mod fmap_merge_axiom_tests;
mod fmap_method_tests;
mod fset_axiom_tests;
mod fset_method_strengthened_tests;
mod fset_method_tests;
mod match_constructor_coverage_tests;
mod multi_bool_quantifier_expansion_tests;
mod path_guard_tests;
mod placeholder_signature_tests;
mod produces_predicate_tests;
mod produces_semantic_companions;
mod quantifier_bool_semantic_tests;
mod reconstruction_axiom_tests;
mod tuple_axiom_tests;
mod type_disjointness_axiom_tests;
mod variable_shadow_tests;
mod view_identity_proof_tests;

// Phase 3: coverage gaps for untested encoder modules (#1946)
mod closure_axiom_body_detect_tests;
mod quantifier_ctor_elim_tests;
mod seq_synth_tests;

// Phase 5: decomposed quantifier_ctor_elim submodule coverage (#1296)
mod quantifier_ctor_elim_submodule_tests;

// Phase 4: adt_axioms.rs + sort_context submodule coverage (#1946)
mod adt_axiom_unit_qualified_tests;
mod arithmetic_binop_sort_sensitive;
mod sort_aware_match_fallback_tests;
mod sort_aware_method_symbols;
mod sort_context_submodule_tests;

// Closure signature parsing/matching (#2106 coverage gap, P1-104)
mod closure_signature_parsing_tests;

// Closure receiver sort inference (#1998 coverage gap, P1-1084)
mod closure_receiver_sort_shadow_tests;
mod closure_receiver_sort_tests;

// Closure demand guards (#1998 coverage gap, P1-1085)
mod closure_demand_guard_tests;

// Soundness-adjacent zero-coverage functions (#2198)
mod soundness_adjacent_coverage;

// Type invariant encoder functions (#1370 coverage gap, P1-122)
mod type_invariant_encoder_tests;

// Standalone test groups
mod bitwise_uf_encoding;
mod bool_logic_fn_iff;
mod collection_encoding;
mod eager_instantiation_integration;
mod eager_instantiation_matching;
mod eq_iff_encoding;
mod final_deref_encoding;
mod method_call_error_paths;
mod mut_borrow_sort_encoding;
mod panic_detection;
mod pure_encoding_expr_structure;
mod pure_encoding_sort_sensitive;
mod result_inference_match_bool;
mod result_inference_sort_detection;
mod sort_roundtrip_tests;
mod var_sort_resolution;
mod verification_result_api;

// End-to-end demotion pipeline integration tests (#2106 safety net)
mod demotion_e2e_tests;

// Field accessor demotion exemption coverage (#2316)
mod field_accessor_demotion_tests;

// ADT constructor demotion exemption (#1474, bug/1504)
mod adt_constructor_demotion_tests;

// Depth-guard polarity proofs for existence-checking walkers (#2473)
mod depth_guard_polarity_tests;

// Logic function dispatch coverage (method_call/logic_dispatch.rs, zero prior tests)
mod logic_dispatch_tests;

// Seq decomposition ordering and propagation invariants (binop.rs #1317)
mod seq_decomposition_ordering_tests;

// Witness-based existential elimination + constant body optimization (#726, #1296)
mod witness_elimination_tests;

// Assertion pipeline state machine coverage (#2514 Tier 1 gap)
mod assertion_pipeline;

// Logic function call-site encoding coverage (#2514 Tier 2 gap)
mod call_encoding_tests;

// Logic function registration edge cases (#2514 Tier 2 gap)
mod logic_fn_mod_tests;

// Expression walker functions coverage (expr.rs, #2514 Tier 2 gap)
mod expr_walker_tests;

// Quantifier encoding infrastructure (#2514 Tier 2 gap: quantifier/mod.rs + pure_quantifier.rs)
mod quantifier_encoding_tests;

// Logical FMapIter produces decomposition/bridge (#2514 Tier 2 gap: produces_predicate.rs)
mod fmap_iter_produces_tests;

// Seq encoding infrastructure (#2514 Tier 2 gap: seq/mod.rs, seq_len_term + shape constraints)
mod seq_mod_tests;

// ADT constructor/selector functions (match_enc/mod.rs, #2514 Tier 2 gap)
mod match_enc_selector_tests;

// MutRef equality decomposition (mut_ref_sort.rs, #2514 Tier 2 gap)
mod mut_ref_decompose_tests;

// GroundTermPool registration, path conditions, flush tracking (ground_pool.rs, #2514 gap)
mod ground_pool_tests;

// Seq prescan: expr_produces_seq + collect_view_names_as_seq (seq/prescan.rs, #2514 gap)
mod seq_prescan_tests;

// Encoder mod.rs functions: ground instances gate, axiom_apply, safe_apply arity, seq restore (#2514)
mod encoder_mod_fn_tests;

// Solver vacuity guard label matching + fail-closed unsat-core behavior (#2514)
mod solver_vacuity_tests;

// FMap/FSet dispatch-to-axiom semantic round-trip proofs (#2514 gap)
mod fmap_dispatch_semantic_contingency_tests;
mod fmap_dispatch_semantic_tests;
mod fset_dispatch_semantic_contingency_tests;
mod fset_dispatch_semantic_tests;

// Sort mapping: Datatype(collection_model)→canonical sort downgrade (#2554)
mod sort_mapping_classifier_tests;

// Eager Fn closure law ground instantiation (#2514 gap: fn_laws.rs, fn_mut_once.rs)
mod closure_eager_law_tests;

// Closure capture selector/projection boundary conditions (#2514 algorithm_audit)
mod closure_capture_selector_tests;

// ay_api safe_select/safe_store boundary conditions (#2514 algorithm_audit)
mod ay_api_safe_select_tests;

// UnknownReason / VerificationResult / negate_existential_postcondition API tests (#1481)
mod unknown_reason_api_tests;
