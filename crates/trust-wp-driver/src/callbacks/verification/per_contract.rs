// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-contract verification body extracted from `verification.rs` (#2468 Phase 6).

use tracing::{info_span, trace};
use trust_wp_ay::type_constants_for_int;
use trust_wp_core::{
    logic::LogicMode,
    tracing_init::{TIMING_STAGE_SOLVE_SPAN, TIMING_STAGE_VC_SPAN},
};

mod clause_phase;
mod pre_transform;
mod reborrow_prophecy;
mod state;
mod trace;

use clause_phase::apply_clause_enrichment_phase;
use pre_transform::apply_pre_transform_rewrites;
pub(super) use state::SharedVerificationState;

use super::{
    super::{
        super::contracts::FunctionContract,
        adt_analysis::{build_adt_decls, build_adt_field_ranges},
        contract_rewrite::rewrite_parsed_contract_structure,
        ghost_context::rustc_span_to_source_span,
        indexed_write_synthesis::synthesize_indexed_write_postconditions,
        iterator_spec_rewrite::rewrite_iterator_spec_methods,
        loop_verify::ghost_rewrite::{
            function_returns_ghost, rewrite_loop_ensures_for_ghost_return,
        },
        parsing::{parse_and_extract_contract, ExtractionContext},
        reporting::{
            report_function_verification_result, FunctionReportContext, ProofAssertCounters,
            VerificationCounters,
        },
        struct_field_map::extract_int_type_from_path,
        verification_context::VerificationContext,
    },
    clause_enrichment::discharge_ensures_already_required,
    contract_transform::{transform_contract, TransformedContract},
    in_function_proof_assert::{verify_in_function_proof_asserts, InFunctionProofAssertContext},
    loop_contract::{check_trait_refinement, verify_contract_loop_path, LoopPathOutcome},
    post_loop_final_values::inject_post_loop_final_values,
    recursive_verify::{verify_recursive_variant_decrease, RecursiveVariantCheckConfig},
    skip_decision::ContractClausePresence,
    solver_dispatch::{
        build_per_function_solver_context_with_captures, dispatch_smt_verification,
        GhostContextParams, SolverParams,
    },
    trace_extraction_results, trace_transformation_results,
};

pub(super) fn verify_single_contract(
    shared: &SharedVerificationState<'_, '_>,
    contract: &FunctionContract,
    def_path: &str,
    counters: &mut VerificationCounters,
    pa_counters: &mut ProofAssertCounters,
) {
    // Check if this function will receive type invariant clauses even without
    // explicit contracts. This prevents parse_and_extract_contract from skipping
    // functions discovered via discover_invariant_bearing_functions (#359).
    let clause_presence = ContractClausePresence::from_contract(contract);
    let has_type_invariant_injection = clause_presence
        .needs_type_invariant_injection(!shared.config.type_invariant_defs.is_empty());

    // Snapshot unsoundness counters before MIR extraction so that
    // driver-level increments (e.g., OpaqueCallTrueAssumption in
    // handle_opaque_call) are captured in the demotion delta (#2206).
    let unsoundness_before = trust_wp_ay::unsoundness::snapshot();
    let user_specs = &shared.prep.user_specs;
    let extraction_ctx = ExtractionContext::new(
        user_specs,
        shared.config.trait_specs,
        shared.config.extern_specs,
        true,
        has_type_invariant_injection,
    );

    let Some(mut parsed) = parse_and_extract_contract(
        shared.tcx,
        contract,
        shared.config.recursive_fns,
        &extraction_ctx,
    ) else {
        // If the contract had clauses but parsing returned None, count as error.
        // This prevents silent "0 verified, 0 failed, 0 errors" when all contracts
        // fail to parse (audit finding: parse failures were silently skipped).
        if clause_presence.has_clauses() {
            counters.errors += 1;
        }
        return;
    };

    let vc_prep_span = info_span!(TIMING_STAGE_VC_SPAN, def_path = %def_path).entered();

    // Apply structural rewrites: type invariant methods, logic method calls,
    // newtype simplification, and named struct field rewriting (#1526 Phase 5).
    #[rustfmt::skip]
    rewrite_parsed_contract_structure(
        shared.tcx, contract.def_id, &mut parsed, shared.config.type_invariant_defs,
        &shared.prep.logic_method_names, &shared.prep.user_shadowed_builtins,
    );

    // Rewrite iterator spec method calls (produces/completed) for
    // supported iterator types (Vec::IntoIter) to Seq-based formulas.
    // Must run after structural rewrites and before SMT emission. (#2172)
    rewrite_iterator_spec_methods(&mut parsed);

    let span = shared.tcx.def_span(contract.def_id);
    let source_map = shared.tcx.sess.source_map();
    let loc = source_map.span_to_diagnostic_string(span);

    // Resolve type-level constants (Self::MIN, Self::MAX) for integer method specs (#688).
    let type_constants = extract_int_type_from_path(def_path).and_then(type_constants_for_int);
    // tcx.def_path_str() returns a local path without crate prefix (e.g., "test"
    // instead of "creusot_test::test"). Logic-function scoping compares parent
    // modules on crate-qualified paths, so prepend the local crate name here.
    let local_crate_name = shared
        .tcx
        .crate_name(rustc_hir::def_id::LOCAL_CRATE)
        .to_string();
    let qualified_def_path = format!("{local_crate_name}::{def_path}");

    apply_pre_transform_rewrites(
        shared,
        contract,
        &mut parsed,
        def_path,
        &loc,
        &qualified_def_path,
    );

    // Apply shared contract transformation: mut-ref rewriting, closure capture
    // transforms, call-assumption/obligation merging (#564 dedup).
    let tc = transform_contract(&parsed);
    if !tc.closure_capture_fields.is_empty() {
        trace!(
            "closure capture fields transformed: {:?}",
            tc.closure_capture_fields
        );
    }

    // Scope module-level logic function visibility (#519, #540).
    let mode_overrides;
    let (logic_fns_opt, mode_overrides_opt) = if shared.logic_fns.is_empty() {
        (None, None)
    } else if shared
        .logic_fns
        .iter()
        .any(|lf| matches!(lf.mode(), LogicMode::OpenSelf | LogicMode::Default))
    {
        mode_overrides =
            super::super::helpers::scope_logic_fn_modes(shared.logic_fns, &qualified_def_path);
        (Some(shared.logic_fns), Some(mode_overrides.as_slice()))
    } else {
        (Some(shared.logic_fns), None)
    };

    // Collect per-function ADT declarations early so both loop and
    // non-loop verification paths can use native datatype encoding (#1982).
    let adt_decls = build_adt_decls(shared.tcx, contract.def_id);
    let adt_decls_opt = if adt_decls.is_empty() {
        None
    } else {
        trace!(adts = adt_decls.len(), "ADT declarations collected");
        Some(adt_decls)
    };
    // Collect per-ADT integer field ranges early too, so the loop verification
    // path (via VerificationContext) can thread `field(x) >= 0` facts the same
    // way the function-level solver dispatch already does (#2702).
    let adt_field_ranges = build_adt_field_ranges(shared.tcx, contract.def_id);
    let adt_field_ranges_opt = if adt_field_ranges.is_empty() {
        None
    } else {
        trace!(
            adts = adt_field_ranges.len(),
            "ADT field range constraints collected",
        );
        Some(adt_field_ranges)
    };
    let type_invariants_opt = shared.prep.type_invariants_opt;

    let vctx = VerificationContext {
        tcx: shared.tcx,
        contract,
        def_path,
        loc: &loc,
        recursive_fns: shared.config.recursive_fns,
        trait_refinement_overrides: shared.config.trait_refinement_overrides,
        trait_contract_map: &shared.prep.trait_contract_map,
        type_invariants_opt,
        logic_fns_opt,
        mode_overrides_opt,
        type_constants: type_constants.as_ref(),
        track_level: shared.config.track_level,
        timeout: shared.config.timeout,
        verbose: shared.config.verbose,
        user_specs,
        trait_specs: shared.config.trait_specs,
        extern_specs: shared.config.extern_specs,
        adt_decls_opt: adt_decls_opt.as_ref(),
        adt_field_ranges_opt: adt_field_ranges_opt.as_ref(),
    };
    drop(vc_prep_span);

    let (loop_exit_assumptions, loop_post_loop_final_values) = {
        let _solve_span = info_span!(TIMING_STAGE_SOLVE_SPAN, def_path = %def_path).entered();
        // Snapshot before loop verification so loop-phase unsoundness
        // increments can be rolled back on ContinueWithAssumptions (#2361).
        // This preserves pre-loop driver increments (e.g., OpaqueCallTrueAssumption)
        // while isolating loop-only counter pollution from the function-level verdict.
        let pre_loop_unsoundness = trust_wp_ay::unsoundness::snapshot();
        match verify_contract_loop_path(&vctx, &parsed, &tc, counters) {
            LoopPathOutcome::Handled => {
                return;
            }
            LoopPathOutcome::NotApplicable => (None, None),
            LoopPathOutcome::ContinueWithAssumptions {
                assumptions,
                return_expr: loop_return_expr,
                post_loop_final_values,
            } => {
                // Restore unsoundness counters to the pre-loop state (#2361).
                // Loop sub-checks (init, preservation, postcondition, variant)
                // handle their own demotion independently. Without this restore,
                // loop-phase increments leak into the function-level demotion
                // baseline and cause spurious Unknown verdicts.
                trust_wp_ay::unsoundness::restore(&pre_loop_unsoundness);
                if let Some(ret_expr) = loop_return_expr {
                    // Loop continuation must prove postconditions from the
                    // post-loop return value, not a stale pre-loop extraction.
                    parsed.result_expr = Some(ret_expr);
                }
                let fv = if post_loop_final_values.is_empty() {
                    None
                } else {
                    Some(post_loop_final_values)
                };
                (Some(assumptions), fv)
            }
        }
    };

    // Phase 2 termination: verify variant decrease at recursive call sites (#208).
    if shared.config.recursive_fns.contains(&contract.def_id)
        && !parsed.loop_fields.variants.is_empty()
    {
        let variant_cfg = RecursiveVariantCheckConfig {
            tcx: shared.tcx,
            contract,
            parsed: &parsed,
            base_requires: &tc.base_requires,
            call_assumptions: &parsed.call_assumptions,
            logic_fns_opt,
            mode_overrides_opt,
            type_invariants_opt,
            type_constants: type_constants.as_ref(),
            track_level: shared.config.track_level,
            timeout: shared.config.timeout,
            verbose: shared.config.verbose,
            def_path,
            loc: &loc,
        };
        let _solve_span = info_span!(TIMING_STAGE_SOLVE_SPAN, def_path = %def_path).entered();
        if verify_recursive_variant_decrease(&variant_cfg, counters) {
            return;
        }
    }

    let vc_gen_span = info_span!(TIMING_STAGE_VC_SPAN, def_path = %def_path).entered();

    trace_transformation_results(&tc, &parsed, def_path);

    let TransformedContract {
        mut effective_requires,
        mut effective_ensures,
        base_requires,
        base_ensures,
        ..
    } = tc;

    // Re-rewrite synthesized `inv(x)` LogicFnCalls into type-qualified
    // MethodCalls so the synthesized `&mut`-param preconditions share the same
    // type-qualified invariant symbol as `^x.invariant()` postconditions
    // (partially_opaque #1), then discharge any residual bare `inv(arg)` reborrow
    // side-conditions on roots with no registered invariant to `true` (#8373).
    // See `rewrite_synthesized_invariant_calls`.
    super::super::type_invariants::rewrite_synthesized_invariant_calls(
        shared.tcx,
        contract.def_id,
        &parsed.arg_names,
        shared.config.type_invariant_defs,
        &mut effective_requires,
        &mut effective_ensures,
    );

    // Ghost return rewrite for ContinueWithAssumptions path (#1709).
    //
    // When a Ghost-returning function's loop invariant is verified and the
    // function-level path continues with loop-exit assumptions, the
    // postcondition still contains `*result == x` (Deref of Ghost wrapper).
    // The loop-level VC applied `rewrite_loop_ensures_for_ghost_return` to
    // its own effective_ensures, but the function-level effective_ensures was
    // not rewritten. Without this, the solver sees `Deref(result)` as an
    // unconstrained expression disconnected from the loop's return value,
    // causing spurious failures like ghost/loop_in_ghost.rs.
    if loop_exit_assumptions.is_some() {
        if let Some(ref ret_expr) = parsed.result_expr {
            let returns_ghost = function_returns_ghost(shared.tcx, contract.def_id);
            if returns_ghost {
                effective_ensures =
                    rewrite_loop_ensures_for_ghost_return(&effective_ensures, true, Some(ret_expr));
                trace!(
                    "rewrote function-level effective_ensures for Ghost return \
                     on ContinueWithAssumptions path (#1709)"
                );
            }
        }
    }

    // Inject loop-exit assumptions into effective_requires (#2085).
    if let Some(ref assumptions) = loop_exit_assumptions {
        effective_requires.extend(assumptions.iter().cloned());
    }
    let post_loop_final_values_for_filter = loop_post_loop_final_values.clone();

    // Inject post-loop deref final values into mut_borrow body (#2085).
    if let Some(loop_final_values) = loop_post_loop_final_values {
        inject_post_loop_final_values(&mut parsed, loop_final_values);
    }

    let closure_capture_infos = apply_clause_enrichment_phase(
        shared,
        contract,
        &mut parsed,
        &mut effective_requires,
        &mut effective_ensures,
        post_loop_final_values_for_filter.as_ref(),
    );

    // Build per-function solver context (#1526).
    let ghost_params = GhostContextParams {
        tcx: shared.tcx,
        ghost_blocks: shared.config.ghost_blocks,
        user_specs,
        trait_specs: shared.config.trait_specs,
        extern_specs: shared.config.extern_specs,
    };
    let solver_ctx = build_per_function_solver_context_with_captures(
        &ghost_params,
        contract,
        &parsed,
        &effective_requires,
        &effective_ensures,
        closure_capture_infos,
    );

    trace_extraction_results(&parsed, contract, def_path);

    // Synthesize IndexMut postconditions from indexed writes (#1317, #1638).
    if let Some(ref mut_borrow) = parsed.mut_borrow.mut_borrow_body {
        synthesize_indexed_write_postconditions(
            &mut_borrow.indexed_writes,
            &mut effective_requires,
            shared.config.verbose,
        );
    }

    discharge_ensures_already_required(&effective_requires, &mut effective_ensures);

    // Discharge existential postcondition goals (e.g. an FnMut adapter's
    // `exists<st1, st2, r> f.postcondition_mut(.., st1, r) &&
    // st1.postcondition_mut(.., st2, result) && resolve(st2)`) by binding the
    // existential variables to the closure post-states / results the body
    // already established as premise facts. Runs here — after all clause
    // enrichment and after the body's call assumptions have landed in
    // `effective_requires` — because the witness terms are those body facts.
    // Sound: proving the ground instance `P(W)` discharges `exists X. P(X)`.
    let witnessed = crate::callbacks::closure_enrichment::witness_existential_postcondition_goals(
        &effective_requires,
        &mut effective_ensures,
    );
    if witnessed > 0 {
        trace!(
            witnessed,
            "existential postcondition goal(s) discharged by ground witnessing"
        );
        // Once the existential postcondition_mut chain is ground-witnessed, the
        // raw `postcondition_mut ==> precondition` forall requires premise is
        // redundant (its ground instances are materialized) but keeps the
        // non-vacuity re-solve from deciding — prune it so the discharged proof
        // is not demoted to quantifier-ematching-exists-incomplete.
        let pruned =
            crate::callbacks::closure_enrichment::prune_materialized_forall_precondition_rules(
                &mut effective_requires,
            );
        if pruned > 0 {
            trace!(
                pruned,
                "materialized forall precondition premise(s) pruned after witnessing"
            );
        }
    }

    drop(vc_gen_span);

    let verification_result = {
        let _solve_span = info_span!(TIMING_STAGE_SOLVE_SPAN, def_path = %def_path).entered();
        let solver_params = SolverParams {
            ghost_context_opt: solver_ctx.ghost_context_opt(),
            logic_fns_opt,
            mode_overrides_opt,
            type_invariants_opt,
            type_constants: type_constants.as_ref(),
            closure_captures_opt: solver_ctx.closure_captures_opt(),
            track_level: shared.config.track_level,
            timeout: shared.config.timeout,
            adt_field_ranges: adt_field_ranges_opt.clone(),
            adt_decls: adt_decls_opt.clone(),
            // BV mode is now always-on: bitwise operations use ay's native
            // BV theory instead of UF approximations (#2666). The
            // `#[bitwise_proof]` annotation and auto-detection are no
            // longer needed for opt-in, but we keep the field for
            // backward compatibility.
            bitwise_proof: true,
        };
        dispatch_smt_verification(
            &parsed,
            &effective_requires,
            &effective_ensures,
            solver_ctx.synthesized_final_values.as_ref(),
            &solver_params,
            contract.ghost,
            unsoundness_before,
        )
    };

    let verification_result =
        verification_result.map_err(|e| match rustc_span_to_source_span(source_map, span) {
            Some(src_span) => e.with_span(src_span),
            None => e,
        });

    // Apply mandatory proof authority: a Verified result must carry a fully
    // replayed certificate. The legacy option value cannot bypass this gate.
    let strict_trust = shared.config.strict_trust;
    let verification_result = verification_result.map(|mut outcome| {
        outcome.result = outcome.result.apply_strict_trust(strict_trust);
        outcome
    });

    // REAL kernel lane: observation only, fail closed — see formula_kernel_lane.rs.
    #[cfg(feature = "clean-kernel")]
    crate::formula_kernel_lane::observe_contract_obligations(
        shared.tcx,
        contract.def_id,
        def_path,
        &effective_requires,
        &effective_ensures,
    );

    let fn_report_ctx = FunctionReportContext {
        def_path,
        loc: &loc,
        contract,
        parsed: &parsed,
        source_map,
    };
    let body_verified = report_function_verification_result(
        verification_result,
        &fn_report_ctx,
        logic_fns_opt,
        shared.unverified_axioms,
        counters,
    );

    if body_verified {
        let _solve_span = info_span!(TIMING_STAGE_SOLVE_SPAN, def_path = %def_path).entered();
        check_trait_refinement(&vctx, &parsed, &base_requires, &base_ensures, counters);
    }

    let _solve_span = info_span!(TIMING_STAGE_SOLVE_SPAN, def_path = %def_path).entered();
    verify_in_function_proof_asserts(
        shared.tcx,
        &InFunctionProofAssertContext {
            contract,
            arg_names: &parsed.arg_names,
            loop_spans: &parsed.loop_fields.all_loop_spans,
            loop_exit_assumptions: loop_exit_assumptions.as_deref(),
            ghost_blocks: shared.config.ghost_blocks,
            user_specs,
            trait_specs: shared.config.trait_specs,
            extern_specs: shared.config.extern_specs,
            mut_borrow_body: parsed.mut_borrow.mut_borrow_body.as_ref(),
            // #prophecy-slots M6: the SAME pins the contract obligation used
            // (`solver_dispatch`), reused rather than recomputed — identical
            // body, identical `arg_names`, identical adjudication.
            projected_final_pins: &parsed.mut_borrow.projected_final_pins,
            pa_setup: shared.pa_setup,
            pa_ctx: &shared.pa_ctx,
            pa_logic_fns_opt: shared.pa_logic_fns_opt,
            type_invariants_opt,
            local_crate_name: &local_crate_name,
            source_map,
            track_level: shared.config.track_level,
            timeout: shared.config.timeout,
            def_path,
        },
        pa_counters,
    );
}
