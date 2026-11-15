// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Verification orchestration functions are inherently long; suppress across submodules
#![allow(clippy::too_many_lines)]

//! Rustc callbacks for MIR extraction
//!
//! This module implements `rustc_driver::Callbacks` to intercept MIR
//! after borrow checking. MIR and the matching borrow set are retained across
//! compiler workers within one checked compiler-context lifetime.
//!
//! # Remaining session caches (#1712)
//!
//! [`thread_locals`] owns extraction-local state including `EXTERN_SPECS`.
//! MIR retention has its own scoped, synchronized registry keyed by the exact
//! live compiler context; it is not a worker-local side channel.
//!
//! All mutable per-function side channels were moved onto explicit contexts
//! (`CallEffects`, `ExtractionSession`) or localized RAII guards. `CacheGuard`
//! clears the extraction-local caches; `with_mir_session` owns MIR cleanup.
//!
//! Reference: `reference/creusot/creusot/src/callbacks.rs`
//!
//! # Logging policy (#1689)
//!
//! - **User-facing final summaries/failures** may remain as `eprintln!` until
//!   #1690 structured result path lands.
//! - **Progress/diagnostic output** uses tracing macros (`info!`/`debug!`/`trace!`)
//!   controlled by `TRUST_WP_LOG` env filter.

pub(crate) mod adt_analysis;
mod callgraph;
mod closure_enrichment;
mod const_items;
mod contract_rewrite;
// The one entry point for placing named-field constructors in specification
// text that is not a function contract (logic-fn bodies, type-invariant
// bodies). See `contract_rewrite::place_named_field_ctors_in_expr`.
pub(crate) use contract_rewrite::place_named_field_ctors_in_expr;
pub(crate) use parsing::closure_capture_index_names;
mod counterexample;
mod creusot_frontend_checks;
mod discovery;
pub(crate) mod encoding_error_breakdown;
mod expr_analysis;
#[cfg(test)]
mod extraction_diagnostics_tests;
mod frontend;
mod function_credit;
mod ghost_context;
mod helpers;
mod indexed_write_synthesis;
pub(crate) mod integer_range;
mod iterator_spec_rewrite;
mod list_match_exit;
mod logic_fn_scope;
mod loop_verify;
mod panic_hook;
mod parsing;
pub(crate) mod proof_assert_extract;
#[cfg(test)]
mod proof_assert_fact_sources_tests;
mod proof_assert_leading_calls;
mod proof_assert_snapshot;
mod proof_assert_snapshot_facts;
mod proof_assert_verify;
#[cfg(test)]
mod proof_assert_verify_tests;
mod proof_assert_wiring;
mod purity_validation;
mod reporting;
pub(crate) mod spec_arith;
pub(crate) mod spec_typecheck;
mod spelled_type_names;
mod struct_field_map;
#[cfg(test)]
mod tests;
pub(crate) mod thread_locals;
mod trait_refinement;
mod type_invariants;
mod verification;
mod verification_context;

use std::borrow::Cow;

// Re-export for cross-module deduplication (Step 8, #2065; #1392).
pub(crate) use closure_enrichment::{
    final_receiver_state_expr, projected_capture_post_state, strip_deref_wrappers,
    strip_receiver_state_wrappers,
};
use discovery::{
    apply_trait_contract_inheritance, discover_abort_obligation_functions,
    discover_closure_capture_invariant_owners, discover_coroutine_obligation_bodies,
    discover_extern_specs, discover_generic_fn_bound_call_functions,
    discover_invariant_bearing_functions, discover_proof_assert_functions, find_contract_functions,
    find_trait_contracts, restate_inherited_clauses,
};
use panic_hook::{is_ay_panic_for_hook, PanicHookGuard};
use parsing::build_trait_spec_table;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Config};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
pub(crate) use thread_locals::{copy_mir_bodies, try_get_body_with_context, CacheGuard};
use tracing::{debug, info, info_span, trace};
pub(crate) use trait_refinement::std_prelude_glob_module;
// Re-export TrackLevel from trust-wp-core for use by trust-wp-ay
pub(crate) use trust_wp_core::TrackLevel;
use type_invariants::build_container_invariant_defs;
pub(crate) use type_invariants::{
    clear_invariant_type_names, instantiate_type_param_invariants, is_trivially_invariant_free,
    mentions_type_param_invariant, type_param_invariant_at, type_param_invariant_of,
    TypeParamInvariantAt,
};
use verification::{
    build_smt_artifacts, emit_smt_artifacts_to_stdout, verify_contracts, write_smt_artifacts_to_dir,
};

/// Configuration options for the trust-wp driver.
#[derive(Debug, Clone)]
#[allow(clippy::struct_excessive_bools)] // Bools are clearer than flags enum here
pub(crate) struct TrustWpOptions {
    /// Show verbose output during verification
    pub(crate) verbose: bool,
    /// Stop compilation after analysis (don't generate code)
    pub(crate) stop_after_analysis: bool,
    /// Force trust-wp callbacks even without trust-wp dependency (for testing)
    pub(crate) force_callbacks: bool,
    /// Emit SMT-LIB2 output for verification conditions
    pub(crate) emit_smt: bool,
    /// Run ay verification directly
    pub(crate) verify: bool,
    /// Memory tracking precision level (default: Auto).
    /// Controls how loads/stores are modeled in SMT.
    pub(crate) track_level: TrackLevel,
    /// Enable wide pointers for bounds checking.
    /// When true, pointers carry size metadata for OOB detection.
    /// Requires `track_level` = `Mem` to have effect.
    pub(crate) wide_pointers: bool,
    /// Filter pattern for function names to verify.
    /// Only functions containing this pattern in their path will be verified.
    pub(crate) filter_pattern: Option<String>,
    /// Per-function verification timeout in seconds.
    /// When set, each ay check_sat() call is limited to this duration.
    /// Default: 60s. `None` means use the default.
    pub(crate) timeout_secs: Option<u64>,
    /// Treat unverified logic function postconditions as errors (#1490).
    /// When true, logic function postconditions that return Unknown are
    /// counted as errors rather than warnings, preventing callers from
    /// relying on unproven axioms.
    pub(crate) strict_axioms: bool,
    /// Compatibility carrier for the retired strict-trust option.
    /// Proof authority is mandatory even if an older caller supplies `false`.
    pub(crate) strict_trust: bool,
    /// Directory for per-function SMT artifact emission (#1691).
    /// When set, each verified function produces a `.smt2` file under this
    /// directory with source-mapping comments.
    pub(crate) emit_smt_dir: Option<std::path::PathBuf>,
}

impl Default for TrustWpOptions {
    fn default() -> Self {
        Self {
            verbose: false,
            stop_after_analysis: false,
            force_callbacks: false,
            emit_smt: false,
            verify: false,
            track_level: TrackLevel::default(),
            wide_pointers: false,
            filter_pattern: None,
            timeout_secs: None,
            strict_axioms: false,
            // Proof authority is mandatory. This field remains temporarily
            // for source compatibility with downstream option construction.
            strict_trust: true,
            emit_smt_dir: None,
        }
    }
}

/// Main trust-wp callbacks for rustc integration.
///
/// This callback:
/// 1. Intercepts borrow-checked MIR via query overrides
/// 2. Retains MIR across compiler workers in the active context
/// 3. Runs analysis and extraction after type checking
pub(crate) struct TrustWpCallbacks {
    opts: TrustWpOptions,
}

impl TrustWpCallbacks {
    pub(crate) fn new(opts: TrustWpOptions) -> Self {
        Self { opts }
    }
}

impl Callbacks for TrustWpCallbacks {
    fn config(&mut self, config: &mut Config) {
        // Override the mir_borrowck query to store bodies with borrow facts
        // Use providers.queries.mir_borrowck (not providers.mir_borrowck) - see Creusot
        config.override_queries = Some(|_sess, providers| {
            // Erase specification type-check closures before borrow checking
            // (see `spec_typecheck`). Must be `mir_built`: by `mir_promoted`
            // drops have been elaborated around the closure values.
            providers.queries.mir_built = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                spec_typecheck::cleanup_spec_tc_closures(tcx, def_id, &mut mir);
                // One name per binding, before anything reads the body (D-237).
                crate::mir_analysis::binding_identity::rename_shadowed_bindings(
                    tcx, def_id, &mut mir,
                );
                tcx.alloc_steal_mir(mir)
            };
            providers.queries.mir_borrowck = |tcx, local_id| {
                // Guard: items without an HIR body (bodyless trait methods,
                // extern declarations) cannot be borrow-checked. Both
                // `copy_mir_bodies` and the default provider panic via
                // `nested_bodies_within` → `body_owned_by` for these. Return
                // an error instead of crashing. (#2229, #2205)
                if tcx.hir_node_by_def_id(local_id).body_id().is_none() {
                    let guar = tcx.dcx().span_delayed_bug(
                        tcx.def_span(local_id),
                        "mir_borrowck called for item without HIR body",
                    );
                    return Err(guar);
                }
                // rustc's own `mir_borrowck` never borrow-checks a body whose
                // type check was tainted by errors (it returns the error
                // guarantee) nor an injected body it should skip; the
                // consumer entry point `get_bodies_with_borrowck_facts` that
                // `copy_mir_bodies` uses has neither guard and runs
                // `do_mir_borrowck` unconditionally, which ICEs on a nested
                // closure whose type is `{type error}` (`universal_regions`:
                // "expected defining type"). A type error in ANY closure of
                // the body — a user closure, or a specification type-check
                // closure whose clause did not type — must stay an ordinary
                // error, so mirror rustc's guard before copying.
                let skip_borrowck = {
                    let (promoted_body, _) = tcx.mir_promoted(local_id);
                    let promoted_body = promoted_body.borrow();
                    promoted_body.tainted_by_errors.is_some() || promoted_body.should_skip()
                };
                if !skip_borrowck {
                    // Store the borrow-checked MIR in our cache
                    copy_mir_bodies(tcx, local_id);
                }
                // Continue with default borrow checking
                (rustc_interface::DEFAULT_QUERY_PROVIDERS
                    .queries
                    .mir_borrowck)(tcx, local_id)
            };
        });
    }

    fn after_expansion<'tcx>(&mut self, c: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        thread_locals::with_mir_session(tcx, || {
            // Install cache guard: clears thread-locals on entry (defensive reset) and
            // on all exits (normal, early return, panic/unwind). See #1025.
            let _cache_guard = CacheGuard::new();
            let mut emitted_result_protocol_line = false;

            // Run rustc's analysis pass (type checking, borrow checking, etc.)
            // The Result is always Ok(()) if it returns; errors are reported via diagnostics.
            // Clippy misidentifies the return type as unit; suppress the false positive.
            #[allow(clippy::let_unit_value, clippy::ignored_unit_patterns)]
            let _ = tcx.analysis(());

            // Check for errors before proceeding
            c.sess.dcx().abort_if_errors();

            // A `__trust_wp_spec_tc` marker the driver does not honour (user
            // written, or on anything but a macro-generated type-check closure or
            // trait-signature helper), or a user item using the reserved helper
            // name prefix, is refused before any discovery: a forged marker must
            // never silently drop a body from verification.
            let forged_spec_tc = spec_typecheck::forged_spec_tc_markers(tcx);
            if !forged_spec_tc.is_empty() {
                for (span, message) in &forged_spec_tc {
                    tcx.dcx().span_err(*span, message.clone());
                }
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            // Before any clause is parsed: the spelled type names this crate
            // gives another meaning (D-202), the names it binds to a type
            // holding a machine integer the parser cannot see (D-205), and a
            // path through a name it binds to a module or a crate (D-206), are
            // refused wherever a clause spells them as a type. `CacheGuard`
            // forgets them when the session ends.
            trust_wp_core::contract_parser::spelled_types::install_shadowed_type_names(
                spelled_type_names::shadowed_type_names(tcx),
            );
            trust_wp_core::contract_parser::spelled_types::install_machine_int_alias_names(
                spelled_type_names::machine_int_alias_names(tcx),
            );
            trust_wp_core::contract_parser::spelled_types::install_module_names(
                spelled_type_names::module_names(tcx),
            );

            // A specification's call whose spelling the contract parser or the
            // encoder reads as a definition rustc did not resolve it to (a rename
            // onto `view` or `seq`) would verify a clause the source does not
            // state; every reader of the clause reads the same text, so nothing
            // of the crate is verified (D-136).
            let misread_spec_calls =
                crate::logic::call_resolution::misread_specification_calls(tcx);
            if !misread_spec_calls.is_empty() {
                for (span, why) in &misread_spec_calls {
                    tcx.dcx().span_err(
                        *span,
                        format!(
                            "trust-wp: {why}; the crate is refused, since the clause would verify \
                         as a claim the source does not make"
                        ),
                    );
                }
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            // Every arithmetic operator of a specification means what its
            // operands' type gives it in the oracle: `u32 + u32` wraps, `x@ + 1`
            // does not (D-232). The parser reads text with no types, so it is
            // handed rustc's typing of every clause before anything is parsed.
            spec_arith::install_spec_arith_readings(tcx);

            // Show configuration
            debug!("trust-wp: track_level={:?}", self.opts.track_level);

            // Reject unimplemented features early to avoid misleading results.
            if self.opts.wide_pointers {
                tcx.dcx().err(
                    "`--wide-pointers` is not yet supported; remove the flag (tracking issue #419)",
                );
                emit_result_protocol_base_exit_code(2);
                // CacheGuard handles cleanup on this return path
                return Compilation::Stop;
            }

            // Extract type invariant body definitions from `impl Invariant for T` logic
            // functions (#359, #645). These provide defining axioms for the `invariant()`
            // uninterpreted predicates used in auto-injected pre/postconditions.
            // Extracted early so that invariant-bearing function discovery can use them.
            let mut type_invariant_defs = super::logic::extract_type_invariant_defs(tcx);
            // Rewrite named field access (e.g., `__trust_wp_field_a(self)`) to positional
            // access (e.g., `__trust_wp_tuple_get_0(self)`) in type invariant bodies so
            // they match the MIR-extracted representations used in contracts and
            // proof_assert assertions. Without this, the SMT solver treats them as
            // unrelated uninterpreted functions and cannot prove invariant-dependent
            // properties. (#1370)
            type_invariants::rewrite_invariant_def_named_fields(tcx, &mut type_invariant_defs);
            if !type_invariant_defs.is_empty() {
                debug!(
                    count = type_invariant_defs.len(),
                    "type invariant definition(s) extracted"
                );
            }

            // Find functions with trust-wp contract attributes
            let mut contracts = find_contract_functions(tcx);

            // Discover additional functions that need verification due to type invariant
            // injection, even without explicit contract annotations (#359).
            discover_invariant_bearing_functions(tcx, &mut contracts, &type_invariant_defs);

            // Discover functions that contain proof_assert! but have no contract attributes.
            // Without this, proof_asserts in contractless ghost functions (e.g., ghost_only()
            // in assert_in_ghost.rs) are never reached by the verification loop. (#1581)
            discover_proof_assert_functions(tcx, &mut contracts);

            // Discover contractless functions that call through a generic
            // `F: Fn/FnMut/FnOnce` bound: each such call owes Creusot's
            // `call requires` goal `f.precondition(args)`. Without this the goal is
            // silently dropped and the run examines nothing.
            discover_generic_fn_bound_call_functions(tcx, &mut contracts);

            // Build synthetic container invariant defs for Vec/VecDeque params that
            // contain invariant-bearing element types. Enables the encoder to assert
            // quantified element invariants: forall i. body[self/index(x@, i)]. (#869)
            // Built before the two discoveries below, which add only bodies whose
            // signatures hold no invariant-bearing type (every such body is a
            // target already), so they synthesize nothing a later build would.
            let container_defs =
                build_container_invariant_defs(tcx, &contracts, &type_invariant_defs);
            if !container_defs.is_empty() {
                debug!(
                    count = container_defs.len(),
                    "container invariant definition(s) synthesized"
                );
            }
            let declared_defs = type_invariant_defs.len();
            type_invariant_defs.extend(container_defs);
            // The definitions are final here. A call that fixes a generic
            // parameter instantiates that parameter's invariant against the SAME
            // name set the parameter-clause builder resolves ADTs against.
            type_invariants::install_invariant_type_names(&type_invariant_defs);

            // Discover contract-free functions that owe an abort obligation
            // (Creusot's `Terminator::Abort` at a diverging call), a local
            // callee's `#[requires]` or the parameter invariants the body a call
            // enters was granted. Without this such a function is a verification
            // target of nothing and a crate whose other items verify exits 0
            // around it. It reads the FINAL definition set, the one the spec
            // tables grant from and the extraction gate and the escape join read.
            discover_abort_obligation_functions(tcx, &mut contracts, &type_invariant_defs);

            // Every coroutine body that owes anything becomes a target of the
            // contract loop's coroutine refusal. Without this the refusal met only
            // bodies another pass had admitted, and an `async` body whose only
            // obligation was an overflow was examined by nothing. It reads the
            // declared definitions: a synthetic container name is not a type.
            discover_coroutine_obligation_bodies(
                tcx,
                &mut contracts,
                &type_invariant_defs[..declared_defs],
            );

            // Discover contractless functions that BUILD a closure holding a
            // capture type-invariant grant. The construction site owes that
            // grant, and an owner the verification loop never visits pays
            // nothing. Runs on the COMPLETE def set, the one the spec table that
            // decides the grant will read, so the owners discovered here are
            // exactly the bodies that will be charged.
            discover_closure_capture_invariant_owners(tcx, &mut contracts, &type_invariant_defs);

            // Find trait method contracts and apply inheritance
            let trait_contracts = find_trait_contracts(tcx);
            if !trait_contracts.is_empty() {
                debug!(
                    count = trait_contracts.len(),
                    "trait method contracts found"
                );
                for tc in &trait_contracts {
                    trace!(
                        trait_path = %tc.trait_path,
                        method = %tc.method_name,
                        requires = tc.requires.len(),
                        ensures = tc.ensures.len(),
                        "trait contract"
                    );
                }
                apply_trait_contract_inheritance(&mut contracts, &trait_contracts);
                crate::param_patterns::refuse_inherited_projections_on_renamed_params(
                    tcx,
                    &mut contracts,
                    &trait_contracts,
                );
            }

            // Trait method DefId -> StdSpec lookup for generic call-site resolution.
            let mut trait_specs =
                build_trait_spec_table(tcx, &trait_contracts, &type_invariant_defs);

            // Find ghost blocks in the crate
            let ghost_blocks = super::ghost::find_ghost_blocks(tcx);
            if !ghost_blocks.is_empty() {
                debug!(count = ghost_blocks.len(), "ghost blocks found");
                for block in &ghost_blocks {
                    let fn_path = tcx.def_path_str(block.containing_fn);
                    trace!(containing_fn = %fn_path, "ghost block");
                }
            }

            // Validate ghost blocks (no writes to non-ghost variables)
            let ghost_errors = super::ghost::validate_ghost_blocks(tcx, &ghost_blocks);
            if !ghost_errors.is_empty() {
                for error in &ghost_errors {
                    tcx.dcx().span_err(error.span, error.message.clone());
                }
                debug!(count = ghost_errors.len(), "ghost validation error(s)");
                emit_result_protocol_base_exit_code(2);
                // CacheGuard handles cleanup on this return path
                return Compilation::Stop;
            }

            let program_context_ghost_errors =
                super::ghost::validate_program_context_ghost_apis(tcx, &ghost_blocks);
            if !program_context_ghost_errors.is_empty() {
                for error in &program_context_ghost_errors {
                    tcx.dcx().span_err(error.span, error.message.clone());
                }
                debug!(
                    count = program_context_ghost_errors.len(),
                    "program-context ghost API error(s)"
                );
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            let tokens_new_errors = super::ghost::validate_tokens_new(tcx);
            if !tokens_new_errors.is_empty() {
                for error in &tokens_new_errors {
                    tcx.dcx().span_err(error.span, error.message.clone());
                }
                debug!(
                    count = tokens_new_errors.len(),
                    "Tokens::new validation error(s)"
                );
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            let purity_errors =
                purity_validation::validate_program_context_logic_calls(tcx, &ghost_blocks);
            if !purity_errors.is_empty() {
                for error in &purity_errors {
                    tcx.dcx().span_err(error.span, error.message.clone());
                }
                debug!(count = purity_errors.len(), "purity validation error(s)");
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            let erasure_attribute_errors = super::ghost::erasure::validate_erasure_attributes(tcx);
            if !erasure_attribute_errors.is_empty() {
                for error in &erasure_attribute_errors {
                    tcx.dcx().span_err(error.span, error.message.clone());
                }
                debug!(
                    count = erasure_attribute_errors.len(),
                    "erasure attribute validation error(s)"
                );
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            // MIR-level ghost erasure soundness check (defense-in-depth, #1768)
            let erasure_errors = super::ghost::erasure::check_ghost_erasure(tcx, &ghost_blocks);
            if !erasure_errors.is_empty() {
                for error in &erasure_errors {
                    tcx.dcx().span_err(error.span, error.message.clone());
                }
                debug!(count = erasure_errors.len(), "ghost erasure check error(s)");
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            // Phase 5c: THIR-level `#[erasure(target)]` equivalence scaffold.
            //
            // Collects every (lhs, rhs) erasure pair discovered from doc markers
            // and runs the driver-side stub validator. This is a structural
            // pre-check — the full Creusot-grade body-equivalence walk is deferred.
            // See `discovery::erasure` for the precise checked/deferred matrix.
            // Errors increment `erasure_errors` in the structured result protocol.
            let erasure_pair_errors = discovery::collect_erasure_pairs(tcx)
                .into_iter()
                .filter_map(|pair| {
                    discovery::validate_erasure_pair(tcx, pair.lhs, pair.rhs)
                        .err()
                        .map(|err| (pair, err))
                })
                .collect::<Vec<_>>();
            if !erasure_pair_errors.is_empty() {
                for (pair, err) in &erasure_pair_errors {
                    crate::result_protocol_state::record_erasure_error();
                    let lhs_path = tcx.def_path_str(pair.lhs);
                    tcx.dcx().err(format!(
                    "trust-wp: #[erasure] equivalence check failed for `{lhs_path}` → `{}`: {err}",
                    pair.target_text
                ));
                }
                debug!(
                    count = erasure_pair_errors.len(),
                    "erasure pair validation error(s)"
                );
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            // Type-level snapshot self-reference rejection (#2686): reject local
            // ADTs that contain `Snapshot<&mut T>` where `T` transitively contains
            // the enclosing type. This closes compat false-accept bug/436_2.
            let snapshot_self_ref_errors = super::ghost::validate_snapshot_self_references(tcx);
            if !snapshot_self_ref_errors.is_empty() {
                for error in &snapshot_self_ref_errors {
                    tcx.dcx().span_err(error.span, error.message.clone());
                }
                debug!(
                    count = snapshot_self_ref_errors.len(),
                    "snapshot self-reference error(s)"
                );
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            // Ghost-type escape check (#2686): Creusot rejects Ghost<T>/Snapshot<T>
            // parameters in non-logic, non-ghost program functions that return
            // non-ghost, non-unit types. This catches the pattern where ghost values
            // are extracted into program context (e.g., `fn bad(x: Ghost<i32>) -> i32`).
            //
            // Safe patterns are allowed:
            // - Logic/predicate functions (#[logic], #[predicate])
            // - Ghost-checked functions (#[check(ghost)])
            // - Functions returning () (e.g., ghost_move_validation fixtures)
            // - Functions returning Ghost<T>/Snapshot<T>
            let ghost_escape_errors = check_ghost_type_escape(tcx, &ghost_blocks);
            if ghost_escape_errors > 0 {
                debug!(count = ghost_escape_errors, "ghost type escape error(s)");
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            let logic_surface_errors = purity_validation::validate_logic_surface_restrictions(tcx);
            if !logic_surface_errors.is_empty() {
                for error in &logic_surface_errors {
                    tcx.dcx().span_err(error.span, error.message.clone());
                }
                debug!(
                    count = logic_surface_errors.len(),
                    "logic surface validation error(s)"
                );
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            // Find logic functions (pure specification helpers)
            let logic_functions = super::logic::find_logic_functions(tcx);
            if !logic_functions.is_empty() {
                debug!(count = logic_functions.len(), "logic functions found");
                for logic_fn in &logic_functions {
                    trace!(name = %logic_fn.name, path = %logic_fn.full_path, "logic function");
                    if let Some(ref body) = logic_fn.body_text {
                        let preview: String = body.chars().take(50).collect();
                        if body.len() > 50 {
                            trace!("  body: {preview}...");
                        } else {
                            trace!("  body: {preview}");
                        }
                    }
                    for ens in &logic_fn.ensures {
                        trace!("  ensures: {ens}");
                    }
                }
            }

            // Convert to LogicFnDef for SMT encoding (Phase 2)
            let mut logic_fn_defs = super::logic::extract_logic_fn_defs(tcx);
            // Trait-method callee clauses are re-parsed at call sites: resolve their
            // colliding logic-function names in the declaring trait's scope now that
            // the identity registry is installed.
            crate::logic::identity::resolve_spec_table_texts(tcx, &mut trait_specs);
            // An impl that inherits its trait method's clauses owes them as
            // granted: resolved in the trait's scope, instantiated at the impl.
            restate_inherited_clauses(tcx, &mut contracts, &trait_specs);
            if !logic_fn_defs.is_empty() {
                let with_ensures = logic_fn_defs
                    .iter()
                    .filter(|d| !d.ensures().is_empty())
                    .count();
                debug!(
                    total = logic_fn_defs.len(),
                    with_ensures, "logic functions parsed successfully"
                );
            }

            let mut logic_purity_errors =
                purity_validation::validate_logic_function_purity(&logic_fn_defs);
            logic_purity_errors.extend(purity_validation::validate_logic_prophetic_calls(
                &logic_fn_defs,
                &purity_validation::local_free_prophetic_logic_paths(tcx),
            ));
            if !logic_purity_errors.is_empty() {
                for error in logic_purity_errors {
                    tcx.dcx().err(error);
                }
                debug!("logic function purity validation error(s)");
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            if stop_on_logic_recursion_errors(tcx) {
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            let logic_law_errors = super::logic::validate_logic_laws(tcx);
            if logic_law_errors > 0 {
                debug!(count = logic_law_errors, "logic law validation error(s)");
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            // A logic function that reads a final value reads its `&mut`
            // parameters as one value, so `^q` collapses onto `*q`: it is
            // withdrawn here, after the validations above read it as written, and
            // every goal that may name it is refused at the encoder's door (D-108).
            // Every contract signature reads a call of one as a final read of its
            // arguments, so the refusals of a final value another holder decides
            // apply to it as to `^` (D-109).
            for path in
                trust_wp_core::logic::final_reads::withdraw_final_readers(&mut logic_fn_defs)
            {
                eprintln!(
                    "trust-wp: note: logic function `{path}` reads a final value (`^`), which a \
                 logic parameter cannot carry: every proof that reads it is refused (D-108)"
                );
            }
            crate::mir_analysis::install_final_readers(
                trust_wp_core::logic::final_reads::FinalReaders::reading_in(&logic_fn_defs),
            );

            // Spec provenance (fail closed): library specifications, sorts and
            // recognisers are keyed by printed paths, and a local item prints
            // without its crate (`crate::core::cmp::max` prints `core::cmp::max`).
            // Every table lookup is DefId-gated, but a crate that defines items at
            // a reserved library root is refused outright so that no printed-path
            // recogniser anywhere can mistake a lookalike for the library item.
            let reserved_root_items = crate::provenance::local_reserved_root_items(tcx);
            if !reserved_root_items.is_empty() {
                for item in &reserved_root_items {
                    eprintln!(
                        "trust-wp: error: local item `crate::{item}` shadows a standard or \
                     spec-library path root; trust-wp identifies library items by \
                     path and refuses to verify a crate that defines lookalikes \
                     (rename the item)"
                    );
                }
                emit_result_protocol_error_exit(reserved_root_items.len() as u64);
                return Compilation::Stop;
            }

            // Merge built-in trust-wp-std extern-spec registry, then overlay local
            // extern_spec! discoveries. Local specs override built-in ones. (#1672)
            //
            // Do not preload the built-in registry while compiling `trust_wp_std`
            // itself: that crate is the source of truth for those extern specs, so
            // treating its own declarations as conflicts would reject valid builds.
            let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
            let include_builtin_extern_specs =
                should_preload_builtin_extern_specs(&local_crate_name);
            let mut extern_specs = if include_builtin_extern_specs {
                trust_wp_driver::builtin_trust_wp_std_specs()
            } else {
                std::collections::HashMap::new()
            };
            let builtin_count = extern_specs.len();
            let (local_specs, local_duplicate_count) = discover_extern_specs(tcx);

            // Merge local extern_specs into the built-in table. Equivalent local
            // declarations are deduplicated; incompatible ones remain fatal.
            let builtin_conflict_paths = if include_builtin_extern_specs {
                trust_wp_driver::merge_local_extern_specs(&mut extern_specs, local_specs)
                    .incompatible_builtin_conflicts
            } else {
                extern_specs.extend(local_specs);
                Vec::new()
            };
            for path in &builtin_conflict_paths {
                eprintln!(
                    "trust-wp: error: extern_spec for `{path}` conflicts with \
                 built-in trust-wp-std specification"
                );
            }

            let builtin_conflict_count = builtin_conflict_paths.len();
            let total_duplicate_errors = local_duplicate_count + builtin_conflict_count;
            if total_duplicate_errors > 0 {
                eprintln!(
                    "trust-wp: error: {} duplicate/conflicting extern_spec declaration(s) found",
                    total_duplicate_errors
                );
                emit_result_protocol_error_exit(total_duplicate_errors as u64);
                return Compilation::Stop;
            }
            if !extern_specs.is_empty() {
                debug!(
                    total = extern_specs.len(),
                    builtin = builtin_count,
                    local = extern_specs.len() - builtin_count,
                    "extern_spec entries found"
                );
                for (path, spec) in &extern_specs {
                    trace!(
                        path = %path,
                        requires = spec.requires.len(),
                        ensures = spec.ensures.len(),
                        "extern_spec"
                    );
                }
            }
            // Creusot frontend refusals that need the merged extern-spec table
            // (ghost purity of external calls, the contractless-external-function
            // lint) or type information (variant WellFounded bound, forbidden
            // `dyn` in specifications). Each only ADDS rejections.
            let creusot_frontend_errors = {
                let mut errors = creusot_frontend_checks::validate_ghost_block_external_calls(
                    tcx,
                    &ghost_blocks,
                    &extern_specs,
                );
                errors.extend(
                    creusot_frontend_checks::validate_contractless_external_calls(
                        tcx,
                        &extern_specs,
                    ),
                );
                errors.extend(creusot_frontend_checks::validate_variant_types(tcx));
                errors.extend(creusot_frontend_checks::validate_reserved_binding_names(
                    tcx,
                ));
                errors.extend(creusot_frontend_checks::validate_derived_name_aliases(tcx));
                errors.extend(creusot_frontend_checks::validate_forbidden_dyn_in_specs(
                    tcx,
                ));
                errors
            };
            if !creusot_frontend_errors.is_empty() {
                for error in &creusot_frontend_errors {
                    tcx.dcx().span_err(error.span, error.message.clone());
                }
                debug!(
                    count = creusot_frontend_errors.len(),
                    "creusot frontend check error(s)"
                );
                emit_result_protocol_base_exit_code(2);
                return Compilation::Stop;
            }

            if !contracts.is_empty() {
                info!(count = contracts.len(), "functions with contracts found");
                for contract in &contracts {
                    let def_path = tcx.def_path_str(contract.def_id);
                    let trusted_suffix = if contract.trusted { " [trusted]" } else { "" };
                    debug!(def_path = %format!("{def_path}{trusted_suffix}"), "contract");
                    for req in &contract.requires {
                        trace!("  requires: {req}");
                    }
                    for ens in &contract.ensures {
                        trace!("  ensures: {ens}");
                    }
                    for inv in &contract.invariants {
                        trace!("  invariant: {inv}");
                    }
                    for var in &contract.variants {
                        trace!("  variant: {var}");
                    }
                }
            }

            // Filter contracts by pattern if specified
            let contracts_to_verify = if let Some(ref pattern) = self.opts.filter_pattern {
                let filtered: Vec<_> = contracts
                    .iter()
                    .filter(|c| {
                        let def_path = tcx.def_path_str(c.def_id);
                        def_path.contains(pattern)
                    })
                    .cloned()
                    .collect();
                if filtered.len() != contracts.len() {
                    info!(
                        filter = %pattern,
                        matched = filtered.len(),
                        total = contracts.len(),
                        "filter applied"
                    );
                }
                Cow::Owned(filtered)
            } else {
                Cow::Borrowed(contracts.as_slice())
            };

            // Phase 2 termination: build call graph and check recursive functions (#208).
            // Build the call graph from the filtered contracts only — unfiltered functions
            // should not cause structural errors when the user asked to verify a specific
            // function via `--filter`.
            let call_graph = callgraph::build_call_graph(tcx, &contracts_to_verify);
            let recursive_fns = callgraph::detect_recursive_nodes(&call_graph);
            let mutual_recursive_fns = callgraph::detect_mutual_recursion(&call_graph);

            // Phase 3: detect indirect-via-helper mutual recursion in #[check(terminates)]
            // SCCs before any of the per-function termination checks. When a terminates
            // function participates in a cycle (size > 1) we emit a "mutual recursion
            // ... not yet supported" diagnostic and suppress the downstream callee /
            // recursive-variant checks so the user sees the root cause, not a symptom.
            let (mut termination_errors, mutual_unsupported_terminates) =
                callgraph::validate_terminates_mutual_recursion_unsupported(
                    tcx,
                    &contracts_to_verify,
                    &call_graph,
                );
            // The recursive-variant check still applies — a mutual-recursion SCC
            // missing variants should report both the unsupported-mutual-recursion
            // diagnostic and the missing-variant guidance (the latter is what the
            // user needs to address first).
            let recursive_termination_errors =
                callgraph::validate_recursive_termination_requirements(
                    &contracts_to_verify,
                    &recursive_fns,
                    &mutual_recursive_fns,
                );
            for (def_id, errs) in recursive_termination_errors {
                termination_errors.entry(def_id).or_default().extend(errs);
            }
            // Check that #[check(terminates)] functions only call other
            // terminates/logic functions (#2665).
            let callee_errors = callgraph::validate_terminates_callee_requirements(
                tcx,
                &contracts_to_verify,
                &call_graph,
            );
            for (def_id, errs) in callee_errors {
                if mutual_unsupported_terminates.contains(&def_id) {
                    continue;
                }
                termination_errors.entry(def_id).or_default().extend(errs);
            }
            // Check direct recursive calls that change generic arguments.
            let polymorphic_recursion_errors =
                callgraph::validate_polymorphic_recursive_calls(tcx, &contracts_to_verify);
            for (def_id, errs) in polymorphic_recursion_errors {
                if mutual_unsupported_terminates.contains(&def_id) {
                    continue;
                }
                termination_errors.entry(def_id).or_default().extend(errs);
            }
            // Check that loops in #[check(terminates)] functions have variants (#2665).
            let loop_errors =
                callgraph::validate_terminates_loop_variant_requirements(&contracts_to_verify);
            for (def_id, errs) in loop_errors {
                termination_errors.entry(def_id).or_default().extend(errs);
            }
            // Check that trait-impl check modes agree (#2665).
            // E.g., trait declares #[check(terminates)] but impl omits it.
            let check_mode_errors =
                callgraph::validate_trait_impl_check_mode_agreement(tcx, &contracts_to_verify);
            for (def_id, errs) in check_mode_errors {
                termination_errors.entry(def_id).or_default().extend(errs);
            }
            // Check for mutual recursion through default trait methods (#2665).
            // Calling a non-logic default trait method from an impl method on
            // the same trait is potential mutual recursion.
            let default_method_errors = callgraph::validate_default_trait_method_mutual_recursion(
                tcx,
                &contracts_to_verify,
                &call_graph,
            );
            for (def_id, errs) in default_method_errors {
                termination_errors.entry(def_id).or_default().extend(errs);
            }
            if !termination_errors.is_empty() {
                for (def_id, errors) in &termination_errors {
                    let def_path = tcx.def_path_str(*def_id);
                    for err in errors {
                        crate::result_protocol_state::record_termination_error();
                        // Emit each detailed termination error through rustc's
                        // diagnostic channel so cargo forwards it in stderr.
                        // Plain eprintln! is swallowed by cargo's RUSTC_WRAPPER
                        // output handling when compilation fails (#1717).
                        tcx.dcx().err(format!(
                            "trust-wp: termination check failed: `{def_path}`: {err}"
                        ));
                    }
                }
                emit_result_protocol_base_exit_code(2);
                // CacheGuard handles cleanup on this return path
                return Compilation::Stop;
            }

            // Install a ay-aware panic hook before verification. ay sort-mismatch
            // panics are caught by catch_unwind in trust-wp-ay, but the default panic
            // hook fires first and prints "thread panicked at ...", which triggers
            // rustc's ICE handler. This custom hook suppresses output for recognized
            // ay panics while forwarding all others to the original handler. (#1532)
            // The guard restores the default hook on drop, preventing unbounded
            // hook chaining across sessions. (#1867)
            let _panic_hook_guard = if self.opts.verify {
                Some(PanicHookGuard::install_ay_filter())
            } else {
                None
            };

            // Build run_config once — used by both verification and SMT emission.
            let timeout_secs = self.opts.timeout_secs.unwrap_or(60);
            let timeout = Some(std::time::Duration::from_secs(timeout_secs));
            let run_config = verification_context::VerificationRunConfig {
                all_contracts: &contracts,
                ghost_blocks: &ghost_blocks,
                logic_fns: &logic_fn_defs,
                type_invariant_defs: &type_invariant_defs,
                trait_specs: &trait_specs,
                trait_contracts: &trait_contracts,
                recursive_fns: &recursive_fns,
                extern_specs: &extern_specs,
                verbose: self.opts.verbose,
                track_level: self.opts.track_level,
                timeout,
                strict_axioms: self.opts.strict_axioms,
                strict_trust: self.opts.strict_trust,
            };

            // Run ay verification if requested
            if self.opts.verify && !contracts_to_verify.is_empty() {
                let _span = info_span!(
                    "trust_wp::verify_crate",
                    contracts_total = contracts_to_verify.len(),
                    track_level = ?self.opts.track_level,
                    verify_enabled = true,
                )
                .entered();
                let summary = verify_contracts(tcx, &contracts_to_verify, &run_config);
                let verification_exit_code = summary.rustc_process_exit_code();

                // Emit structured result wire line when requested by cargo-trust-wp (#1690).
                emit_result_protocol_line(&summary);
                emitted_result_protocol_line = true;

                // Propagate the verification result protocol exit code (#1365):
                // 0=verified, 1=failure, 2=encoding/solver error.
                // Previously callers had to parse stderr to determine outcomes.
                if verification_exit_code != 0 {
                    emit_requested_smt(tcx, &contracts_to_verify, &run_config, &self.opts);
                    std::process::exit(verification_exit_code);
                }
            }

            // Generate SMT output if requested
            emit_requested_smt(tcx, &contracts_to_verify, &run_config, &self.opts);

            debug!("MIR extraction complete for the active compiler context");

            if !emitted_result_protocol_line {
                // Fail closed (CLAUDE.md "The command line"): a verify run that
                // reached no verification target examined no obligation, so it
                // proved nothing and must not report success. `--no-verify`
                // (analysis-only) runs keep exit 0.
                emit_result_protocol_base_exit_code(i32::from(self.opts.verify) * 2);
            }

            // CacheGuard::drop() handles cleanup; no manual call needed.

            if self.opts.stop_after_analysis {
                Compilation::Stop
            } else {
                Compilation::Continue
            }
        })
    }
}

/// Emit the structured result protocol wire line when `TRUST_WP_RESULT_PROTOCOL`
/// is set (#1690).
///
/// Emits exactly one machine-readable line to stderr. `cargo-trust-wp` strips
/// this line before forwarding human-readable output.
fn emit_result_protocol_line(summary: &reporting::VerificationSummary) {
    if std::env::var(trust_wp_core::result_protocol::RESULT_PROTOCOL_ENV).is_ok() {
        let mut wire = summary.to_structured_result();
        crate::result_protocol_state::snapshot_fatal_result_counters().merge_into(&mut wire);
        // Fail closed: verification ran but examined no obligation (every
        // counter is zero), so nothing was proved. Same predicate the
        // `trust-wp` front door uses (`proved_nothing`).
        if wire.examined_nothing() && wire.base_exit_code == 0 {
            wire.base_exit_code = 2;
        }
        eprintln!("{}", wire.to_wire_line());
    }
}

/// Emit a protocol line for analysis/early-stop paths that do not have a full
/// verification summary (#1690).
fn emit_result_protocol_base_exit_code(base_exit_code: i32) {
    if std::env::var(trust_wp_core::result_protocol::RESULT_PROTOCOL_ENV).is_ok() {
        let wire = crate::result_protocol_state::snapshot_fatal_result_counters()
            .into_structured_result(base_exit_code);
        eprintln!("{}", wire.to_wire_line());
    }
}

/// Emit a protocol line for early-stop paths that are driver errors rather
/// than parse/termination/recursion categories.
fn emit_result_protocol_error_exit(error_count: u64) {
    if std::env::var(trust_wp_core::result_protocol::RESULT_PROTOCOL_ENV).is_ok() {
        let mut wire = crate::result_protocol_state::snapshot_fatal_result_counters()
            .into_structured_result(2);
        wire.errors = error_count;
        eprintln!("{}", wire.to_wire_line());
    }
}

/// Emit SMT artifacts to the requested sinks (stdout and/or directory).
///
/// Returns early if neither `--emit-smt` nor `--emit-smt-dir` is set, or if
/// there are no contracts. Builds artifacts once and writes files first, then
/// prints to stdout — so a later stdout failure does not drop on-disk artifacts.
/// (#1691)
fn emit_requested_smt(
    tcx: TyCtxt<'_>,
    contracts: &[super::contracts::FunctionContract],
    config: &verification_context::VerificationRunConfig<'_>,
    opts: &TrustWpOptions,
) {
    let wants_stdout = opts.emit_smt;
    let wants_dir = opts.emit_smt_dir.is_some();
    if (!wants_stdout && !wants_dir) || contracts.is_empty() {
        return;
    }

    let artifacts = build_smt_artifacts(
        tcx,
        contracts,
        config.recursive_fns,
        config.type_invariant_defs,
        config.trait_specs,
        config.extern_specs,
        config.logic_fns,
    );

    // Write files first (safer default — stdout issues should not lose on-disk artifacts)
    if let Some(ref dir) = opts.emit_smt_dir {
        write_smt_artifacts_to_dir(dir, &artifacts);
    }

    if wants_stdout {
        emit_smt_artifacts_to_stdout(&artifacts);
    }
}

fn stop_on_logic_recursion_errors(tcx: TyCtxt<'_>) -> bool {
    let logic_recursion_errors = super::logic::validate_logic_fn_recursion(tcx);
    if logic_recursion_errors.is_empty() {
        return false;
    }

    for error in logic_recursion_errors {
        crate::result_protocol_state::record_logic_recursion_error();
        tcx.dcx().err(format!(
            "trust-wp: logic recursion check failed: `{}`: {}",
            error.full_path, error.message
        ));
    }
    true
}

/// Check for Ghost/Snapshot type escape (#2686).
///
/// Detects non-logic, non-ghost program functions that accept `Ghost<T>` or
/// `Snapshot<T>` parameters and return a non-ghost, non-unit type. This pattern
/// allows extracting ghost values into program context, which is unsound.
///
/// Returns the number of errors emitted.
fn check_ghost_type_escape(tcx: TyCtxt<'_>, ghost_blocks: &[super::ghost::GhostBlock]) -> usize {
    use rustc_hir::{def::DefKind, def_id::LocalDefId};

    // Skip trust-wp infrastructure crates — they legitimately use Ghost<T>
    // parameters for specification purposes (extern specs, ghost helpers).
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    if matches!(
        local_crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts" | "trust_wp_lib"
    ) {
        return 0;
    }

    let mut error_count = 0usize;
    let mut ghost_spans_by_fn: std::collections::HashMap<LocalDefId, Vec<rustc_span::Span>> =
        std::collections::HashMap::new();
    for block in ghost_blocks {
        ghost_spans_by_fn
            .entry(block.containing_fn)
            .or_default()
            .push(block.span);
    }

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        let def_kind = tcx.def_kind(def_id);

        // Only check functions and associated functions (methods).
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        // Specification type-check helpers (`__trust_wp_spec_tc_*`, emitted for
        // contracts on bodyless trait methods) are not program code.
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }

        let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
        let attrs = tcx.hir_attrs(hir_id);

        // Skip logic/predicate functions — Ghost<T> parameters are expected.
        if super::logic::discovery::has_logic_marker(attrs) {
            continue;
        }

        // Skip #[check(ghost)] functions — ghost context is expected.
        if crate::attr_utils::has_check_mode(attrs, "ghost") {
            continue;
        }

        // Skip #[check(terminates)] functions — they may use ghost params.
        if crate::attr_utils::has_check_mode(attrs, "terminates") {
            continue;
        }

        // Get the function signature.
        let sig = tcx.fn_sig(def_id).instantiate_identity();
        let sig = sig.skip_binder();
        let inputs = sig.inputs();
        let output = sig.output();

        // Check if any parameter is Ghost<T> or Snapshot<T> in a shape that can
        // actually feed a non-ghost result. Creusot examples commonly pass
        // erased invariant tokens through executable APIs; those tokens are
        // authority, not values being extracted.
        let has_ghost_param = inputs
            .iter()
            .any(|ty| is_escape_relevant_ghost_param(tcx, *ty));
        if !has_ghost_param {
            continue;
        }

        // Allow if return type is unit.
        if output.is_unit() {
            continue;
        }

        // Allow if return type is Ghost<T> or Snapshot<T>.
        if super::ghost::type_helpers::is_ghost_like_type(tcx, output) {
            continue;
        }

        // Allow if return type is a reference to Ghost<T> or Snapshot<T>.
        // This handles `&Ghost<T>`, `&Snapshot<T>` return types.
        let peeled_output = output.peel_refs();
        if super::ghost::type_helpers::is_ghost_like_type(tcx, peeled_output) {
            continue;
        }

        let def_path = tcx.def_path_str(def_id);
        if tcx
            .hir_node_by_def_id(local_def_id)
            .associated_body()
            .is_none()
        {
            continue;
        }

        let Some(body_with_facts) = try_get_body_with_context(tcx, local_def_id) else {
            let span = tcx.def_span(def_id);
            tcx.dcx().span_err(
                span,
                format!(
                    "ghost type escape: function `{def_path}` accepts Ghost/Snapshot \
                     parameter(s) and returns non-ghost type `{output}`, but trust-wp could \
                     not inspect its MIR body to prove the ghost data is not extracted."
                ),
            );
            error_count += 1;
            continue;
        };

        let errors = super::ghost::erasure::check_ghost_type_escape_body(
            tcx,
            &body_with_facts.body,
            ghost_spans_by_fn
                .get(&local_def_id)
                .map_or(&[], Vec::as_slice),
            &def_path,
            output,
        );
        for error in errors {
            tcx.dcx().span_err(error.span, error.message);
            error_count += 1;
        }
    }

    error_count
}

fn is_escape_relevant_ghost_param<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let Some((wrapper_name, inner_ty)) = ghost_wrapper_inner_type(tcx, ty) else {
        return false;
    };

    // Invariant tokens are erased permission authority. A program function may
    // require them to open an invariant and still return ordinary runtime data
    // borrowed from non-ghost inputs.
    if wrapper_name == "Ghost" && is_invariant_tokens_type(tcx, inner_ty.peel_refs()) {
        return false;
    }

    true
}

fn ghost_wrapper_inner_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> Option<(&'static str, Ty<'tcx>)> {
    let inner = ty.peel_refs();
    let TyKind::Adt(adt_def, args) = inner.kind() else {
        return None;
    };
    let adt_def_id = adt_def.did();
    let crate_name = tcx.crate_name(adt_def_id.krate).to_string();
    let def_path = tcx.def_path_str(adt_def_id);
    if !is_trust_wp_ghost_or_snapshot_path(&crate_name, &def_path) {
        return None;
    }
    let wrapper_name = def_path.rsplit("::").next().unwrap_or("");
    let wrapper_name = match wrapper_name {
        "Ghost" => "Ghost",
        "Snapshot" => "Snapshot",
        _ => return None,
    };
    let inner_ty = args.iter().find_map(|arg| arg.as_type())?;
    Some((wrapper_name, inner_ty))
}

fn is_invariant_tokens_type(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return false;
    };
    let adt_def_id = adt_def.did();
    let crate_name = tcx.crate_name(adt_def_id.krate).to_string();
    let def_path = tcx.def_path_str(adt_def_id);
    matches!(
        crate_name.as_str(),
        "trust_wp_std" | "creusot_std" | "creusot_contracts"
    ) && def_path.rsplit("::").next() == Some("Tokens")
}

fn is_trust_wp_ghost_or_snapshot_path(crate_name: &str, def_path: &str) -> bool {
    if !matches!(
        crate_name,
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts"
    ) {
        return false;
    }
    matches!(def_path.rsplit("::").next(), Some("Ghost" | "Snapshot"))
}

fn should_preload_builtin_extern_specs(local_crate_name: &str) -> bool {
    local_crate_name != "trust_wp_std"
}

/// Default callbacks that just run normal rustc compilation.
pub(crate) struct DefaultCallbacks;

impl Callbacks for DefaultCallbacks {}
