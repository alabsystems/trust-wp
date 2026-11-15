// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

use rustc_hir::def_id::DefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};
use tracing::info_span;
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::{tuple_field_logic_fn_index, tuple_field_logic_fn_name},
        ProjectedFinalPin, PureExpr,
    },
    logic::TypeInvariantDef,
    tracing_init::{TIMING_STAGE_EXTRACT_SPAN, TIMING_STAGE_PARSE_SPAN},
};
use trust_wp_driver::StdSpec;

use super::{
    arg_names::{
        closure_capture_substitutions, collapse_projected_field_captures,
        collect_mut_ref_arg_names, get_arg_names_for_mir_extraction,
    },
    clauses::{parse_clause_inputs, ParsedClauseInputs},
    types::{LoopFields, LoopObligationGroup, MutBorrowFields, ParsedContract},
};
use crate::{
    callbacks::{
        discovery::{
            fn_calls_through_generic_fn_bound, fn_owes_abort_or_callee_precondition,
            has_arithmetic_panic_sites, is_bodyful_trait_method,
        },
        try_get_body_with_context,
    },
    contracts::FunctionContract,
    mir_analysis::{
        body_entry_diverges_via_panic, body_has_reachable_obligation_source,
        body_returns_a_stale_store_read, clear_qualified_assoc_const_definitions,
        collect_arithmetic_panic_obligations, collect_call_effects_for_blocks,
        collect_loop_body_call_obligations_split, collect_post_loop_arithmetic_obligations,
        collect_unannotated_loop_arithmetic_obligations, collect_unannotated_loop_obligations,
        contract_signature, detect_loops,
        diagnostics::{ExtractionDiagKind, ExtractionDiagnostics},
        effects::fail_closed_marker,
        extract_loop_body, extract_mut_borrow_body, extract_param_destructuring_substitutions,
        extract_return_expr_spanned, extract_return_expr_with_context_detailed, get_mir_body,
        loop_assigned_locals_by_header, loop_condition_exit_write, loop_has_unmodeled_exit,
        loop_lane_exit, normalize_immutable_ref_param_derefs, params_with_stale_call_final_credit,
        take_qualified_assoc_const_definitions, unwalked_charged_assert_sites,
        with_charged_assert_recording, with_dead_edge_recording, ArithmeticRegion, CallSpecContext,
        LaneExit, LoopAnalysis, LoopBodySpecContext, LoopEntryValues, MutBorrowBody,
        ProvedDeadEdges, SpannedBodyExpr,
    },
};

#[derive(Default)]
struct ExtractionData {
    result_expr: Option<PureExpr>,
    result_expr_spanned: Option<SpannedBodyExpr>,
    mut_borrow_body: Option<MutBorrowBody>,
    /// Caller-side expiry pins proven by `projected_expiry` (#prophecy-slots M5).
    projected_final_pins: Vec<ProjectedFinalPin>,
    loop_analysis: Option<LoopAnalysis>,
    loop_obligation_groups: Vec<LoopObligationGroup>,
    mut_ref_param_names: HashSet<String>,
    stale_call_final_params: HashSet<String>,
    param_destructuring_subs: HashMap<String, PureExpr>,
    call_assumptions: Vec<PureExpr>,
    pre_loop_call_assumptions: Vec<PureExpr>,
    call_obligations: Vec<PureExpr>,
    pre_loop_call_obligations: Vec<PureExpr>,
    post_loop_call_obligations: Vec<PureExpr>,
    /// #1075/#1401 returning-path facts (premise only the postconditions).
    returning_path_facts: Vec<PureExpr>,
    /// Set when context extraction gave up before walking the whole body
    /// while the body can still carry obligations (see
    /// `ParsedContract::extraction_fail_closed_reason`).
    extraction_fail_closed_reason: Option<String>,
    /// How many of `call_obligations` are the panic-unreachability goal for a
    /// body that can never return (see `ParsedContract`).
    panic_unreachability_obligations: usize,
    /// How many of `call_obligations` are a callee's USER-WRITTEN
    /// `#[requires(false)]` (see `ParsedContract`).
    user_written_false_obligations: usize,
    /// Switch edges the primary walk proved never taken (see `ParsedContract`).
    proved_dead_edges: ProvedDeadEdges,
}

pub(in crate::callbacks) struct ExtractionContext<'a> {
    pub(super) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) extern_specs: &'a HashMap<String, StdSpec>,
    /// The session's final invariant definitions, the set discovery read when
    /// it made a contract-free caller a target (`fn_owes_abort_or_callee_precondition`).
    pub(super) type_invariant_defs: &'a [TypeInvariantDef],
    pub(super) report_errors: bool,
    pub(super) has_type_invariant_injection: bool,
}

impl<'a> ExtractionContext<'a> {
    pub(in crate::callbacks) fn new(
        user_specs: &'a HashMap<DefId, StdSpec>,
        trait_specs: &'a HashMap<DefId, StdSpec>,
        extern_specs: &'a HashMap<String, StdSpec>,
        type_invariant_defs: &'a [TypeInvariantDef],
        report_errors: bool,
        has_type_invariant_injection: bool,
    ) -> Self {
        Self {
            user_specs,
            trait_specs,
            extern_specs,
            type_invariant_defs,
            report_errors,
            has_type_invariant_injection,
        }
    }
}

/// Parse a contract's expressions and extract MIR body.
/// Returns None if there are no valid contract expressions.
pub(in crate::callbacks) fn parse_and_extract_contract(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    recursive_fns: &HashSet<DefId>,
    ctx: &ExtractionContext<'_>,
) -> Option<ParsedContract> {
    let parse_span = info_span!(TIMING_STAGE_PARSE_SPAN).entered();
    let mut clause_inputs = parse_clause_inputs(tcx, contract, ctx.report_errors)?;

    rename_binders_apart_from_program_names(tcx, contract, &mut clause_inputs);
    let state_params =
        place_parameter_reads_of(tcx, contract, &mut clause_inputs, ctx.report_errors)?;
    apply_capture_substitutions(tcx, contract, &mut clause_inputs);
    clause_inputs.rewrite_each_expr(|expr| {
        crate::assoc_const_paths::normalize_local_assoc_const_paths(tcx, contract.def_id, expr)
    });

    let has_explicit_or_injected_clauses =
        clause_inputs.has_explicit_clauses() || ctx.has_type_invariant_injection;

    // Most empty-contract functions are intentionally skipped.
    // Exception: trait default methods with bodies may still carry call-site
    // obligations that must be proved (e.g., default method calls contracted
    // trait method, #1203).
    // Contract-free functions with machine-int arithmetic panic sites owe
    // Creusot's program-function preconditions for those operations.
    // A second exception: calls through a generic `F: Fn/FnMut/FnOnce` bound
    // owe Creusot's `call requires` goal `f.precondition(args)`, so a function
    // whose only obligations are those calls is still a target.
    // A third: a diverging call is Creusot's `Terminator::Abort` goal, a
    // contracted callee's `#[requires]` is its `callee requires` goal and a
    // built-in index is its `index in bounds` goal. This
    // reads the SAME predicate `discover_abort_obligation_functions` used to
    // make the function a target: a body admitted there and refused here would
    // be a target of nothing, which is the shape this exception exists to
    // close.
    if !has_explicit_or_injected_clauses
        && !(is_bodyful_trait_method(tcx, contract.local_def_id)
            || has_arithmetic_panic_sites(tcx, contract.local_def_id)
            || fn_calls_through_generic_fn_bound(tcx, contract.local_def_id)
            || fn_owes_abort_or_callee_precondition(
                tcx,
                contract.local_def_id,
                ctx.type_invariant_defs,
            ))
    {
        return None;
    }

    drop(parse_span);

    let extract_span = info_span!(TIMING_STAGE_EXTRACT_SPAN).entered();
    let arg_names = prepare_arg_names(tcx, contract, &clause_inputs.ensures)?;
    warm_mir_cache(tcx, contract);

    clear_qualified_assoc_const_definitions();
    let mut extraction_data = extract_contract_body(
        tcx,
        contract,
        recursive_fns,
        &arg_names,
        clause_inputs.needs_loop_analysis(),
        ctx,
    );

    let mut assoc_const_substitutions = take_qualified_assoc_const_definitions();
    assoc_const_substitutions
        .extend(crate::mir_analysis::extract::collect_generic_assoc_const_definitions(tcx));
    clause_inputs.rewrite_all_exprs(&assoc_const_substitutions);
    // `requires`/`ensures` already name a pattern binding as its parameter
    // projection in their text (D-177), the text every caller reads too. They
    // are not rewritten again from this body's MIR: for an impl method they
    // may be the TRAIT's clauses, whose names are the trait's parameters, and
    // this body's binding of the same spelling would capture them
    // (trait_clause_inherited_pattern_binding_captures_trait_param).
    clause_inputs.rewrite_body_level_exprs(&extraction_data.param_destructuring_subs);
    if let Some(body_with_context) = try_get_body_with_context(tcx, contract.local_def_id) {
        let mir_body = get_mir_body(&body_with_context);
        let normalize_ref_derefs = normalize_immutable_ref_param_derefs(tcx, mir_body, &arg_names);
        clause_inputs.rewrite_each_expr(|expr| normalize_ref_derefs(expr));
    }
    apply_capture_substitutions_to_extraction_data(tcx, contract, &mut extraction_data);
    drop(extract_span);

    let mut parsed = assemble_parsed_contract(
        contract,
        clause_inputs,
        arg_names,
        state_params,
        extraction_data,
    );
    // Recognize the recursive `&mut self` match-reborrow shape (rusthorn
    // take_some) for prophecy-pinning premise synthesis in per_contract.
    if let Some(body_with_context) = try_get_body_with_context(tcx, contract.local_def_id) {
        let mir_body = get_mir_body(&body_with_context);
        parsed.reborrow_prophecy = crate::mir_analysis::analyze_reborrow_prophecy(
            tcx,
            contract.def_id,
            mir_body,
            &parsed.arg_names,
        );
    }
    rewrite_current_closure_projected_fields(tcx, contract, &mut parsed);
    Some(parsed)
}

/// Rename apart every binder in a clause that shadows a name the passes
/// below read as a program variable: a parameter, `result`, `self`, a generic
/// parameter, or a name some clause reads free (a local, a constant). Those
/// passes key on the name (a parameter's sort, a `&mut` parameter's final
/// value, a closure capture's field), so each read a shadowing binder as the
/// program variable: `let p = e + 7; p@ == e@` read `p@` as the parameter's.
fn rename_binders_apart_from_program_names(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    clause_inputs: &mut ParsedClauseInputs,
) {
    let mut names: HashSet<String> =
        get_arg_names_for_mir_extraction(tcx, contract.def_id, contract.local_def_id)
            .into_iter()
            .collect();
    names.extend(["result", "self"].map(String::from));
    let mut generics = Some(tcx.generics_of(contract.def_id));
    while let Some(level) = generics {
        names.extend(
            level
                .own_params
                .iter()
                .map(|param| param.name.as_str().to_string()),
        );
        generics = level.parent.map(|parent| tcx.generics_of(parent));
    }
    clause_inputs.rewrite_each_expr(|expr| {
        names.extend(expr.free_vars());
        expr.clone()
    });
    clause_inputs.rewrite_each_expr(|expr| expr.rename_binders_apart(|name| names.contains(name)));
}

/// Read every parameter of the contract where its clauses read it, through
/// `formula::elaborate::state` over the signature every call of this
/// function reads its clauses over too ([`contract_signature`]): a binder of
/// a parameter is the parameter, `old(..)` included, and a clause that reads a
/// parameter at a reference level its type does not have (`*x` of an `x:
/// i32`, `^r` of an `r: &i32`), or a postcondition that reads a `&mut`
/// parameter's referent through a value the state rule cannot see the
/// parameter in (`*t.0` of a `let t = (p, 0)`, a `&mut` a destructuring
/// parameter binds), is refused. A closure's parameters are read alike; its
/// environment is none of them, and its captures change between calls.
///
/// Returns the signature's `&mut`-holding parameters, the set
/// `contract_transform` reads the postconditions' states over (every call
/// reads them over the same set, `call_signature`), or `None` on a refusal.
fn place_parameter_reads_of(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    clause_inputs: &mut ParsedClauseInputs,
    report_errors: bool,
) -> Option<HashSet<String>> {
    use trust_wp_core::formula::elaborate::{
        first_final_held_through_a_reference_parameter, place_parameter_reads,
        resolve_aliases_with, ClauseKind,
    };

    let mut params = get_arg_names_for_mir_extraction(tcx, contract.def_id, contract.local_def_id);
    if tcx.def_kind(contract.def_id) == rustc_hir::def::DefKind::Closure && !params.is_empty() {
        params.remove(0);
    }
    let signature = contract_signature(tcx, contract.def_id, &params);
    let def_path = tcx.def_path_str(contract.def_id);
    let mut refusal = None;
    let mut place = |kind: &str, clause_kind, clauses: &mut Vec<PureExpr>, texts: &[String]| {
        for (at, clause) in clauses.iter_mut().enumerate() {
            if refusal.is_some() {
                return;
            }
            match place_parameter_reads(clause, &signature, clause_kind) {
                Ok(placed) => *clause = placed,
                Err(reason) => {
                    let text = texts.get(at).map_or("", String::as_str);
                    refusal = Some(format!(
                        "failed to parse {kind} '{text}' of `{def_path}`: {reason}"
                    ));
                }
            }
        }
    };
    place(
        "requires",
        ClauseKind::Precondition,
        &mut clause_inputs.requires,
        &contract.requires,
    );
    place(
        "ensures",
        ClauseKind::Postcondition,
        &mut clause_inputs.ensures,
        &contract.ensures,
    );
    if let Some(refusal) = refusal {
        if report_errors {
            crate::result_protocol_state::record_parse_error();
        }
        eprintln!("trust-wp: frontend diagnostic: {refusal}");
        return None;
    }
    let reference = |name: &str| signature.reference(name);
    let mut loop_refusal = None;
    for expr in clause_inputs
        .invariants
        .iter_mut()
        .chain(clause_inputs.variants.iter_mut())
        .chain(
            clause_inputs
                .per_loop_invariants
                .iter_mut()
                .chain(clause_inputs.per_loop_variants.iter_mut())
                .flat_map(|(_, _, exprs)| exprs.iter_mut()),
        )
    {
        *expr = resolve_aliases_with(expr, &|name| signature.has(name));
        // A loop invariant's `^x.m`, `^*x` of a reference parameter reads
        // the final value of a borrow `x`'s referent holds, as a clause of
        // the contract does: refused by the same typed decision (D-183).
        if loop_refusal.is_none() {
            if let Some(reason) = first_final_held_through_a_reference_parameter(
                expr,
                &reference,
                signature.final_readers(),
            ) {
                loop_refusal = Some(format!(
                    "loop invariant final value refused (fail-closed): loop invariant or variant \
                     '{expr}' of `{def_path}`: {reason}"
                ));
            }
        }
    }
    if let Some(refusal) = loop_refusal {
        if report_errors {
            crate::result_protocol_state::record_parse_error();
        }
        eprintln!("trust-wp: frontend diagnostic: {refusal}");
        return None;
    }
    Some(signature.mut_ref_params().clone())
}

fn apply_capture_substitutions(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    clause_inputs: &mut ParsedClauseInputs,
) {
    // For closures, map captured variable names to closure-env field names so
    // contracts and MIR extraction use the same symbols (Phase 3, #358).
    let result = closure_capture_substitutions(tcx, contract.local_def_id);
    clause_inputs.rewrite_all_exprs(&result.substitutions);

    // Rust 2021 minimal captures: when a closure captures `p.1` (not the whole
    // `p`), collapse `__trust_wp_tuple_get_1(Var("p"))` → `Var("self.N")`. (#2554)
    if !result.projected_captures.is_empty() {
        clause_inputs.rewrite_each_expr(|expr| {
            collapse_projected_field_captures(expr, &result.projected_captures)
        });
    }
}

#[allow(clippy::needless_pass_by_value)] // PureExpr by-value is idiomatic for rewrite chains
fn rewrite_closure_capture_expr(
    expr: PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    projected_captures: &[(String, usize, String)],
) -> PureExpr {
    let substituted = expr.substitute(substitutions);
    if projected_captures.is_empty() {
        substituted
    } else {
        collapse_projected_field_captures(&substituted, projected_captures)
    }
}

fn apply_capture_substitutions_to_extraction_data(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    extraction_data: &mut ExtractionData,
) {
    let result = closure_capture_substitutions(tcx, contract.local_def_id);
    if result.substitutions.is_empty() && result.projected_captures.is_empty() {
        return;
    }

    let rewrite = |expr: PureExpr| {
        rewrite_closure_capture_expr(expr, &result.substitutions, &result.projected_captures)
    };

    extraction_data.result_expr = extraction_data.result_expr.take().map(&rewrite);
    extraction_data.result_expr_spanned =
        extraction_data
            .result_expr_spanned
            .take()
            .map(|spanned| SpannedBodyExpr {
                expr: rewrite(spanned.expr),
                span: spanned.span,
            });
    extraction_data.call_assumptions = extraction_data
        .call_assumptions
        .drain(..)
        .map(&rewrite)
        .collect();
    extraction_data.pre_loop_call_assumptions = extraction_data
        .pre_loop_call_assumptions
        .drain(..)
        .map(&rewrite)
        .collect();
    extraction_data.call_obligations = extraction_data
        .call_obligations
        .drain(..)
        .map(&rewrite)
        .collect();
    extraction_data.pre_loop_call_obligations = extraction_data
        .pre_loop_call_obligations
        .drain(..)
        .map(&rewrite)
        .collect();
    extraction_data.post_loop_call_obligations = extraction_data
        .post_loop_call_obligations
        .drain(..)
        .map(&rewrite)
        .collect();
    extraction_data.returning_path_facts = extraction_data
        .returning_path_facts
        .drain(..)
        .map(&rewrite)
        .collect();
    for group in &mut extraction_data.loop_obligation_groups {
        group.condition = group.condition.clone().map(&rewrite);
        group.obligations = group.obligations.drain(..).map(&rewrite).collect();
    }
}

fn rewrite_current_closure_projected_fields(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    parsed: &mut ParsedContract,
) {
    if tcx.def_kind(contract.local_def_id.to_def_id()) != rustc_hir::def::DefKind::Closure {
        return;
    }

    parsed.rewrite_all_exprs(rewrite_current_closure_projected_field_expr);
}

fn rewrite_current_closure_projected_field_expr(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(rewrite_current_closure_projected_field_node)
}

fn rewrite_current_closure_projected_field_node(expr: PureExpr) -> PureExpr {
    if let Some(projected) = rewrite_current_closure_nested_tuple_selector(&expr) {
        return projected;
    }
    let PureExpr::Var(name, _) = &expr else {
        return expr;
    };
    let mut segments = name.split('.');
    let Some("self") = segments.next() else {
        return expr;
    };
    let Some(capture_idx) = segments.next() else {
        return expr;
    };
    if capture_idx.parse::<usize>().is_err() {
        return expr;
    }

    let field_path: Option<Vec<usize>> = segments
        .map(|segment| segment.parse::<usize>().ok())
        .collect();
    let Some(field_path) = field_path else {
        return expr;
    };
    if field_path.is_empty() {
        return expr;
    }

    let mut projected = PureExpr::Var(format!("self.{capture_idx}"), None);
    for field_idx in field_path {
        projected = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(field_idx),
            args: vec![projected],
        };
    }
    projected
}

fn rewrite_current_closure_nested_tuple_selector(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    if args.len() != 1 || tuple_field_logic_fn_index(name).is_none() {
        return None;
    }
    let PureExpr::LogicFnCall {
        name: capture_selector,
        args: capture_args,
    } = &args[0]
    else {
        return None;
    };
    let capture_idx = tuple_field_logic_fn_index(capture_selector)?;
    if !matches!(
        capture_args.as_slice(),
        [PureExpr::Var(base, _)] if base == "self"
    ) {
        return None;
    }
    Some(PureExpr::LogicFnCall {
        name: name.clone(),
        args: vec![PureExpr::Var(format!("self.{capture_idx}"), None)],
    })
}

fn prepare_arg_names(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    ensures: &[PureExpr],
) -> Option<Vec<String>> {
    let arg_names = get_arg_names_for_mir_extraction(tcx, contract.def_id, contract.local_def_id);

    // Reject functions where a parameter is named `result` and ensures clauses
    // use it as a free variable. The `result` identifier is reserved for the
    // return value in postconditions; a parameter with the same name creates an
    // ambiguity that can cause unsound verification (#674).
    //
    // Closure-binder forms like `#[ensures(|(fst, snd)| fst == snd)]` are safe
    // because the closure parameters shadow the reserved name — `"result"` is
    // not free in the parsed postcondition (#2304).
    if arg_names.iter().any(|name| name == "result") && ensures_uses_reserved_result_name(ensures) {
        let def_path = tcx.def_path_str(contract.def_id);
        eprintln!(
            "trust-wp: error: function `{def_path}` has a parameter named `result`, \
             which conflicts with the reserved `result` identifier in #[ensures] postconditions"
        );
        return None;
    }

    Some(arg_names)
}

/// Returns `true` if any `ensures` clause uses `"result"` as a free variable.
///
/// Closure parameters, quantifier binders, let bindings, and match patterns
/// all shadow the name, so `#[ensures(|(fst, snd)| fst == snd)]` returns
/// `false` even when the function has a parameter named `result` (#2304).
pub(super) fn ensures_uses_reserved_result_name(ensures: &[PureExpr]) -> bool {
    ensures
        .iter()
        .any(|expr| expr.free_vars().contains("result"))
}

fn warm_mir_cache(tcx: TyCtxt<'_>, contract: &FunctionContract) {
    // Ensure borrow checking has run within the active MIR-retention scope.
    // Without this, try_get_body_with_context returns None and we can't
    // extract mut_borrow_body for mutable reference verification.
    // Guard: skip items without an HIR body. Required trait methods are the
    // key case: `is_mir_available` can still be true because rustc synthesizes
    // an unreachable shim, but `mir_borrowck` panics via `body_owned_by`.
    // (#972, #2437)
    let def_id = contract.local_def_id.to_def_id();
    if !tcx.is_mir_available(def_id)
        || tcx
            .hir_node_by_def_id(contract.local_def_id)
            .body_id()
            .is_none()
    {
        return;
    }

    let root = tcx.typeck_root_def_id(def_id).expect_local();
    let _ = tcx.mir_borrowck(root);
}

/// The spec table a recursive function's own body extraction must see.
///
/// A recursive function's self-call resolves against this table, so the
/// function's OWN contract has to be in it. `build_user_spec_table` drops any
/// contract whose requires AND ensures are both empty, so without this
/// injection a `#[check(terminates)] #[variant(n)]` function that writes no
/// `#[requires]`/`#[ensures]` has no entry, its self-call falls through
/// `resolve_call` to Step 9 Opaque, and `handle_opaque_call` owes it
/// `requires(false)` — a fabricated obligation that becomes the function's only
/// `ensures` clause and refutes it at the degenerate `n = 1` (D-26).
///
/// THE INJECTION IS UNCONDITIONAL ON THE CONTRACT BEING NON-EMPTY, and that is
/// the point: an EMPTY self-spec is exactly Creusot's treatment of a local
/// contract-less callee. `creusot/src/translation/specification.rs:266-275`
/// pushes `requires false` only when
/// `contract.is_empty() && !def_id.is_local() && is_external_crate(krate) &&
/// item_type == Program` — a LOCAL callee keeps an empty contract and its
/// caller stays provable.
///
/// An empty self-spec is not a free pass. `handle_direct_spec_call` binds the
/// call result to a fresh symbol and havocs EVERY `&mut` argument
/// (`spec_mutating_ref_arg_positions` with `callee_forwards_borrows = false`
/// returns `all_mut_ref_arg_positions`, ignoring the spec's text), so the
/// caller learns nothing about the result and nothing about the referents. The
/// function's own body obligations — variant decrease, machine-integer
/// arithmetic, panic sites — are unaffected: they are raised by the body walk,
/// not by the self-call's spec.
///
/// Scope: this table is built per contract and is used only for THAT
/// function's own body extraction, so the injected entry is visible to the
/// self-call and to nothing else. A call to some OTHER local contract-less
/// function still resolves Opaque and is still owed `requires(false)`.
pub(super) fn effective_user_specs_for_extraction<'a>(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    recursive_fns: &HashSet<DefId>,
    arg_names: &[String],
    user_specs: &'a HashMap<DefId, StdSpec>,
) -> Cow<'a, HashMap<DefId, StdSpec>> {
    if recursive_fns.contains(&contract.def_id) {
        let mut self_spec = StdSpec {
            // READ, never recomputed: the self-call owes exactly the parameter
            // type invariants the body holds as premises, and this entry
            // overrides the table's, so blanking it left a recursive call the
            // one call site in the crate that paid nothing. An absent table
            // entry means `build_user_spec_table` computed no clause for this
            // callee, which is the same empty vector.
            inv_requires: user_specs
                .get(&contract.def_id)
                .map(|spec| spec.inv_requires.clone())
                .unwrap_or_default(),
            // Carried for the same reason, one relation over: this map is what
            // the closure-construction site reads to decide what it owes, and
            // a blanked vector here would grant a body premises the site that
            // built it never paid for.
            capture_inv_requires: user_specs
                .get(&contract.def_id)
                .map(|spec| spec.capture_inv_requires.clone())
                .unwrap_or_default(),
            requires: contract.requires.clone(),
            ensures: contract.ensures.clone(),
            param_names: Some(arg_names.to_vec()),
        };
        // The RAW contract text, unlike the table entry this overrides, has
        // not had its colliding logic-function names resolved; without this a
        // recursive call re-parses `self.m(..)` as an unresolvable short name
        // and the encoder refuses the whole clause.
        crate::logic::identity::resolve_spec_clauses_in_scope(tcx, contract.def_id, &mut self_spec);
        let mut merged = user_specs.clone();
        merged.insert(contract.def_id, self_spec);
        Cow::Owned(merged)
    } else {
        Cow::Borrowed(user_specs)
    }
}

fn extract_contract_body(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    recursive_fns: &HashSet<DefId>,
    arg_names: &[String],
    needs_loop_analysis: bool,
    ctx: &ExtractionContext<'_>,
) -> ExtractionData {
    let Some(body_with_facts) = try_get_body_with_context(tcx, contract.local_def_id) else {
        return ExtractionData::default();
    };

    // Self-spec injection: ensure the function's own spec includes explicit
    // param_names so that recursive self-calls resolve via DirectSpec with
    // correct parameter-to-argument substitutions. build_user_spec_table
    // inserts specs with param_names: None; adding explicit param_names here
    // ensures resolve_arg_names_or_warn has a fallback for recursive calls
    // where tcx arg name resolution might fail (#1322).
    let effective_user_specs = effective_user_specs_for_extraction(
        tcx,
        contract,
        recursive_fns,
        arg_names,
        ctx.user_specs,
    );

    let mir_body = get_mir_body(&body_with_facts);
    // Try to extract return expression with context for function call support
    // This uses TyCtxt to resolve function paths and look up std specs
    // Charged assert sites (arithmetic panic asserts, index bounds checks)
    // for which a KEPT obligation lane stated an obligation (the primary
    // extraction below, the loop / entry / post-loop / unannotated region
    // walks). Checked against every reachable site at the
    // end of this function: a site no lane walked demotes the verdict.
    let charged_asserts_walked: std::cell::RefCell<HashSet<rustc_middle::mir::BasicBlock>> =
        std::cell::RefCell::new(HashSet::new());
    let ((context_outcome, primary_dead_edges), primary_sites) =
        with_charged_assert_recording(mir_body, || {
            with_dead_edge_recording(tcx, mir_body, || {
                extract_return_expr_with_context_detailed(
                    tcx,
                    mir_body,
                    arg_names,
                    &effective_user_specs,
                    ctx.trait_specs,
                    ctx.extern_specs,
                )
            })
        });
    charged_asserts_walked.borrow_mut().extend(primary_sites);
    // A walk that gave up proves no edge dead: the verdict it feeds is
    // demoted by `extraction_fail_closed_reason` or rests on a fallback walk.
    let proved_dead_edges = if context_outcome.value.is_some() {
        primary_dead_edges
    } else {
        ProvedDeadEdges::default()
    };
    // Also extract with source spans for better error reporting
    // Now supports function calls with std spec lookup (see #63)
    let result_expr_spanned = extract_return_expr_spanned(
        tcx,
        mir_body,
        arg_names,
        &effective_user_specs,
        ctx.trait_specs,
        ctx.extern_specs,
    );
    let used_spanned_fallback = context_outcome.value.is_none() && result_expr_spanned.is_some();
    if ctx.report_errors && context_outcome.value.is_none() {
        if let Some(warning) = format_context_extraction_warning(
            &tcx.def_path_str(contract.def_id),
            &context_outcome.diagnostics,
            used_spanned_fallback,
        ) {
            eprintln!("{warning}");
        }
    }
    // Fail closed: when context extraction returned no value
    // because of a real gap (anything but a control-flow cycle, which the loop
    // lanes own), obligations past the gap — a panic arm, an `assert!`, a
    // callee precondition — may never have been walked. If the body has any
    // such site, a `Verified` verdict for this contract is demoted to unknown.
    // A body whose entry diverges via a panic already carries the `false`
    // obligation below, which subsumes every obligation it could miss.
    let mut extraction_fail_closed_reason = if context_outcome.value.is_none() {
        context_outcome
            .diagnostics
            .entries
            .iter()
            .find(|diag| diag.kind != ExtractionDiagKind::ControlFlowCycle)
            .map(|diag| diag.kind.to_string())
            .filter(|_| {
                body_has_reachable_obligation_source(mir_body)
                    && !body_entry_diverges_via_panic(tcx, mir_body)
            })
    } else {
        None
    };
    let extraction_effects = context_outcome.effects;
    // Fallback: when context extraction returns None but the spanned pass
    // succeeds, reuse the spanned expression as the body result so
    // postconditions involving `result` are still connected to the return value.
    let result_expr = context_outcome
        .value
        .or_else(|| result_expr_spanned.as_ref().map(|sp| sp.expr.clone()));

    // #prophecy-slots M5: prove the caller-side death points for `&mut`
    // borrows that arrive inside a call result. Independent of the `&mut`
    // parameter lane: a body with no `&mut` parameters can still take a
    // payload borrow out of a call and let it expire.
    let projected_expiry = crate::mir_analysis::projected_expiry::collect_projected_expiry_pins(
        tcx, mir_body, arg_names,
    );
    if !projected_expiry.is_empty() {
        tracing::debug!(
            "projected_expiry: {} PROVEN caller-side expiry pin(s) in {}",
            projected_expiry.pins.len(),
            tcx.def_path_str(contract.def_id),
        );
    }
    if !projected_expiry.disarms.is_empty() {
        tracing::debug!(
            "projected_expiry: {} candidate shape(s) disarmed in {}: {:?}",
            projected_expiry.disarms.len(),
            tcx.def_path_str(contract.def_id),
            projected_expiry.disarms,
        );
    }
    let projected_final_pins = projected_expiry.pins;

    // Try to extract mutable borrow body (for &mut parameters)
    let mut_borrow_body = extract_mut_borrow_body(
        tcx,
        mir_body,
        Some(&body_with_facts),
        arg_names,
        &effective_user_specs,
        ctx.trait_specs,
        ctx.extern_specs,
    );
    let delayed_writeback_assumptions = mut_borrow_body.as_ref().map_or_else(Vec::new, |body| {
        // Parents whose final value was spec-advanced to a non-identity
        // post-state (e.g. `v.push(x)`: `^v == push_back(*v, ..)`) get the
        // same `*parent == ^child` suppression as mutation-continued
        // parents: the delayed (two-phase) writeback would fuse the
        // entry-time `parent_current` with the post-mutation child final
        // and collapse base premises to UNSAT (bug/two_phase).
        let mut suppressed_parents = body.mutation_continued_params.clone();
        for (name, final_expr) in &body.final_values {
            if !is_identity_final_value_expr(name, final_expr) {
                suppressed_parents.insert(name.clone());
            }
        }
        filter_delayed_writebacks_for_mutation_continued(
            &body.delayed_writeback_assumptions,
            &suppressed_parents,
        )
    });

    // Detect loops if there are invariants or variants to verify
    let loop_analysis = needs_loop_analysis.then(|| detect_loops(mir_body));

    // Collect per-loop call-site obligations paired with their loop
    // conditions (#752). The function-level extraction walks INTO loop
    // bodies (default on_false_edge continues through FalseUnwind), so
    // calls inside loops DO trigger apply_preconditions and appear in
    // extraction_effects.obligations. Walk each loop's body blocks
    // separately and pair obligations with the loop's condition.
    //
    // For nested loops, each loop's obligations use *exclusive* body blocks
    // (excluding inner loop non-header blocks). Without this, calls inside
    // an inner loop get collected for the outer loop's obligation group with
    // the outer loop's condition, causing false verification failures when
    // the inner loop's condition is needed to prove the precondition.
    let loop_condition_spec_ctx = CallSpecContext {
        tcx,
        user_specs: &effective_user_specs,
        trait_specs: ctx.trait_specs,
        extern_specs: ctx.extern_specs,
    };

    // Blocks outside a loop body (must-diverge arms) that some loop lane walk
    // processed; the block-slice walkers may leave their checks to it.
    let mut loop_lane_owned_blocks: HashSet<rustc_middle::mir::BasicBlock> = HashSet::new();
    // Obligations the loop lane reached where the loop condition is not
    // established (loop-exit arms, code before the condition switch).
    // Appended as condition-free groups AFTER the per-loop groups, so the
    // per-loop index (`loop_verify`) and `single_loop_condition` are unchanged.
    let mut condition_free_groups: Vec<LoopObligationGroup> = Vec::new();
    let mut loop_obligation_groups: Vec<LoopObligationGroup> = loop_analysis
        .as_ref()
        .map(|analysis| {
            let loop_assigned_by_header = loop_assigned_locals_by_header(tcx, mir_body, analysis);
            analysis
                .loops
                .iter()
                .enumerate()
                .map(|(loop_index, loop_info)| {
                    // Compute exclusive body blocks: remove blocks belonging to
                    // inner loops (keeping their headers for CFG traversal).
                    let exclusive_blocks = {
                        let mut blocks = loop_info.body_blocks.clone();
                        for other in &analysis.loops {
                            if other.header != loop_info.header
                                && loop_info.body_blocks.contains(&other.header)
                            {
                                for bb in &other.body_blocks {
                                    if *bb != other.header {
                                        blocks.remove(bb);
                                    }
                                }
                            }
                        }
                        blocks
                    };
                    let name_restore_blocks = {
                        let mut blocks = loop_info.body_blocks.clone();
                        for other in &analysis.loops {
                            if other.header != loop_info.header
                                && other.body_blocks.contains(&loop_info.header)
                            {
                                blocks.extend(other.body_blocks.iter().copied());
                            }
                        }
                        blocks
                    };
                    let loop_body_expr = extract_loop_body(
                        mir_body,
                        arg_names,
                        loop_info,
                        Some(&analysis.loops),
                        Some(&loop_condition_spec_ctx),
                    );
                    let loop_spec_ctx = LoopBodySpecContext {
                        user_specs: &effective_user_specs,
                        trait_specs: ctx.trait_specs,
                        extern_specs: ctx.extern_specs,
                        body_blocks: &exclusive_blocks,
                        name_restore_blocks: Some(&name_restore_blocks),
                        arithmetic: None,
                        all_loops: Some(&analysis.loops),
                        condition_switch: loop_body_expr.condition_switch,
                    };
                    let split = collect_loop_body_call_obligations_split(
                        tcx,
                        mir_body,
                        arg_names,
                        loop_info.header,
                        &loop_spec_ctx,
                    );
                    loop_lane_owned_blocks.extend(split.off_body_blocks.iter().copied());
                    let mut injected_fail_closed = split.injected_fail_closed;
                    let mut condition_free_injected_fail_closed =
                        split.condition_free_injected_fail_closed;
                    let mut obligations = split.obligations;
                    let mut condition_free_obligations = split.condition_free_obligations;
                    // In-loop machine-int arithmetic panic obligations, split
                    // like the call lane's: those reached through the in-body
                    // arm of the condition switch are checked under the
                    // invariant + loop condition, every other one (the exit
                    // arm's diverging tail, code before the switch) without
                    // the condition.
                    let (arithmetic, sites) = with_charged_assert_recording(mir_body, || {
                        collect_arithmetic_panic_obligations(
                            tcx,
                            mir_body,
                            arg_names,
                            &ArithmeticRegion {
                                start: loop_info.header,
                                region_blocks: &exclusive_blocks,
                                loop_carried_blocks: &name_restore_blocks,
                                named_loop_carried_symbolic: true,
                                all_loops: Some(&analysis.loops),
                                condition_switch: loop_body_expr.condition_switch,
                            },
                            &effective_user_specs,
                            ctx.trait_specs,
                            ctx.extern_specs,
                            &loop_assigned_by_header,
                        )
                    });
                    charged_asserts_walked.borrow_mut().extend(sites);
                    injected_fail_closed |= arithmetic.injected_fail_closed;
                    condition_free_injected_fail_closed |=
                        arithmetic.condition_free_injected_fail_closed;
                    let unstated_entry_values = arithmetic.unstated_entry_values;
                    obligations.extend(arithmetic.obligations);
                    condition_free_obligations.extend(arithmetic.condition_free_obligations);
                    // This lane names a parameter by its ENTRY name (the one
                    // `requires` constrains) even when the loop (or an
                    // enclosing loop) assigns the parameter, so a call reading
                    // the updated value would be discharged against the entry
                    // value (`fn f(mut x) requires(x == 0) { #[invariant(true)]
                    // while .. { need_zero(x); x = 5 } }` would verify). The
                    // group's guards, loop condition and invariants share that
                    // conflation, so the group's obligations cannot be stated
                    // soundly here: fail closed. The post-loop continuation
                    // shares the conflation even with no call in the loop —
                    // the invariant at the exit and the post-loop return walk
                    // name the parameter by its entry name, so `while .. { x =
                    // 9 } x` under `requires(x@ == 0)` would prove `result@ ==
                    // 0` (s41v2_inv_param_result.rs) and `ensures(x@ == 9)`
                    // about the entry value would follow from the exit
                    // invariant (s41v2_inv_param_entry_ensures.rs) — so the
                    // guard must not depend on the group having obligations.
                    if loop_assigns_by_value_parameter(
                        mir_body,
                        arg_names.len(),
                        &name_restore_blocks,
                    ) {
                        obligations = vec![fail_closed_marker("loop-name-restore")];
                        condition_free_obligations = vec![fail_closed_marker("loop-name-restore")];
                    }
                    // The loop path models only the resolved exit edge. A
                    // `break` / in-loop `return` joining the post-loop code
                    // would be verified from the exit state (`!cond`, the
                    // invariant, the path-insensitive post-loop return walk):
                    // `#[invariant(true)] while i < 10 { if i == 3 { break } ..
                    // } i` would prove `result >= 10`
                    // (s41v2_inv_break_exitcond.rs). Fail closed.
                    //
                    // Both checks read the exit the lane takes its condition
                    // from (D-234): the first switch after the header may be
                    // a branch inside the condition with no exit arm. A loop
                    // that some path leaves while no exit edge is the lane's
                    // is refused as one with an unmodeled exit.
                    match loop_lane_exit(mir_body, loop_info, loop_body_expr.condition_switch) {
                        LaneExit::Edge(switch, exit) => {
                            if loop_has_unmodeled_exit(mir_body, loop_info, (switch, exit)) {
                                obligations = vec![fail_closed_marker("loop-unmodeled-exit")];
                                condition_free_obligations =
                                    vec![fail_closed_marker("loop-unmodeled-exit")];
                            }
                            // The pass that leaves the loop runs the path from
                            // the header to the exit switch once more, after the
                            // state the invariant describes; the exit and the
                            // post-loop continuation read the header state, so
                            // a write on that path that code after the loop
                            // reads is in no VC
                            // (loop_condition_block_write_before_exit_read_after.rs).
                            // Fail closed.
                            else if let Some(write) = loop_condition_exit_write(
                                tcx,
                                mir_body,
                                loop_info,
                                (switch, exit),
                            ) {
                                tracing::debug!(%write, "loop condition writes what the code after the loop reads");
                                obligations = vec![fail_closed_marker("loop-condition-exit-write")];
                                condition_free_obligations =
                                    vec![fail_closed_marker("loop-condition-exit-write")];
                            }
                        }
                        LaneExit::Unresolved => {
                            obligations = vec![fail_closed_marker("loop-exit-unresolved")];
                            condition_free_obligations =
                                vec![fail_closed_marker("loop-exit-unresolved")];
                        }
                        LaneExit::Never => {}
                    }
                    let pre_loop_bbs = collect_pre_loop_blocks(mir_body, &loop_info.body_blocks);
                    let mut assumptions = if pre_loop_bbs.is_empty() {
                        Vec::new()
                    } else {
                        // These premises reach the goals inside the loop,
                        // where a local's bare name is its value on the
                        // current pass, not at the loop's entry (D-243).
                        collect_call_effects_for_blocks(
                            tcx,
                            mir_body,
                            arg_names,
                            &pre_loop_bbs,
                            &loop_lane_owned_blocks,
                            &effective_user_specs,
                            ctx.trait_specs,
                            ctx.extern_specs,
                            LoopEntryValues::Omitted,
                        )
                        .assumptions
                        .into_iter()
                        .filter(expr_mentions_call_result_var)
                        .collect()
                    };
                    // The condition's own call runs before the switch on every
                    // pass through the header; its postcondition speaks of the
                    // value the condition reads.
                    for fact in &loop_body_expr.condition_facts {
                        if !assumptions.contains(fact) {
                            assumptions.push(fact.clone());
                        }
                    }
                    if !condition_free_obligations.is_empty() {
                        condition_free_groups.push(LoopObligationGroup {
                            assumptions: assumptions.clone(),
                            obligations: condition_free_obligations,
                            condition: None,
                            loop_index: Some(loop_index),
                            condition_unstated: None,
                            pre_loop_stored_names: loop_body_expr
                                .pre_loop_deref_stored_names
                                .clone(),
                            unstated_entry_values: unstated_entry_values.clone(),
                            injected_fail_closed: condition_free_injected_fail_closed,
                        });
                    }
                    LoopObligationGroup {
                        assumptions,
                        obligations,
                        condition: loop_body_expr.condition,
                        loop_index: Some(loop_index),
                        condition_unstated: loop_body_expr.condition_unstated,
                        pre_loop_stored_names: loop_body_expr.pre_loop_deref_stored_names,
                        unstated_entry_values,
                        injected_fail_closed,
                    }
                })
                .collect()
        })
        .unwrap_or_default();
    loop_obligation_groups.extend(condition_free_groups);
    if std::env::var_os("TRUST_WP_LOOP_GROUP_DUMP").is_some() {
        for (index, group) in loop_obligation_groups.iter().enumerate() {
            eprintln!(
                "TRUST_WP_LOOP_GROUP_DUMP group={index} condition={:?} obligations={:?}",
                group.condition, group.obligations
            );
        }
        eprintln!("TRUST_WP_LOOP_GROUP_DUMP loop_lane_owned_blocks={loop_lane_owned_blocks:?}");
    }

    // Extract name substitutions for destructured parameters (#1075).
    // When parameters use tuple/struct destructuring, the HIR name
    // extraction falls back to positional names. The debug info in MIR
    // provides the actual binding names used in contracts.
    let param_destructuring_subs =
        extract_param_destructuring_substitutions(tcx, mir_body, arg_names);

    // Filter both call_assumptions AND call_obligations to exclude in-loop
    // effects when loop analysis is active. (#2496)
    //
    // The function-level MIR extraction walks into loop bodies and collects
    // call effects from ALL BBs — including those inside loops. For obligations,
    // the per-loop obligation groups separately collect these with proper loop
    // conditions. For assumptions, the leak is more dangerous: loop-body
    // postcondition-derived assumptions (e.g., `seen == true`) become
    // unconditional facts on the post-loop VC, even though the loop may execute
    // zero times.
    //
    // Gate on loop presence (not obligation non-empty), because a loop can
    // contribute assumptions without contributing any precondition obligations.
    // Use block-scoped extraction on the non-loop BB complement to recover only
    // the pre/post-loop call effects.
    // #1075/#1401 returning-path facts premise only the postconditions. They
    // are taken only from a loop-free body: a switch inside a loop body is
    // re-evaluated per iteration, and the single symbolic walk does not
    // describe every iteration's state.
    let returning_path_facts: Vec<PureExpr> = if detect_loops(mir_body).has_loops {
        Vec::new()
    } else {
        let normalize_ref_derefs = normalize_immutable_ref_param_derefs(tcx, mir_body, arg_names);
        extraction_effects
            .returning_path_facts
            .iter()
            .map(&normalize_ref_derefs)
            .collect()
    };
    let (
        call_assumptions,
        pre_loop_call_assumptions,
        call_obligations,
        pre_loop_call_obligations,
        post_loop_call_obligations,
        user_written_false_obligations,
    ) = if loop_analysis
        .as_ref()
        .is_some_and(|analysis| analysis.has_loops)
    {
        // Compute all loop body BBs across all loops.
        let all_loop_bbs: HashSet<rustc_middle::mir::BasicBlock> = loop_analysis
            .as_ref()
            .map(|a| {
                a.loops
                    .iter()
                    .flat_map(|l| l.body_blocks.iter().copied())
                    .collect()
            })
            .unwrap_or_default();
        // Build the complement: all function BBs minus loop body BBs.
        let non_loop_bbs: HashSet<_> = mir_body
            .basic_blocks
            .indices()
            .filter(|bb| !all_loop_bbs.contains(bb))
            .collect();
        let pre_loop_bbs = collect_pre_loop_blocks(mir_body, &all_loop_bbs);
        let post_loop_bbs: HashSet<_> = non_loop_bbs
            .iter()
            .copied()
            .filter(|bb| !pre_loop_bbs.contains(bb))
            .collect();
        if non_loop_bbs.is_empty() {
            (
                delayed_writeback_assumptions,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                0,
            )
        } else {
            let non_loop_effects = collect_call_effects_for_blocks(
                tcx,
                mir_body,
                arg_names,
                &non_loop_bbs,
                &loop_lane_owned_blocks,
                &effective_user_specs,
                ctx.trait_specs,
                ctx.extern_specs,
                LoopEntryValues::Stated,
            );
            let (pre_loop_assumptions, pre_loop_obligations) = if pre_loop_bbs.is_empty() {
                (Vec::new(), Vec::new())
            } else {
                let effects = collect_call_effects_for_blocks(
                    tcx,
                    mir_body,
                    arg_names,
                    &pre_loop_bbs,
                    &loop_lane_owned_blocks,
                    &effective_user_specs,
                    ctx.trait_specs,
                    ctx.extern_specs,
                    LoopEntryValues::Stated,
                );
                (effects.assumptions, effects.obligations)
            };
            let post_loop_obligations = if post_loop_bbs.is_empty() {
                Vec::new()
            } else {
                collect_call_effects_for_blocks(
                    tcx,
                    mir_body,
                    arg_names,
                    &post_loop_bbs,
                    &loop_lane_owned_blocks,
                    &effective_user_specs,
                    ctx.trait_specs,
                    ctx.extern_specs,
                    LoopEntryValues::Omitted,
                )
                .obligations
            };
            // Mapping closure axioms are universally quantified and sound
            // regardless of loop execution. Include them from the full
            // extraction to avoid losing axioms that the block-scoped
            // walker cannot detect (requires full extraction context).
            let mut assumptions = non_loop_effects.assumptions;
            let normalize_ref_derefs =
                normalize_immutable_ref_param_derefs(tcx, mir_body, arg_names);
            for assumption in &mut assumptions {
                *assumption = normalize_ref_derefs(assumption);
            }
            for mc in &extraction_effects.mapping_closures {
                if let Some(axiom) = mc.to_forall_axiom() {
                    assumptions.push(axiom);
                }
            }
            // map_inv collect view facts (#2170): stated only for acyclic sites
            // that dominate every return, with a unique source and identical
            // facts on every extraction (spec_resolution.rs).
            for fact in &extraction_effects.map_inv_collect_assumptions() {
                if !assumptions.contains(fact) {
                    assumptions.push(fact.clone());
                }
            }
            assumptions.extend(delayed_writeback_assumptions);
            // Machine-int arithmetic panic obligations outside the loops: the
            // region reached from the entry (pre-loop values are exact), and
            // the region after each loop exit (loop-written locals re-bound).
            let non_loop_user_written_false_obligations =
                non_loop_effects.user_written_false_obligations;
            let mut non_loop_obligations = non_loop_effects.obligations;
            let mut pre_loop_obligations = pre_loop_obligations;
            let mut post_loop_obligations = post_loop_obligations;
            if let Some(analysis) = loop_analysis.as_ref() {
                let loop_assigned_by_header =
                    loop_assigned_locals_by_header(tcx, mir_body, analysis);
                let no_carried_blocks = HashSet::new();
                let (entry_arithmetic, entry_sites) =
                    with_charged_assert_recording(mir_body, || {
                        collect_arithmetic_panic_obligations(
                            tcx,
                            mir_body,
                            arg_names,
                            &ArithmeticRegion {
                                start: rustc_middle::mir::START_BLOCK,
                                region_blocks: &non_loop_bbs,
                                loop_carried_blocks: &no_carried_blocks,
                                named_loop_carried_symbolic: true,
                                all_loops: None,
                                condition_switch: None,
                            },
                            &effective_user_specs,
                            ctx.trait_specs,
                            ctx.extern_specs,
                            &loop_assigned_by_header,
                        )
                        .into_all()
                    });
                let (exit_arithmetic, exit_sites) = with_charged_assert_recording(mir_body, || {
                    collect_post_loop_arithmetic_obligations(
                        tcx,
                        mir_body,
                        arg_names,
                        &all_loop_bbs,
                        true,
                        &effective_user_specs,
                        ctx.trait_specs,
                        ctx.extern_specs,
                        &loop_assigned_by_header,
                    )
                });
                charged_asserts_walked.borrow_mut().extend(entry_sites);
                charged_asserts_walked.borrow_mut().extend(exit_sites);
                non_loop_obligations.extend(entry_arithmetic.iter().cloned());
                non_loop_obligations.extend(exit_arithmetic.iter().cloned());
                pre_loop_obligations.extend(entry_arithmetic);
                post_loop_obligations.extend(exit_arithmetic);
            }
            // The primary walk's return sink is a statement, not a call: the
            // block-scoped walks above never see it, so its fail-closed `false`
            // is carried here by the same predicate.
            if body_returns_a_stale_store_read(tcx, mir_body, &all_loop_bbs) {
                non_loop_obligations.push(PureExpr::Bool(false));
                post_loop_obligations.push(PureExpr::Bool(false));
            }
            (
                assumptions,
                pre_loop_assumptions,
                non_loop_obligations,
                pre_loop_obligations,
                post_loop_obligations,
                non_loop_user_written_false_obligations,
            )
        }
    } else {
        // No loops: use the full extraction effects directly.
        let map_inv_collect_assumptions = extraction_effects.map_inv_collect_assumptions();
        let mut assumptions = extraction_effects.assumptions;
        let normalize_ref_derefs = normalize_immutable_ref_param_derefs(tcx, mir_body, arg_names);
        for assumption in &mut assumptions {
            *assumption = normalize_ref_derefs(assumption);
        }
        for mc in &extraction_effects.mapping_closures {
            if let Some(axiom) = mc.to_forall_axiom() {
                assumptions.push(axiom);
            }
        }
        // map_inv collect view facts (#2170); gated as above.
        for fact in &map_inv_collect_assumptions {
            if !assumptions.contains(fact) {
                assumptions.push(fact.clone());
            }
        }
        assumptions.extend(delayed_writeback_assumptions);
        let user_written_false_obligations = extraction_effects.user_written_false_obligations;
        let mut obligations = extraction_effects.obligations;
        // Loops without any invariant have no loop VC: their bodies (and the
        // code after them) are walked for arithmetic panic obligations with
        // loop-carried locals havocked.
        if loop_analysis.is_none() {
            let (arithmetic, sites) = with_charged_assert_recording(mir_body, || {
                collect_unannotated_loop_arithmetic_obligations(
                    tcx,
                    mir_body,
                    arg_names,
                    &effective_user_specs,
                    ctx.trait_specs,
                    ctx.extern_specs,
                )
            });
            charged_asserts_walked.borrow_mut().extend(sites);
            obligations.extend(arithmetic);
        }
        // Loops without any invariant or variant have no loop VC, and the
        // primary extractor skips their bodies: every call precondition and
        // panic arm reachable through a loop header is collected here from a
        // havocked loop state (Creusot's implicit `invariant true`).
        if loop_analysis.is_none() {
            obligations.extend(collect_unannotated_loop_obligations(
                tcx,
                mir_body,
                arg_names,
                &effective_user_specs,
                ctx.trait_specs,
                ctx.extern_specs,
            ));
        }
        (
            assumptions.clone(),
            assumptions,
            obligations.clone(),
            obligations,
            Vec::new(),
            user_written_false_obligations,
        )
    };

    // A body that can never return because every path panics has no switch
    // arm to carry the panic-unreachability obligation (`fn f() { panic!() }`,
    // `fn die() -> ! { panic!() }`). Creusot's goal for such a body is the
    // Abort being unreachable, i.e. `false` under the preconditions; without
    // this obligation `#[ensures(true)]` is proved vacuously (and a body whose
    // extraction returns None is credited as verified).
    let (mut call_obligations, mut pre_loop_call_obligations) =
        (call_obligations, pre_loop_call_obligations);
    // Counted, not just pushed (D-27). Every OTHER `false` in this list means
    // "trust-wp could not model something here" and must not license a
    // refutation; THIS one is a goal Creusot states too and trust-wp can
    // genuinely refute, so the verdict gate has to be able to tell them apart.
    let mut panic_unreachability_obligations = 0usize;
    if body_entry_diverges_via_panic(tcx, mir_body) {
        call_obligations.push(PureExpr::Bool(false));
        pre_loop_call_obligations.push(PureExpr::Bool(false));
        panic_unreachability_obligations = 1;
    }

    // Structural coverage: every reachable charged assert — machine-int
    // arithmetic panic assert or index bounds check — must have had its
    // obligation stated by a lane whose obligations are kept. A site no walk
    // reached (code after an inner loop exit, a region no lane owns) is never
    // silently dropped: a `verified` verdict is demoted to unknown. This is
    // what lets `unchecked_panic_sites` leave both classes out of the
    // clause-free cap.
    let unwalked = unwalked_charged_assert_sites(mir_body, &charged_asserts_walked.borrow());
    if !unwalked.is_empty() && extraction_fail_closed_reason.is_none() {
        let blocks: Vec<String> = unwalked.iter().map(|bb| format!("{bb:?}")).collect();
        extraction_fail_closed_reason = Some(format!(
            "partial: runtime check site not walked ({})",
            blocks.join(", ")
        ));
    }

    // handback-entry-value: a `&mut` parameter written through and then handed
    // back as the return value is NOT the entry borrow the extraction names.
    // Replace it with a fresh carrier so `result == p` stops being the
    // syntactic identity `p == p`, keeping only the prophecy premise.
    let mut call_assumptions = call_assumptions;
    let result_expr = super::handback::refuse_stale_handback_result(
        tcx,
        mir_body,
        arg_names,
        result_expr,
        &mut call_assumptions,
    );

    ExtractionData {
        result_expr,
        result_expr_spanned,
        mut_borrow_body,
        projected_final_pins,
        loop_analysis,
        loop_obligation_groups,
        mut_ref_param_names: collect_mut_ref_arg_names(tcx, mir_body, arg_names),
        stale_call_final_params: params_with_stale_call_final_credit(tcx, mir_body, arg_names),
        param_destructuring_subs,
        call_assumptions,
        pre_loop_call_assumptions,
        call_obligations,
        pre_loop_call_obligations,
        post_loop_call_obligations,
        returning_path_facts,
        extraction_fail_closed_reason,
        panic_unreachability_obligations,
        user_written_false_obligations,
        proved_dead_edges,
    }
}

/// Whether `blocks` may change a parameter's own storage: a whole or
/// field-projected assignment, a call destination, a discriminant write, or a
/// `&mut` / raw borrow of the parameter place (`p.0 = 5` and `set5(&mut x)`
/// in the loop change it too; a whole-local match misses them). Writes
/// THROUGH a `&mut` parameter (a `Deref` projection) do not change the
/// parameter's own value and are owned by the mut-borrow lanes.
fn loop_assigns_by_value_parameter(
    body: &rustc_middle::mir::Body<'_>,
    arg_count: usize,
    blocks: &HashSet<BasicBlock>,
) -> bool {
    use rustc_middle::mir::{
        BorrowKind, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    };
    let writes_param_storage = |place: &Place<'_>| {
        let index = place.local.as_usize();
        index >= 1
            && index <= arg_count
            && !place
                .projection
                .iter()
                .any(|elem| matches!(elem, ProjectionElem::Deref))
    };
    blocks.iter().any(|&bb| {
        let data = &body.basic_blocks[bb];
        data.statements.iter().any(|stmt| match &stmt.kind {
            StatementKind::Assign((place, rvalue)) => {
                writes_param_storage(place)
                    || matches!(
                        rvalue,
                        Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed)
                        | Rvalue::RawPtr(_, borrowed)
                            if writes_param_storage(borrowed)
                    )
            }
            StatementKind::SetDiscriminant {
                place: deref!(place),
                ..
            } => writes_param_storage(place),
            _ => false,
        }) || matches!(
            &data.terminator().kind,
            TerminatorKind::Call { destination, .. } if writes_param_storage(destination)
        )
    })
}

fn collect_pre_loop_blocks(
    body: &rustc_middle::mir::Body<'_>,
    all_loop_bbs: &HashSet<BasicBlock>,
) -> HashSet<BasicBlock> {
    let mut visited = HashSet::new();
    let mut worklist = vec![BasicBlock::from_u32(0)];
    while let Some(bb) = worklist.pop() {
        if all_loop_bbs.contains(&bb) || !visited.insert(bb) {
            continue;
        }
        for succ in body.basic_blocks[bb].terminator().successors() {
            if !all_loop_bbs.contains(&succ) {
                worklist.push(succ);
            }
        }
    }
    visited
}

fn expr_mentions_call_result_var(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => name.starts_with("$call_"),
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_mentions_call_result_var(lhs) || expr_mentions_call_result_var(rhs)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_mentions_call_result_var(inner),
        PureExpr::Let { value, body, .. } => {
            expr_mentions_call_result_var(value) || expr_mentions_call_result_var(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_mentions_call_result_var(assumption) || expr_mentions_call_result_var(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_mentions_call_result_var(obligation) || expr_mentions_call_result_var(body)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_mentions_call_result_var(cond)
                || expr_mentions_call_result_var(then_expr)
                || expr_mentions_call_result_var(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            expr_mentions_call_result_var(body)
                || triggers.iter().flatten().any(expr_mentions_call_result_var)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(expr_mentions_call_result_var),
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_mentions_call_result_var(receiver)
                || args.iter().any(expr_mentions_call_result_var)
        }
        PureExpr::Closure { body, .. } => expr_mentions_call_result_var(body),
        _ => false,
    }
}

pub(super) fn format_context_extraction_warning(
    def_path: &str,
    diagnostics: &ExtractionDiagnostics,
    used_spanned_fallback: bool,
) -> Option<String> {
    let detail = diagnostics.render_summary()?;
    let status = if used_spanned_fallback {
        "using spanned fallback after context extraction failed"
    } else {
        "MIR context extraction failed"
    };
    Some(format!("trust-wp: warning: {def_path}: {status}: {detail}"))
}

fn assemble_parsed_contract(
    contract: &FunctionContract,
    clause_inputs: ParsedClauseInputs,
    arg_names: Vec<String>,
    state_params: HashSet<String>,
    extraction_data: ExtractionData,
) -> ParsedContract {
    let ParsedClauseInputs {
        requires,
        ensures,
        invariants,
        per_loop_invariants,
        per_loop_variants,
        variants,
    } = clause_inputs;

    let ExtractionData {
        result_expr,
        result_expr_spanned,
        mut_borrow_body,
        projected_final_pins,
        loop_analysis,
        loop_obligation_groups,
        mut_ref_param_names,
        stale_call_final_params,
        param_destructuring_subs: _,
        call_assumptions,
        pre_loop_call_assumptions,
        call_obligations,
        pre_loop_call_obligations,
        post_loop_call_obligations,
        returning_path_facts,
        extraction_fail_closed_reason,
        panic_unreachability_obligations,
        user_written_false_obligations,
        proved_dead_edges,
    } = extraction_data;

    ParsedContract {
        requires,
        ensures,
        result_expr,
        result_expr_spanned,
        arg_names,
        call_assumptions,
        pre_loop_call_assumptions,
        call_obligations,
        pre_loop_call_obligations,
        post_loop_call_obligations,
        returning_path_facts,
        extraction_fail_closed_reason,
        panic_unreachability_obligations,
        user_written_false_obligations,
        proved_dead_edges,
        loop_fields: LoopFields {
            invariants,
            per_loop_invariants,
            per_loop_variants,
            all_loop_spans: contract.all_loop_spans.clone(),
            variants,
            loop_analysis,
            loop_obligation_groups,
        },
        mut_borrow: MutBorrowFields {
            mut_borrow_body,
            mut_ref_param_names,
            state_params,
            projected_final_pins,
            stale_call_final_params,
        },
        reborrow_prophecy: None,
    }
}

/// Identity-final check mirroring
/// `trust-wp-ay::verify::mut_borrow::resolve::is_identity_final_value`:
/// `Deref(Var(name))` (possibly through branch-symmetric `Ite`s) means the
/// parameter's exit state is its entry state — everything else is an advanced
/// (post-mutation) final value.
fn is_identity_final_value_expr(var_name: &str, final_expr: &PureExpr) -> bool {
    match final_expr {
        PureExpr::Deref(inner) => {
            matches!(inner.as_ref(), PureExpr::Var(name, _) if name == var_name)
        }
        PureExpr::Ite(_, then_branch, else_branch) => {
            is_identity_final_value_expr(var_name, then_branch)
                && is_identity_final_value_expr(var_name, else_branch)
        }
        _ => false,
    }
}

/// Filter delayed-writeback assumptions for mutation-continued parents
/// (bug/682 / #5).
///
/// `build_delayed_writeback_assumptions` (trust-wp-driver `mir_analysis`)
/// emits two flavors of equality per two-phase writeback:
///   1. `*parent == ^child`  (the reservation-time writeback)
///   2. `^parent == ^child`  (the final-side propagation, only when `child`
///      is final at the reborrow site)
///
/// When the parent is in `mutation_continued_params`, the call_assumption
/// already advances `parent_final` through the child's final on the *post-
/// call* side. The encoder uses a single SSA-style `<parent>_current` name
/// for the parent's *entry-time* current value, so asserting
/// `*parent == ^child` (= `parent_current == child_final`) fuses the
/// entry-time current with the post-call value. Combined with a
/// precondition that pins `*parent` to a concrete value (e.g.
/// `*a == 3u64` in bug/682) and the call_assumption
/// (`child_final > parent_current`), this collapses base premises to UNSAT
/// and trips the vacuity guard. This is the delayed-writeback (two-phase
/// borrow) analogue of the gate in
/// `crates/trust-wp-ay/src/verify/mut_borrow/resolve.rs::emit_prophecy_writebacks`
/// (the gate there catches only the *immediate* writeback path; #2663).
///
/// The `^parent == ^child` propagation is the prophecy chain on the *final*
/// side and is consistent with the call_assumption, so it is preserved.
///
/// A parent that is a reborrow in such a parameter's chain is gated alike
/// (D-107): its `_current` is its value when it was taken, the parameter's
/// entry value, so the same fusion assumed the callee left the child as it
/// was.
fn filter_delayed_writebacks_for_mutation_continued(
    assumptions: &[PureExpr],
    mutation_continued_params: &HashSet<String>,
) -> Vec<PureExpr> {
    if mutation_continued_params.is_empty() {
        return assumptions.to_vec();
    }
    assumptions
        .iter()
        .filter(|expr| {
            !is_deref_var_eq_final_var_for_mutation_continued(expr, mutation_continued_params)
        })
        .cloned()
        .collect()
}

/// Match `Deref(Var(name, _)) == Final(Var(_, _))` where `name` is a
/// mutation-continued parameter or a reborrow in one's chain
/// (`trust_wp_core::formula::reborrow_root`). Returns `true` when the
/// assumption is the `*parent == ^child` reservation-time writeback that must
/// be suppressed.
fn is_deref_var_eq_final_var_for_mutation_continued(
    expr: &PureExpr,
    mutation_continued_params: &HashSet<String>,
) -> bool {
    let PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Eq, rhs) = expr else {
        return false;
    };
    let parent_name = extract_deref_var_name(lhs);
    let is_final_var = matches!(rhs.as_ref(), PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(_, _)));
    if !is_final_var {
        return false;
    }
    parent_name.is_some_and(|name| {
        mutation_continued_params.contains(&name)
            || mutation_continued_params.contains(trust_wp_core::formula::reborrow_root(&name))
    })
}

fn extract_deref_var_name(expr: &PureExpr) -> Option<String> {
    if let PureExpr::Deref(inner) = expr {
        if let PureExpr::Var(name, _) = inner.as_ref() {
            return Some(name.clone());
        }
    }
    None
}

#[cfg(test)]
mod delayed_writeback_filter_tests {
    use std::sync::Arc;

    use trust_wp_core::formula::BinOp;

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn reservation_writeback(parent: &str, child: &str) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(var(parent)))),
            BinOp::Eq,
            Arc::new(PureExpr::Final(Arc::new(var(child)))),
        )
    }

    fn final_writeback(parent: &str, child: &str) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(var(parent)))),
            BinOp::Eq,
            Arc::new(PureExpr::Final(Arc::new(var(child)))),
        )
    }

    #[test]
    fn advanced_parent_suppresses_only_its_reservation_writeback() {
        let suppressed = HashSet::from(["v".to_string()]);
        let v_reservation = reservation_writeback("v", "v_child");
        let v_final = final_writeback("v", "v_child");
        let other_reservation = reservation_writeback("other", "other_child");
        let assumptions = vec![
            v_reservation.clone(),
            v_final.clone(),
            other_reservation.clone(),
        ];

        let filtered = filter_delayed_writebacks_for_mutation_continued(&assumptions, &suppressed);

        assert!(!filtered.contains(&v_reservation));
        assert!(filtered.contains(&v_final));
        assert!(filtered.contains(&other_reservation));
    }

    /// `keep(v, &mut *p)`: the outer reborrow's `_current` is `p`'s entry
    /// value, so `*p$rb9 == ^p$rb9$rb8` of a mutation-continued `p` assumed
    /// the callee left the argument unchanged (D-107).
    #[test]
    fn a_reborrow_in_a_suppressed_parameter_chain_is_suppressed_too() {
        let suppressed = HashSet::from(["p".to_string()]);
        let chain_reservation = reservation_writeback("p$rb9", "p$rb9$rb8");
        let chain_final = final_writeback("p$rb9", "p$rb9$rb8");
        let other_chain = reservation_writeback("v$rb7", "v$rb7$rb6");
        let assumptions = vec![
            chain_reservation.clone(),
            chain_final.clone(),
            other_chain.clone(),
        ];

        let filtered = filter_delayed_writebacks_for_mutation_continued(&assumptions, &suppressed);

        assert!(!filtered.contains(&chain_reservation));
        assert!(filtered.contains(&chain_final));
        assert!(filtered.contains(&other_chain));
    }

    #[test]
    fn identity_final_detection_requires_every_branch_to_preserve_entry_value() {
        let identity = PureExpr::Deref(Arc::new(var("v")));
        let advanced = PureExpr::Final(Arc::new(var("v_child")));
        let condition = Arc::new(PureExpr::Bool(true));

        assert!(is_identity_final_value_expr("v", &identity));
        assert!(is_identity_final_value_expr(
            "v",
            &PureExpr::Ite(
                condition.clone(),
                Arc::new(identity.clone()),
                Arc::new(identity.clone()),
            )
        ));
        assert!(!is_identity_final_value_expr(
            "v",
            &PureExpr::Ite(
                condition.clone(),
                Arc::new(advanced.clone()),
                Arc::new(advanced.clone()),
            ),
        ));
        assert!(!is_identity_final_value_expr(
            "v",
            &PureExpr::Ite(condition, Arc::new(identity), Arc::new(advanced)),
        ));
    }
}
