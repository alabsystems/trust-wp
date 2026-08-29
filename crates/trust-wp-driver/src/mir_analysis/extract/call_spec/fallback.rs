// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{CallSiteContext, *};

/// Handle an opaque call (no spec found) — create a fresh variable with range
/// constraints, inject `requires(false)` obligation (Creusot approach), and
/// havoc `&mut` arguments to conservatively model potential mutation (#2048).
///
/// The `requires(false)` obligation makes any function that calls an opaque
/// function unprovable at the encoding level, rather than relying solely on
/// post-hoc demotion via the `OpaqueCallTrueAssumption` unsoundness counter.
/// This is architecturally sound: the proof is impossible (not just demoted),
/// matching Creusot's treatment of unspecified functions. (#2663)
pub(super) fn handle_opaque_call<'tcx>(
    call_site: CallSiteContext<'_, 'tcx>,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    let CallSiteContext {
        tcx,
        body,
        args,
        destination,
        next_bb,
        mut local_exprs,
        visited,
        ctx,
        projected_write_facts,
    } = call_site;
    trust_wp_ay::unsoundness::increment(trust_wp_ay::UnsoundnessCategory::OpaqueCallTrueAssumption);
    // Creusot approach: inject `requires(false)` so calling an opaque function
    // makes the caller's postcondition unprovable. This is fail-closed: if we
    // don't know what the function does, we can't prove anything about its caller.
    effects.obligations.push(PureExpr::Bool(false));
    let dest_ty = body.local_decls[destination.local].ty;
    let opaque = PureExpr::Var(
        format!("_call_{}", destination.local.as_u32()),
        ty_to_expr_sort_enriched(tcx, dest_ty),
    );
    let pointer_bits = u32::try_from(tcx.data_layout.pointer_size().bits()).unwrap_or(64);
    let range_constraints = crate::callbacks::integer_range::build_integer_range_for_var(
        opaque.clone(),
        dest_ty,
        pointer_bits,
    );
    effects.assumptions.extend(range_constraints);
    local_exprs.insert(destination.local, opaque);
    propagate_mutating_ref_arg_states(
        &mut local_exprs,
        body,
        ctx.arg_names,
        args,
        Some(effects),
        None,
    );
    wrap_projected_facts(
        projected_write_facts.to_vec(),
        super::extract_from_block_with_context(
            tcx,
            body,
            next_bb,
            local_exprs,
            visited,
            ctx,
            effects,
        ),
    )
}
