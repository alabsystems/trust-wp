// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What `result` is bound to when the function-level check continues after
//! the loop lanes (D-165).

use std::collections::HashMap;

use trust_wp_core::formula::PureExpr;

use crate::callbacks::reporting::LoopCaveats;

/// The loop continuation's premises for the function-level check: the
/// loop-exit assumptions, the post-loop final values of `&mut` parameters, and
/// what the check may not claim (why a counterexample there is unknown rather
/// than FAILED, or a proof no credit).
pub(super) type LoopContinuation = (
    Option<Vec<PureExpr>>,
    Option<HashMap<String, PureExpr>>,
    LoopCaveats,
);

/// Binds `result_expr` to the value the post-loop walk returns, the value of
/// every path from the loop's exit to `Return`.
///
/// With no such value, the function-level check reads no body value at all:
/// `result` is unbound and the whole-body extraction's facts are dropped with
/// it. That extraction cannot stand in: it names a local by its source name
/// AFTER a post-loop write (`t.0 = x` becomes the fact `t.0 == x`), while the
/// loop-exit facts name the same local at the loop's exit (`t == (0, 0)`), and
/// the two together prove `x == 0` -- for `ensures(result == 0)` of `t.0`, and
/// for `ensures(x == 0)`, which never mentions `result`. A proof without the
/// body's facts holds whatever they say, so it stands; a counterexample may
/// contradict them, so it is never a FAILED verdict.
pub(super) fn continue_after_loop(
    result_expr: &mut Option<PureExpr>,
    assumptions: Vec<PureExpr>,
    loop_return_expr: Option<PureExpr>,
    post_loop_final_values: HashMap<String, PureExpr>,
    mut caveats: LoopCaveats,
) -> LoopContinuation {
    match loop_return_expr {
        Some(ret_expr) => *result_expr = Some(ret_expr),
        None => {
            *result_expr = None;
            caveats.result_unbound = Some("no single post-loop return value".to_string());
        }
    }
    let final_values = if post_loop_final_values.is_empty() {
        None
    } else {
        Some(post_loop_final_values)
    };
    (Some(assumptions), final_values, caveats)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_post_loop_value_unbinds_result_and_withholds_a_counterexample() {
        let mut result_expr = Some(PureExpr::Int(0));
        let (_, _, caveats) = continue_after_loop(
            &mut result_expr,
            Vec::new(),
            None,
            HashMap::new(),
            LoopCaveats::default(),
        );
        assert!(
            result_expr.is_none(),
            "the whole-body value must not stand in for the post-loop one"
        );
        assert_eq!(
            caveats.incomplete_or_unbound(),
            Some("no single post-loop return value")
        );
        assert!(
            caveats.incomplete_loop.is_none(),
            "an unbound `result` withholds a counterexample but leaves a proof its credit"
        );
    }

    #[test]
    fn a_post_loop_value_binds_result_and_keeps_the_loop_verdict() {
        let mut result_expr = Some(PureExpr::Int(0));
        let (_, _, caveats) = continue_after_loop(
            &mut result_expr,
            Vec::new(),
            Some(PureExpr::Int(7)),
            HashMap::new(),
            LoopCaveats::default(),
        );
        assert_eq!(result_expr, Some(PureExpr::Int(7)));
        assert!(caveats.incomplete_or_unbound().is_none());
    }
}

/// `assumptions` (the loop lane's exit facts) without the facts that mention a
/// name the body of `def_id` binds to more than one local (D-189). The facts
/// name source names, which the function-level VC and the proof_assert pass
/// read by name: in `let i = 0; { let mut i = 0; while i < n { .. } } i` a
/// fact about the loop's `i` would be read as one about the `i` returned.
/// Without the body there is no telling which name is which: none is kept.
pub(super) fn drop_facts_over_ambiguous_names(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_span::def_id::DefId,
    mut assumptions: Vec<trust_wp_core::formula::PureExpr>,
) -> Vec<trust_wp_core::formula::PureExpr> {
    let Some(body_with_facts) = def_id
        .as_local()
        .and_then(|local| super::super::super::try_get_body_with_context(tcx, local))
    else {
        return Vec::new();
    };
    let ambiguous = crate::mir_analysis::fact_scope::ambiguous_debug_names(
        crate::mir_analysis::get_mir_body(&body_with_facts),
    );
    assumptions.retain(|fact| !fact.free_vars().iter().any(|name| ambiguous.contains(name)));
    assumptions
}
