// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Try-operator (`?`) pattern recognition and extraction.
//!
//! Detects the MIR desugaring of `x?` (`Try::branch` → `SwitchInt` →
//! Continue/Break) and generates datatype-aware expressions that model
//! the success path. Extracted from `branching.rs` as part of the
//! decomposition in #1644.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::PureExpr;

use super::{
    super::effects::CallEffects,
    extract_from_block_with_context,
    helpers::{rvalue_reads_from_local, translate_rvalue_with_enum_variants},
    BlockExtractionContext,
};

/// Input state for try-operator (`?`) pattern extraction.
///
/// Bundles the call-site-specific data (type classification, argument
/// expression, destination) with the owned traversal state
/// (`local_exprs`, `visited`) to reduce the parameter count of
/// [`try_extract_try_operator`]. (#2657)
pub(super) struct TryOperatorInput {
    pub(super) is_option: bool,
    pub(super) arg_expr: PureExpr,
    pub(super) next_bb: BasicBlock,
    pub(super) destination_local: Local,
    pub(super) local_exprs: HashMap<Local, PureExpr>,
    pub(super) visited: HashSet<BasicBlock>,
}

/// Returns `true` when the given def path matches `<T as Try>::branch`.
pub(super) fn is_try_branch_path(path: &str) -> bool {
    // The def path is `std::ops::Try::branch` or a variant with
    // `core::ops::try_trait::Try::branch`. Match the trait method name.
    path == "std::ops::Try::branch"
        || path.ends_with("::Try::branch")
        || path.contains("::Try>::branch")
}

/// Detect whether a function call is `<T as Try>::branch` by checking
/// the def path for `try_trait::Try::branch` or `::branch` on a known
/// Try implementor (Option, Result).
///
/// Returns `true` when the call matches the Try::branch pattern.
pub(super) fn is_try_branch_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    // Provenance: `::Try::branch` is a suffix match; a local `Try` lookalike
    // must not get `?` desugaring semantics.
    if !crate::provenance::is_std_item(tcx, def_id) {
        return false;
    }
    let path = tcx.def_path_str(def_id);
    is_try_branch_path(&path)
}

/// Classify a Try self-type path as Option/Result for `?` extraction.
///
/// Returns:
/// - `Some(true)` for Option
/// - `Some(false)` for Result
/// - `None` for unsupported Try implementors
pub(super) fn classify_try_self_adt_path(adt_path: &str) -> Option<bool> {
    if adt_path == "Option"
        || adt_path == "std::option::Option"
        || adt_path == "core::option::Option"
    {
        return Some(true);
    }

    if adt_path == "Result"
        || adt_path == "std::result::Result"
        || adt_path == "core::result::Result"
    {
        return Some(false);
    }

    None
}

/// Classify the Self type of a Try::branch call.
/// Returns `Some(true)` for Option, `Some(false)` for Result,
/// `None` for unsupported types (ControlFlow, Poll, custom impls).
pub(super) fn try_branch_type_is_option(tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<bool> {
    if let Operand::Constant(deref!(constant)) = func {
        if let rustc_middle::ty::TyKind::FnDef(_, substs) = constant.const_.ty().kind() {
            if let Some(self_ty) = substs.skip_binder().first().and_then(|s| s.as_type()) {
                if let rustc_middle::ty::TyKind::Adt(adt_def, _) = self_ty.kind() {
                    // Provenance: the bare `Option` / `Result` spellings would
                    // otherwise classify a local enum of the same name.
                    if !crate::provenance::is_std_item(tcx, adt_def.did()) {
                        return None;
                    }
                    let adt_path = tcx.def_path_str(adt_def.did());
                    return classify_try_self_adt_path(&adt_path);
                }
            }
        }
    }
    None
}

/// Try to extract the `?` (try) operator pattern by recognizing the
/// `Try::branch(x) → SwitchInt → Continue/Break` MIR desugaring.
///
/// When `Try::branch(x)` has no spec, the normal opaque-call fallback
/// produces unconstrained variables. This function detects the pattern
/// and generates datatype-aware expressions instead:
///
/// For `x?` where `x: Option<T>`:
///   `LetAssume(is_some(x), <continue_body with inner=x>)`
///
/// For `x?` where `x: Result<T, E>`:
///   `LetAssume(is_ok(x), <continue_body with inner=x>)`
///
/// The inner value maps to the original argument because the extraction
/// pipeline collapses single-field ADT constructors to identity
/// (`Some(v) → v`, `Ok(v) → v`). The Break arm (early return via
/// `FromResidual::from_residual()`) is skipped.
///
/// Returns `Some(PureExpr)` if the pattern was matched and extraction
/// succeeded from the Continue arm. Returns `None` to fall through to
/// the normal opaque-call handling. (#1266)
pub(super) fn try_extract_try_operator<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    input: TryOperatorInput,
    ctx: &BlockExtractionContext<'_>,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    let TryOperatorInput {
        is_option,
        arg_expr,
        next_bb,
        destination_local,
        mut local_exprs,
        mut visited,
    } = input;
    // Determine the is_variant and unwrap method names based on type.
    let is_variant_method = if is_option { "is_some" } else { "is_ok" };

    // Walk next_bb: it should contain a Discriminant assignment + SwitchInt.
    let next_data = &body.basic_blocks[next_bb];
    let term = next_data.terminator();

    // Find the Continue arm's target block from the SwitchInt terminator.
    // ControlFlow::Continue has discriminant 0.
    let continue_bb = match &term.kind {
        TerminatorKind::SwitchInt { targets, .. } => targets
            .iter()
            .find(|(val, _)| *val == 0)
            .map_or(targets.otherwise(), |(_, bb)| bb),
        // If next_bb doesn't end with SwitchInt, this isn't the expected pattern.
        // Could be a Goto to the SwitchInt block — try one more level.
        TerminatorKind::Goto { target, .. } => {
            let goto_data = &body.basic_blocks[*target];
            match &goto_data.terminator().kind {
                TerminatorKind::SwitchInt { targets, .. } => targets
                    .iter()
                    .find(|(val, _)| *val == 0)
                    .map_or(targets.otherwise(), |(_, bb)| bb),
                _ => return None,
            }
        }
        _ => return None,
    };

    // Now extract from the Continue arm. In the Continue block, the MIR
    // assigns `_inner = (branch_result as Continue).0`. We need to:
    // 1. Set the inner value to `unwrap(x)` instead of `tuple_get_0(opaque)`
    // 2. Extract the rest of the Continue path normally.
    //
    // We process continue_bb's statements ourselves and then follow
    // its terminator, rather than calling extract_from_block_with_context
    // on continue_bb (which would re-process statements and overwrite
    // our substitution with tuple_get_0 of the opaque var).
    //
    // The inner value after `x?` is the unwrapped content of `x`.
    // For Option<T>, `x?` yields the `T` inside `Some(t)`.
    // For Result<T,E>, `x?` yields the `T` inside `Ok(t)`.
    //
    // We use `unwrap(x)` which the ay encoder maps to the ADT accessor
    // for the success variant. This pairs with the LetAssume wrapper
    // (is_some(x) / is_ok(x)) that constrains `x` to the success case,
    // making the unwrap well-defined. (#1266)
    let inner_expr = PureExpr::MethodCall {
        receiver: Arc::new(arg_expr.clone()),
        method: "unwrap".to_string(),
        args: vec![],
    };

    // Mark the SwitchInt block(s) as visited so we don't re-enter them.
    visited.insert(next_bb);

    let continue_data = &body.basic_blocks[continue_bb];
    for stmt in &continue_data.statements {
        if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
            if place.projection.is_empty() {
                if rvalue_reads_from_local(rvalue, destination_local) {
                    // This reads from the branch result (Downcast+Field).
                    // Override with the inner value instead of tuple_get_0(opaque).
                    local_exprs.insert(place.local, inner_expr.clone());
                } else if let Some(expr) = translate_rvalue_with_enum_variants(
                    tcx,
                    rvalue,
                    &local_exprs,
                    Some(body),
                    None,
                    None,
                ) {
                    local_exprs.insert(place.local, expr);
                }
            }
            // Skip projected assignments (writes to struct fields).
        }
    }

    // Follow continue_bb's terminator to the next block and extract from there.
    let continue_term = continue_data.terminator();
    let continue_result = match &continue_term.kind {
        TerminatorKind::Goto { target, .. } => {
            extract_from_block_with_context(tcx, body, *target, local_exprs, visited, ctx, effects)
        }
        TerminatorKind::Drop { place, target, .. } => {
            // D-140, as the primary walk's `on_drop_place`.
            if let Some(changed) = super::drop_glue_writes::locals_changed_by_drop(tcx, body, place)
            {
                let mut changed: Vec<Local> = changed.into_iter().collect();
                changed.sort();
                for local in changed {
                    let sort = super::super::translate::ty_to_expr_sort_enriched(
                        tcx,
                        body.local_decls[local].ty,
                    );
                    let name =
                        super::unannotated_loops::fresh_name(&format!("drop{}", local.as_usize()));
                    local_exprs.insert(local, PureExpr::Var(name, sort));
                }
                super::borrow_carriers::note_unsupported();
            }
            extract_from_block_with_context(tcx, body, *target, local_exprs, visited, ctx, effects)
        }
        TerminatorKind::Return => local_exprs.get(&Local::from_u32(0)).cloned(),
        _ => {
            // Unexpected terminator (e.g., Assert, Call). Fall back to
            // returning None so the caller uses the normal opaque-call
            // path. The Goto/Drop cases cover the standard ? desugaring.
            return None;
        }
    };

    // Build Ite(is_some(x) / is_ok(x), continue_body, x) to model
    // both paths of the `?` operator:
    //
    //   - Success path (is_some/is_ok): the continue body produces the
    //     normal return value (e.g., `Some(unwrap(x))` for `Some(x?)`).
    //
    //   - Failure path (!is_some/!is_ok): the `?` desugars to an early
    //     return via `FromResidual::from_residual(residual)`. For
    //     Option→Option and Result→Result, this is identity: the input
    //     `x` (which must be None / Err) is returned directly. Using `x`
    //     as the else branch captures this without needing a spec for
    //     `from_residual`. (#2675)
    //
    // Previously this used `LetAssume` which only modeled the success
    // path, leaving the result unconstrained when `x` was the failure
    // variant. This caused spurious counterexamples where the solver
    // could set `result` to an arbitrary value in the failure case.
    continue_result.map(|body_expr| {
        // Reconstruction optimization: when the continue body wraps
        // `unwrap(x)` back in the same constructor (e.g., `Some(unwrap(x))`
        // or `Ok(unwrap(x))`), the Ite is equivalent to just `x`. This is
        // because:
        //   - is_some(x) => Some(unwrap(x)) == x  (reconstruction axiom)
        //   - !is_some(x) => else-branch is x     (identity)
        //
        // Simplifying avoids sort mismatch in the ay encoder: the true-branch
        // `Some(unwrap(x))` encodes as Datatype(OptionInt) while `x` encodes
        // as Int, causing `safe_ite` to replace one branch with a fresh
        // unconstrained constant. (#2675)
        if is_reconstruction_of(&body_expr, &arg_expr) {
            return arg_expr;
        }

        PureExpr::Ite(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(arg_expr.clone()),
                method: is_variant_method.to_string(),
                args: vec![],
            }),
            Arc::new(body_expr),
            Arc::new(arg_expr),
        )
    })
}

/// Detect whether `body_expr` is a reconstruction of `arg_expr`: i.e.,
/// `Constructor(unwrap(arg_expr))` for some recognized ADT constructor.
///
/// Matches patterns like:
/// - `Some(x.unwrap())` where `x` is `arg_expr`
/// - `Ok(x.unwrap())` where `x` is `arg_expr`
///
/// These are identity by the ADT reconstruction axiom:
/// `is_some(x) => Some(unwrap(x)) == x`.
pub(super) fn is_reconstruction_of(body_expr: &PureExpr, arg_expr: &PureExpr) -> bool {
    // Match: LogicFnCall { name: "Some"|"Ok"|"Option::Some"|"Result::Ok",
    //                       args: [MethodCall { receiver: arg, method: "unwrap" }] }
    let PureExpr::LogicFnCall { name, args } = body_expr else {
        return false;
    };
    // The constructor name may be bare ("Some"/"Ok") from ay-level tests,
    // short-qualified ("Option::Some"/"Result::Ok"), or fully qualified from
    // MIR extraction (for example "core::option::Option::Some").
    let is_some_ctor =
        matches!(name.as_str(), "Some" | "Option::Some") || name.ends_with("::Option::Some");
    let is_ok_ctor = matches!(name.as_str(), "Ok" | "Result::Ok") || name.ends_with("::Result::Ok");
    if !is_some_ctor && !is_ok_ctor {
        return false;
    }
    if args.len() != 1 {
        return false;
    }
    let PureExpr::MethodCall {
        receiver,
        method,
        args: inner_args,
    } = &args[0]
    else {
        return false;
    };
    if method != "unwrap" || !inner_args.is_empty() {
        return false;
    }
    // Check that the receiver is the same as arg_expr.
    receiver.as_ref() == arg_expr
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- is_try_branch_path ---

    #[test]
    fn test_is_try_branch_path_exact_std() {
        assert!(is_try_branch_path("std::ops::Try::branch"));
    }

    #[test]
    fn test_is_try_branch_path_ends_with_try_branch() {
        assert!(is_try_branch_path("core::ops::try_trait::Try::branch"));
    }

    #[test]
    fn test_is_try_branch_path_angle_bracket_with_module() {
        // The `contains("::Try>::branch")` arm matches module-qualified impl blocks
        assert!(is_try_branch_path(
            "<Option<i32> as core::ops::try_trait::Try>::branch"
        ));
    }

    #[test]
    fn test_is_try_branch_path_bare_angle_bracket_not_matched() {
        // `<T as Try>::branch` without `::` before `Try>` does NOT match
        // any of the three patterns — this is intentional since rustc def paths
        // use the module-qualified form, not bare trait names.
        assert!(!is_try_branch_path("<Option<i32> as Try>::branch"));
    }

    #[test]
    fn test_is_try_branch_path_unrelated_function() {
        assert!(!is_try_branch_path("std::vec::Vec::push"));
    }

    #[test]
    fn test_is_try_branch_path_empty_string() {
        assert!(!is_try_branch_path(""));
    }

    #[test]
    fn test_is_try_branch_path_partial_match_not_suffix() {
        // "branch" alone should not match — needs ::Try::branch or Try>::branch
        assert!(!is_try_branch_path("branch"));
    }

    #[test]
    fn test_is_try_branch_path_similar_but_wrong() {
        assert!(!is_try_branch_path("std::ops::Try::call"));
        assert!(!is_try_branch_path("std::ops::NotTry::branch"));
    }

    // --- classify_try_self_adt_path ---

    #[test]
    fn test_classify_option_short() {
        assert_eq!(classify_try_self_adt_path("Option"), Some(true));
    }

    #[test]
    fn test_classify_option_std() {
        assert_eq!(
            classify_try_self_adt_path("std::option::Option"),
            Some(true)
        );
    }

    #[test]
    fn test_classify_option_core() {
        assert_eq!(
            classify_try_self_adt_path("core::option::Option"),
            Some(true)
        );
    }

    #[test]
    fn test_classify_result_short() {
        assert_eq!(classify_try_self_adt_path("Result"), Some(false));
    }

    #[test]
    fn test_classify_result_std() {
        assert_eq!(
            classify_try_self_adt_path("std::result::Result"),
            Some(false)
        );
    }

    #[test]
    fn test_classify_result_core() {
        assert_eq!(
            classify_try_self_adt_path("core::result::Result"),
            Some(false)
        );
    }

    #[test]
    fn test_classify_unsupported_type() {
        assert_eq!(classify_try_self_adt_path("ControlFlow"), None);
    }

    #[test]
    fn test_classify_empty_string() {
        assert_eq!(classify_try_self_adt_path(""), None);
    }

    #[test]
    fn test_classify_poll() {
        assert_eq!(classify_try_self_adt_path("std::task::Poll"), None);
    }

    // --- is_reconstruction_of ---

    fn make_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn make_unwrap(receiver: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "unwrap".to_string(),
            args: vec![],
        }
    }

    fn make_ctor(name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args,
        }
    }

    #[test]
    fn test_reconstruction_some_unwrap_x() {
        let x = make_var("x");
        let body = make_ctor("Some", vec![make_unwrap(x.clone())]);
        assert!(is_reconstruction_of(&body, &x));
    }

    #[test]
    fn test_reconstruction_fully_qualified_option_some_unwrap_x() {
        let x = make_var("x");
        let body = make_ctor("core::option::Option::Some", vec![make_unwrap(x.clone())]);
        assert!(is_reconstruction_of(&body, &x));
    }

    #[test]
    fn test_reconstruction_fully_qualified_result_ok_unwrap_x() {
        let x = make_var("x");
        let body = make_ctor("core::result::Result::Ok", vec![make_unwrap(x.clone())]);
        assert!(is_reconstruction_of(&body, &x));
    }

    #[test]
    fn test_reconstruction_ok_unwrap_x() {
        let x = make_var("x");
        let body = make_ctor("Ok", vec![make_unwrap(x.clone())]);
        assert!(is_reconstruction_of(&body, &x));
    }

    #[test]
    fn test_reconstruction_different_receiver_not_matched() {
        let x = make_var("x");
        let y = make_var("y");
        let body = make_ctor("Some", vec![make_unwrap(y)]);
        assert!(!is_reconstruction_of(&body, &x));
    }

    #[test]
    fn test_reconstruction_wrong_constructor_not_matched() {
        let x = make_var("x");
        let body = make_ctor("Err", vec![make_unwrap(x.clone())]);
        assert!(!is_reconstruction_of(&body, &x));
    }

    #[test]
    fn test_reconstruction_wrong_method_not_matched() {
        let x = make_var("x");
        let body = make_ctor(
            "Some",
            vec![PureExpr::MethodCall {
                receiver: Arc::new(x.clone()),
                method: "unwrap_or".to_string(),
                args: vec![],
            }],
        );
        assert!(!is_reconstruction_of(&body, &x));
    }

    #[test]
    fn test_reconstruction_bare_var_not_matched() {
        let x = make_var("x");
        assert!(!is_reconstruction_of(&x, &x));
    }

    #[test]
    fn test_reconstruction_multi_arg_not_matched() {
        let x = make_var("x");
        let body = make_ctor("Some", vec![make_unwrap(x.clone()), PureExpr::Int(0)]);
        assert!(!is_reconstruction_of(&body, &x));
    }

    // Qualified constructor names from MIR extraction

    #[test]
    fn test_reconstruction_qualified_option_some() {
        let x = make_var("x");
        let body = make_ctor("Option::Some", vec![make_unwrap(x.clone())]);
        assert!(is_reconstruction_of(&body, &x));
    }

    #[test]
    fn test_reconstruction_qualified_result_ok() {
        let x = make_var("x");
        let body = make_ctor("Result::Ok", vec![make_unwrap(x.clone())]);
        assert!(is_reconstruction_of(&body, &x));
    }

    #[test]
    fn test_reconstruction_qualified_result_err_not_matched() {
        let x = make_var("x");
        let body = make_ctor("Result::Err", vec![make_unwrap(x.clone())]);
        assert!(!is_reconstruction_of(&body, &x));
    }
}
