// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct lowering for trusted cell builtins.
//!
//! This Phase 1 lane bypasses generic std-spec string parsing for the
//! `PredCell` / `PermCell` surface used by #2316 and emits canonical `PureExpr`
//! assumptions/obligations directly.

use std::sync::Arc;

use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
    BinOp, ExprSort, PureExpr,
};

use super::{
    super::{
        effects::{CallEffects, ExtractionSession},
        translate::ty_to_expr_sort_enriched,
    },
    call_args::{call_result_symbol, translate_call_args_for_substitutions_with_tcx},
    call_resolve_shared::CellBuiltin,
    call_resolve_util::wrap_call_context,
    call_spec::CallSiteContext,
    closure::{
        propagate_mutating_receiver_state_with_captures,
        propagate_mutating_ref_arg_states_for_positions,
    },
    extract_from_block_with_context,
    helpers::wrap_projected_facts,
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct CellBuiltinApplication {
    result_expr: PureExpr,
    assumptions: Vec<PureExpr>,
    obligations: Vec<PureExpr>,
    mutating_ref_positions: Vec<usize>,
    mutates_receiver: bool,
}

pub(super) fn handle_cell_builtin_call<'tcx>(
    call_site: CallSiteContext<'_, 'tcx>,
    session: &mut ExtractionSession<'_>,
    effects: &mut CallEffects,
    builtin: CellBuiltin,
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
    let mut arg_exprs: Vec<PureExpr> =
        translate_call_args_for_substitutions_with_tcx(args, &local_exprs, Some(body), Some(tcx))
            .into_iter()
            .map(|arg| arg.expr)
            .collect();
    if matches!(
        builtin,
        CellBuiltin::PermCellSet
            | CellBuiltin::PermCellGet
            | CellBuiltin::PermCellBorrow
            | CellBuiltin::PermCellBorrowMut
            | CellBuiltin::PermCellReplace
            | CellBuiltin::PermCellIntoInner
            | CellBuiltin::PermCellTake
    ) {
        if let Some(receiver) = arg_exprs.first_mut() {
            *receiver =
                effective_permcell_receiver_state(receiver.clone(), projected_write_facts, effects);
        }
    }
    let pre_call_self = arg_exprs.first().cloned();
    let arg_sorts: Vec<Option<ExprSort>> = args
        .iter()
        .map(|arg| ty_to_expr_sort_enriched(tcx, arg.node.ty(&body.local_decls, tcx)))
        .collect();
    let result_expr = call_result_symbol(body, destination.local, tcx);
    let result_sort = ty_to_expr_sort_enriched(tcx, body.local_decls[destination.local].ty);
    let application = build_cell_builtin_application(
        builtin,
        &arg_exprs,
        &arg_sorts,
        result_expr.clone(),
        result_sort,
    );

    if let Some(identity) = predcell_receiver_view_identity(builtin, pre_call_self.as_ref()) {
        session.effects.assumptions.push(identity);
    }

    session
        .effects
        .obligations
        .extend(application.obligations.iter().cloned());
    session
        .effects
        .assumptions
        .extend(application.assumptions.iter().cloned());
    propagate_mutating_ref_arg_states_for_positions(
        &mut local_exprs,
        body,
        ctx.arg_names,
        args,
        &application.mutating_ref_positions,
        Some(effects),
        None,
    );
    if application.mutates_receiver {
        effects.has_mutating_call_effect = true;
        if let Some(self_expr) = pre_call_self.as_ref() {
            propagate_mutating_receiver_state_with_captures(
                &mut local_exprs,
                body,
                ctx.arg_names,
                self_expr,
                None,
            );
        }
    }
    if builtin == CellBuiltin::PermCellBorrowMut {
        if let (Some(receiver), PureExpr::Var(result_name, _)) =
            (pre_call_self.as_ref(), &application.result_expr)
        {
            effects
                .mut_ref_result_receivers
                .insert(result_name.clone(), receiver.clone());
        }
    }
    local_exprs.insert(destination.local, application.result_expr);

    wrap_call_context(
        wrap_projected_facts(
            projected_write_facts.to_vec(),
            extract_from_block_with_context(tcx, body, next_bb, local_exprs, visited, ctx, effects),
        ),
        ctx.scope_call_context,
        &mut *session.effects,
    )
}

fn build_cell_builtin_application(
    builtin: CellBuiltin,
    args: &[PureExpr],
    _arg_sorts: &[Option<ExprSort>],
    result_expr: PureExpr,
    _result_sort: Option<ExprSort>,
) -> CellBuiltinApplication {
    match builtin {
        CellBuiltin::PredCellNew => {
            let value = args[0].clone();
            let pred = args[1].clone();
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![eq(view(result_expr), pred.clone())],
                obligations: vec![mapping_lookup(pred, value)],
                mutating_ref_positions: Vec::new(),
                mutates_receiver: false,
            }
        }
        CellBuiltin::PredCellGet => CellBuiltinApplication {
            result_expr: result_expr.clone(),
            assumptions: vec![predcell_holds(args[0].clone(), result_expr)],
            obligations: Vec::new(),
            mutating_ref_positions: Vec::new(),
            mutates_receiver: false,
        },
        CellBuiltin::PredCellSet => CellBuiltinApplication {
            result_expr,
            assumptions: Vec::new(),
            obligations: vec![predcell_holds(args[0].clone(), args[1].clone())],
            mutating_ref_positions: Vec::new(),
            mutates_receiver: false,
        },
        CellBuiltin::PredCellSwap => {
            // PredCell::swap(self, other)
            // requires: forall<x: _> self@[x] == other@[x]
            let left = args[0].clone();
            let right = args[1].clone();
            let x_var = PureExpr::Var("x".to_string(), None);
            let left_lookup = mapping_lookup(view(left), x_var.clone());
            let right_lookup = mapping_lookup(view(right), x_var.clone());
            CellBuiltinApplication {
                result_expr,
                assumptions: Vec::new(),
                obligations: vec![PureExpr::Forall {
                    var: "x".to_string(),
                    var_sort: None,
                    body: Arc::new(eq(left_lookup.clone(), right_lookup)),
                    triggers: vec![vec![left_lookup]],
                }],
                mutating_ref_positions: Vec::new(),
                mutates_receiver: false,
            }
        }
        CellBuiltin::PredCellReplace => CellBuiltinApplication {
            result_expr: result_expr.clone(),
            assumptions: vec![predcell_holds(args[0].clone(), result_expr)],
            obligations: vec![predcell_holds(args[0].clone(), args[1].clone())],
            mutating_ref_positions: Vec::new(),
            mutates_receiver: false,
        },
        CellBuiltin::PredCellIntoInner => CellBuiltinApplication {
            result_expr: result_expr.clone(),
            assumptions: vec![predcell_holds(args[0].clone(), result_expr)],
            obligations: Vec::new(),
            mutating_ref_positions: Vec::new(),
            mutates_receiver: false,
        },
        CellBuiltin::PredCellUpdate => {
            // PredCell::update(self, f)
            // requires: forall<x: _> self@[x] ==> f.precondition((x,))
            // requires: forall<x: _, res: _> self@[x] && f.postcondition_once((x,), res) ==> self@[res]
            let cell = args[0].clone();
            let closure = args[1].clone();
            let x_var = PureExpr::Var("x".to_string(), None);
            let res_var = PureExpr::Var("res".to_string(), None);
            let x_tuple = tuple(vec![x_var.clone()]);
            let holds_x = predcell_holds(cell.clone(), x_var.clone());
            let precondition = method(closure.clone(), "precondition", vec![x_tuple.clone()]);
            let postcondition = method(
                closure,
                "postcondition_once",
                vec![x_tuple, res_var.clone()],
            );
            let preserves_pred = predcell_holds(cell, res_var);
            CellBuiltinApplication {
                result_expr,
                assumptions: Vec::new(),
                obligations: vec![
                    PureExpr::Forall {
                        var: "x".to_string(),
                        var_sort: None,
                        body: Arc::new(bin(holds_x.clone(), BinOp::Implies, precondition.clone())),
                        triggers: vec![vec![holds_x.clone()]],
                    },
                    PureExpr::Forall {
                        var: "x".to_string(),
                        var_sort: None,
                        body: Arc::new(PureExpr::Forall {
                            var: "res".to_string(),
                            var_sort: None,
                            body: Arc::new(bin(
                                and(holds_x.clone(), postcondition.clone()),
                                BinOp::Implies,
                                preserves_pred,
                            )),
                            triggers: vec![vec![postcondition]],
                        }),
                        triggers: Vec::new(),
                    },
                ],
                mutating_ref_positions: Vec::new(),
                mutates_receiver: false,
            }
        }
        CellBuiltin::PredCellFromMut => {
            let target = args[0].clone();
            let pred = args[1].clone();
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![
                    mapping_lookup(pred.clone(), final_expr(target.clone())),
                    eq(view(result_expr), pred.clone()),
                ],
                obligations: vec![mapping_lookup(pred, deref(target))],
                mutating_ref_positions: vec![0],
                mutates_receiver: false,
            }
        }
        CellBuiltin::PredCellAsSliceOfCells => {
            let pred = args[1].clone();
            let pred_len = method(pred.clone(), "len", vec![]);
            let predcell_slice_elem_bridge = |index: PureExpr| {
                eq(
                    view(method(
                        result_expr.clone(),
                        "index_logic",
                        vec![index.clone()],
                    )),
                    method(pred.clone(), "index_logic", vec![index]),
                )
            };
            let bounded_elem_bridge = |index: i64| {
                let index_expr = int(index);
                bin(
                    bin(index_expr.clone(), BinOp::Lt, pred_len.clone()),
                    BinOp::Implies,
                    predcell_slice_elem_bridge(index_expr),
                )
            };

            let i_var = int_var("i");
            let result_elem_view = view(method(
                result_expr.clone(),
                "index_logic",
                vec![i_var.clone()],
            ));
            // Direct Mapping-level equality bridge matching Creusot's spec:
            //   forall<i: Int> 0 <= i < pred.len() ==> result[i]@ == pred[i]
            //
            // Previous versions used a nested double-quantifier pointwise form
            // (`forall i. forall x. ... result[i]@[x] == pred[i][x]`) which avoided
            // a sort mismatch but created a formula that ay's CEGQI engine could not
            // instantiate (quantifier-cegqi-incomplete on splits_up).
            //
            // The sort mismatch between Mapping-sorted LHS (View of PredCellSlice
            // element) and Int-sorted RHS (Seq element coercion) is now handled by
            // the ay encoder's sort restoration mechanism:
            // - `try_restore_seq_element_from_int` bridges Seq element sorts back
            //   to Mapping when equality targets require it
            // - `__predcell_slice_elem_view` UF declarations provide the PredCellSlice
            //   element-to-Mapping lift
            //
            // The single-quantifier form is simpler, matches Creusot's postcondition
            // exactly, and produces formulas that ay can reason about. (#2316)
            let elem_bridge = PureExpr::Forall {
                var: "i".to_string(),
                var_sort: Some(ExprSort::Int),
                body: Arc::new(bin(
                    and(
                        bin(int(0), BinOp::Le, i_var.clone()),
                        bin(i_var.clone(), BinOp::Lt, pred_len.clone()),
                    ),
                    BinOp::Implies,
                    predcell_slice_elem_bridge(i_var.clone()),
                )),
                triggers: vec![vec![result_elem_view]],
            };
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![
                    eq(
                        method(view(result_expr.clone()), "len", vec![]),
                        pred_len.clone(),
                    ),
                    bounded_elem_bridge(0),
                    bounded_elem_bridge(1),
                    elem_bridge,
                ],
                obligations: Vec::new(),
                mutating_ref_positions: Vec::new(),
                mutates_receiver: false,
            }
        }
        CellBuiltin::PermCellNew => {
            // PermCell::new(value) -> (cell, perm)
            // Public contract surface: cell@ == value. The returned permission
            // also guards exactly that cell; keep this as an identity fact
            // between the cell and `perm.ward()`, without tying `perm@` to the
            // value sort that caused false sort conflicts in Box/Ghost paths.
            let value = args[0].clone();
            let cell = tuple_field(result_expr.clone(), 0);
            let perm = tuple_field(result_expr.clone(), 1);
            let ward = method(perm, "ward", Vec::new());
            CellBuiltinApplication {
                result_expr,
                assumptions: vec![eq(view(cell.clone()), value), eq(cell, ward)],
                obligations: Vec::new(),
                mutating_ref_positions: Vec::new(),
                mutates_receiver: false,
            }
        }
        CellBuiltin::PermCellSet => {
            // PermCell::set(cell, &mut perm, value)
            // ensures: (^self)@ == value
            let cell = args[0].clone();
            let value = args[2].clone();
            CellBuiltinApplication {
                result_expr,
                assumptions: vec![eq(view(final_expr(cell)), value)],
                obligations: Vec::new(),
                mutating_ref_positions: vec![1],
                mutates_receiver: true,
            }
        }
        CellBuiltin::PermCellGet => {
            // PermCell::get(cell, perm) -> T
            // Creusot model: result == self@
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![eq(result_expr, view(args[0].clone()))],
                obligations: Vec::new(),
                mutating_ref_positions: Vec::new(),
                mutates_receiver: false,
            }
        }
        CellBuiltin::PermCellBorrow => {
            // PermCell::borrow(cell, perm) -> &T
            // Creusot model: *result == self@
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![eq(deref(result_expr), view(args[0].clone()))],
                obligations: Vec::new(),
                mutating_ref_positions: Vec::new(),
                mutates_receiver: false,
            }
        }
        CellBuiltin::PermCellBorrowMut => {
            // PermCell::borrow_mut(cell, &mut perm) -> &mut T
            // Creusot model: *result == self@, ^result == (^self)@
            let cell = args[0].clone();
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![
                    eq(deref(result_expr.clone()), view(cell.clone())),
                    eq(final_expr(result_expr), view(final_expr(cell))),
                ],
                obligations: Vec::new(),
                mutating_ref_positions: vec![1],
                mutates_receiver: false,
            }
        }
        CellBuiltin::PermCellReplace => {
            // PermCell::replace(cell, &mut perm, new_value) -> old_value
            // Creusot model: result == self@, (^self)@ == new_value
            let cell = args[0].clone();
            let value = args[2].clone();
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![
                    eq(result_expr, view(cell.clone())),
                    eq(view(final_expr(cell)), value),
                ],
                obligations: Vec::new(),
                mutating_ref_positions: vec![1],
                mutates_receiver: true,
            }
        }
        CellBuiltin::PermCellIntoInner => {
            // PermCell::into_inner(cell, perm) -> T
            // Creusot model: result == self@
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![eq(result_expr, view(args[0].clone()))],
                obligations: Vec::new(),
                mutating_ref_positions: Vec::new(),
                mutates_receiver: false,
            }
        }
        CellBuiltin::PredCellTake => {
            // PredCell::take(self) -> T
            // Creusot model: self@[result], requires Default::default() satisfies predicate.
            // The Default::default() obligation is deferred to the spec-string path;
            // the builtin lane just models the result value extraction.
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![predcell_holds(args[0].clone(), result_expr)],
                obligations: Vec::new(),
                mutating_ref_positions: Vec::new(),
                mutates_receiver: false,
            }
        }
        CellBuiltin::PermCellTake => {
            // PermCell::take(self, perm) -> T
            // Creusot model: result == self@, (^self)@ == Default::default()
            // The Default::default() postcondition is deferred to the spec-string path.
            let cell = args[0].clone();
            CellBuiltinApplication {
                result_expr: result_expr.clone(),
                assumptions: vec![eq(result_expr, view(cell.clone()))],
                obligations: Vec::new(),
                mutating_ref_positions: vec![1],
                mutates_receiver: true,
            }
        }
        CellBuiltin::PermCellFromMut => {
            // PermCell::from_mut(t: &mut T) -> (&PermCell<T>, Ghost<&mut Perm<...>>)
            // Creusot model: result.0@ == *t, (^result.0)@ == ^t
            let target = args[0].clone();
            let cell = tuple_field(result_expr.clone(), 0);
            CellBuiltinApplication {
                result_expr,
                assumptions: vec![
                    eq(view(cell.clone()), deref(target.clone())),
                    eq(view(final_expr(cell)), final_expr(target)),
                ],
                obligations: Vec::new(),
                mutating_ref_positions: vec![0],
                mutates_receiver: false,
            }
        }
        CellBuiltin::PermWard => CellBuiltinApplication {
            result_expr: method(args[0].clone(), "ward", Vec::new()),
            assumptions: Vec::new(),
            obligations: Vec::new(),
            mutating_ref_positions: Vec::new(),
            mutates_receiver: false,
        },
    }
}

/// Connecting identity `(*c)@ == c@` for a PredCell predicate builtin whose
/// method receiver is `Deref(Var)` (i.e. `(*c)` for `c: &PredCell` /
/// `&mut PredCell`).
///
/// The contract's bare `c@` lowers to `View(Var("c"))` (encoded const
/// `c_view`), while the get/set/replace/etc. predicate obligations are stated
/// over the method receiver `(*c)@` = `View(Deref(Var("c")))` (encoded const
/// `c_current_view`). These denote the SAME predicate Mapping — `View` of a
/// reference is definitionally the `View` of its referent — but the encoder
/// declares them as distinct uninterpreted Mapping constants, so the
/// precondition's closure-predicate axiom (`c@ == |z| ...`, tied to `c_view`)
/// never reaches the obligation's `mapping_get(c_current_view, ...)` and the
/// goal is reported as a spurious counterexample (#2316).
///
/// SOUND: the equated terms are provably equal in every model (a `Deref(Var)`
/// PredCell receiver can only arise from `(*c)` where `c` is a reference, and
/// reference `View` is transparent), so this only identifies two already-equal
/// Mapping values. As a hypothesis added to the VC antecedent it is monotone
/// for should_succeed goals and — being a universal tautology — can never
/// validate an otherwise-invalid goal (no false-accept).
fn predcell_receiver_view_identity(
    builtin: CellBuiltin,
    cell: Option<&PureExpr>,
) -> Option<PureExpr> {
    if !matches!(
        builtin,
        CellBuiltin::PredCellGet
            | CellBuiltin::PredCellSet
            | CellBuiltin::PredCellReplace
            | CellBuiltin::PredCellIntoInner
            | CellBuiltin::PredCellTake
            | CellBuiltin::PredCellUpdate
    ) {
        return None;
    }
    let cell = cell?;
    let PureExpr::Deref(inner) = cell else {
        return None;
    };
    if !matches!(inner.as_ref(), PureExpr::Var(..)) {
        return None;
    }
    Some(eq(view(cell.clone()), view(inner.as_ref().clone())))
}

fn predcell_holds(cell: PureExpr, value: PureExpr) -> PureExpr {
    mapping_lookup(view(cell), value)
}

fn mapping_lookup(receiver: PureExpr, key: PureExpr) -> PureExpr {
    method(receiver, "index_logic", vec![key])
}

fn method(receiver: PureExpr, name: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: name.to_string(),
        args,
    }
}

fn view(expr: PureExpr) -> PureExpr {
    PureExpr::View(Arc::new(expr))
}

fn deref(expr: PureExpr) -> PureExpr {
    PureExpr::Deref(Arc::new(expr))
}

fn final_expr(expr: PureExpr) -> PureExpr {
    PureExpr::Final(Arc::new(expr))
}

fn tuple_field(expr: PureExpr, index: usize) -> PureExpr {
    PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(index),
        args: vec![expr],
    }
}

fn tuple(args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(args.len()),
        args,
    }
}

fn eq(left: PureExpr, right: PureExpr) -> PureExpr {
    bin(left, BinOp::Eq, right)
}

fn and(left: PureExpr, right: PureExpr) -> PureExpr {
    bin(left, BinOp::And, right)
}

fn bin(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
}

fn int(value: i64) -> PureExpr {
    PureExpr::Int(value)
}

fn int_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Int))
}

fn effective_permcell_receiver_state(
    receiver: PureExpr,
    projected_write_facts: &[(PureExpr, PureExpr)],
    effects: &CallEffects,
) -> PureExpr {
    if projected_write_facts.is_empty() {
        return receiver;
    }

    let receiver_final_view = view(final_expr(receiver.clone()));
    for (lhs, _) in projected_write_facts {
        let PureExpr::Deref(inner) = lhs else {
            continue;
        };
        let PureExpr::Var(result_name, _) = inner.as_ref() else {
            continue;
        };
        if effects.assumptions.iter().any(|assumption| {
            assumption_links_result_final_to_receiver(assumption, result_name, &receiver_final_view)
        }) {
            return final_expr(receiver);
        }
    }

    receiver
}

fn assumption_links_result_final_to_receiver(
    assumption: &PureExpr,
    result_name: &str,
    receiver_final_view: &PureExpr,
) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = assumption else {
        return false;
    };
    (is_final_result_var(left.as_ref(), result_name) && right.as_ref() == receiver_final_view)
        || (is_final_result_var(right.as_ref(), result_name)
            && left.as_ref() == receiver_final_view)
}

fn is_final_result_var(expr: &PureExpr, result_name: &str) -> bool {
    matches!(
        expr,
        PureExpr::Final(inner)
            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == result_name)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str, sort: Option<ExprSort>) -> PureExpr {
        PureExpr::Var(name.to_string(), sort)
    }

    #[test]
    fn predcell_as_slice_of_cells_emits_single_quantifier_elem_bridge() {
        let result = var(
            "call_7",
            Some(ExprSort::Ref(Box::new(ExprSort::Datatype(1)))),
        );
        let pred = var("pred", Some(ExprSort::Seq));
        let application = build_cell_builtin_application(
            CellBuiltin::PredCellAsSliceOfCells,
            &[var("self", None), pred],
            &[None, Some(ExprSort::Seq)],
            result,
            Some(ExprSort::Ref(Box::new(ExprSort::Datatype(1)))),
        );

        // 4 assumptions: length equality, concrete 0/1 instances, and the
        // general element bridge (#2316).
        assert_eq!(application.assumptions.len(), 4);
        for (offset, assumption) in application.assumptions[1..3].iter().enumerate() {
            let index = offset as i64;
            assert!(
                matches!(assumption, PureExpr::BinOp(_, BinOp::Implies, _)),
                "expected bounded concrete bridge for index {index}, got {assumption:?}"
            );
        }
        // assumptions[3] is the single forall element bridge matching Creusot spec:
        //   forall i: Int. 0 <= i < pred.len() ==> result[i]@ == pred[i]
        match &application.assumptions[3] {
            PureExpr::Forall {
                var: qvar,
                var_sort,
                body,
                triggers,
            } => {
                assert_eq!(qvar, "i");
                assert_eq!(*var_sort, Some(ExprSort::Int));
                assert_eq!(triggers.len(), 1);
                // Body should be an implication (not a nested forall)
                assert!(
                    matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Implies, _)),
                    "expected single-level implication bridge, got {body:?}"
                );
                // Verify it's NOT a nested forall (regression guard for the old
                // double-quantifier form that caused quantifier-cegqi-incomplete)
                assert!(
                    !matches!(body.as_ref(), PureExpr::Forall { .. }),
                    "bridge must be single-quantifier, not nested"
                );
            }
            other => panic!("expected single forall bridge, got {other:?}"),
        }
    }

    #[test]
    fn permcell_replace_threads_view_final_state() {
        let result = var("call_9", Some(ExprSort::Int));
        let value = var("value", Some(ExprSort::Int));
        let cell = var("self", Some(ExprSort::Datatype(1)));
        let perm = var("own", Some(ExprSort::Int));
        let application = build_cell_builtin_application(
            CellBuiltin::PermCellReplace,
            &[cell.clone(), perm, value.clone()],
            &[None, Some(ExprSort::Int), Some(ExprSort::Int)],
            result.clone(),
            Some(ExprSort::Int),
        );

        assert_eq!(application.mutating_ref_positions, vec![1]);
        assert!(application.mutates_receiver);
        assert_eq!(application.assumptions.len(), 2);
        // First assumption: result == view(self)
        match &application.assumptions[0] {
            PureExpr::BinOp(left, BinOp::Eq, right) => {
                assert_eq!(left.as_ref(), &result);
                assert_eq!(right.as_ref(), &view(cell.clone()));
            }
            other => panic!("expected equality assumption, got {other:?}"),
        }
        // Second assumption: view(final(self)) == new_value
        match &application.assumptions[1] {
            PureExpr::BinOp(left, BinOp::Eq, right) => {
                assert_eq!(left.as_ref(), &view(final_expr(cell)));
                assert_eq!(right.as_ref(), &value);
            }
            other => panic!("expected equality assumption, got {other:?}"),
        }
    }

    #[test]
    fn permcell_borrow_mut_threads_cell_view_state() {
        let result = var("call_7", Some(ExprSort::MutRef(Box::new(ExprSort::Int))));
        let cell = var("self", Some(ExprSort::Datatype(1)));
        let application = build_cell_builtin_application(
            CellBuiltin::PermCellBorrowMut,
            &[
                cell.clone(),
                var(
                    "own",
                    Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(2)))),
                ),
            ],
            &[
                Some(ExprSort::Datatype(1)),
                Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(2)))),
            ],
            result.clone(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        );

        assert_eq!(application.mutating_ref_positions, vec![1]);
        assert!(!application.mutates_receiver);
        assert_eq!(
            application.assumptions,
            vec![
                eq(deref(result.clone()), view(cell.clone())),
                eq(final_expr(result), view(final_expr(cell))),
            ]
        );
    }

    #[test]
    fn projected_write_advances_permcell_receiver_state() {
        let receiver = var("self", Some(ExprSort::Datatype(1)));
        let result_name = "call_16";
        let projected_write_facts = vec![(
            deref(var(
                result_name,
                Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
            )),
            int(2),
        )];
        let mut effects = CallEffects::new();
        effects.assumptions.push(eq(
            final_expr(var(
                result_name,
                Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
            )),
            view(final_expr(receiver.clone())),
        ));

        assert_eq!(
            effective_permcell_receiver_state(receiver.clone(), &projected_write_facts, &effects),
            final_expr(receiver),
        );
    }

    #[test]
    fn permcell_new_ties_cell_value_and_ward_identity() {
        let value = var("value", Some(ExprSort::Int));
        let result = var("call_3", Some(ExprSort::Tuple(2)));
        let application = build_cell_builtin_application(
            CellBuiltin::PermCellNew,
            std::slice::from_ref(&value),
            &[Some(ExprSort::Int)],
            result.clone(),
            Some(ExprSort::Tuple(2)),
        );

        assert_eq!(application.assumptions.len(), 2);
        match &application.assumptions[0] {
            PureExpr::BinOp(left, BinOp::Eq, right) => {
                assert!(
                    matches!(left.as_ref(), PureExpr::View(_)),
                    "expected View(...) on lhs, got {left:?}"
                );
                assert_eq!(right.as_ref(), &value);
            }
            other => panic!("expected equality assumption, got {other:?}"),
        }
        assert_eq!(
            application.assumptions[1],
            eq(
                tuple_field(result.clone(), 0),
                method(tuple_field(result, 1), "ward", Vec::new())
            )
        );
    }

    #[test]
    fn perm_ward_returns_stable_method_term() {
        let receiver = var("perm", Some(ExprSort::Datatype(2)));
        let result = var(
            "call_7",
            Some(ExprSort::Ref(Box::new(ExprSort::Datatype(1)))),
        );
        let application = build_cell_builtin_application(
            CellBuiltin::PermWard,
            std::slice::from_ref(&receiver),
            &[Some(ExprSort::Datatype(2))],
            result,
            Some(ExprSort::Ref(Box::new(ExprSort::Datatype(1)))),
        );

        assert_eq!(
            application.result_expr,
            method(receiver, "ward", Vec::new())
        );
        assert!(application.assumptions.is_empty());
    }

    #[test]
    fn predcell_take_emits_holds_assumption() {
        let cell = var("self", Some(ExprSort::Datatype(1)));
        let result = var("call_10", Some(ExprSort::Int));
        let application = build_cell_builtin_application(
            CellBuiltin::PredCellTake,
            std::slice::from_ref(&cell),
            &[Some(ExprSort::Datatype(1))],
            result.clone(),
            Some(ExprSort::Int),
        );

        assert_eq!(application.assumptions.len(), 1);
        assert_eq!(application.assumptions[0], predcell_holds(cell, result),);
        assert!(application.obligations.is_empty());
        assert!(application.mutating_ref_positions.is_empty());
        assert!(!application.mutates_receiver);
    }

    #[test]
    fn permcell_take_threads_view_state() {
        let cell = var("self", Some(ExprSort::Datatype(1)));
        let perm = var("own", Some(ExprSort::Int));
        let result = var("call_11", Some(ExprSort::Int));
        let application = build_cell_builtin_application(
            CellBuiltin::PermCellTake,
            &[cell.clone(), perm],
            &[Some(ExprSort::Datatype(1)), Some(ExprSort::Int)],
            result.clone(),
            Some(ExprSort::Int),
        );

        assert_eq!(application.assumptions.len(), 1);
        assert_eq!(application.assumptions[0], eq(result, view(cell)),);
        assert!(application.obligations.is_empty());
        assert_eq!(application.mutating_ref_positions, vec![1]);
        assert!(application.mutates_receiver);
    }

    #[test]
    fn permcell_from_mut_threads_view_and_final() {
        let target = var("target", Some(ExprSort::MutRef(Box::new(ExprSort::Int))));
        let result = var("call_12", Some(ExprSort::Tuple(2)));
        let application = build_cell_builtin_application(
            CellBuiltin::PermCellFromMut,
            std::slice::from_ref(&target),
            &[Some(ExprSort::MutRef(Box::new(ExprSort::Int)))],
            result.clone(),
            Some(ExprSort::Tuple(2)),
        );

        let cell = tuple_field(result, 0);
        assert_eq!(application.assumptions.len(), 2);
        assert_eq!(
            application.assumptions[0],
            eq(view(cell.clone()), deref(target.clone())),
        );
        assert_eq!(
            application.assumptions[1],
            eq(view(final_expr(cell)), final_expr(target)),
        );
        assert!(application.obligations.is_empty());
        assert_eq!(application.mutating_ref_positions, vec![0]);
        assert!(!application.mutates_receiver);
    }

    #[test]
    fn predcell_new_assumes_view_eq_pred_and_obligates_pred_holds() {
        let value = var("value", Some(ExprSort::Int));
        let pred = var("pred", None);
        let result = var("call_13", Some(ExprSort::Datatype(1)));
        let application = build_cell_builtin_application(
            CellBuiltin::PredCellNew,
            &[value.clone(), pred.clone()],
            &[Some(ExprSort::Int), None],
            result.clone(),
            Some(ExprSort::Datatype(1)),
        );

        assert_eq!(
            application.assumptions,
            vec![eq(view(result), pred.clone())]
        );
        assert_eq!(application.obligations, vec![mapping_lookup(pred, value)]);
        assert!(application.mutating_ref_positions.is_empty());
        assert!(!application.mutates_receiver);
    }

    #[test]
    fn predcell_get_returns_predcell_holds() {
        let cell = var("self", Some(ExprSort::Datatype(1)));
        let result = var("call_14", Some(ExprSort::Int));
        let application = build_cell_builtin_application(
            CellBuiltin::PredCellGet,
            std::slice::from_ref(&cell),
            &[Some(ExprSort::Datatype(1))],
            result.clone(),
            Some(ExprSort::Int),
        );

        assert_eq!(application.assumptions, vec![predcell_holds(cell, result)]);
        assert!(application.obligations.is_empty());
        assert!(application.mutating_ref_positions.is_empty());
        assert!(!application.mutates_receiver);
    }

    #[test]
    fn predcell_set_obligates_predcell_holds() {
        let cell = var("self", Some(ExprSort::Datatype(1)));
        let value = var("value", Some(ExprSort::Int));
        let application = build_cell_builtin_application(
            CellBuiltin::PredCellSet,
            &[cell.clone(), value.clone()],
            &[Some(ExprSort::Datatype(1)), Some(ExprSort::Int)],
            var("call_15", None),
            None,
        );

        assert!(application.assumptions.is_empty());
        assert_eq!(application.obligations, vec![predcell_holds(cell, value)]);
        assert!(application.mutating_ref_positions.is_empty());
        assert!(!application.mutates_receiver);
    }

    #[test]
    fn predcell_replace_assumes_old_and_obligates_new() {
        let cell = var("self", Some(ExprSort::Datatype(1)));
        let value = var("value", Some(ExprSort::Int));
        let result = var("call_16", Some(ExprSort::Int));
        let application = build_cell_builtin_application(
            CellBuiltin::PredCellReplace,
            &[cell.clone(), value.clone()],
            &[Some(ExprSort::Datatype(1)), Some(ExprSort::Int)],
            result.clone(),
            Some(ExprSort::Int),
        );

        assert_eq!(
            application.assumptions,
            vec![predcell_holds(cell.clone(), result)]
        );
        assert_eq!(application.obligations, vec![predcell_holds(cell, value)]);
        assert!(application.mutating_ref_positions.is_empty());
        assert!(!application.mutates_receiver);
    }

    #[test]
    fn predcell_into_inner_returns_predcell_holds() {
        let cell = var("self", Some(ExprSort::Datatype(1)));
        let result = var("call_17", Some(ExprSort::Int));
        let application = build_cell_builtin_application(
            CellBuiltin::PredCellIntoInner,
            std::slice::from_ref(&cell),
            &[Some(ExprSort::Datatype(1))],
            result.clone(),
            Some(ExprSort::Int),
        );

        assert_eq!(application.assumptions, vec![predcell_holds(cell, result)]);
        assert!(application.obligations.is_empty());
        assert!(application.mutating_ref_positions.is_empty());
        assert!(!application.mutates_receiver);
    }

    #[test]
    fn permcell_get_returns_view_equality() {
        let cell = var("self", Some(ExprSort::Datatype(1)));
        let perm = var("perm", Some(ExprSort::Int));
        let result = var("call_18", Some(ExprSort::Int));
        let application = build_cell_builtin_application(
            CellBuiltin::PermCellGet,
            &[cell.clone(), perm],
            &[Some(ExprSort::Datatype(1)), Some(ExprSort::Int)],
            result.clone(),
            Some(ExprSort::Int),
        );

        assert_eq!(application.assumptions, vec![eq(result, view(cell))]);
        assert!(application.obligations.is_empty());
        assert!(application.mutating_ref_positions.is_empty());
        assert!(!application.mutates_receiver);
    }
}
