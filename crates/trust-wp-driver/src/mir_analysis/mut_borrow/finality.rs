// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use rustc_middle::{
    mir::{Body, Local, Place, Rvalue, StatementKind},
    ty::{TyCtxt, TyKind},
};
use trust_wp_core::formula::{BinOp, BorrowIdOrigin, BorrowIdStep, PureExpr};

use crate::mir_analysis::{
    resolver::ReborrowWriteback,
    translate::{translate_rvalue, ty_to_expr_sort_enriched},
};

pub(super) struct ReborrowMetadata {
    pub(super) finality: HashMap<String, trust_wp_core::formula::BorrowFinality>,
    pub(super) borrow_id_origins: HashMap<String, BorrowIdOrigin>,
}

/// Compute borrow finality and borrow-id provenance for all reborrows.
///
/// Runs the `NotFinalPlaces` backward dataflow analysis and queries each
/// reborrow location to determine if the parent borrow is final (never used
/// after the reborrow). In the same MIR walk, classify the child borrow id as
/// same-parent, projection-derived, or fresh. (#2141, #2181)
pub(super) fn compute_reborrow_metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
) -> ReborrowMetadata {
    use rustc_middle::mir::BorrowKind;
    use rustc_mir_dataflow::Analysis;
    use trust_wp_core::formula::BorrowFinality;

    let mut finality_map = HashMap::new();
    let mut borrow_id_origins = HashMap::new();

    // Collect &mut parameter locals and their names.
    let mut local_to_name: HashMap<Local, String> = HashMap::new();
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();

    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let ty = body.local_decls[local].ty;
        if matches!(
            ty.kind(),
            TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
        ) {
            local_to_name.insert(local, name.clone());
        }
        let sort = ty_to_expr_sort_enriched(tcx, ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
    }

    if local_to_name.is_empty() {
        return ReborrowMetadata {
            finality: finality_map,
            borrow_id_origins,
        };
    }

    // Run the backward dataflow analysis up front.
    let analysis = crate::mir_analysis::not_final_places::NotFinalPlaces::new(tcx, body);
    let results = analysis.iterate_to_fixpoint(tcx, body, None);
    let mut cursor = results.into_results_cursor(body);

    // Scan for reborrows (`dest = &mut *source`) and query finality at each site.
    for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
        for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
            let StatementKind::Assign((dest, rvalue)) = &stmt.kind else {
                continue;
            };

            if dest.projection.is_empty() {
                match translate_rvalue(rvalue, &local_exprs, Some(body)) {
                    Some(expr) => {
                        local_exprs.insert(dest.local, expr);
                    }
                    None => {
                        local_exprs.remove(&dest.local);
                    }
                }
            }

            if let Rvalue::Ref(_, BorrowKind::Mut { .. }, place) = rvalue {
                if dest.projection.is_empty()
                    && !place.projection.is_empty()
                    && place.projection.first() == Some(&rustc_middle::mir::ProjectionElem::Deref)
                    && local_to_name.contains_key(&place.local)
                {
                    let parent_name = local_to_name
                        .get(&place.local)
                        .cloned()
                        .unwrap_or_else(|| format!("$reborrow_{}", place.local.as_u32()));
                    let child_name = format!("{parent_name}$rb{}", dest.local.as_u32());

                    local_to_name.insert(dest.local, child_name.clone());

                    let location = rustc_middle::mir::Location {
                        block: bb_idx,
                        statement_index: stmt_idx,
                    };
                    let finality =
                        match crate::mir_analysis::not_final_places::NotFinalPlaces::is_final_at(
                            &mut cursor,
                            place,
                            location,
                        ) {
                            Some(deref_pos) => BorrowFinality::Final { deref_pos },
                            None => BorrowFinality::Fresh,
                        };
                    let borrow_id_origin =
                        classify_borrow_id_origin(place, &parent_name, &finality, &local_exprs);
                    finality_map.insert(child_name.clone(), finality);
                    borrow_id_origins.insert(child_name, borrow_id_origin);
                }
            }
        }
    }

    ReborrowMetadata {
        finality: finality_map,
        borrow_id_origins,
    }
}

fn classify_borrow_id_origin(
    place: &Place<'_>,
    parent_name: &str,
    finality: &trust_wp_core::formula::BorrowFinality,
    local_exprs: &HashMap<Local, PureExpr>,
) -> BorrowIdOrigin {
    use trust_wp_core::formula::BorrowFinality;

    if matches!(finality, BorrowFinality::Fresh) {
        return BorrowIdOrigin::Fresh {
            parent: parent_name.to_string(),
        };
    }

    let Some(steps) = translate_borrow_id_steps(place, local_exprs) else {
        return BorrowIdOrigin::Fresh {
            parent: parent_name.to_string(),
        };
    };

    if steps.is_empty() {
        BorrowIdOrigin::SameParent {
            parent: parent_name.to_string(),
        }
    } else {
        BorrowIdOrigin::Derived {
            parent: parent_name.to_string(),
            steps,
        }
    }
}

fn translate_borrow_id_steps(
    place: &Place<'_>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<Vec<BorrowIdStep>> {
    use rustc_middle::mir::ProjectionElem;

    let mut steps = Vec::new();
    for projection in place.projection.iter().skip(1) {
        match projection {
            ProjectionElem::Field(field, _) => steps.push(BorrowIdStep::Field(field.as_u32())),
            ProjectionElem::Index(local) => {
                steps.push(BorrowIdStep::Index(local_exprs.get(&local)?.clone()));
            }
            ProjectionElem::ConstantIndex { offset, .. } => {
                steps.push(BorrowIdStep::Index(PureExpr::Int(
                    i64::try_from(offset).ok()?,
                )));
            }
            _ => return None,
        }
    }
    Some(steps)
}

pub(super) fn build_delayed_writeback_assumptions(
    writebacks: &[ReborrowWriteback],
    finality: &HashMap<String, trust_wp_core::formula::BorrowFinality>,
) -> Vec<PureExpr> {
    let mut assumptions = Vec::new();
    for writeback in writebacks
        .iter()
        .filter(|writeback| writeback.activation.is_some())
    {
        assumptions.push(PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                writeback.parent_name.clone(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                writeback.child_name.clone(),
                None,
            )))),
        ));

        if finality.get(&writeback.child_name).is_some_and(|value| {
            matches!(value, trust_wp_core::formula::BorrowFinality::Final { .. })
        }) {
            assumptions.push(PureExpr::BinOp(
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    writeback.parent_name.clone(),
                    None,
                )))),
                BinOp::Eq,
                Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    writeback.child_name.clone(),
                    None,
                )))),
            ));
        }
    }
    assumptions
}
