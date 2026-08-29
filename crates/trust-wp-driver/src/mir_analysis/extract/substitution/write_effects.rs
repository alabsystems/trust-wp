// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use rustc_middle::mir::{Body, Local, Location, Place, ProjectionElem, Rvalue};
use rustc_span::Span;
use trust_wp_core::formula::PureExpr;

use super::{
    super::{
        super::translate::{translate_place, ExprLookup},
        closure::record_name_update_with_capture_alias,
        helpers::{local_has_source_binding, source_name_for_local},
    },
    visitor::SubstitutionVisitor,
};

struct ProjectedWriteLookup<'a> {
    locals: &'a std::collections::HashMap<Local, PureExpr>,
    deref_exprs: &'a std::collections::HashMap<Local, PureExpr>,
}

impl ExprLookup for ProjectedWriteLookup<'_> {
    fn get_expr(&self, local: &Local) -> Option<&PureExpr> {
        self.locals.get(local)
    }

    fn get_deref_expr(&self, local: &Local) -> Option<&PureExpr> {
        self.deref_exprs.get(local)
    }
}

impl<'a, 'tcx> SubstitutionVisitor<'a, 'tcx> {
    pub(super) fn effect_is_in_region(&self, span: Span) -> bool {
        let Some(region_span) = self.cutoff.region_span else {
            return true;
        };
        let region = region_span.source_callsite();
        let effect = span.source_callsite();
        if region.is_dummy() || effect.is_dummy() {
            return false;
        }
        region.lo() <= effect.lo() && effect.hi() <= region.hi()
    }

    /// Record a borrow chain entry for direct borrows and reborrows.
    pub(super) fn record_borrow_chain(&mut self, dest_local: Local, rvalue: &Rvalue<'tcx>) {
        if let Rvalue::Ref(_, _, ref_place) = rvalue {
            let is_direct = ref_place.projection.is_empty();
            let is_reborrow = ref_place.projection.len() == 1
                && matches!(ref_place.projection.first(), Some(ProjectionElem::Deref));
            if is_direct || is_reborrow {
                self.borrow_of.insert(dest_local, ref_place.local);
            }
        }
    }

    /// Handle a single-deref write: `(*_N) = expr` (#746 AC1).
    pub(super) fn handle_single_deref_write(
        &mut self,
        place: &Place<'tcx>,
        expr: &PureExpr,
        body: &Body<'tcx>,
    ) {
        self.deref_exprs.insert(place.local, expr.clone());
        // Writes through temp aliases (`_tmp = p.0; *_tmp = v`) should
        // update the resolved source name (e.g., `b`) when available.
        if let Some(PureExpr::Var(name, _)) = self.local_exprs.get(&place.local) {
            if !local_has_source_binding(body, place.local, self.arg_names) {
                // Distinguish reference-chain aliases from Box-deref temporaries.
                // Reference chains (`_tmp = &mut x`) have a borrow_of entry: the
                // single-deref write `*_tmp = v` changes the named variable `x`,
                // so the name_update uses the bare name.
                // Box-deref temporaries (`_inner = (*box)` where box: Box<T>) do
                // NOT have a borrow_of entry because Box deref is a value copy in
                // MIR, not a reborrow. The single-deref write `*_inner = v`
                // changes what the Box contents point to, which is one deref
                // deeper than the local's expression. Use `*name` to record the
                // correct deref level. (#2318)
                let effective_name = if self.borrow_of.contains_key(&place.local) {
                    name.clone()
                } else {
                    format!("*{name}")
                };
                record_name_update_with_capture_alias(
                    &mut self.name_updates,
                    &effective_name,
                    expr,
                    self.ctx.closure_capture_names.as_deref(),
                );
                // Ghost double-deref decomposition (#2691): when rustc decomposes
                // `**g2 = 1` (where `g2: Ghost<&mut T>`) into `deref_mut(g2)` +
                // `*result = 1`, the single-deref write through the carrier
                // produces `g2 -> Int(1)`. But the correct substitution for the
                // postcondition `(^*g2) == 1` is `*g2 -> Int(1)`. Record a
                // deref-prefixed name update through the capture alias so that
                // `derive_final_deref_ghost_substitutions` can derive `^*g2`.
                let deref_key = format!("*{name}");
                record_name_update_with_capture_alias(
                    &mut self.name_updates,
                    &deref_key,
                    expr,
                    self.ctx.closure_capture_names.as_deref(),
                );
            }
        }
        // Propagate transitively through borrow chains (#899):
        // if C borrows B borrows A, writing *C = expr should
        // set deref_exprs for B, A, and any further ancestors.
        let mut current = place.local;
        while let Some(&origin) = self.borrow_of.get(&current) {
            self.deref_exprs.insert(origin, expr.clone());
            current = origin;
        }
    }

    /// Handle a double-deref write: `**g2 = expr` through a named variable.
    ///
    /// When `place.projection == [Deref, Deref]` and the place's local resolves
    /// to a named variable (e.g., `g2` of type `Ghost<&mut i32>`), the write
    /// targets the inner pointee. Record this as a deref substitution so the
    /// ghost context produces `*g2 → expr`, which can then derive `^*g2 → expr`
    /// for postcondition matching. (#2671)
    pub(super) fn handle_double_deref_write(
        &mut self,
        place: &Place<'tcx>,
        expr: &PureExpr,
        body: &Body<'tcx>,
    ) {
        // Record as a deref write on the place's local.
        self.deref_exprs.insert(place.local, expr.clone());

        // The place's local may be a call-result temporary (e.g., from
        // Ghost::deref_mut) that aliases a source-named variable like `g2`.
        // Find all locals that share the same Var name and set deref_exprs
        // on them so build_name_substitutions emits `*g2 → expr`.
        if let Some(PureExpr::Var(target_name, _)) = self.local_exprs.get(&place.local) {
            let target_name = target_name.clone();
            let locals_for_name: Vec<Local> = self
                .local_exprs
                .iter()
                .filter_map(|(local, expr)| {
                    if let PureExpr::Var(name, _) = expr {
                        if name == &target_name {
                            return Some(*local);
                        }
                    }
                    None
                })
                .collect();
            for local in locals_for_name {
                self.deref_exprs.insert(local, expr.clone());
            }
        }

        // Propagate through borrow chains: if this local borrows another,
        // the deref write also applies to ancestors.
        let mut current = place.local;
        while let Some(&origin) = self.borrow_of.get(&current) {
            self.deref_exprs.insert(origin, expr.clone());
            current = origin;
        }

        // Closure capture deref propagation (#2691): in ghost closure MIR,
        // `**g2 = 1` where `g2` is a capture is decomposed by rustc into
        // `deref_mut` calls + a double-deref write on a temporary. The
        // temporary's borrow chain may lead to a carrier local whose name
        // can be resolved to the capture name via `closure_capture_names`.
        // Record a `*capture_name` deref-keyed name_update so the ghost
        // context produces `*g2 → expr` → `^*g2 → expr`.
        //
        // Also check the place local itself (not just borrow chain
        // ancestors), since it may directly hold a carrier or `self.N`
        // Var expression.
        let locals_to_check = {
            let mut v = vec![place.local];
            let mut cur = place.local;
            while let Some(&origin) = self.borrow_of.get(&cur) {
                v.push(origin);
                cur = origin;
            }
            v
        };
        for local in locals_to_check {
            if let Some(PureExpr::Var(name, _)) = self.local_exprs.get(&local) {
                if !local_has_source_binding(body, local, self.arg_names) {
                    let deref_key = format!("*{name}");
                    record_name_update_with_capture_alias(
                        &mut self.name_updates,
                        &deref_key,
                        expr,
                        self.ctx.closure_capture_names.as_deref(),
                    );
                }
            }
        }
    }

    /// Handle a projected deref write: `*p.0 = ...` mutates source
    /// variables through aliases returned from calls.
    pub(super) fn handle_projected_deref_write(&mut self, place: &Place<'tcx>, expr: &PureExpr) {
        let lookup = ProjectedWriteLookup {
            locals: &self.local_exprs,
            deref_exprs: &self.deref_exprs,
        };
        if let Some(PureExpr::Var(name, _)) = translate_place(place, &lookup) {
            record_name_update_with_capture_alias(
                &mut self.name_updates,
                &name,
                expr,
                self.ctx.closure_capture_names.as_deref(),
            );
        }
    }

    pub(super) fn handle_storage_dead(
        &mut self,
        local: Local,
        body: &Body<'tcx>,
        location: Location,
    ) {
        let span = body.basic_blocks[location.block].statements[location.statement_index]
            .source_info
            .span;
        if !self.effect_is_in_region(span) {
            return;
        }

        self.local_exprs.remove(&local);
        self.deref_exprs.remove(&local);
        self.borrow_of.remove(&local);
        self.borrow_of
            .retain(|borrower, origin| *borrower != local && *origin != local);

        if let Some(name) = source_name_for_local(body, local, self.arg_names) {
            self.name_updates.remove(&name);
        }
    }
}
