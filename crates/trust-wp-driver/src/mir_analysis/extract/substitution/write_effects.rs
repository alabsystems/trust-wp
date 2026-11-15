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
                let mut origin = ref_place.local;
                // A reborrow of the `&mut` a ghost cell's `deref_mut` handed
                // back (`let r = &mut *g;` lowers to a reborrow of the call's
                // anonymous result): that temporary reaches `StorageDead` at
                // the end of its statement and its edge is erased with it, so
                // the reborrow must be chained to the cell the temporary
                // borrows, not to the temporary. Confined to a ghost-like
                // target, whose payload IS the cell's whole value.
                // Durable only for a destination the body assigns once and
                // never takes the address of, for the same reason as every
                // other edge that outlives its statement.
                if is_reborrow
                    && !local_has_source_binding(self.body, origin, self.arg_names)
                    && super::visitor::local_assigned_exactly_once(self.body, dest_local)
                    && !super::visitor::local_escapes_by_reference(self.body, dest_local)
                {
                    if let Some(&cell) = self.borrow_of.get(&origin) {
                        if crate::ghost::type_helpers::is_ghost_like_type(
                            self.tcx,
                            self.body.local_decls[cell].ty,
                        ) {
                            origin = cell;
                        }
                    }
                }
                tracing::debug!("borrow edge: {:?} -> {:?}", dest_local, origin);
                self.borrow_of.insert(dest_local, origin);
            }
        }
    }

    /// Apply a deref write to the owner place the MIR resolver names.
    ///
    /// The edge map reaches the owner only when every hop happened to be an
    /// `Rvalue::Ref` with an empty or `[Deref]` projection and no coercion
    /// temporary died on the way. The resolver reaches it whenever the body
    /// decides it, so this is the same sink for the shapes the map misses,
    /// plus the one thing the map has no room for: a field path.
    pub(super) fn apply_governed_deref_write(
        &mut self,
        base: Local,
        path: &[usize],
        expr: &PureExpr,
        body: &Body<'tcx>,
        location: Location,
    ) {
        if path.is_empty() {
            // A reference-valued owner is a pointer SLOT, and the deref sink
            // states `*name -> value` beside `name -> value`: for a slot the
            // first of those names a level this write never touched, and a
            // fact about the wrong sort can make an unrelated goal provable.
            // Redirecting a slot is the handback lane's business anyway.
            let ty = body.local_decls[base].ty;
            if ty.is_ref() || ty.is_raw_ptr() {
                // Not crediting is not the same as leaving the maps alone. A
                // store INTO a pointer slot REDIRECTS it, so every fact that
                // named what the slot used to point at is now about the wrong
                // place: the edge map would keep resolving a later `*slot`
                // to the old owner and read a value this write never put
                // there. Retire them here, for the same reason the ambiguous
                // lane retires them -- the resolver knowing the slot moved is
                // worth nothing if the lane that answers reads does not.
                self.retire_recorded_writes_to(base, body);
                let downstream: Vec<Local> = self
                    .borrow_of
                    .keys()
                    .copied()
                    .filter(|&borrower| self.borrow_chain_reaches(borrower, base))
                    .collect();
                for borrower in downstream {
                    self.borrow_of.remove(&borrower);
                    self.deref_exprs.remove(&borrower);
                }
                self.borrow_of.remove(&base);
                self.deref_exprs.remove(&base);
                self.local_exprs.remove(&base);
                return;
            }
            // The written value may name the owner's PRE-write value (`*r +=
            // 1` translates to `x + 1`). Resolve it against the binding in
            // force now, before it becomes that binding: the name lane
            // resolves a recorded deref value against the bindings too, and
            // an unresolved self-reference would be resolved a second time
            // into `(x + 1) + 1`.
            let mut resolved = expr.clone();
            if let Some(name) = source_name_for_local(body, base, self.arg_names) {
                if let Some(current) = self.local_exprs.get(&base) {
                    let mut self_ref = std::collections::HashMap::new();
                    self_ref.insert(name.clone(), current.clone());
                    resolved = resolved.substitute(&self_ref);
                }
                // A name update recorded before this write states the owner's
                // pre-write value under the same name.
                self.name_updates.remove(&name);
            }
            // The whole of the owner IS this value now. Recording it only in
            // the deref sink left the owner's own binding at its entry value,
            // so a later READ of the owner (`x = x + 1`) translated the value
            // the write replaced.
            self.local_exprs.insert(base, resolved.clone());
            self.deref_exprs.insert(base, resolved);
            return;
        }
        // A borrow of a PROJECTION: `*r = v` changes `base.<path>`, not the
        // whole of `base`. Rebind `base` to the functional update of its
        // current value so the sibling fields stay exact and the written one
        // stops reporting its entry value. An update this lane cannot
        // represent rebinds `base` to a FRESH symbol — never the stale value,
        // which would pin a pre-write fact beside the post-write ones and
        // manufacture the UNSAT premise set the vacuity guard rejects.
        let ty = body.local_decls[base].ty;
        let updated = self.local_exprs.get(&base).cloned().and_then(|current| {
            super::super::primary::local_functional_update(
                self.tcx,
                &self.local_exprs,
                current,
                ty,
                path,
                expr.clone(),
            )
        });
        let value = updated.unwrap_or_else(|| {
            PureExpr::Var(
                format!(
                    "$governed_havoc_{}_{}_{}",
                    base.as_u32(),
                    location.block.as_u32(),
                    location.statement_index
                ),
                super::super::super::translate::ty_to_expr_sort_enriched(self.tcx, ty),
            )
        });
        self.local_exprs.insert(base, value);
        // A name update recorded before this write states the owner's
        // pre-write value under the same name.
        if let Some(name) = source_name_for_local(body, base, self.arg_names) {
            self.name_updates.remove(&name);
        }
    }

    /// A write whose owner the body does not pin down to ONE place: every
    /// candidate loses its recorded value, and no candidate is told the value.
    ///
    /// Havoc loses a premise the prover could have used; it can never
    /// manufacture one. The written value is deliberately not applied to any
    /// candidate — that would be picking a branch — and the stale pre-write
    /// value is deliberately not kept, which would pin an entry-value fact
    /// beside the post-write ones.
    pub(super) fn invalidate_governed_candidates(
        &mut self,
        candidates: &[(Local, Vec<usize>)],
        body: &Body<'tcx>,
        location: Location,
    ) {
        for (base, _) in candidates {
            self.retire_recorded_writes_to(*base, body);
            let downstream: Vec<Local> = self
                .borrow_of
                .keys()
                .copied()
                .filter(|&borrower| self.borrow_chain_reaches(borrower, *base))
                .collect();
            for borrower in downstream {
                self.borrow_of.remove(&borrower);
                self.deref_exprs.remove(&borrower);
            }
            let ty = body.local_decls[*base].ty;
            self.local_exprs.insert(
                *base,
                PureExpr::Var(
                    format!(
                        "$governed_ambig_{}_{}_{}",
                        base.as_u32(),
                        location.block.as_u32(),
                        location.statement_index
                    ),
                    super::super::super::translate::ty_to_expr_sort_enriched(self.tcx, ty),
                ),
            );
        }
    }

    /// Retire every value another lane recorded as speaking for `local`,
    /// because `local` has just been written DIRECTLY.
    ///
    /// The write-back lanes record a value for the place a `&mut` governs —
    /// in the deref sink, under the owner's source name, or on a borrower
    /// whose edge still ends at the owner. The owner's own assignment is the
    /// later write, and borrowck guarantees no borrow of it is live across
    /// that assignment, so every one of those records is stale from here on.
    /// Dropping one costs a fact the prover could have used; keeping one
    /// lets it speak for a place the program has since overwritten, which is
    /// a false accept. Drop. This is the mirror of the `borrow_of` edge the
    /// same assignment already retires: the lane that RECORDS a value for a
    /// place and the lane that OVERWRITES that place must agree.
    pub(super) fn retire_recorded_writes_to(&mut self, local: Local, body: &Body<'tcx>) {
        self.deref_exprs.remove(&local);
        let stale: Vec<Local> = self
            .deref_exprs
            .keys()
            .copied()
            .filter(|&borrower| self.borrow_chain_reaches(borrower, local))
            .collect();
        for borrower in stale {
            self.deref_exprs.remove(&borrower);
        }
        if let Some(name) = source_name_for_local(body, local, self.arg_names) {
            self.name_updates.remove(&name);
        }
    }

    /// Whether `from` reaches `target` by following borrow edges. Bounded by
    /// the edge count so a cyclic map cannot spin.
    fn borrow_chain_reaches(&self, from: Local, target: Local) -> bool {
        let mut current = from;
        for _ in 0..=self.borrow_of.len() {
            match self.borrow_of.get(&current) {
                Some(&origin) if origin == target => return true,
                Some(&origin) => current = origin,
                None => return false,
            }
        }
        false
    }

    /// Handle a single-deref write: `(*_N) = expr` (#746 AC1).
    pub(super) fn handle_single_deref_write(
        &mut self,
        place: &Place<'tcx>,
        expr: &PureExpr,
        body: &Body<'tcx>,
    ) {
        tracing::debug!(
            "single deref write through {:?} = {:?}; chain {:?}; local_expr {:?}",
            place.local,
            expr,
            self.borrow_of.get(&place.local),
            self.local_exprs.get(&place.local)
        );
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
