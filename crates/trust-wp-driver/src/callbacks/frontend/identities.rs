// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resolve the designated library vocabulary once. Item names are used only to
//! build this canonical inventory, never to interpret a call being lowered.

use std::collections::HashMap;

use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::{LiteralSide, Op, Refusal, UnaryOp};

#[derive(Clone, Copy)]
pub(super) enum Helper {
    Binary(Op),
    Literal(Op, LiteralSide),
    Unary(UnaryOp),
    IntLiteral,
    Erased,
}

pub(in crate::callbacks) struct CanonicalHelpers<'tcx> {
    tcx: TyCtxt<'tcx>,
    calls: HashMap<DefId, Helper>,
    int: DefId,
}

impl<'tcx> CanonicalHelpers<'tcx> {
    pub(in crate::callbacks) fn discover(tcx: TyCtxt<'tcx>) -> Result<Self, Refusal> {
        let mut crates = tcx
            .crates(())
            .iter()
            .copied()
            .filter(|&id| tcx.crate_name(id).as_str() == "trust_wp_std");
        let krate = crates
            .next()
            .ok_or(Refusal::MissingCanonicalItem("trust_wp_std"))?;
        if crates.next().is_some() {
            return Err(Refusal::AmbiguousCanonicalCrate);
        }
        let root = krate.as_def_id();
        let tc = child(tcx, root, "__spec_tc")?;
        let logic = child(tcx, root, "logic")?;
        let mut this = Self {
            tcx,
            calls: HashMap::new(),
            int: child(tcx, logic, "Int")?,
        };
        for (name, op) in [
            ("equal", Op::Eq),
            ("equal_pa", Op::Eq),
            ("neq", Op::Ne),
            ("neq_pa", Op::Ne),
            ("implication", Op::Implies),
        ] {
            this.calls
                .insert(function(tcx, tc, name)?, Helper::Binary(op));
        }
        for (right, left, op) in [
            ("eq_lit", "eq_lit_left", Op::Eq),
            ("ne_lit", "ne_lit_left", Op::Ne),
            ("lt_lit", "lt_lit_left", Op::Lt),
            ("le_lit", "le_lit_left", Op::Le),
            ("gt_lit", "gt_lit_left", Op::Gt),
            ("ge_lit", "ge_lit_left", Op::Ge),
            ("add_lit", "add_lit_left", Op::Add),
            ("sub_lit", "sub_lit_left", Op::Sub),
            ("mul_lit", "mul_lit_left", Op::Mul),
            ("div_lit", "div_lit_left", Op::Div),
            ("rem_lit", "rem_lit_left", Op::Rem),
        ] {
            this.calls.insert(
                function(tcx, tc, right)?,
                Helper::Literal(op, LiteralSide::Right),
            );
            this.calls.insert(
                function(tcx, tc, left)?,
                Helper::Literal(op, LiteralSide::Left),
            );
        }
        for (tr, name, op) in [
            ("AddTc", "add_tc", Op::Add),
            ("SubTc", "sub_tc", Op::Sub),
            ("MulTc", "mul_tc", Op::Mul),
            ("DivTc", "div_tc", Op::Div),
            ("RemTc", "rem_tc", Op::Rem),
        ] {
            this.calls.insert(
                associated(tcx, child(tcx, tc, tr)?, name)?,
                Helper::Binary(op),
            );
        }
        this.calls.insert(
            associated(tcx, child(tcx, tc, "NegTc")?, "neg_tc")?,
            Helper::Unary(UnaryOp::Neg),
        );
        let ord = child(tcx, logic, "OrdLogic")?;
        for (name, op) in [
            ("lt_log", Op::Lt),
            ("le_log", Op::Le),
            ("gt_log", Op::Gt),
            ("ge_log", Op::Ge),
        ] {
            this.calls
                .insert(associated(tcx, ord, name)?, Helper::Binary(op));
        }
        this.calls
            .insert(function(tcx, tc, "int_lit")?, Helper::IntLiteral);
        this.calls
            .insert(function(tcx, tc, "dead")?, Helper::Erased);
        Ok(this)
    }

    pub(super) fn get(&self, id: DefId) -> Option<Helper> {
        self.calls.get(&id).copied()
    }

    /// DefId indices are meaningful only within this compiler's GlobalCtxt.
    pub(super) fn belongs_to(&self, tcx: TyCtxt<'tcx>) -> bool {
        std::ptr::eq(*self.tcx, *tcx)
    }

    pub(super) fn integer(&self, ty: Ty<'_>) -> bool {
        matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
            || matches!(ty.kind(), TyKind::Adt(def, _) if def.did() == self.int)
    }

    pub(super) fn scalar(&self, ty: Ty<'_>) -> bool {
        self.integer(ty) || matches!(ty.kind(), TyKind::Bool | TyKind::Char)
    }
}

fn child(tcx: TyCtxt<'_>, module: DefId, name: &'static str) -> Result<DefId, Refusal> {
    item(tcx, module, name, Namespace::TypeNS)
}

fn function(tcx: TyCtxt<'_>, module: DefId, name: &'static str) -> Result<DefId, Refusal> {
    item(tcx, module, name, Namespace::ValueNS)
}

fn item(
    tcx: TyCtxt<'_>,
    module: DefId,
    name: &'static str,
    namespace: Namespace,
) -> Result<DefId, Refusal> {
    let mut matches = tcx
        .module_children(module)
        .iter()
        .filter(|item| item.ident.name.as_str() == name && item.res.ns() == Some(namespace))
        .filter_map(|item| item.res.opt_def_id());
    let id = matches.next().ok_or(Refusal::MissingCanonicalItem(name))?;
    // Reexports can occupy two namespaces with one identity.
    if matches.any(|other| other != id) {
        return Err(Refusal::MissingCanonicalItem(name));
    }
    Ok(id)
}

fn associated(tcx: TyCtxt<'_>, trait_id: DefId, name: &'static str) -> Result<DefId, Refusal> {
    tcx.associated_items(trait_id)
        .in_definition_order()
        .find(|item| tcx.item_name(item.def_id).as_str() == name)
        .map(|item| item.def_id)
        .ok_or(Refusal::MissingCanonicalItem(name))
}
