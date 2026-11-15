// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A clause's raw-pointer casts, read at the operand's type.
//!
//! The contract parser has no types, so `e as *const X` reaches the driver as
//! a pending marker around `e`. Here the marker becomes the identity or
//! `thin(e)` by the same [`ptr_cast_kind`] the MIR translation of the body's
//! casts asks, in the same owner's typing environment. A marker whose operand
//! type or target type is not read here stays, and the encoder refuses it.
//!
//! The operand's type is read only where it is certain: a name no binder of
//! the clause shadows that the owner's body binds at one type (its
//! parameters included), `result` in an owner whose body binds no local of
//! that name, `old(..)` of such a name, or another cast (whose type is the
//! one it writes). The target is read from the written text: a generic
//! parameter of the owner, a sized primitive, `()` or a slice of those.
//! The text is not resolved, so an item in a block (`type str = u8;`) can
//! make it name another type. `str` is therefore not read: shadowed by a
//! sized type it would read a cast that drops the length as the identity
//! (raw_ptr_clause_cast_to_str_shadowed_by_block_alias.rs). A shadowed sized
//! primitive can only turn the identity into `thin`, which proves less. A
//! generic parameter is read only while no item written in the owner's body
//! can name it (D-148): shadowed by a sized type it would read a cast that
//! drops the metadata as the identity
//! (raw_ptr_proof_assert_cast_to_generic_shadowed_by_block_alias.rs).

use std::{collections::HashMap, sync::Arc};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt};
use trust_wp_core::formula::{
    internal::builtins::PTR_CAST_PENDING_PREFIX, MatchArm, Pattern, PureExpr,
};

use crate::mir_analysis::translate::ptr_cast::{apply_ptr_cast, ptr_cast_kind, raw_pointee};

/// `expr` with every pending raw-pointer cast whose kind is read in `owner`
/// replaced by what it denotes.
pub(crate) fn classify_pointer_casts(tcx: TyCtxt<'_>, owner: DefId, expr: &PureExpr) -> PureExpr {
    if !mentions_pending_cast(expr) || !owner.is_local() {
        return expr.clone();
    }
    let mut pass = Pass {
        tcx,
        owner,
        bound: Vec::new(),
        locals: None,
        opaque_scopes: 0,
    };
    pass.rewrite(expr).0
}

fn mentions_pending_cast(expr: &PureExpr) -> bool {
    use trust_wp_core::formula::PureExprDepthLimitedTraversalExt;
    expr.any_recursive_with_depth_limit(512, true, |node| {
        matches!(node, PureExpr::LogicFnCall { name, .. } if name.starts_with(PTR_CAST_PENDING_PREFIX))
    })
}

struct Pass<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    /// Names the clause itself binds, innermost last.
    bound: Vec<String>,
    /// Every name the owner's body binds, at its one type (`None` when bound
    /// at two types).
    locals: Option<HashMap<String, Option<Ty<'tcx>>>>,
    /// Depth of match arms whose pattern binds names this pass cannot list:
    /// inside one, no name is typed.
    opaque_scopes: usize,
}

impl<'tcx> Pass<'tcx> {
    fn with_bound<T>(&mut self, names: &[String], f: impl FnOnce(&mut Self) -> T) -> T {
        let mark = self.bound.len();
        self.bound.extend(names.iter().cloned());
        let out = f(self);
        self.bound.truncate(mark);
        out
    }

    fn local_type(&mut self, name: &str) -> Option<Ty<'tcx>> {
        let (tcx, owner) = (self.tcx, self.owner);
        self.locals
            .get_or_insert_with(|| crate::logic::identity::body_binding_types(tcx, owner))
            .get(name)
            .copied()
            .flatten()
    }

    /// The Rust type of `expr` where it is certain, else `None`.
    fn type_of(&mut self, expr: &PureExpr) -> Option<Ty<'tcx>> {
        if self.opaque_scopes > 0 {
            return None;
        }
        match expr {
            PureExpr::Old(inner) => self.type_of(inner),
            PureExpr::Var(name, _) if self.bound.iter().any(|bound| bound == name) => None,
            PureExpr::Var(name, _) if name == "result" => {
                if self.local_type_bound("result") {
                    return None;
                }
                crate::logic::identity_typed::owner_signature(self.tcx, self.owner)
                    .map(|(_, output)| output)
            }
            PureExpr::Var(name, _) => self.local_type(name),
            _ => None,
        }
    }

    fn local_type_bound(&mut self, name: &str) -> bool {
        let (tcx, owner) = (self.tcx, self.owner);
        self.locals
            .get_or_insert_with(|| crate::logic::identity::body_binding_types(tcx, owner))
            .contains_key(name)
    }

    /// The rewritten expression and, for a cast, the type it writes.
    fn rewrite(&mut self, expr: &PureExpr) -> (PureExpr, Option<Ty<'tcx>>) {
        let out = match expr {
            PureExpr::LogicFnCall { name, args } => {
                if let (Some(pointee), [operand]) =
                    (name.strip_prefix(PTR_CAST_PENDING_PREFIX), args.as_slice())
                {
                    let (operand_expr, cast_ty) = self.rewrite(operand);
                    let operand_ty = cast_ty.or_else(|| self.type_of(operand));
                    let target = written_pointee(self.tcx, self.owner, pointee);
                    let kind = operand_ty
                        .and_then(raw_pointee)
                        .zip(target)
                        .and_then(|(from, to)| ptr_cast_kind(self.tcx, self.owner, from, to));
                    let target_ptr = target.map(|to| Ty::new_imm_ptr(self.tcx, to));
                    return match kind {
                        Some(kind) => (apply_ptr_cast(kind, operand_expr), target_ptr),
                        None => (
                            PureExpr::LogicFnCall {
                                name: name.clone(),
                                args: vec![operand_expr],
                            },
                            target_ptr,
                        ),
                    };
                }
                PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: args.iter().map(|arg| self.rewrite(arg).0).collect(),
                }
            }
            PureExpr::BinOp(l, op, r) => PureExpr::BinOp(
                Arc::new(self.rewrite(l).0),
                *op,
                Arc::new(self.rewrite(r).0),
            ),
            PureExpr::UnOp(op, inner) => PureExpr::UnOp(*op, Arc::new(self.rewrite(inner).0)),
            PureExpr::Ite(c, t, e) => PureExpr::Ite(
                Arc::new(self.rewrite(c).0),
                Arc::new(self.rewrite(t).0),
                Arc::new(self.rewrite(e).0),
            ),
            PureExpr::Old(inner) => PureExpr::Old(Arc::new(self.rewrite(inner).0)),
            PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(self.rewrite(inner).0)),
            PureExpr::Final(inner) => PureExpr::Final(Arc::new(self.rewrite(inner).0)),
            PureExpr::View(inner) => PureExpr::View(Arc::new(self.rewrite(inner).0)),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => PureExpr::MethodCall {
                receiver: Arc::new(self.rewrite(receiver).0),
                method: method.clone(),
                args: args.iter().map(|arg| self.rewrite(arg).0).collect(),
            },
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => self.with_bound(std::slice::from_ref(var), |this| PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(this.rewrite(body).0),
                triggers: triggers
                    .iter()
                    .map(|trigger| trigger.iter().map(|t| this.rewrite(t).0).collect())
                    .collect(),
            }),
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => self.with_bound(std::slice::from_ref(var), |this| PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(this.rewrite(body).0),
                triggers: triggers
                    .iter()
                    .map(|trigger| trigger.iter().map(|t| this.rewrite(t).0).collect())
                    .collect(),
            }),
            PureExpr::Match { scrutinee, arms } => PureExpr::Match {
                scrutinee: Arc::new(self.rewrite(scrutinee).0),
                arms: arms
                    .iter()
                    .map(|arm| {
                        let mut names = Vec::new();
                        let known = pattern_names(&arm.pattern, &mut names);
                        let rewrite_arm = |this: &mut Self| MatchArm {
                            pattern: arm.pattern.clone(),
                            body: this.rewrite(&arm.body).0,
                        };
                        if known {
                            self.with_bound(&names, rewrite_arm)
                        } else {
                            self.opaque_scopes += 1;
                            let arm = rewrite_arm(self);
                            self.opaque_scopes -= 1;
                            arm
                        }
                    })
                    .collect(),
            },
            PureExpr::Let { var, value, body } => {
                let value = Arc::new(self.rewrite(value).0);
                self.with_bound(std::slice::from_ref(var), |this| PureExpr::Let {
                    var: var.clone(),
                    value,
                    body: Arc::new(this.rewrite(body).0),
                })
            }
            PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
                assumption: Arc::new(self.rewrite(assumption).0),
                body: Arc::new(self.rewrite(body).0),
            },
            PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
                obligation: Arc::new(self.rewrite(obligation).0),
                body: Arc::new(self.rewrite(body).0),
            },
            PureExpr::Closure { params, body } => {
                let names: Vec<String> = params.iter().map(|(name, _)| name.clone()).collect();
                self.with_bound(&names, |this| PureExpr::Closure {
                    params: params.clone(),
                    body: Arc::new(this.rewrite(body).0),
                })
            }
            // Leaves, and any node kind this pass does not descend into: a
            // pending cast left inside one is refused by the encoder.
            _ => expr.clone(),
        };
        (out, None)
    }
}

/// The names `pattern` binds, pushed onto `out`; `false` when it has a form
/// this pass does not list.
fn pattern_names(pattern: &Pattern, out: &mut Vec<String>) -> bool {
    match pattern {
        Pattern::Wildcard | Pattern::Literal(_) => true,
        Pattern::Binding(name) => {
            out.push(name.clone());
            true
        }
        Pattern::Alias { alias, pattern } => {
            out.push(alias.clone());
            pattern_names(pattern, out)
        }
        Pattern::Constructor { inner, .. } => inner
            .as_deref()
            .is_none_or(|inner| pattern_names(inner, out)),
        Pattern::Tuple(items) => items.iter().all(|item| pattern_names(item, out)),
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

/// The type a written pointee names in `owner`, where it is one of the
/// spellings read here.
fn written_pointee<'tcx>(tcx: TyCtxt<'tcx>, owner: DefId, text: &str) -> Option<Ty<'tcx>> {
    let text = text.trim();
    if let Some(inner) = text
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
    {
        if inner.contains(';') {
            return None;
        }
        return written_pointee(tcx, owner, inner).map(|elem| Ty::new_slice(tcx, elem));
    }
    let types = &tcx.types;
    let primitive = match text {
        "()" => Some(types.unit),
        "bool" => Some(types.bool),
        "char" => Some(types.char),
        "u8" => Some(types.u8),
        "u16" => Some(types.u16),
        "u32" => Some(types.u32),
        "u64" => Some(types.u64),
        "u128" => Some(types.u128),
        "usize" => Some(types.usize),
        "i8" => Some(types.i8),
        "i16" => Some(types.i16),
        "i32" => Some(types.i32),
        "i64" => Some(types.i64),
        "i128" => Some(types.i128),
        "isize" => Some(types.isize),
        "f32" => Some(types.f32),
        "f64" => Some(types.f64),
        _ => None,
    };
    if let Some(param) = generic_type_param(tcx, owner, text) {
        return (!body_item_may_name(tcx, owner, text)).then_some(param);
    }
    // A type item in the owner's module shadows the primitive of its name.
    primitive.filter(|_| !module_declares_type(tcx, owner, text))
}

fn module_declares_type(tcx: TyCtxt<'_>, owner: DefId, name: &str) -> bool {
    let Some(local) = owner.as_local() else {
        return true;
    };
    let module = tcx.parent_module_from_def_id(local).to_local_def_id();
    tcx.module_children_local(module).iter().any(|child| {
        child.ident.name.as_str() == name
            && matches!(
                child.res,
                rustc_hir::def::Res::Def(
                    rustc_hir::def::DefKind::Struct
                        | rustc_hir::def::DefKind::Enum
                        | rustc_hir::def::DefKind::Union
                        | rustc_hir::def::DefKind::TyAlias
                        | rustc_hir::def::DefKind::ForeignTy
                        | rustc_hir::def::DefKind::Trait,
                    _
                )
            )
    })
}

/// Whether an item written inside the body `owner` belongs to, at any depth,
/// can name `name` there: an item called `name`, a `use` that imports under
/// `name`, or a glob `use`, which may import anything. A block item shadows a
/// generic parameter of its name in the text of its block, so the parameter
/// is not what the written target means. Items outside the body cannot shadow
/// the owner's own parameters, and an enclosing impl's parameters are nearer
/// than any block around the impl.
fn body_item_may_name(tcx: TyCtxt<'_>, owner: DefId, name: &str) -> bool {
    use rustc_hir::{def::DefKind, ItemKind, UseKind};
    let root = tcx.typeck_root_def_id(owner);
    let written_inside = |item: DefId| {
        let mut current = item;
        while let Some(parent) = tcx.opt_parent(current) {
            if parent == root {
                return true;
            }
            if matches!(tcx.def_kind(parent), DefKind::Mod) {
                return false;
            }
            current = parent;
        }
        false
    };
    tcx.hir_crate_items(()).free_items().any(|item_id| {
        let item = tcx.hir_item(item_id);
        let names_it = match item.kind {
            ItemKind::Use(_) => {
                crate::hir_use::item_use_leaves(item)
                    .into_iter()
                    .any(|(_, kind)| match kind {
                        UseKind::Single(ident) => ident.name.as_str() == name,
                        UseKind::Glob => true,
                        UseKind::Nested { .. } => false,
                    })
            }
            _ => tcx
                .opt_item_name(item.owner_id.to_def_id())
                .is_some_and(|item_name| item_name.as_str() == name),
        };
        names_it && written_inside(item.owner_id.to_def_id())
    })
}

/// The generic type parameter of `owner` (or of an item enclosing it) that
/// `name` spells.
fn generic_type_param<'tcx>(tcx: TyCtxt<'tcx>, owner: DefId, name: &str) -> Option<Ty<'tcx>> {
    let mut generics = Some(tcx.generics_of(owner));
    while let Some(current) = generics {
        if let Some(param) = current
            .own_params
            .iter()
            .find(|param| param.name.as_str() == name)
        {
            return match param.kind {
                ty::GenericParamDefKind::Type { .. } => {
                    Some(Ty::new_param(tcx, param.index, param.name))
                }
                _ => None,
            };
        }
        generics = current.parent.map(|parent| tcx.generics_of(parent));
    }
    None
}
