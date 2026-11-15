// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use rustc_ast::LitKind;
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_middle::{
    mir::{BinOp, BorrowKind, UnOp},
    thir::{self, ExprId, LogicalOp, Thir},
    ty::{Ty, TyCtxt, TyKind},
};

use super::{
    identities::Helper, Binding, CanonicalHelpers, ExprKind, LiteralSide, Op, Origin, Refusal,
    TypedClause, TypedExpr, UnaryOp,
};
use crate::callbacks::spec_typecheck::{clause_markers, clause_tag};

/// Refuse a partial owner contract before lowering any clause. The macro's
/// current parser can decline to emit a vehicle while retaining the owner's
/// marker; silently collecting only the closures would lose those obligations.
/// Tags are compared as an exact multiset, including duplicate clauses.
pub(in crate::callbacks) fn lower_owner_clauses<'tcx>(
    tcx: TyCtxt<'tcx>,
    helpers: &CanonicalHelpers<'tcx>,
    owner: LocalDefId,
) -> Result<Vec<TypedClause<'tcx>>, Refusal> {
    if !helpers.belongs_to(tcx) {
        return Err(Refusal::CompilerContextMismatch);
    }
    let mut missing = clause_markers(tcx, owner.to_def_id());
    let mut closures = Vec::new();
    for closure in tcx
        .hir_body_owners()
        .filter(|&id| tcx.def_kind(id) == DefKind::Closure && tcx.local_parent(id) == owner)
    {
        let Some(tag) = clause_tag(tcx, closure) else {
            continue;
        };
        let Some(position) = missing.iter().position(|marker| marker == &tag) else {
            return Err(Refusal::UnauthenticatedClause);
        };
        missing.remove(position);
        closures.push(closure);
    }
    if !missing.is_empty() {
        return Err(Refusal::MissingClauseVehicles(missing));
    }
    closures
        .into_iter()
        .map(|closure| lower_clause(tcx, helpers, owner, closure))
        .collect()
}

/// Read one authenticated macro clause. Neither the tag text nor source spans
/// participate in lowering. A caller cannot turn an arbitrary closure into a
/// specification by supplying its own tag.
pub(in crate::callbacks) fn lower_clause<'tcx>(
    tcx: TyCtxt<'tcx>,
    helpers: &CanonicalHelpers<'tcx>,
    owner: LocalDefId,
    closure: LocalDefId,
) -> Result<TypedClause<'tcx>, Refusal> {
    if !helpers.belongs_to(tcx) {
        return Err(Refusal::CompilerContextMismatch);
    }
    if tcx.def_kind(closure) != DefKind::Closure || tcx.local_parent(closure) != owner {
        return Err(Refusal::UnauthenticatedClause);
    }
    let tag = clause_tag(tcx, closure).ok_or(Refusal::UnauthenticatedClause)?;
    if !clause_markers(tcx, owner.to_def_id()).contains(&tag) {
        return Err(Refusal::UnauthenticatedClause);
    }
    let (cached, root) = tcx
        .thir_body(closure)
        .map_err(|_| Refusal::ThirUnavailable)?;
    if cached.is_stolen() {
        return Err(Refusal::ThirStolen);
    }
    let thir = cached.borrow();
    let body = Lowerer {
        thir: &thir,
        helpers,
        remaining: 4096,
    }
    .expr(root, 0)?;
    if body.ty != tcx.types.bool {
        return Err(Refusal::UnsupportedType);
    }
    Ok(TypedClause {
        owner,
        closure,
        tag,
        body,
    })
}

struct Lowerer<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    helpers: &'a CanonicalHelpers<'tcx>,
    remaining: usize,
}

/// Narrow compiler-test seam for the production callee guard. It returns no
/// typed IR and does not bypass the authenticated-clause constructor.
#[cfg(test)]
pub(in crate::callbacks) fn check_callee_surface_for_test<'tcx>(
    helpers: &CanonicalHelpers<'tcx>,
    thir: &Thir<'tcx>,
    fun: ExprId,
    function_ty: Ty<'tcx>,
) -> Result<(), Refusal> {
    Lowerer {
        thir,
        helpers,
        remaining: 4096,
    }
    .canonical_callee(fun, function_ty, 0)
}

impl<'tcx> Lowerer<'_, 'tcx> {
    fn expr(&mut self, id: ExprId, depth: usize) -> Result<TypedExpr<'tcx>, Refusal> {
        if depth >= 128 || self.remaining == 0 {
            return Err(Refusal::LimitExceeded);
        }
        self.remaining -= 1;
        let expr = &self.thir[id];
        // Calls dispatch before type checks so erased `dead()` has its precise
        // refusal even though its result may be an otherwise unsupported type.
        if let thir::ExprKind::Call { ty, fun, args, .. } = &expr.kind {
            let TyKind::FnDef(callee, _) = ty.kind() else {
                return Err(Refusal::UnsupportedExpression);
            };
            self.canonical_callee(*fun, *ty, depth + 1)?;
            return self.call(*callee, args, expr.ty, expr.span, depth);
        }
        let kind = match &expr.kind {
            thir::ExprKind::Scope { value, .. } | thir::ExprKind::ValueExpr { source: value } => {
                let mut lowered = self.expr(*value, depth + 1)?;
                if lowered.ty != expr.ty {
                    return Err(Refusal::UnsupportedType);
                }
                lowered.span = expr.span;
                return Ok(lowered);
            }
            thir::ExprKind::Block { block } => {
                let block = &self.thir[*block];
                if !block.stmts.is_empty() || block.targeted_by_break {
                    return Err(Refusal::UnsupportedExpression);
                }
                let mut lowered =
                    self.expr(block.expr.ok_or(Refusal::UnsupportedExpression)?, depth + 1)?;
                if lowered.ty != expr.ty {
                    return Err(Refusal::UnsupportedType);
                }
                lowered.span = expr.span;
                return Ok(lowered);
            }
            thir::ExprKind::Literal { lit, neg } => match lit.node {
                LitKind::Int(magnitude, _)
                    if matches!(expr.ty.kind(), TyKind::Int(_) | TyKind::Uint(_)) =>
                {
                    ExprKind::Integer {
                        magnitude: magnitude.get(),
                        negative: *neg,
                    }
                }
                LitKind::Bool(value) if !neg => ExprKind::Bool(value),
                LitKind::Char(value) if !neg => ExprKind::Char(value),
                _ => return Err(Refusal::UnsupportedExpression),
            },
            thir::ExprKind::VarRef { id } if self.value_type(expr.ty) => {
                ExprKind::Binding(Binding::Local(*id))
            }
            thir::ExprKind::UpvarRef {
                closure_def_id,
                var_hir_id,
            } if self.value_type(expr.ty) => ExprKind::Binding(Binding::Upvar {
                closure: *closure_def_id,
                variable: *var_hir_id,
            }),
            thir::ExprKind::Borrow {
                borrow_kind: BorrowKind::Shared,
                arg,
            } => {
                let arg = self.expr(*arg, depth + 1)?;
                let TyKind::Ref(_, inner, _) = expr.ty.kind() else {
                    return Err(Refusal::UnsupportedType);
                };
                if *inner != arg.ty {
                    return Err(Refusal::UnsupportedType);
                }
                ExprKind::Borrow(Box::new(arg))
            }
            thir::ExprKind::Deref { arg } => {
                let arg = self.expr(*arg, depth + 1)?;
                let TyKind::Ref(_, inner, _) = arg.ty.kind() else {
                    return Err(Refusal::UnsupportedType);
                };
                if *inner != expr.ty {
                    return Err(Refusal::UnsupportedType);
                }
                ExprKind::Deref(Box::new(arg))
            }
            thir::ExprKind::Unary { op, arg } => {
                let arg = self.expr(*arg, depth + 1)?;
                let op = match op {
                    UnOp::Not => UnaryOp::Not,
                    UnOp::Neg => UnaryOp::Neg,
                    _ => return Err(Refusal::UnsupportedExpression),
                };
                if arg.ty != expr.ty
                    || !self.helpers.scalar(arg.ty)
                    || matches!(arg.ty.kind(), TyKind::Char)
                {
                    return Err(Refusal::UnsupportedType);
                }
                ExprKind::Unary {
                    op,
                    origin: Origin::Native,
                    arg: Box::new(arg),
                }
            }
            thir::ExprKind::Binary { op, lhs, rhs } => {
                let op = native_op(*op).ok_or(Refusal::UnsupportedExpression)?;
                let lhs = self.expr(*lhs, depth + 1)?;
                let rhs = self.expr(*rhs, depth + 1)?;
                if !self.helpers.scalar(lhs.ty) || !self.helpers.scalar(rhs.ty) {
                    return Err(Refusal::UnsupportedType);
                }
                ExprKind::Binary {
                    op,
                    origin: Origin::Native,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            thir::ExprKind::LogicalOp { op, lhs, rhs } => {
                let lhs = self.expr(*lhs, depth + 1)?;
                let rhs = self.expr(*rhs, depth + 1)?;
                if !lhs.ty.is_bool() || !rhs.ty.is_bool() {
                    return Err(Refusal::UnsupportedType);
                }
                ExprKind::Binary {
                    op: match op {
                        LogicalOp::And => Op::And,
                        LogicalOp::Or => Op::Or,
                    },
                    origin: Origin::Native,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            _ => return Err(Refusal::UnsupportedExpression),
        };
        Ok(TypedExpr {
            ty: expr.ty,
            span: expr.span,
            kind,
        })
    }

    fn call(
        &mut self,
        callee: rustc_hir::def_id::DefId,
        args: &[ExprId],
        ty: Ty<'tcx>,
        span: rustc_span::Span,
        depth: usize,
    ) -> Result<TypedExpr<'tcx>, Refusal> {
        let helper = self
            .helpers
            .get(callee)
            .ok_or(Refusal::UnsupportedCall(callee))?;
        if matches!(helper, Helper::Erased) {
            return Err(Refusal::ErasedCall(callee));
        }
        let invalid = || Refusal::InvalidHelperArguments(callee);
        let kind = match helper {
            Helper::Binary(op) | Helper::Literal(op, _) => {
                let [lhs, rhs] = args else {
                    return Err(invalid());
                };
                let lhs = self.expr(*lhs, depth + 1)?;
                let rhs = self.expr(*rhs, depth + 1)?;
                if !self.helpers.scalar(lhs.ty) || !self.helpers.scalar(rhs.ty) {
                    return Err(invalid());
                }
                let origin = if let Helper::Literal(_, side) = helper {
                    let (literal, value) = match side {
                        LiteralSide::Left => (&lhs, &rhs),
                        LiteralSide::Right => (&rhs, &lhs),
                    };
                    if !self.helpers.integer(value.ty)
                        || !matches!(
                            literal.ty.kind(),
                            TyKind::Int(rustc_ast::IntTy::I128)
                                | TyKind::Uint(rustc_ast::UintTy::U128)
                        )
                        || !integer_carrier(literal)
                    {
                        return Err(invalid());
                    }
                    Origin::LiteralHelper {
                        helper: callee,
                        side,
                        value_ty: value.ty,
                    }
                } else {
                    Origin::Helper(callee)
                };
                ExprKind::Binary {
                    op,
                    origin,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            Helper::Unary(op) => {
                let [arg] = args else {
                    return Err(invalid());
                };
                let arg = self.expr(*arg, depth + 1)?;
                if !self.helpers.integer(arg.ty) || ty != arg.ty {
                    return Err(invalid());
                }
                ExprKind::Unary {
                    op,
                    origin: Origin::Helper(callee),
                    arg: Box::new(arg),
                }
            }
            Helper::IntLiteral => {
                let [arg] = args else {
                    return Err(invalid());
                };
                let carrier = self.expr(*arg, depth + 1)?;
                if !integer_carrier(&carrier)
                    || !matches!(carrier.ty.kind(), TyKind::Uint(rustc_ast::UintTy::U128))
                    || !self.helpers.integer(ty)
                {
                    return Err(invalid());
                }
                ExprKind::IntLiteral {
                    helper: callee,
                    carrier: Box::new(carrier),
                }
            }
            Helper::Erased => unreachable!("handled before arguments"),
        };
        Ok(TypedExpr { ty, span, kind })
    }

    fn value_type(&self, mut ty: Ty<'tcx>) -> bool {
        while let TyKind::Ref(_, inner, _) = ty.kind() {
            ty = *inner;
        }
        self.helpers.scalar(ty)
    }

    /// The FnDef return type alone does not prove that evaluating the callee
    /// is inert: `{ effect(); canonical_helper }(args)` has that same type.
    /// Accept only the actual function-item literal and transparent wrappers.
    fn canonical_callee(
        &mut self,
        id: ExprId,
        function_ty: Ty<'tcx>,
        depth: usize,
    ) -> Result<(), Refusal> {
        if depth >= 128 || self.remaining == 0 {
            return Err(Refusal::LimitExceeded);
        }
        self.remaining -= 1;
        let expr = &self.thir[id];
        if expr.ty != function_ty {
            return Err(Refusal::NontrivialCallee);
        }
        match &expr.kind {
            thir::ExprKind::ZstLiteral { .. } => Ok(()),
            thir::ExprKind::Scope { value, .. } | thir::ExprKind::ValueExpr { source: value } => {
                self.canonical_callee(*value, function_ty, depth + 1)
            }
            _ => Err(Refusal::NontrivialCallee),
        }
    }
}

fn integer_carrier(expr: &TypedExpr<'_>) -> bool {
    match &expr.kind {
        ExprKind::Integer { .. } => true,
        ExprKind::Unary {
            op: UnaryOp::Neg,
            origin: Origin::Native,
            arg,
        } => matches!(arg.kind, ExprKind::Integer { .. }),
        _ => false,
    }
}

fn native_op(op: BinOp) -> Option<Op> {
    Some(match op {
        BinOp::Eq => Op::Eq,
        BinOp::Ne => Op::Ne,
        BinOp::Lt => Op::Lt,
        BinOp::Le => Op::Le,
        BinOp::Gt => Op::Gt,
        BinOp::Ge => Op::Ge,
        BinOp::Add => Op::Add,
        BinOp::Sub => Op::Sub,
        BinOp::Mul => Op::Mul,
        BinOp::Div => Op::Div,
        BinOp::Rem => Op::Rem,
        BinOp::BitAnd => Op::BitAnd,
        BinOp::BitOr => Op::BitOr,
        BinOp::BitXor => Op::BitXor,
        BinOp::Shl => Op::Shl,
        BinOp::Shr => Op::Shr,
        _ => return None,
    })
}
