// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Display implementations for all formula types.

use std::borrow::Cow;

use super::{
    pure_expr::{ExprSort, MatchArm, Pattern, PureExpr},
    types::{BinOp, Location, Permission, UnOp, Value},
    Formula,
};

/// Format an optional `ExprSort` for display in quantifier/closure signatures.
///
/// Non-parametric variants (Bool, Int, Seq, Unit, `FMap`) use zero-allocation
/// `Cow::Borrowed`. Parametric variants (Datatype, Tuple, Ref, MutRef) allocate via
/// `Cow::Owned`. Returns `"_"` for `None`.
fn expr_sort_display(sort: Option<&ExprSort>) -> Cow<'static, str> {
    match sort {
        Some(ExprSort::Bool) => Cow::Borrowed("Bool"),
        Some(ExprSort::Int) => Cow::Borrowed("Int"),
        Some(ExprSort::Seq) => Cow::Borrowed("Seq"),
        Some(ExprSort::Unit) => Cow::Borrowed("()"),
        Some(ExprSort::FMap) => Cow::Borrowed("FMap"),
        Some(ExprSort::Datatype(id)) => Cow::Owned(format!(
            "Datatype({})",
            super::sort_intern::resolve_sort_name(*id)
        )),
        Some(ExprSort::Tuple(n)) => Cow::Owned(format!("Tuple({n})")),
        Some(ExprSort::Ref(inner)) => Cow::Owned(format!("&{inner}")),
        Some(ExprSort::MutRef(inner)) => Cow::Owned(format!("&mut {inner}")),
        Some(ExprSort::TypeParam(id)) => Cow::Owned(format!(
            "TypeParam({})",
            super::sort_intern::resolve_sort_name(*id)
        )),
        Some(ExprSort::Float) => Cow::Borrowed("Float"),
        None => Cow::Borrowed("_"),
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Mod => write!(f, "%"),
            BinOp::DivTrunc => write!(f, "/"),
            BinOp::RemTrunc => write!(f, "%"),
            BinOp::Shl => write!(f, "<<"),
            BinOp::Shr => write!(f, ">>"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitXor => write!(f, "^"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Ge => write!(f, ">="),
            BinOp::And => write!(f, "&&"),
            BinOp::Or => write!(f, "||"),
            BinOp::Implies => write!(f, "==>"),
        }
    }
}

impl std::fmt::Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "!"),
            UnOp::Neg => write!(f, "-"),
            UnOp::BitNot => write!(f, "~"),
        }
    }
}

impl std::fmt::Display for Pattern {
    // Binding and nullary Constructor have identical output format but different semantics
    #[allow(clippy::match_same_arms)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Wildcard => write!(f, "_"),
            Pattern::Binding(name) => write!(f, "{name}"),
            Pattern::Literal(expr) => write!(f, "{expr}"),
            Pattern::Constructor { name, inner: None } => write!(f, "{name}"),
            Pattern::Constructor {
                name,
                inner: Some(inner),
            } => write!(f, "{name}({inner})"),
            Pattern::Alias { alias, pattern } => write!(f, "{alias} @ {pattern}"),
            Pattern::Tuple(elements) => {
                write!(f, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{elem}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl std::fmt::Display for MatchArm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} => {}", self.pattern, self.body)
    }
}

impl std::fmt::Display for PureExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PureExpr::Bool(b) => write!(f, "{b}"),
            PureExpr::Int(n) => write!(f, "{n}"),
            PureExpr::Float(v) => write!(f, "{v}"),
            PureExpr::Var(name, _) => write!(f, "{name}"),
            PureExpr::BinOp(l, op, r) => write!(f, "({l} {op} {r})"),
            PureExpr::UnOp(op, inner) => write!(f, "{op}{inner}"),
            PureExpr::Ite(c, t, e) => write!(f, "if {c} {{ {t} }} else {{ {e} }}"),
            PureExpr::Old(inner) => write!(f, "old({inner})"),
            PureExpr::Deref(inner) => write!(f, "*{inner}"),
            PureExpr::Final(inner) => write!(f, "^{inner}"),
            PureExpr::View(inner) => write!(f, "{inner}@"),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                write!(f, "{receiver}.{method}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let sort_str = expr_sort_display(var_sort.as_ref());
                write!(f, "forall<{var}: {sort_str}> {body}")?;
                if !triggers.is_empty() {
                    write!(f, " [triggers: {triggers:?}]")?;
                }
                Ok(())
            }
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let sort_str = expr_sort_display(var_sort.as_ref());
                write!(f, "exists<{var}: {sort_str}> {body}")?;
                if !triggers.is_empty() {
                    write!(f, " [triggers: {triggers:?}]")?;
                }
                Ok(())
            }
            PureExpr::Match { scrutinee, arms } => {
                write!(f, "match {scrutinee} {{ ")?;
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} => {}", arm.pattern, arm.body)?;
                }
                write!(f, " }}")
            }
            PureExpr::LogicFnCall { name, args } => {
                // Extract short name from qualified path
                let short_name = name.rsplit("::").next().unwrap_or(name);
                write!(f, "{short_name}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            PureExpr::Let { var, value, body } => {
                write!(f, "let {var} = {value}; {body}")
            }
            PureExpr::LetAssume { assumption, body } => {
                write!(f, "assume {assumption}; {body}")
            }
            PureExpr::LetObligation { obligation, body } => {
                write!(f, "obligation {obligation}; {body}")
            }
            PureExpr::Closure { params, body } => {
                write!(f, "|")?;
                for (i, (name, sort)) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    if sort.is_some() {
                        write!(f, "{name}: {}", expr_sort_display(sort.as_ref()))?;
                    } else {
                        write!(f, "{name}")?;
                    }
                }
                write!(f, "| {body}")
            }
        }
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Expr(e) => write!(f, "{e}"),
            Value::Unknown => write!(f, "_"),
        }
    }
}

impl std::fmt::Display for Permission {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let denom = self.denominator.get();
        if self.numerator == 1 && denom == 1 {
            write!(f, "full")
        } else if self.numerator == 1 && denom == 2 {
            write!(f, "half")
        } else {
            write!(f, "{}/{}", self.numerator, denom)
        }
    }
}

impl std::fmt::Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::True => write!(f, "true"),
            Formula::False => write!(f, "false"),
            Formula::Pure(e) => write!(f, "{e}"),
            Formula::PointsTo {
                location,
                value,
                permission,
            } => write!(f, "{location} ↦[{permission}] {value}"),
            Formula::MutBorrow {
                var,
                current,
                final_val,
                id,
            } => write!(f, "borrow({var}: *={current}, ^={final_val}, id={id})"),
            Formula::SepConj(p, q) => write!(f, "({p} * {q})"),
            Formula::And(p, q) => write!(f, "({p} ∧ {q})"),
            Formula::Or(p, q) => write!(f, "({p} ∨ {q})"),
            Formula::Implies(p, q) => write!(f, "({p} → {q})"),
            Formula::MagicWand(p, q) => write!(f, "({p} -* {q})"),
            Formula::Exists { var, body, .. } => write!(f, "∃{var}. {body}"),
            Formula::Forall { var, body, .. } => write!(f, "∀{var}. {body}"),
        }
    }
}
