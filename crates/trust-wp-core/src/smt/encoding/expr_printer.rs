// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 expression printer.
//!
//! Converts `PureExpr` AST nodes to SMT-LIB2 text, writing directly into a
//! string buffer to avoid intermediate allocations.

use std::fmt::Write;

use super::{context::SmtContext, MAX_RECURSION_DEPTH};
use crate::formula::{BinOp, PureExpr, UnOp};

/// Convert a `PureExpr` to SMT-LIB2 format.
///
/// This applies RustHorn-style encoding for `old`, `deref`, `final`, and
/// view expressions, producing `*_current`, `*_final`, and `*_view` names.
#[must_use]
pub fn expr_to_smt(expr: &PureExpr) -> String {
    let mut s = String::new();
    write_expr_ctx(&mut s, expr, SmtContext::Normal);
    s
}

pub(super) fn write_bool(out: &mut String, value: bool) {
    out.push_str(if value { "true" } else { "false" });
}

pub(super) fn method_smt_name(method: &str) -> &str {
    match method {
        "len" => "seq_len",
        "index_logic" => "seq_index_logic",
        "push_back" => "seq_push_back",
        _ => method,
    }
}

/// Write a variable name as SMT, handling Rust integer constants.
pub(super) fn write_var(out: &mut String, name: &str) {
    out.push_str(match name {
        "i8::MIN" => "(- 128)",
        "i8::MAX" => "127",
        "i16::MIN" => "(- 32768)",
        "i16::MAX" => "32767",
        "i32::MIN" => "(- 2147483648)",
        "i32::MAX" => "2147483647",
        "i64::MIN" | "isize::MIN" => "(- 9223372036854775808)",
        "i64::MAX" | "isize::MAX" => "9223372036854775807",
        "i128::MIN" => "(- 170141183460469231731687303715884105728)",
        "i128::MAX" => "170141183460469231731687303715884105727",
        "u8::MIN" | "u16::MIN" | "u32::MIN" | "u64::MIN" | "u128::MIN" | "usize::MIN" => "0",
        "u8::MAX" => "255",
        "u16::MAX" => "65535",
        "u32::MAX" => "4294967295",
        "u64::MAX" | "usize::MAX" => "18446744073709551615",
        "u128::MAX" => "340282366920938463463374607431768211455",
        _ => {
            out.push_str(name);
            return;
        }
    });
}

fn write_int(out: &mut String, n: i64) {
    if n < 0 {
        if n == i64::MIN {
            out.push_str("(- 9223372036854775808)");
        } else {
            let _ = write!(out, "(- {})", -n);
        }
    } else {
        let _ = write!(out, "{n}");
    }
}

fn write_var_old_prefix(out: &mut String, name: &str) {
    if name.contains("::") {
        write_var(out, name);
    } else {
        let _ = write!(out, "old_{name}");
    }
}

pub(super) fn write_var_ctx(out: &mut String, name: &str, ctx: SmtContext) {
    match ctx {
        SmtContext::Normal => write_var(out, name),
        SmtContext::Old => write_var_old_prefix(out, name),
    }
}

/// Write an `old(expr)` expression to SMT.
///
/// For mutable borrow contracts: `old(*v)` is the same as `*v` (both are `v_current`)
/// because `*v` already represents the entry-state value in `RustHorn` encoding.
fn write_old(out: &mut String, inner: &PureExpr, ctx: SmtContext, depth: usize) {
    match ctx {
        SmtContext::Normal => match inner {
            PureExpr::Deref(_) => write_expr_depth(out, inner, SmtContext::Normal, depth),
            PureExpr::Var(name, _) => write_var_old_prefix(out, name),
            _ => write_expr_depth(out, inner, SmtContext::Old, depth),
        },
        SmtContext::Old => write_expr_depth(out, inner, ctx, depth),
    }
}

fn write_deref(out: &mut String, inner: &PureExpr, ctx: SmtContext, depth: usize) {
    if let PureExpr::Var(name, _) = inner {
        match ctx {
            SmtContext::Normal => {
                let _ = write!(out, "{name}_current");
            }
            SmtContext::Old => {
                let _ = write!(out, "old_{name}_current");
            }
        }
    } else {
        write_expr_depth(out, inner, ctx, depth);
        out.push_str("_current");
    }
}

fn write_final(out: &mut String, inner: &PureExpr, ctx: SmtContext, depth: usize) {
    if let PureExpr::Var(name, _) = inner {
        match ctx {
            SmtContext::Normal => {
                let _ = write!(out, "{name}_final");
            }
            SmtContext::Old => {
                let _ = write!(out, "old_{name}_final");
            }
        }
    } else {
        write_expr_depth(out, inner, ctx, depth);
        out.push_str("_final");
    }
}

fn write_view(out: &mut String, inner: &PureExpr, ctx: SmtContext, depth: usize) {
    match ctx {
        SmtContext::Normal => match inner {
            PureExpr::Var(name, _) => {
                let _ = write!(out, "{name}_view");
            }
            PureExpr::Deref(d) => {
                if let PureExpr::Var(name, _) = d.as_ref() {
                    let _ = write!(out, "{name}_current_view");
                } else {
                    write_expr_depth(out, inner, ctx, depth);
                    out.push_str("_view");
                }
            }
            PureExpr::Final(f) => {
                if let PureExpr::Var(name, _) = f.as_ref() {
                    let _ = write!(out, "{name}_final_view");
                } else {
                    write_expr_depth(out, inner, ctx, depth);
                    out.push_str("_view");
                }
            }
            _ => {
                write_expr_depth(out, inner, ctx, depth);
                out.push_str("_view");
            }
        },
        SmtContext::Old => {
            if let PureExpr::Var(name, _) = inner {
                let _ = write!(out, "old_{name}_view");
            } else {
                write_expr_depth(out, inner, ctx, depth);
                out.push_str("_view");
            }
        }
    }
}

/// Write a quantifier with optional triggers.
///
/// SMT-LIB2 triggers use the `!` annotation with `:pattern` attributes:
/// ```text
/// (forall ((x Int)) (! body :pattern ((f x)) :pattern ((g x))))
/// ```
fn write_quantifier(
    out: &mut String,
    quantifier: &str,
    var: &str,
    body: &PureExpr,
    triggers: &[Vec<PureExpr>],
    ctx: SmtContext,
    depth: usize,
) {
    let _ = write!(out, "({quantifier} (({var} Int)) ");
    if triggers.is_empty() {
        write_expr_depth(out, body, ctx, depth);
    } else {
        out.push_str("(! ");
        write_expr_depth(out, body, ctx, depth);
        for trigger in triggers {
            out.push_str(" :pattern (");
            for (i, e) in trigger.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                write_expr_depth(out, e, ctx, depth);
            }
            out.push(')');
        }
        out.push(')');
    }
    out.push(')');
}

/// Write a binary operator application in SMT-LIB2 format.
fn write_binop(
    out: &mut String,
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    ctx: SmtContext,
    depth: usize,
) {
    if let Some(uf_name) = op.smt_int_uf_name() {
        out.push('(');
        out.push_str(uf_name);
        out.push(' ');
        write_expr_depth(out, left, ctx, depth);
        out.push(' ');
        write_expr_depth(out, right, ctx, depth);
        out.push(')');
        return;
    }

    // Truncated (Rust signed) div/mod. SMT-LIB `div`/`mod` are EUCLIDEAN, so we
    // emit a toward-zero form derived from them, let-binding the operands so they
    // are not duplicated (and so nested truncated ops stay correct via let
    // scoping):
    //   RemTrunc a b = let m = (mod a b) in (a >= 0 ? m : (m = 0 ? 0 : m - |b|))
    //   DivTrunc a b = let q = (div a b), r = (mod a b) in
    //                  ((a >= 0 || r = 0) ? q : (b > 0 ? q+1 : q-1))
    if matches!(op, BinOp::DivTrunc | BinOp::RemTrunc) {
        out.push_str("(let ((_tw_a ");
        write_expr_depth(out, left, ctx, depth);
        out.push_str(") (_tw_b ");
        write_expr_depth(out, right, ctx, depth);
        out.push_str(")) ");
        if matches!(op, BinOp::RemTrunc) {
            out.push_str(
                "(let ((_tw_m (mod _tw_a _tw_b))) (ite (>= _tw_a 0) _tw_m (ite (= _tw_m 0) 0 (- _tw_m (abs _tw_b)))))",
            );
        } else {
            out.push_str(
                "(let ((_tw_q (div _tw_a _tw_b)) (_tw_r (mod _tw_a _tw_b))) (ite (or (>= _tw_a 0) (= _tw_r 0)) _tw_q (ite (> _tw_b 0) (+ _tw_q 1) (- _tw_q 1))))",
            );
        }
        out.push(')');
        return;
    }

    let op_str = match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "div",
        BinOp::Mod => "mod",
        BinOp::DivTrunc | BinOp::RemTrunc => {
            unreachable!("truncated div/mod handled by the toward-zero fast path above")
        }
        BinOp::Eq => "=",
        BinOp::Ne => {
            out.push_str("(not (= ");
            write_expr_depth(out, left, ctx, depth);
            out.push(' ');
            write_expr_depth(out, right, ctx, depth);
            out.push_str("))");
            return;
        }
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Implies => "=>",
        BinOp::Shl | BinOp::Shr | BinOp::BitAnd | BinOp::BitXor | BinOp::BitOr => {
            unreachable!("bitwise ops handled by smt_int_uf_name() fast path")
        }
    };
    out.push('(');
    out.push_str(op_str);
    out.push(' ');
    write_expr_depth(out, left, ctx, depth);
    out.push(' ');
    write_expr_depth(out, right, ctx, depth);
    out.push(')');
}

/// Core expression to SMT conversion — writes directly to a buffer (#506 F1).
///
/// Eliminates O(n × depth) intermediate String allocations from the recursive
/// `format!()` pattern. All child expressions write into the same buffer.
pub(super) fn write_expr_ctx(out: &mut String, expr: &PureExpr, ctx: SmtContext) {
    write_expr_depth(out, expr, ctx, 0);
}

#[allow(clippy::too_many_lines)]
fn write_expr_depth(out: &mut String, expr: &PureExpr, ctx: SmtContext, depth: usize) {
    if depth > MAX_RECURSION_DEPTH {
        out.push_str("DEEP_EXPR");
        return;
    }
    match expr {
        PureExpr::Bool(value) => write_bool(out, *value),
        PureExpr::Int(n) => write_int(out, *n),
        PureExpr::Float(f) => {
            use std::fmt::Write;
            let _ = write!(out, "{}", f.to_f64());
        }
        PureExpr::Var(name, _) => write_var_ctx(out, name, ctx),
        PureExpr::BinOp(left, op, right) => write_binop(out, left, *op, right, ctx, depth + 1),
        PureExpr::UnOp(op, operand) => {
            out.push_str(match op {
                UnOp::Not => "(not ",
                UnOp::Neg => "(- ",
                // BitNot: encode as (bvnot (int2bv operand)) in text mode.
                // In practice, the ay encoder handles BV conversion; the SMT
                // text printer uses a UF placeholder. (#2697)
                UnOp::BitNot => "(__trust_wp_bit_not ",
            });
            write_expr_depth(out, operand, ctx, depth + 1);
            out.push(')');
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            out.push_str("(ite ");
            write_expr_depth(out, cond, ctx, depth + 1);
            out.push(' ');
            write_expr_depth(out, then_expr, ctx, depth + 1);
            out.push(' ');
            write_expr_depth(out, else_expr, ctx, depth + 1);
            out.push(')');
        }
        PureExpr::Old(inner) => write_old(out, inner, ctx, depth + 1),
        PureExpr::Deref(inner) => write_deref(out, inner, ctx, depth + 1),
        PureExpr::Final(inner) => write_final(out, inner, ctx, depth + 1),
        PureExpr::View(inner) => write_view(out, inner, ctx, depth + 1),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            out.push('(');
            out.push_str(method_smt_name(method));
            out.push(' ');
            write_expr_depth(out, receiver, ctx, depth + 1);
            for a in args {
                out.push(' ');
                write_expr_depth(out, a, ctx, depth + 1);
            }
            out.push(')');
        }
        PureExpr::Forall {
            var,
            var_sort: _,
            body,
            triggers,
        } => write_quantifier(out, "forall", var, body, triggers, ctx, depth + 1),
        PureExpr::Exists {
            var,
            var_sort: _,
            body,
            triggers,
        } => write_quantifier(out, "exists", var, body, triggers, ctx, depth + 1),
        PureExpr::Match { scrutinee, arms } => {
            write_match_ite(out, scrutinee, arms, ctx, depth + 1);
        }
        PureExpr::LogicFnCall { name, args } => {
            out.push('(');
            out.push_str(&crate::logic::logic_fn_smt_name(name));
            for a in args {
                out.push(' ');
                write_expr_depth(out, a, ctx, depth + 1);
            }
            out.push(')');
        }
        PureExpr::Let { var, value, body } => {
            // SMT-LIB2: (let ((var value)) body)
            out.push_str("(let ((");
            out.push_str(var);
            out.push(' ');
            write_expr_depth(out, value, ctx, depth + 1);
            out.push_str(")) ");
            write_expr_depth(out, body, ctx, depth + 1);
            out.push(')');
        }
        PureExpr::LetAssume { assumption, body } => {
            // SMT-LIB2: (=> assumption body) — scoped implication (#815)
            out.push_str("(=> ");
            write_expr_depth(out, assumption, ctx, depth + 1);
            out.push(' ');
            write_expr_depth(out, body, ctx, depth + 1);
            out.push(')');
        }
        PureExpr::LetObligation { obligation, body } => {
            // SMT-LIB2: (and obligation body) — obligation conjunction (#815)
            out.push_str("(and ");
            write_expr_depth(out, obligation, ctx, depth + 1);
            out.push(' ');
            write_expr_depth(out, body, ctx, depth + 1);
            out.push(')');
        }
        PureExpr::Closure { body, .. } => {
            // Closures are not directly representable in SMT-LIB2; emit the
            // body as a best-effort approximation (the encoder will handle
            // proper lambda semantics or reject at a higher level).
            write_expr_depth(out, body, ctx, depth + 1);
        }
    }
}

/// Write a match expression as nested if-then-else with context tracking.
fn write_match_ite(
    out: &mut String,
    scrutinee: &PureExpr,
    arms: &[crate::formula::MatchArm],
    ctx: SmtContext,
    depth: usize,
) {
    if arms.is_empty() {
        out.push_str("false");
        return;
    }
    // Build from innermost (last arm = default) outward. Each wrapping arm
    // prepends "(ite cond body " and appends " inner)", so we accumulate
    // into a temporary buffer and swap.
    let mut inner = String::new();
    write_expr_depth(
        &mut inner,
        &arms.last().expect("non-empty by early return above").body,
        ctx,
        depth,
    );
    for arm in arms.iter().rev().skip(1) {
        let mut wrapped = String::new();
        wrapped.push_str("(ite ");
        write_pattern_condition(&mut wrapped, &arm.pattern, scrutinee, ctx, depth);
        wrapped.push(' ');
        write_expr_depth(&mut wrapped, &arm.body, ctx, depth);
        wrapped.push(' ');
        wrapped.push_str(&inner);
        wrapped.push(')');
        inner = wrapped;
    }
    out.push_str(&inner);
}

fn write_pattern_condition(
    out: &mut String,
    pattern: &crate::formula::Pattern,
    scrutinee: &PureExpr,
    ctx: SmtContext,
    depth: usize,
) {
    use crate::formula::Pattern;

    match pattern {
        Pattern::Wildcard | Pattern::Binding(_) => out.push_str("true"),
        Pattern::Alias { pattern, .. } => {
            write_pattern_condition(out, pattern, scrutinee, ctx, depth);
        }
        Pattern::Literal(lit) => {
            out.push_str("(= ");
            write_expr_depth(out, scrutinee, ctx, depth);
            out.push(' ');
            write_expr_depth(out, lit, ctx, depth);
            out.push(')');
        }
        Pattern::Constructor { name, .. } => match name.as_str() {
            "Some" => {
                out.push_str("(is_some ");
                write_expr_depth(out, scrutinee, ctx, depth);
                out.push(')');
            }
            "None" => {
                out.push_str("(not (is_some ");
                write_expr_depth(out, scrutinee, ctx, depth);
                out.push_str("))");
            }
            _ => {
                let _ = write!(out, "(is_{} ", name.to_lowercase());
                write_expr_depth(out, scrutinee, ctx, depth);
                out.push(')');
            }
        },
        Pattern::Tuple(_) => {
            // Tuple patterns always match structurally.
            out.push_str("true");
        }
    }
}
