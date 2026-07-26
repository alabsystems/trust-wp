// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT preamble generation.
//!
//! Generates SMT-LIB2 preamble declarations for heap modeling, sequence types,
//! and bitwise operations.

use std::fmt::Write;

use super::MAX_RECURSION_DEPTH;
use crate::formula::{BinOp, PureExpr};
#[cfg(test)]
use crate::formula::{Formula, Value};

/// Generate SMT-LIB2 preamble for heap modeling (separation logic).
///
/// Creates array declarations for:
/// - `heap_contents`: Maps addresses to values (Int -> Int)
/// - `heap_domain`: Tracks allocated addresses (Int -> Bool)
/// - `heap_perms`: Permission values at each address (Int -> Int, scaled `0..PERM_SCALE`)
///
/// This preamble is required when encoding `PointsTo` or `SepConj` formulas.
#[cfg(test)]
pub(crate) fn generate_heap_preamble() -> String {
    r"; Heap model for separation logic
(declare-const heap_contents (Array Int Int))
(declare-const heap_domain (Array Int Bool))
(declare-const heap_perms (Array Int Int))
"
    .to_string()
}

/// Check if a formula requires the heap preamble (contains `PointsTo` or `SepConj`).
#[cfg(test)]
pub(crate) fn needs_heap_preamble(formula: &Formula) -> bool {
    needs_heap_preamble_inner(formula, 0)
}

#[cfg(test)]
fn needs_heap_preamble_inner(formula: &Formula, depth: usize) -> bool {
    if depth > MAX_RECURSION_DEPTH {
        return false;
    }
    match formula {
        Formula::PointsTo { .. } => true,
        Formula::SepConj(l, r)
        | Formula::And(l, r)
        | Formula::Or(l, r)
        | Formula::Implies(l, r)
        | Formula::MagicWand(l, r) => {
            needs_heap_preamble_inner(l, depth + 1) || needs_heap_preamble_inner(r, depth + 1)
        }
        Formula::Forall { body, triggers, .. } | Formula::Exists { body, triggers, .. } => {
            needs_heap_preamble_inner(body, depth + 1)
                || triggers
                    .iter()
                    .any(|p| p.iter().any(|t| needs_heap_preamble_inner(t, depth + 1)))
        }
        Formula::True | Formula::False | Formula::Pure(_) | Formula::MutBorrow { .. } => false,
    }
}

/// Generate SMT-LIB2 preamble for `Seq<T>` logical sequences (Part of #111).
///
/// Creates uninterpreted function declarations for sequence operations:
/// - `seq_len`: Returns sequence length
/// - `seq_index_logic`: Returns element at index
/// - `seq_push_back`: Returns sequence with element appended
/// - `seq_empty`: Empty sequence constant
///
/// This preamble is required when encoding formulas that contain `View` or `MethodCall`
/// expressions operating on logical sequences.
///
/// **Note:** This is the legacy UF-based Seq encoding used by `--emit-smt` output.
/// The actual verifier (`trust-wp-ay`) uses an Array+Length encoding for Seq that
/// differs from this preamble. The `--emit-smt` output is a debugging aid and
/// may not exactly match the solver input. (Part of #1539)
pub(crate) fn generate_seq_preamble() -> String {
    r"; Seq<T> model - logical sequence type (uninterpreted sort)
; Each Seq@ expression maps to an opaque Seq sort value
; Seq operations are modeled as uninterpreted functions with axioms

(declare-sort Seq 0)

; Uninterpreted functions for Seq operations
(declare-fun seq_len (Seq) Int)
(declare-fun seq_index_logic (Seq Int) Int)
(declare-fun seq_push_back (Seq Int) Seq)
(declare-const seq_empty Seq)

; Axiom: seq_len is non-negative
(assert (forall ((s Seq)) (>= (seq_len s) 0)))

; Axiom: empty sequence has length 0
(assert (= (seq_len seq_empty) 0))

; Axiom: push_back increases length by 1
(assert (forall ((s Seq) (v Int))
  (= (seq_len (seq_push_back s v)) (+ (seq_len s) 1))))

; Axiom: push_back preserves existing elements
(assert (forall ((s Seq) (v Int) (i Int))
  (=> (and (>= i 0) (< i (seq_len s)))
      (= (seq_index_logic (seq_push_back s v) i) (seq_index_logic s i)))))

; Axiom: push_back stores new element at end
(assert (forall ((s Seq) (v Int))
  (= (seq_index_logic (seq_push_back s v) (seq_len s)) v)))
"
    .to_string()
}

/// Generate SMT-LIB2 preamble for integer bitwise UF fallback operators.
///
/// Bitwise operators are currently encoded as uninterpreted functions over Int.
pub(crate) fn generate_bitwise_preamble() -> String {
    let mut out = String::from("; Integer bitwise fallback UFs\n");
    for op in [
        BinOp::Shl,
        BinOp::Shr,
        BinOp::BitAnd,
        BinOp::BitXor,
        BinOp::BitOr,
    ] {
        let name = op
            .smt_int_uf_name()
            .expect("bitwise operator must have an SMT UF name");
        let _ = writeln!(out, "(declare-fun {name} (Int Int) Int)");
    }
    out
}

/// Check if a formula requires bitwise UF declarations.
#[cfg(test)]
pub(crate) fn needs_bitwise_preamble(formula: &Formula) -> bool {
    needs_bitwise_preamble_inner(formula, 0)
}

#[cfg(test)]
fn needs_bitwise_preamble_inner(formula: &Formula, depth: usize) -> bool {
    if depth > MAX_RECURSION_DEPTH {
        return false;
    }
    match formula {
        Formula::Pure(expr) => needs_bitwise_preamble_expr_inner(expr, depth + 1),
        Formula::And(l, r)
        | Formula::Or(l, r)
        | Formula::Implies(l, r)
        | Formula::SepConj(l, r)
        | Formula::MagicWand(l, r) => {
            needs_bitwise_preamble_inner(l, depth + 1) || needs_bitwise_preamble_inner(r, depth + 1)
        }
        Formula::Forall { body, triggers, .. } | Formula::Exists { body, triggers, .. } => {
            needs_bitwise_preamble_inner(body, depth + 1)
                || triggers
                    .iter()
                    .any(|p| p.iter().any(|t| needs_bitwise_preamble_inner(t, depth + 1)))
        }
        Formula::PointsTo { value, .. } => match value {
            Value::Expr(expr) => needs_bitwise_preamble_expr_inner(expr, depth + 1),
            Value::Unknown => false,
        },
        Formula::MutBorrow {
            current,
            final_val,
            id,
            ..
        } => {
            needs_bitwise_preamble_expr_inner(current, depth + 1)
                || needs_bitwise_preamble_expr_inner(final_val, depth + 1)
                || needs_bitwise_preamble_expr_inner(id, depth + 1)
        }
        Formula::True | Formula::False => false,
    }
}

/// Check if a formula requires the Seq preamble (contains `View` or Seq `MethodCall`).
#[cfg(test)]
pub(crate) fn needs_seq_preamble(formula: &Formula) -> bool {
    needs_seq_preamble_inner(formula, 0)
}

#[cfg(test)]
fn needs_seq_preamble_inner(formula: &Formula, depth: usize) -> bool {
    if depth > MAX_RECURSION_DEPTH {
        return false;
    }
    match formula {
        Formula::Pure(expr) => needs_seq_preamble_expr_inner(expr, depth + 1),
        // Binary formula variants - check both sides for Seq usage
        Formula::And(l, r)
        | Formula::Or(l, r)
        | Formula::Implies(l, r)
        | Formula::SepConj(l, r)
        | Formula::MagicWand(l, r) => {
            needs_seq_preamble_inner(l, depth + 1) || needs_seq_preamble_inner(r, depth + 1)
        }
        Formula::Forall { body, triggers, .. } | Formula::Exists { body, triggers, .. } => {
            needs_seq_preamble_inner(body, depth + 1)
                || triggers
                    .iter()
                    .any(|p| p.iter().any(|t| needs_seq_preamble_inner(t, depth + 1)))
        }
        Formula::PointsTo { value, .. } => match value {
            Value::Expr(expr) => needs_seq_preamble_expr_inner(expr, depth + 1),
            Value::Unknown => false,
        },
        Formula::MutBorrow {
            current,
            final_val,
            id,
            ..
        } => {
            needs_seq_preamble_expr_inner(current, depth + 1)
                || needs_seq_preamble_expr_inner(final_val, depth + 1)
                || needs_seq_preamble_expr_inner(id, depth + 1)
        }
        Formula::True | Formula::False => false,
    }
}

#[cfg(test)]
fn needs_seq_preamble_expr_inner(expr: &PureExpr, depth: usize) -> bool {
    if depth > MAX_RECURSION_DEPTH {
        return false;
    }
    match expr {
        PureExpr::View(_) => true,
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            // Known Seq methods trigger preamble need
            let is_seq_method = matches!(method.as_str(), "len" | "index_logic" | "push_back");
            // Also check receiver and arguments for nested Views
            is_seq_method
                || needs_seq_preamble_expr_inner(receiver, depth + 1)
                || args
                    .iter()
                    .any(|a| needs_seq_preamble_expr_inner(a, depth + 1))
        }
        PureExpr::BinOp(l, _, r) => {
            needs_seq_preamble_expr_inner(l, depth + 1)
                || needs_seq_preamble_expr_inner(r, depth + 1)
        }
        PureExpr::UnOp(_, inner) => needs_seq_preamble_expr_inner(inner, depth + 1),
        PureExpr::Ite(c, t, e) => {
            needs_seq_preamble_expr_inner(c, depth + 1)
                || needs_seq_preamble_expr_inner(t, depth + 1)
                || needs_seq_preamble_expr_inner(e, depth + 1)
        }
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            needs_seq_preamble_expr_inner(inner, depth + 1)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            needs_seq_preamble_expr_inner(body, depth + 1)
                || triggers.iter().any(|t| {
                    t.iter()
                        .any(|e| needs_seq_preamble_expr_inner(e, depth + 1))
                })
        }
        PureExpr::Match { scrutinee, arms } => {
            needs_seq_preamble_expr_inner(scrutinee, depth + 1)
                || arms
                    .iter()
                    .any(|arm| needs_seq_preamble_expr_inner(&arm.body, depth + 1))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|a| needs_seq_preamble_expr_inner(a, depth + 1)),
        PureExpr::Let { value, body, .. } => {
            needs_seq_preamble_expr_inner(value, depth + 1)
                || needs_seq_preamble_expr_inner(body, depth + 1)
        }
        PureExpr::LetAssume { assumption, body } => {
            needs_seq_preamble_expr_inner(assumption, depth + 1)
                || needs_seq_preamble_expr_inner(body, depth + 1)
        }
        PureExpr::LetObligation { obligation, body } => {
            needs_seq_preamble_expr_inner(obligation, depth + 1)
                || needs_seq_preamble_expr_inner(body, depth + 1)
        }
        PureExpr::Closure { body, .. } => needs_seq_preamble_expr_inner(body, depth + 1),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
    }
}

pub(super) fn needs_bitwise_preamble_expr(expr: &PureExpr) -> bool {
    needs_bitwise_preamble_expr_inner(expr, 0)
}

fn needs_bitwise_preamble_expr_inner(expr: &PureExpr, depth: usize) -> bool {
    if depth > MAX_RECURSION_DEPTH {
        return false;
    }
    match expr {
        PureExpr::BinOp(l, op, r) => {
            op.smt_int_uf_name().is_some()
                || needs_bitwise_preamble_expr_inner(l, depth + 1)
                || needs_bitwise_preamble_expr_inner(r, depth + 1)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => needs_bitwise_preamble_expr_inner(inner, depth + 1),
        PureExpr::Ite(c, t, e) => {
            needs_bitwise_preamble_expr_inner(c, depth + 1)
                || needs_bitwise_preamble_expr_inner(t, depth + 1)
                || needs_bitwise_preamble_expr_inner(e, depth + 1)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            needs_bitwise_preamble_expr_inner(receiver, depth + 1)
                || args
                    .iter()
                    .any(|a| needs_bitwise_preamble_expr_inner(a, depth + 1))
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            needs_bitwise_preamble_expr_inner(body, depth + 1)
                || triggers.iter().any(|trigger| {
                    trigger
                        .iter()
                        .any(|e| needs_bitwise_preamble_expr_inner(e, depth + 1))
                })
        }
        PureExpr::Match { scrutinee, arms } => {
            needs_bitwise_preamble_expr_inner(scrutinee, depth + 1)
                || arms
                    .iter()
                    .any(|arm| needs_bitwise_preamble_expr_inner(&arm.body, depth + 1))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|a| needs_bitwise_preamble_expr_inner(a, depth + 1)),
        PureExpr::Let { value, body, .. } => {
            needs_bitwise_preamble_expr_inner(value, depth + 1)
                || needs_bitwise_preamble_expr_inner(body, depth + 1)
        }
        PureExpr::LetAssume { assumption, body } => {
            needs_bitwise_preamble_expr_inner(assumption, depth + 1)
                || needs_bitwise_preamble_expr_inner(body, depth + 1)
        }
        PureExpr::LetObligation { obligation, body } => {
            needs_bitwise_preamble_expr_inner(obligation, depth + 1)
                || needs_bitwise_preamble_expr_inner(body, depth + 1)
        }
        PureExpr::Closure { body, .. } => needs_bitwise_preamble_expr_inner(body, depth + 1),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
    }
}
