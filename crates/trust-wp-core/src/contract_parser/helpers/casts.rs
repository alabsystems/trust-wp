// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Casts (`e as T`), type ascriptions (`e : T`) and `let` annotations.
//!
//! A cast changes a value: `256_u64 as u8` is `0`, `-1_i64 as u64` is
//! `u64::MAX`. It is lowered to the exact integer arithmetic Rust's `as`
//! performs between integer types, or the clause is refused by name; it is
//! never read as its operand. An ascription never changes a value, but it
//! states the operand's sort, so it is kept in the AST as a sort the
//! consumers check (a name's own annotation, or its syntactic sort). An
//! ascription that contradicts the operand's syntactic sort is refused, and
//! so is one that contradicts the sort its name already has in scope: a
//! consumer reading the annotation would otherwise read a bound name at a
//! sort its binder does not give it. One on an operand that has neither (a
//! dereference, a call) leaves the AST unchanged and is recorded as
//! unchecked, for the consumers that must refuse it.

use std::sync::Arc;

use super::super::{ContractParser, ParseError};
use crate::formula::{BinOp, ExprSort, MatchArm, PureExpr, UnOp};

/// `2^32`, the largest modulus the lowering spells: `PureExpr::Int` is an
/// `i64`, so `2^64` has no literal, and a 64-bit cast is assembled from two
/// 32-bit halves instead.
const TWO_POW_32: i64 = 1 << 32;

/// A fixed-width integer type a modeled cast targets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IntTarget {
    bits: u32,
    signed: bool,
}

/// The integer type `text` names, or why a cast to it is not modeled.
fn cast_target(text: &str) -> Result<IntTarget, &'static str> {
    let target = |bits, signed| Ok(IntTarget { bits, signed });
    match text {
        "u8" => target(8, false),
        "u16" => target(16, false),
        "u32" => target(32, false),
        "u64" => target(64, false),
        "i8" => target(8, true),
        "i16" => target(16, true),
        "i32" => target(32, true),
        "i64" => target(64, true),
        "u128" | "i128" => Err("a 128-bit result exceeds what native replay evaluates"),
        "usize" | "isize" => {
            Err("its width is the target's pointer width, which a clause does not fix")
        }
        "f32" | "f64" => Err("a float cast rounds; a contract states no float operation but `==`"),
        "Int" | "int" => Err("`Int` is not a Rust cast target"),
        _ => Err("only casts to `u8`..`u64` and `i8`..`i64` are modeled"),
    }
}

/// The pointee of a raw pointer type written `*const X` / `*mut X`, with its
/// whitespace collapsed, or `None` for any other type.
fn raw_pointer_pointee(text: &str) -> Option<String> {
    let rest = text.strip_prefix('*')?.trim_start();
    let pointee = rest
        .strip_prefix("const")
        .or_else(|| rest.strip_prefix("mut"))?;
    if !pointee.starts_with(char::is_whitespace) {
        return None;
    }
    let pointee = pointee.split_whitespace().collect::<Vec<_>>().join(" ");
    (!pointee.is_empty()).then_some(pointee)
}

/// The inclusive value range of an integer literal suffix, or `None` for a
/// suffix whose literals are unbounded (`int`) or not integers.
pub(in crate::contract_parser) fn literal_suffix_range(suffix: &str) -> Option<(i128, i128)> {
    let unsigned = |bits: u32| Some((0, (1_i128 << bits) - 1));
    let signed = |bits: u32| Some((-(1_i128 << (bits - 1)), (1_i128 << (bits - 1)) - 1));
    match suffix {
        "u8" => unsigned(8),
        "u16" => unsigned(16),
        "u32" => unsigned(32),
        "u64" => unsigned(64),
        // `u128::MAX` has no `i128`; the literal parser admits `i64` values
        // only, so every one a `u128` holds lies in this range.
        "u128" => Some((0, i128::MAX)),
        "i8" => signed(8),
        "i16" => signed(16),
        "i32" => signed(32),
        "i64" => signed(64),
        "i128" => Some((i128::MIN, i128::MAX)),
        // Whatever the pointer width, a negative literal is not a `usize`.
        // An `isize` is at least 16 bits wide; wider values are left to the
        // compiler that fixes the target (the literal's VALUE is not in
        // doubt wherever it compiles).
        "usize" => Some((0, i128::MAX)),
        "isize" => Some((i128::MIN, i128::MAX)),
        _ => None,
    }
}

/// The sort `expr` has by its outermost syntax alone, where that fixes one.
fn syntactic_sort(expr: &PureExpr) -> Option<ExprSort> {
    match expr {
        PureExpr::Int(_) => Some(ExprSort::Int),
        PureExpr::Bool(_) => Some(ExprSort::Bool),
        // An unsuffixed literal takes the format its context infers.
        PureExpr::Float(bits) => bits.width().map(ExprSort::Float),
        PureExpr::BinOp(_, op, _) => Some(match op {
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or
            | BinOp::Implies => ExprSort::Bool,
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::DivTrunc
            | BinOp::RemTrunc
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::BitAnd
            | BinOp::BitXor
            | BinOp::BitOr => ExprSort::Int,
        }),
        PureExpr::UnOp(UnOp::Not, _) | PureExpr::Forall { .. } | PureExpr::Exists { .. } => {
            Some(ExprSort::Bool)
        }
        PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, _) => Some(ExprSort::Int),
        _ => None,
    }
}

/// Where [`ascribe_sort`] put an annotation.
#[derive(Default)]
struct Ascribed {
    /// Names the annotation became the sort of.
    names: Vec<String>,
    /// Operands that carry no sort the AST records and none their syntax
    /// fixes, so the annotation on them is dropped unchecked.
    unchecked: Vec<PureExpr>,
}

/// `expr` read at `sort`: a name takes the sort as its annotation (pushed
/// through `old`, `if` branches and a `let` body to the names that yield the
/// value), and is recorded in `ascribed`; anything else must not have
/// another sort by its syntax, and an operand with no syntactic sort (a
/// dereference, a call, a `match`) is recorded as unchecked. `Err` carries
/// the sort `expr` has instead.
fn ascribe_sort(
    expr: PureExpr,
    sort: &ExprSort,
    ascribed: &mut Ascribed,
) -> Result<PureExpr, ExprSort> {
    match expr {
        PureExpr::Var(name, None) => {
            ascribed.names.push(name.clone());
            Ok(PureExpr::Var(name, Some(sort.clone())))
        }
        PureExpr::Var(name, Some(own)) => {
            if own == *sort {
                Ok(PureExpr::Var(name, Some(own)))
            } else {
                Err(own)
            }
        }
        PureExpr::Old(inner) => Ok(PureExpr::Old(Arc::new(ascribe_sort(
            Arc::unwrap_or_clone(inner),
            sort,
            ascribed,
        )?))),
        PureExpr::Ite(cond, then_expr, else_expr) => Ok(PureExpr::Ite(
            cond,
            Arc::new(ascribe_sort(
                Arc::unwrap_or_clone(then_expr),
                sort,
                ascribed,
            )?),
            Arc::new(ascribe_sort(
                Arc::unwrap_or_clone(else_expr),
                sort,
                ascribed,
            )?),
        )),
        PureExpr::Let { var, value, body } => Ok(PureExpr::Let {
            var,
            value,
            body: Arc::new(ascribe_sort(Arc::unwrap_or_clone(body), sort, ascribed)?),
        }),
        other => match syntactic_sort(&other) {
            Some(own) if own != *sort => Err(own),
            Some(_) => Ok(other),
            None => {
                ascribed.unchecked.push(other.clone());
                Ok(other)
            }
        },
    }
}

/// The binders in force at a point of a parsed expression, innermost last,
/// each with the sort it gives its name where one is known.
type Scope = Vec<(String, Option<ExprSort>)>;

/// What the innermost binder of a name in a [`Scope`] says of it.
enum InScope<'scope> {
    /// No binder of the name is in scope.
    Free,
    /// A binder that fixes no sort (an elided binder type, a match-arm
    /// pattern).
    Unsorted,
    /// A binder that gives the name this sort.
    Sorted(&'scope ExprSort),
}

fn in_scope<'scope>(scope: &'scope Scope, name: &str) -> InScope<'scope> {
    match scope.iter().rev().find(|(bound, _)| bound == name) {
        None => InScope::Free,
        Some((_, None)) => InScope::Unsorted,
        Some((_, Some(sort))) => InScope::Sorted(sort),
    }
}

/// The sort `expr` has where its syntax, an annotation or a binder in
/// `scope` fixes one: what a `let` of `expr` gives its name.
fn scoped_sort(expr: &PureExpr, scope: &mut Scope) -> Option<ExprSort> {
    match expr {
        PureExpr::Var(_, Some(sort)) => Some(sort.clone()),
        PureExpr::Var(name, None) => match in_scope(scope, name) {
            InScope::Sorted(sort) => Some(sort.clone()),
            InScope::Unsorted | InScope::Free => None,
        },
        PureExpr::Old(inner) => scoped_sort(inner, scope),
        // `*e` has the sort `e` references, and `^e` that of a mutable one.
        PureExpr::Deref(inner) => match scoped_sort(inner, scope)? {
            ExprSort::Ref(referent) | ExprSort::MutRef(referent) => Some(*referent),
            _ => None,
        },
        PureExpr::Final(inner) => match scoped_sort(inner, scope)? {
            ExprSort::MutRef(referent) => Some(*referent),
            _ => None,
        },
        PureExpr::Ite(_, then_expr, else_expr) => {
            match (scoped_sort(then_expr, scope), scoped_sort(else_expr, scope)) {
                (Some(then_sort), Some(else_sort)) => (then_sort == else_sort).then_some(then_sort),
                (known, None) | (None, known) => known,
            }
        }
        PureExpr::Let { var, value, body } => {
            let value_sort = scoped_sort(value, scope);
            scope.push((var.clone(), value_sort));
            let sort = scoped_sort(body, scope);
            scope.pop();
            sort
        }
        other => syntactic_sort(other),
    }
}

/// A name an annotation reads at one sort where its binder gives it another.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::contract_parser) struct ScopeDisagreement {
    pub(in crate::contract_parser) name: String,
    pub(in crate::contract_parser) annotated: ExprSort,
    pub(in crate::contract_parser) bound: ExprSort,
}

/// The first name of `expr`, in a left-to-right walk, whose annotation
/// disagrees with the sort the innermost binder of that name gives it: a
/// quantifier binder's declared type, a closure parameter's, or the sort of
/// the value a `let` binds it to. A binder that fixes no sort (an elided
/// binder type, a match-arm pattern) agrees with any annotation, and a free
/// name's annotations are left to the consumers, which compare them with the
/// name's other uses.
pub(in crate::contract_parser) fn first_scope_disagreement(
    expr: &PureExpr,
) -> Option<ScopeDisagreement> {
    first_disagreement_in(expr, &mut Vec::new())
}

fn first_disagreement_in_all<'expr>(
    exprs: impl IntoIterator<Item = &'expr PureExpr>,
    scope: &mut Scope,
) -> Option<ScopeDisagreement> {
    exprs
        .into_iter()
        .find_map(|expr| first_disagreement_in(expr, scope))
}

fn first_disagreement_in_arm(arm: &MatchArm, scope: &mut Scope) -> Option<ScopeDisagreement> {
    let names = arm.pattern.bound_names();
    let depth = scope.len();
    scope.extend(names.into_iter().map(|name| (name.to_string(), None)));
    let found = first_disagreement_in(&arm.body, scope);
    scope.truncate(depth);
    found
}

fn first_disagreement_in(expr: &PureExpr, scope: &mut Scope) -> Option<ScopeDisagreement> {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, None) => None,
        PureExpr::Var(name, Some(annotated)) => match in_scope(scope, name) {
            InScope::Sorted(bound) if bound != annotated => Some(ScopeDisagreement {
                name: name.clone(),
                annotated: annotated.clone(),
                bound: bound.clone(),
            }),
            InScope::Sorted(_) | InScope::Unsorted | InScope::Free => None,
        },
        PureExpr::BinOp(left, _, right)
        | PureExpr::LetAssume {
            assumption: left,
            body: right,
        }
        | PureExpr::LetObligation {
            obligation: left,
            body: right,
        } => first_disagreement_in_all([left.as_ref(), right.as_ref()], scope),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => first_disagreement_in(inner, scope),
        PureExpr::Ite(cond, then_expr, else_expr) => first_disagreement_in_all(
            [cond.as_ref(), then_expr.as_ref(), else_expr.as_ref()],
            scope,
        ),
        PureExpr::MethodCall { receiver, args, .. } => first_disagreement_in(receiver, scope)
            .or_else(|| first_disagreement_in_all(args, scope)),
        PureExpr::LogicFnCall { args, .. } => first_disagreement_in_all(args, scope),
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        }
        | PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            scope.push((var.clone(), var_sort.clone()));
            let found = first_disagreement_in(body, scope)
                .or_else(|| first_disagreement_in_all(triggers.iter().flatten(), scope));
            scope.pop();
            found
        }
        PureExpr::Match { scrutinee, arms } => {
            first_disagreement_in(scrutinee, scope).or_else(|| {
                arms.iter()
                    .find_map(|arm| first_disagreement_in_arm(arm, scope))
            })
        }
        PureExpr::Let { var, value, body } => first_disagreement_in(value, scope).or_else(|| {
            let value_sort = scoped_sort(value, scope);
            scope.push((var.clone(), value_sort));
            let found = first_disagreement_in(body, scope);
            scope.pop();
            found
        }),
        PureExpr::Closure { params, body } => {
            let depth = scope.len();
            scope.extend(params.iter().cloned());
            let found = first_disagreement_in(body, scope);
            scope.truncate(depth);
            found
        }
    }
}

fn int(value: i64) -> Arc<PureExpr> {
    Arc::new(PureExpr::Int(value))
}

fn binop(left: PureExpr, op: BinOp, right: Arc<PureExpr>) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), op, right)
}

/// `value mod 2^bits` for `bits <= 32`, Euclidean: the low `bits` bits of
/// the two's-complement value, read unsigned.
fn low_bits(value: PureExpr, bits: u32) -> PureExpr {
    binop(value, BinOp::Mod, int(1_i64 << bits))
}

/// The value in `[-2^(bits-1), 2^(bits-1))` congruent to `value` modulo
/// `2^bits`, for `bits <= 32`.
fn wrap_signed(value: PureExpr, bits: u32) -> PureExpr {
    let half = 1_i64 << (bits - 1);
    binop(
        low_bits(binop(value, BinOp::Add, int(half)), bits),
        BinOp::Sub,
        int(half),
    )
}

/// Whether duplicating `expr` in the lowering costs nothing.
fn is_atomic(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(..) | PureExpr::Int(_) | PureExpr::Bool(_) => true,
        PureExpr::Old(inner) => matches!(inner.as_ref(), PureExpr::Var(..)),
        _ => false,
    }
}

impl ContractParser<'_> {
    /// Model `operand as <text>` (the type text as written), or refuse the
    /// clause naming the cast. `at` is where the cast's `as` starts.
    ///
    /// Rust's `as` between integer types is value-exact modular arithmetic:
    /// truncation keeps the low bits, sign extension and zero extension keep
    /// the source value, and a same-width cast reinterprets the bits. For a
    /// source value `v` of ANY integer type, all of these give the one value
    /// of the target's range congruent to `v` modulo `2^bits`, so the
    /// lowering needs the target alone: `v mod 2^bits` (Euclidean) for an
    /// unsigned target, shifted into the signed range for a signed one. A
    /// 64-bit target is assembled from 32-bit halves (`2^64` has no `i64`
    /// literal): `v mod 2^64 = (v mod 2^32) + 2^32 * ((v div 2^32) mod 2^32)`,
    /// and the signed form wraps the high half instead.
    ///
    /// A non-integer operand (a `bool`, a float, a pointer) reaches the
    /// arithmetic at its own sort, where every consumer either converts it
    /// exactly (`bool` to 0/1), reads it as an unconstrained integer (every
    /// value the cast can produce is then covered), or refuses it.
    ///
    /// A cast to a raw pointer type (`*const X`, `*mut X`) becomes the
    /// pending marker [`PTR_CAST_PENDING_PREFIX`](crate::formula::internal::builtins::PTR_CAST_PENDING_PREFIX)
    /// applied to the operand, for the driver to read at the operand's type.
    pub(in crate::contract_parser) fn lower_cast(
        &mut self,
        operand: PureExpr,
        text: &str,
        at: usize,
    ) -> Result<PureExpr, ParseError> {
        if let Some(pointee) = raw_pointer_pointee(text) {
            // Identity or `thin` depends on whether the two pointees are
            // sized, which only the driver can read; until it does, the cast
            // is a marker the encoder refuses, never its operand.
            return Ok(PureExpr::LogicFnCall {
                name: format!(
                    "{}{pointee}",
                    crate::formula::internal::builtins::PTR_CAST_PENDING_PREFIX
                ),
                args: vec![operand],
            });
        }
        let target = cast_target(text).map_err(|why| ParseError {
            message: format!("cast `as {text}` is not modeled: {why}"),
            position: at,
        })?;
        if target.bits <= 32 {
            return Ok(if target.signed {
                wrap_signed(operand, target.bits)
            } else {
                low_bits(operand, target.bits)
            });
        }
        let (value, bind) = if is_atomic(&operand) {
            (operand, None)
        } else {
            let name = format!("$cast{}", self.cast_counter);
            self.cast_counter = self.cast_counter.saturating_add(1);
            (PureExpr::Var(name.clone(), None), Some((name, operand)))
        };
        let high = binop(value.clone(), BinOp::Div, int(TWO_POW_32));
        let high = if target.signed {
            wrap_signed(high, 32)
        } else {
            low_bits(high, 32)
        };
        let lowered = binop(
            low_bits(value, 32),
            BinOp::Add,
            Arc::new(PureExpr::BinOp(int(TWO_POW_32), BinOp::Mul, Arc::new(high))),
        );
        Ok(match bind {
            None => lowered,
            Some((var, operand)) => PureExpr::Let {
                var,
                value: Arc::new(operand),
                body: Arc::new(lowered),
            },
        })
    }

    /// Keep `operand : <text>` in the AST as the sort it states. `sort` is
    /// what the parser maps the written type to. Only `Int`/`bool`-sorted
    /// types (the integer types and `bool`) constrain the operand here; any
    /// other type is left to consumers that read the written type itself.
    /// `what` names the annotation for the refusal (an ascription or a `let`
    /// annotation) and `at` is where it starts. Each name the annotation
    /// lands on is recorded with `at`, for the scope check the finished parse
    /// makes ([`Self::check_annotations_agree_with_scope`]); an operand it
    /// cannot land on or check (`(*p : Int)`) is recorded as an unchecked
    /// annotation, which a consumer that relies on annotations refuses.
    pub(in crate::contract_parser) fn ascribe(
        &mut self,
        operand: PureExpr,
        sort: Option<&ExprSort>,
        text: &str,
        what: &str,
        at: usize,
    ) -> Result<PureExpr, ParseError> {
        let Some(sort @ (ExprSort::Int | ExprSort::Bool)) = sort else {
            return Ok(operand);
        };
        if let (PureExpr::Int(value), Some((low, high))) = (&operand, literal_suffix_range(text)) {
            if !(low..=high).contains(&i128::from(*value)) {
                return Err(ParseError {
                    message: format!(
                        "{what} `: {text}` on the literal {value}, which `{text}` cannot hold"
                    ),
                    position: at,
                });
            }
        }
        if let Some(borrow) = self.annotated_borrow(&operand) {
            return Err(ParseError {
                message: format!(
                    "{what} `: {text}` on the borrow `{borrow}`: a borrow is a reference, never \
                     an integer or a `bool`"
                ),
                position: at,
            });
        }
        let mut ascribed = Ascribed::default();
        let expr = ascribe_sort(operand, sort, &mut ascribed).map_err(|own| ParseError {
            message: format!(
                "{what} `: {text}` on an operand of sort {own}: an annotation never changes a \
                 value, so one that changes its sort is refused"
            ),
            position: at,
        })?;
        self.annotated_names.extend(
            ascribed
                .names
                .into_iter()
                .map(|name| (name, sort.clone(), at)),
        );
        for operand in ascribed.unchecked {
            let operand = self.display(&operand);
            self.unchecked_annotations
                .push(format!("{what} `: {text}` on `{operand}`"));
        }
        Ok(expr)
    }

    /// Refuse a finished parse in which an annotation reads a name at a sort
    /// other than the one the name's binder gives it
    /// ([`first_scope_disagreement`]): `forall<v: bool> (v : Int) + 1 > v`
    /// would otherwise carry `v` at `Int` under a `bool` binder, and a
    /// consumer that reads the annotation proves a claim about an integer
    /// the binder does not range over. The error sits at the first
    /// annotation of that name at that sort.
    pub(in crate::contract_parser) fn check_annotations_agree_with_scope(
        &self,
        expr: &PureExpr,
    ) -> Result<(), ParseError> {
        let Some(ScopeDisagreement {
            name,
            annotated,
            bound,
        }) = first_scope_disagreement(expr)
        else {
            return Ok(());
        };
        let position = self
            .annotated_names
            .iter()
            .find(|(annotated_name, sort, _)| *annotated_name == name && *sort == annotated)
            .map_or(0, |(_, _, at)| *at);
        Err(ParseError {
            message: format!(
                "`{name}` is annotated at sort {annotated} where it is bound at sort {bound}: an \
                 annotation never changes a value, so one that changes its sort is refused"
            ),
            position,
        })
    }
}
