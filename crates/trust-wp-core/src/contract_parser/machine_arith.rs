// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What an arithmetic operator written in clause text means: its operands'
//! type decides it (D-232, D-135 item 3).
//!
//! In the pinned oracle an operator on machine-integer operands means what
//! creusot-std's logic impl gives it: `u32 + u32` is `UInt32$BW$.add`, a
//! bit-vector addition that WRAPS, and so are `-`, `*` and unary `-`; on `@`
//! views and `Int` the same operators are mathematical. Clause text carries
//! no types, so the reading cannot be decided here. The driver has rustc's
//! type check of every clause (`trust-wp-macros`' type-check vehicle) and
//! installs, per clause text, what each operator kind of that text is applied
//! to ([`install`]). The parser then builds every operator it reads from the
//! text at that type ([`OpReading`]) or refuses the clause; a text the driver
//! installed nothing for is read only where its syntax fixes an `Int` operand.
//!
//! With nothing installed (the proc macros, the CLI, the library) every
//! operator is read as it always was, mathematically. Those readers have no
//! type check to ask.
//!
//! The kinds are matched by count, not by position: a kind reads as one type
//! only when the type check gives every operator of that kind in the text that
//! type, and the parse builds exactly as many operators of the kind from the
//! text as the type check holds ([`ContractParser::check_written_arith`]). An
//! operator the type check did not see can then never be read at the type of
//! one it did.

use std::{
    collections::{BTreeMap, HashMap},
    sync::{Arc, RwLock},
};

use super::{ContractParser, ParseError};
use crate::formula::{BinOp, PureExpr, UnOp};

/// An operator of clause text whose meaning depends on its operands' type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArithOp {
    /// Binary `+`.
    Add,
    /// Binary `-`.
    Sub,
    /// Binary `*`.
    Mul,
    /// Binary `/`.
    Div,
    /// Binary `%`.
    Rem,
    /// Unary `-` on anything but an integer literal.
    Neg,
    /// `<<`.
    Shl,
    /// `>>`.
    Shr,
    /// Unary `!`.
    Not,
}

impl ArithOp {
    /// The operator as the text writes it.
    #[must_use]
    pub const fn spelling(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub | Self::Neg => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
            Self::Shl => "<<",
            Self::Shr => ">>",
            Self::Not => "!",
        }
    }

    /// The kind of a binary operator the parser builds from the text, if it
    /// is one whose meaning depends on its operands' type.
    #[must_use]
    pub const fn of_binop(op: BinOp) -> Option<Self> {
        match op {
            BinOp::Add => Some(Self::Add),
            BinOp::Sub => Some(Self::Sub),
            BinOp::Mul => Some(Self::Mul),
            BinOp::DivTrunc => Some(Self::Div),
            BinOp::RemTrunc => Some(Self::Rem),
            BinOp::Shl => Some(Self::Shl),
            BinOp::Shr => Some(Self::Shr),
            _ => None,
        }
    }
}

/// A fixed-width integer type: `bits` of 8, 16, 32 or 64.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MachineInt {
    pub bits: u32,
    pub signed: bool,
}

impl MachineInt {
    /// The type, or `None` for a width the wrapping lowering does not spell:
    /// a 128-bit value exceeds what native replay evaluates, as for a cast
    /// (`helpers/casts.rs`).
    #[must_use]
    pub fn new(bits: u32, signed: bool) -> Option<Self> {
        matches!(bits, 8 | 16 | 32 | 64).then_some(Self { bits, signed })
    }

    fn min(self) -> i128 {
        if self.signed {
            -(1_i128 << (self.bits - 1))
        } else {
            0
        }
    }

    fn max(self) -> i128 {
        if self.signed {
            (1_i128 << (self.bits - 1)) - 1
        } else {
            (1_i128 << self.bits) - 1
        }
    }

    fn modulus(self) -> i128 {
        1_i128 << self.bits
    }

    /// The type's name, for a refusal.
    #[must_use]
    pub fn name(self) -> String {
        format!("{}{}", if self.signed { 'i' } else { 'u' }, self.bits)
    }
}

/// How the parser reads every operator of one kind in one text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpReading {
    /// Mathematical integer arithmetic: the type check applies every operator
    /// of the kind to `Int` (or to a type the text stack reads as it is
    /// written, a float).
    Mathematical,
    /// The oracle's operation on this machine integer, which wraps: the type
    /// check applies every operator of the kind to it.
    Wrapping(MachineInt),
    /// No type check says what the operands are: an operator is read
    /// mathematically where its syntax fixes an `Int` operand (an `@` view, a
    /// `.len()`, `Int` arithmetic) and refused elsewhere.
    Syntactic,
    /// Refused, for this reason.
    Refused(String),
}

/// What the type check of one clause text says of one operator kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KindReading {
    pub reading: OpReading,
    /// How many operators of the kind the type check holds; `None` when it
    /// does not count them (the reading is then not one of a type).
    pub typed: Option<usize>,
}

/// What the type check of one clause text says of each operator kind. A kind
/// it holds no operator of reads [`OpReading::Syntactic`] and counts zero.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TextReading {
    pub kinds: BTreeMap<ArithOp, KindReading>,
}

impl TextReading {
    fn of(&self, op: ArithOp) -> KindReading {
        self.kinds.get(&op).cloned().unwrap_or(KindReading {
            reading: OpReading::Syntactic,
            typed: Some(0),
        })
    }

    /// The reading of one text two type checks give: a kind keeps a reading
    /// only where both agree on it, and is refused where they do not.
    #[must_use]
    pub fn merge(&self, other: &Self) -> Self {
        let mut kinds = BTreeMap::new();
        for op in self.kinds.keys().chain(other.kinds.keys()).copied() {
            let (a, b) = (self.of(op), other.of(op));
            let merged = if a == b {
                a
            } else {
                KindReading {
                    reading: OpReading::Refused(format!(
                        "the text is written for more than one item, and their type checks \
                         apply `{}` to different types",
                        op.spelling()
                    )),
                    typed: None,
                }
            };
            kinds.insert(op, merged);
        }
        Self { kinds }
    }

    /// The reading of a text that is also written where no type check reads
    /// it. The parser cannot tell the occurrences apart, so each kind keeps
    /// only what holds whatever that occurrence's operands are: a kind the
    /// type check applies to `Int` is read by syntax alone, and any other is
    /// refused.
    #[must_use]
    pub fn with_untyped_occurrence(&self) -> Self {
        let kinds = self
            .kinds
            .iter()
            .map(|(op, kind)| {
                let reading = match &kind.reading {
                    OpReading::Mathematical | OpReading::Syntactic => OpReading::Syntactic,
                    OpReading::Wrapping(ty) => OpReading::Refused(format!(
                        "the text is also written where no type check reads it, and the type \
                         check that does applies `{}` to `{}`",
                        op.spelling(),
                        ty.name()
                    )),
                    OpReading::Refused(why) => OpReading::Refused(why.clone()),
                };
                (
                    *op,
                    KindReading {
                        reading,
                        typed: None,
                    },
                )
            })
            .collect();
        Self { kinds }
    }
}

/// The readings installed for one compilation.
#[derive(Debug, Default)]
struct Registry {
    texts: HashMap<String, TextReading>,
}

static INSTALLED: RwLock<Option<Arc<Registry>>> = RwLock::new(None);

thread_local! {
    /// A reading installed for this thread alone, ahead of [`INSTALLED`]:
    /// how a test reads text without changing what other tests' threads read.
    static OVERRIDE: std::cell::RefCell<Option<Arc<Registry>>> =
        const { std::cell::RefCell::new(None) };
    /// Set while [`read_as_program`] parses program source.
    static PROGRAM_SOURCE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Run `parse` reading every operator of the text it parses mathematically,
/// whatever is installed: for PROGRAM source (a constant's initializer), not
/// a specification. rustc evaluates program arithmetic with overflow an
/// error, so a value it yields is the mathematical one; the wrapping reading
/// belongs to logic alone.
pub fn read_as_program<R>(parse: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            PROGRAM_SOURCE.with(|flag| flag.set(self.0));
        }
    }
    let _restore = Restore(PROGRAM_SOURCE.with(|flag| flag.replace(true)));
    parse()
}

/// Install the reading of every clause text a type check holds. Every text
/// the map does not name is then read [`OpReading::Syntactic`].
pub fn install(texts: HashMap<String, TextReading>) {
    let registry = Some(Arc::new(Registry { texts }));
    match INSTALLED.write() {
        Ok(mut slot) => *slot = registry,
        Err(poisoned) => *poisoned.into_inner() = registry,
    }
}

/// Undo [`install`]: every operator reads as it did before it.
pub fn uninstall() {
    match INSTALLED.write() {
        Ok(mut slot) => *slot = None,
        Err(poisoned) => *poisoned.into_inner() = None,
    }
}

/// Install `texts` for the current thread only, until [`clear_for_thread`].
pub fn install_for_thread(texts: HashMap<String, TextReading>) {
    OVERRIDE.with(|slot| *slot.borrow_mut() = Some(Arc::new(Registry { texts })));
}

/// Undo [`install_for_thread`].
pub fn clear_for_thread() {
    OVERRIDE.with(|slot| *slot.borrow_mut() = None);
}

/// What the parser of `input` reads its operators as.
#[derive(Debug, Clone)]
pub(super) enum TextArith {
    /// Nothing is installed: every operator reads as it always did.
    Uninstalled,
    /// The driver installed readings and this text has one.
    Read(Arc<TextReading>),
    /// The driver installed readings and this text has none.
    Untyped,
}

impl TextArith {
    pub(super) fn for_input(input: &str) -> Self {
        if PROGRAM_SOURCE.with(std::cell::Cell::get) {
            return Self::Uninstalled;
        }
        let registry =
            OVERRIDE
                .with(|slot| slot.borrow().clone())
                .or_else(|| match INSTALLED.read() {
                    Ok(slot) => slot.clone(),
                    Err(poisoned) => poisoned.into_inner().clone(),
                });
        match registry {
            None => Self::Uninstalled,
            Some(registry) => match registry.texts.get(input) {
                Some(reading) => Self::Read(Arc::new(reading.clone())),
                None => Self::Untyped,
            },
        }
    }

    fn reading(&self, op: ArithOp) -> KindReading {
        match self {
            Self::Uninstalled => KindReading {
                reading: OpReading::Mathematical,
                typed: None,
            },
            Self::Read(text) => text.of(op),
            // `!` reads as boolean negation wherever no type check says
            // otherwise: it is the logical connective far more often than
            // an integer's complement, which the type-checked path refuses.
            Self::Untyped if op == ArithOp::Not => KindReading {
                reading: OpReading::Mathematical,
                typed: None,
            },
            Self::Untyped => KindReading {
                reading: OpReading::Syntactic,
                typed: None,
            },
        }
    }
}

/// One operator the parse built from the text.
#[derive(Debug, Clone, Copy)]
pub(super) struct WrittenSite {
    op: ArithOp,
    wrapped: bool,
    int_syntax: bool,
    at: usize,
}

/// Whether `expr` is an `Int` by its syntax alone: an `@` view, a `.len()`,
/// or `Int` arithmetic on one. An integer literal is not: it takes the type
/// of the operand beside it. Past a nesting depth the answer is "no", which
/// can only refuse: the walk stays linear in a long operator chain.
fn is_int_syntax(expr: &PureExpr) -> bool {
    int_syntax_within(expr, 32)
}

fn int_syntax_within(expr: &PureExpr, depth: u32) -> bool {
    let Some(depth) = depth.checked_sub(1) else {
        return false;
    };
    match expr {
        PureExpr::View(_) => true,
        PureExpr::Old(inner) => int_syntax_within(inner, depth),
        PureExpr::MethodCall { method, args, .. } => method == "len" && args.is_empty(),
        PureExpr::BinOp(left, op, right) if ArithOp::of_binop(*op).is_some() => {
            int_syntax_within(left, depth)
                || int_syntax_within(right, depth)
                || (is_int_literal(left) && is_int_literal(right))
        }
        PureExpr::UnOp(UnOp::Neg, inner) => int_syntax_within(inner, depth),
        PureExpr::Ite(_, then, otherwise) => {
            int_syntax_within(then, depth) || int_syntax_within(otherwise, depth)
        }
        _ => false,
    }
}

fn is_int_literal(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) => true,
        PureExpr::UnOp(UnOp::Neg, inner) => matches!(inner.as_ref(), PureExpr::Int(_)),
        _ => false,
    }
}

/// A binary operator is on `Int` by syntax when either operand is, or when
/// both are literals (Pearlite's literals are `Int`).
fn binary_is_int_syntax(left: &PureExpr, right: &PureExpr) -> bool {
    is_int_syntax(left) || is_int_syntax(right) || (is_int_literal(left) && is_int_literal(right))
}

fn literal_value(expr: &PureExpr) -> Option<i128> {
    match expr {
        PureExpr::Int(value) => Some(i128::from(*value)),
        PureExpr::UnOp(UnOp::Neg, inner) => match inner.as_ref() {
            PureExpr::Int(value) => Some(-i128::from(*value)),
            _ => None,
        },
        _ => None,
    }
}

/// `value` as a sum of `i64` literals, which the encoder folds back into one
/// constant: `PureExpr::Int` holds an `i64`, and a 64-bit type's modulus and
/// its unsigned maximum do not fit one.
fn constant(value: i128) -> PureExpr {
    let step = i128::from(i64::MAX);
    let mut rest = value;
    let mut parts = Vec::new();
    while rest > step {
        parts.push(i64::MAX);
        rest -= step;
    }
    while rest < -step {
        parts.push(-i64::MAX);
        rest += step;
    }
    // `rest` now fits an i64 by the loops above.
    parts.push(i64::try_from(rest).unwrap_or_default());
    let mut parts = parts.into_iter().map(PureExpr::Int);
    let first = parts.next().unwrap_or(PureExpr::Int(0));
    parts.fold(first, |sum, part| binop(sum, BinOp::Add, part))
}

fn binop(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
}

fn ite(cond: PureExpr, then: PureExpr, otherwise: PureExpr) -> PureExpr {
    PureExpr::Ite(Arc::new(cond), Arc::new(then), Arc::new(otherwise))
}

/// The name of the placeholder a wrapping operator is built as until the
/// whole text is parsed ([`ContractParser::settle_wraps`]). No text may
/// spell it: a clause that does is refused before it is read.
const WRAP_MARKER_PREFIX: &str = "__trust_wp_spec_wrap_";

/// A wrapping operator whose cases are not yet placed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Wrap {
    Add(MachineInt),
    Sub(MachineInt),
    Neg(MachineInt),
}

impl Wrap {
    fn marker(self, value: PureExpr) -> PureExpr {
        let (op, ty) = match self {
            Self::Add(ty) => ("add", ty),
            Self::Sub(ty) => ("sub", ty),
            Self::Neg(ty) => ("neg", ty),
        };
        PureExpr::LogicFnCall {
            name: format!("{WRAP_MARKER_PREFIX}{op}_{}", ty.name()),
            args: vec![value],
        }
    }

    fn of_marker(expr: &PureExpr) -> Option<(Self, &PureExpr)> {
        let PureExpr::LogicFnCall { name, args } = expr else {
            return None;
        };
        let (op, ty) = name.strip_prefix(WRAP_MARKER_PREFIX)?.split_once('_')?;
        let signed = match ty.as_bytes().first()? {
            b'i' => true,
            b'u' => false,
            _ => return None,
        };
        let ty = MachineInt::new(ty[1..].parse().ok()?, signed)?;
        let wrap = match op {
            "add" => Self::Add(ty),
            "sub" => Self::Sub(ty),
            "neg" => Self::Neg(ty),
            _ => return None,
        };
        match args.as_slice() {
            [value] => Some((wrap, value)),
            _ => None,
        }
    }

    /// The oracle's result as disjoint cases over `value`, the operator's
    /// mathematical result (the operand, for a negation). Both operands are
    /// in range, so a sum or difference is at most one modulus out of it.
    fn cases(self, value: &PureExpr) -> Vec<(PureExpr, PureExpr)> {
        let v = || value.clone();
        let and = |a, b| binop(a, BinOp::And, b);
        match self {
            Self::Add(ty) | Self::Sub(ty) => {
                let over = matches!(self, Self::Add(_)) || ty.signed;
                let under = matches!(self, Self::Sub(_)) || ty.signed;
                let mut cases = Vec::new();
                let mut in_range: Option<PureExpr> = None;
                if over {
                    cases.push((
                        binop(v(), BinOp::Gt, constant(ty.max())),
                        binop(v(), BinOp::Sub, constant(ty.modulus())),
                    ));
                    in_range = Some(binop(v(), BinOp::Le, constant(ty.max())));
                }
                if under {
                    cases.push((
                        binop(v(), BinOp::Lt, constant(ty.min())),
                        binop(v(), BinOp::Add, constant(ty.modulus())),
                    ));
                    let low = binop(v(), BinOp::Ge, constant(ty.min()));
                    in_range = Some(match in_range {
                        Some(high) => and(low, high),
                        None => low,
                    });
                }
                cases.push((in_range.unwrap_or(PureExpr::Bool(true)), v()));
                cases
            }
            // Only the minimum leaves the range, and it wraps onto itself.
            Self::Neg(ty) if ty.signed => vec![
                (binop(v(), BinOp::Eq, constant(ty.min())), v()),
                (
                    binop(v(), BinOp::Ne, constant(ty.min())),
                    PureExpr::UnOp(UnOp::Neg, Arc::new(v())),
                ),
            ],
            Self::Neg(ty) => vec![
                (binop(v(), BinOp::Eq, PureExpr::Int(0)), PureExpr::Int(0)),
                (
                    binop(v(), BinOp::Ne, PureExpr::Int(0)),
                    binop(constant(ty.modulus()), BinOp::Sub, v()),
                ),
            ],
        }
    }

    /// The cases as one term: the last case is the `else`.
    fn as_term(self, value: &PureExpr) -> PureExpr {
        let mut cases = self.cases(value).into_iter().rev();
        let last = cases.next().map_or_else(|| value.clone(), |(_, v)| v);
        cases.fold(last, |otherwise, (cond, then)| ite(cond, then, otherwise))
    }
}

/// How many cases one comparison may be split into before its remaining
/// wrapping operators are left as terms.
const MAX_LIFTED_CASES: usize = 32;

/// Whether `expr` holds a wrapping placeholder outside every binder and
/// `old`: one whose cases may be stated around the comparison holding it.
fn find_liftable(expr: &PureExpr) -> Option<&PureExpr> {
    if let Some((_, value)) = Wrap::of_marker(expr) {
        // The innermost first: a placeholder inside another's value is
        // placed before the one around it.
        return find_liftable(value).or(Some(expr));
    }
    match expr {
        PureExpr::BinOp(left, _, right) => find_liftable(left).or_else(|| find_liftable(right)),
        PureExpr::UnOp(_, inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            find_liftable(inner)
        }
        PureExpr::View(inner) => find_liftable(inner),
        PureExpr::Ite(cond, then, otherwise) => find_liftable(cond)
            .or_else(|| find_liftable(then))
            .or_else(|| find_liftable(otherwise)),
        PureExpr::LogicFnCall { args, .. } => args.iter().find_map(find_liftable),
        PureExpr::MethodCall { receiver, args, .. } => {
            find_liftable(receiver).or_else(|| args.iter().find_map(find_liftable))
        }
        // `old` reads its operand in another state, and a binder scopes
        // names a case condition would read outside it.
        _ => None,
    }
}

/// `expr` with the one placeholder `target` replaced by `with`.
fn replace_marker(expr: &PureExpr, target: &PureExpr, with: &PureExpr) -> PureExpr {
    if std::ptr::eq(expr, target) {
        return with.clone();
    }
    let go = |e: &Arc<PureExpr>| Arc::new(replace_marker(e, target, with));
    match expr {
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(go(left), *op, go(right)),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(*op, go(inner)),
        PureExpr::Deref(inner) => PureExpr::Deref(go(inner)),
        PureExpr::Final(inner) => PureExpr::Final(go(inner)),
        PureExpr::View(inner) => PureExpr::View(go(inner)),
        PureExpr::Ite(cond, then, otherwise) => PureExpr::Ite(go(cond), go(then), go(otherwise)),
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|a| replace_marker(a, target, with))
                .collect(),
        },
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: go(receiver),
            method: method.clone(),
            args: args
                .iter()
                .map(|a| replace_marker(a, target, with))
                .collect(),
        },
        other => other.clone(),
    }
}

/// `comparison` with its placeholders stated as cases around it: the
/// conjunction, over the oracle's cases, of `case ==> comparison at that
/// case's value`. The comparison is a boolean, so the conjunction stands
/// where it stood; the solver then meets no `ite` of integers, whose
/// refutation its strict certificate does not replay.
fn lift_comparison(comparison: PureExpr, budget: usize) -> PureExpr {
    let Some(marker) = find_liftable(&comparison) else {
        return comparison;
    };
    let Some((wrap, value)) = Wrap::of_marker(marker) else {
        return comparison;
    };
    let cases = wrap.cases(value);
    if cases.len() > budget {
        return comparison;
    }
    let budget = budget / cases.len();
    let lifted: Vec<PureExpr> = cases
        .into_iter()
        .map(|(cond, case_value)| {
            let at_case = replace_marker(&comparison, marker, &case_value);
            binop(cond, BinOp::Implies, lift_comparison(at_case, budget))
        })
        .collect();
    let mut lifted = lifted.into_iter();
    let first = lifted.next().unwrap_or(PureExpr::Bool(true));
    lifted.fold(first, |all, case| binop(all, BinOp::And, case))
}

const fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

/// Every comparison of `expr` with its placeholders lifted, innermost
/// first; then every placeholder left (one under `old` or a binder inside a
/// comparison, or outside any comparison) as its term.
fn settle(expr: &PureExpr) -> PureExpr {
    let lifted = expr.rewrite_bottom_up(|node| match node {
        PureExpr::BinOp(_, op, _) if is_comparison(op) => lift_comparison(node, MAX_LIFTED_CASES),
        other => other,
    });
    lifted.rewrite_bottom_up(|node| match Wrap::of_marker(&node) {
        Some((wrap, value)) => wrap.as_term(value),
        None => node,
    })
}

impl ContractParser<'_> {
    /// `product`, a product of two values of `ty`, reduced into `ty`'s range
    /// (Euclidean `mod`, shifted for a signed type).
    fn wrap_product(product: PureExpr, ty: MachineInt) -> PureExpr {
        let modulus = constant(ty.modulus());
        if ty.signed {
            let half = constant(-ty.min());
            binop(
                binop(
                    binop(product, BinOp::Add, half.clone()),
                    BinOp::Mod,
                    modulus,
                ),
                BinOp::Sub,
                half,
            )
        } else {
            binop(product, BinOp::Mod, modulus)
        }
    }

    /// The parsed text with every wrapping operator in its final form
    /// ([`settle`]), or a refusal of a text that spells the placeholder.
    pub(super) fn settle_wraps(&self, expr: PureExpr) -> Result<PureExpr, ParseError> {
        if let Some(position) = self.input.find(WRAP_MARKER_PREFIX) {
            return Err(ParseError {
                message: format!("`{WRAP_MARKER_PREFIX}` is reserved for trust-wp (D-232)"),
                position,
            });
        }
        if !self.written_sites.iter().any(|site| site.wrapped) {
            return Ok(expr);
        }
        Ok(settle(&expr))
    }

    /// Refuse an integer literal operand `ty` has no value for: it would
    /// otherwise be read at a value the operator's type cannot hold.
    fn check_literal_operand(
        &self,
        operand: &PureExpr,
        op: ArithOp,
        ty: MachineInt,
        at: usize,
    ) -> Result<(), ParseError> {
        match literal_value(operand) {
            Some(value) if !(ty.min()..=ty.max()).contains(&value) => Err(ParseError {
                message: format!(
                    "the literal {value} beside `{}` on `{}` is not a value of `{}` (D-232)",
                    op.spelling(),
                    ty.name(),
                    ty.name()
                ),
                position: at,
            }),
            _ => Ok(()),
        }
    }

    fn arith_refusal(op: ArithOp, at: usize, why: &str) -> ParseError {
        ParseError {
            message: format!(
                "`{}` in this clause has no reading trust-wp can give it: {why} (D-232)",
                op.spelling()
            ),
            position: at,
        }
    }

    /// Whether any reading of this parse may ask whether an operand is an
    /// `Int` by its syntax: never when nothing is installed.
    fn needs_int_syntax(&self) -> bool {
        !matches!(self.arith, TextArith::Uninstalled)
    }

    /// The reading of a kind for this parse, and a refusal when it reads none.
    fn read_written_operator(
        &self,
        op: ArithOp,
        int_syntax: bool,
        at: usize,
    ) -> Result<Option<MachineInt>, ParseError> {
        match self.arith.reading(op).reading {
            OpReading::Mathematical => Ok(None),
            OpReading::Wrapping(ty) => Ok(Some(ty)),
            OpReading::Syntactic if int_syntax => Ok(None),
            OpReading::Syntactic => Err(Self::arith_refusal(
                op,
                at,
                "the clause is written where no type check says what its operands are, and \
                 its syntax does not make one an `Int`; on machine integers the oracle's \
                 operator wraps",
            )),
            OpReading::Refused(why) => Err(Self::arith_refusal(op, at, &why)),
        }
    }

    /// `left op right` for a binary operator the text writes at `at`.
    pub(super) fn written_binop(
        &mut self,
        left: PureExpr,
        op: BinOp,
        right: PureExpr,
        at: usize,
    ) -> Result<PureExpr, ParseError> {
        let Some(kind) = ArithOp::of_binop(op) else {
            return Ok(binop(left, op, right));
        };
        let int_syntax = self.needs_int_syntax() && binary_is_int_syntax(&left, &right);
        let ty = self.read_written_operator(kind, int_syntax, at)?;
        self.written_sites.push(WrittenSite {
            op: kind,
            wrapped: ty.is_some(),
            int_syntax,
            at,
        });
        let Some(ty) = ty else {
            return Ok(binop(left, op, right));
        };
        self.check_literal_operand(&left, kind, ty, at)?;
        if matches!(kind, ArithOp::Shl | ArithOp::Shr) {
            // The amount has its own type: only the shifted operand is `ty`.
            return Self::written_shift(kind, left, &right, ty, at);
        }
        self.check_literal_operand(&right, kind, ty, at)?;
        Ok(match kind {
            ArithOp::Add => Wrap::Add(ty).marker(binop(left, op, right)),
            ArithOp::Sub => Wrap::Sub(ty).marker(binop(left, op, right)),
            ArithOp::Mul => Self::wrap_product(binop(left, op, right), ty),
            _ => {
                return Err(Self::arith_refusal(
                    kind,
                    at,
                    &format!(
                        "the oracle's `{}` on `{}` is not modelled",
                        kind.spelling(),
                        ty.name()
                    ),
                ))
            }
        })
    }

    /// `value << amount` or `value >> amount` on `ty` as the oracle reads it:
    /// the amount recast to `ty` (`of_int`, so taken modulo `2^bits`), then
    /// `lsl_bv`, `lsr_bv` or, on a signed type, `asr_bv`, each of which
    /// shifts every bit out at an amount of `bits` or more. A literal amount
    /// is a multiplication or a floor division by a constant; any other
    /// amount is refused.
    fn written_shift(
        kind: ArithOp,
        value: PureExpr,
        amount: &PureExpr,
        ty: MachineInt,
        at: usize,
    ) -> Result<PureExpr, ParseError> {
        let Some(amount) = literal_value(amount) else {
            return Err(Self::arith_refusal(
                kind,
                at,
                &format!(
                    "the oracle's `{}` on `{}` by an amount that is not a literal is its \
                     bit-vector shift, which trust-wp's reading of the clause does not model",
                    kind.spelling(),
                    ty.name()
                ),
            ));
        };
        let amount = amount.rem_euclid(ty.modulus());
        let factor = || constant(1_i128 << amount);
        Ok(if amount >= i128::from(ty.bits) {
            if kind == ArithOp::Shr && ty.signed {
                // An arithmetic shift of every bit out leaves the sign.
                ite(
                    binop(value, BinOp::Lt, PureExpr::Int(0)),
                    PureExpr::Int(-1),
                    PureExpr::Int(0),
                )
            } else {
                PureExpr::Int(0)
            }
        } else if kind == ArithOp::Shl {
            Self::wrap_product(binop(value, BinOp::Mul, factor()), ty)
        } else {
            // Euclidean division by a positive constant is the floor: the
            // logical shift of an unsigned value and the arithmetic shift of
            // a signed one.
            binop(value, BinOp::Div, factor())
        })
    }

    /// `-operand` for a unary minus the text writes at `at`. A minus on an
    /// integer literal is a negative literal, not an operator.
    pub(super) fn written_neg(
        &mut self,
        operand: PureExpr,
        at: usize,
    ) -> Result<PureExpr, ParseError> {
        if matches!(operand, PureExpr::Int(_)) {
            return Ok(PureExpr::UnOp(UnOp::Neg, Arc::new(operand)));
        }
        let int_syntax = self.needs_int_syntax() && is_int_syntax(&operand);
        let ty = self.read_written_operator(ArithOp::Neg, int_syntax, at)?;
        self.written_sites.push(WrittenSite {
            op: ArithOp::Neg,
            wrapped: ty.is_some(),
            int_syntax,
            at,
        });
        let Some(ty) = ty else {
            return Ok(PureExpr::UnOp(UnOp::Neg, Arc::new(operand)));
        };
        Ok(Wrap::Neg(ty).marker(operand))
    }

    /// `!operand` for a `!` the text writes at `at`.
    pub(super) fn written_not(
        &mut self,
        operand: PureExpr,
        at: usize,
    ) -> Result<PureExpr, ParseError> {
        // Boolean negation by default: a reading of `!` other than the
        // connective is only ever a refusal.
        if let OpReading::Refused(why) = self.arith.reading(ArithOp::Not).reading {
            return Err(Self::arith_refusal(ArithOp::Not, at, &why));
        }
        Ok(PureExpr::UnOp(UnOp::Not, Arc::new(operand)))
    }

    /// After the whole text is parsed: every kind read at a type was built
    /// exactly as often as the type check holds it. A parse that built more
    /// (a desugaring, a duplicated operand) or fewer (a dropped subterm) of a
    /// wrapped kind has an operator the type check did not type, so the
    /// clause is refused; one of a mathematical kind keeps only operators
    /// whose syntax fixes an `Int`.
    pub(super) fn check_written_arith(&self) -> Result<(), ParseError> {
        if self.arith_nested {
            return Ok(());
        }
        let TextArith::Read(text) = &self.arith else {
            return Ok(());
        };
        for (op, kind) in &text.kinds {
            let Some(typed) = kind.typed else { continue };
            let sites: Vec<&WrittenSite> =
                self.written_sites.iter().filter(|s| s.op == *op).collect();
            if sites.len() == typed {
                continue;
            }
            let why = format!(
                "the clause's type check holds {typed} `{}` and the parse read {}",
                op.spelling(),
                sites.len()
            );
            if let Some(site) = sites.iter().find(|s| s.wrapped || !s.int_syntax) {
                return Err(Self::arith_refusal(*op, site.at, &why));
            }
            if sites.is_empty() && matches!(kind.reading, OpReading::Wrapping(_)) {
                return Err(Self::arith_refusal(*op, 0, &why));
            }
        }
        Ok(())
    }

    /// Hand a nested parser (a generic argument's) this parser's reading.
    pub(super) fn share_arith_with(&self, nested: &mut ContractParser<'_>) {
        nested.arith = self.arith.clone();
        nested.arith_nested = true;
    }

    /// Take back what a nested parser built.
    pub(super) fn absorb_arith(&mut self, nested: &ContractParser<'_>, offset: usize) {
        self.written_sites
            .extend(nested.written_sites.iter().map(|site| WrittenSite {
                at: site.at + offset,
                ..*site
            }));
    }
}

#[cfg(test)]
#[path = "machine_arith_tests.rs"]
mod tests;
