// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Reference levels the text writes and the AST has no node for: a borrow
//! (`&e`, `&mut e`), a binding by reference (`ref x`, `ref mut x`) and a
//! pattern that matches through a reference (`&p`, `&mut p`).
//!
//! While a clause is parsed each of these is a marker in the AST, so a level
//! is tracked by structure, through parentheses, nested borrows, `let` and
//! every branch of an `if` or `match`:
//! - `*` of a borrow is the borrowed value (`*&e`, `*(&e)`, `**(& &e)` are
//!   `e`), and so is `*r` of a name a `let` binds to a borrow (`let r = &e;
//!   *r`, `let ref r = e; *r`), and `*` of an `if` or `match` every branch of
//!   which is a borrow;
//! - `let &p = e` (`&mut p`) matches `p` against `*e`, and `let ref x @ p =
//!   e` binds `x` to a borrow of `e` and matches `p` against `e` itself;
//! - `^` of a borrow, of a name bound to one, or of an operand whose
//!   resolution drops a borrow, is a parse error: `^` of a shared reference
//!   has no reading, and the final value of a reborrow is a reference, where
//!   the AST would read the final value of the borrowed operand itself;
//! - `*` or `^` of an `if` or `match` whose branches are at different levels
//!   is a parse error: it would read each branch at another level.
//!
//! [`ContractParser::resolve_references`] removes every marker from a
//! finished parse. A borrow no `*` read through is kept as its operand, a
//! reference level below the text, and recorded
//! ([`super::super::ContractElisions::dropped_borrows`]); a reference pattern
//! outside a `let` (a `match` arm, `let … else`, `if let`, a closure
//! parameter) is kept as its inner pattern and recorded
//! ([`super::super::ContractElisions::dropped_reference_patterns`]). Every
//! consumer reads the same AST, so no lane reads a dereference or a final
//! value one reference level off; a consumer that reads sorts refuses what
//! was recorded.

use std::sync::Arc;

use super::super::{ContractParser, ParseError};
use crate::formula::{MatchArm, Pattern, PureExpr};

/// The call a borrow is while the parse is in progress: `&e` is
/// `__trust_wp_borrow(e, i)`, `i` indexing [`ContractParser::references`].
const BORROW_MARKER: &str = "__trust_wp_borrow";
/// The constructor a pattern `&p` (`&mut p`) is while the parse is in
/// progress: `__trust_wp_deref_pattern#i(p)`.
const DEREF_PATTERN_MARKER: &str = "__trust_wp_deref_pattern#";
/// The constructor a binding by reference `ref x` (`ref mut x`) is while the
/// parse is in progress: `__trust_wp_by_reference#i(x)`.
const BY_REFERENCE_MARKER: &str = "__trust_wp_by_reference#";

/// A pattern that writes a reference level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReferenceSite {
    /// `ref x`, `ref mut x`: `x` binds a reference to the matched value.
    ByReference,
    /// `&p`, `&mut p`: `p` matches the referent.
    DerefPattern,
}

/// A reference level the text writes (a borrow, or a reference pattern), by
/// source range.
#[derive(Debug, Clone, Copy)]
pub(in crate::contract_parser) struct Reference {
    start: usize,
    end: usize,
}

/// How a finished parse dropped a reference level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::contract_parser) enum Dropped {
    /// A reference the AST keeps as its operand.
    Borrow,
    /// A reference pattern the AST keeps as its inner pattern.
    Pattern,
}

/// A borrow marker's operand and reference index.
fn as_borrow(expr: &PureExpr) -> Option<(&PureExpr, usize)> {
    match expr {
        PureExpr::LogicFnCall { name, args } if name == BORROW_MARKER => match args.as_slice() {
            [operand, PureExpr::Int(index)] => Some((operand, usize::try_from(*index).ok()?)),
            _ => None,
        },
        _ => None,
    }
}

fn borrow_marker(operand: PureExpr, index: usize) -> PureExpr {
    PureExpr::LogicFnCall {
        name: BORROW_MARKER.to_string(),
        args: vec![
            operand,
            PureExpr::Int(i64::try_from(index).unwrap_or(i64::MAX)),
        ],
    }
}

fn reference_marker(site: ReferenceSite, index: usize, inner: Pattern) -> Pattern {
    let marker = match site {
        ReferenceSite::DerefPattern => DEREF_PATTERN_MARKER,
        ReferenceSite::ByReference => BY_REFERENCE_MARKER,
    };
    Pattern::Constructor {
        name: format!("{marker}{index}"),
        inner: Some(Box::new(inner)),
    }
}

/// A reference pattern marker's site, reference index and inner pattern.
fn as_reference_pattern(pattern: &Pattern) -> Option<(ReferenceSite, usize, &Pattern)> {
    let Pattern::Constructor {
        name,
        inner: Some(inner),
    } = pattern
    else {
        return None;
    };
    let (site, index) = if let Some(index) = name.strip_prefix(DEREF_PATTERN_MARKER) {
        (ReferenceSite::DerefPattern, index)
    } else {
        (
            ReferenceSite::ByReference,
            name.strip_prefix(BY_REFERENCE_MARKER)?,
        )
    };
    Some((site, index.parse().ok()?, inner))
}

/// `pattern` with every reference-level marker replaced by its inner
/// pattern.
fn unmark_pattern(pattern: Pattern) -> Pattern {
    if let Some((_, _, inner)) = as_reference_pattern(&pattern) {
        return unmark_pattern(inner.clone());
    }
    match pattern {
        Pattern::Constructor { name, inner } => Pattern::Constructor {
            name,
            inner: inner.map(|inner| Box::new(unmark_pattern(*inner))),
        },
        Pattern::Alias { alias, pattern } => Pattern::Alias {
            alias,
            pattern: Box::new(unmark_pattern(*pattern)),
        },
        Pattern::Tuple(elements) => {
            Pattern::Tuple(elements.into_iter().map(unmark_pattern).collect())
        }
        Pattern::Wildcard | Pattern::Binding(_) | Pattern::Literal(_) => pattern,
    }
}

/// `pattern` below its outermost reference patterns: what a `let` of it
/// binds, whatever levels it matches through.
pub(in crate::contract_parser) fn peel_reference_patterns(pattern: &Pattern) -> &Pattern {
    match as_reference_pattern(pattern) {
        Some((_, _, inner)) => peel_reference_patterns(inner),
        None => pattern,
    }
}

/// `*operand`: the borrowed value when `operand` is a borrow.
pub(in crate::contract_parser) fn dereference(operand: PureExpr) -> PureExpr {
    match as_borrow(&operand) {
        Some((borrowed, _)) => borrowed.clone(),
        None => PureExpr::Deref(Arc::new(operand)),
    }
}

/// `let pattern = value` for a reference pattern: the pattern it leaves and
/// the value that pattern matches. `&p` matches `p` against `*value`, and
/// `ref x` binds `x` to a borrow of `value`.
pub(in crate::contract_parser) fn match_through_reference(
    pattern: &Pattern,
    value: PureExpr,
) -> Option<(Pattern, PureExpr)> {
    let (site, index, inner) = as_reference_pattern(pattern)?;
    let value = match site {
        ReferenceSite::DerefPattern => dereference(value),
        ReferenceSite::ByReference => borrow_marker(value, index),
    };
    Some((inner.clone(), value))
}

/// The reference levels a value has that the AST dropped.
#[derive(Debug, Clone, Default)]
struct Levels {
    /// Innermost first, each level the borrows that write it: one per branch
    /// of an `if` or `match` whose every branch is a borrow at that level.
    levels: Vec<Vec<usize>>,
    /// Borrows one branch of the value writes and another does not
    /// (`if c { &p } else { q }`): `*` or `^` of the value would read each
    /// branch at a different reference level. Already recorded as dropped.
    uneven: Vec<usize>,
}

impl Levels {
    fn none() -> Self {
        Self::default()
    }

    fn is_empty(&self) -> bool {
        self.levels.is_empty() && self.uneven.is_empty()
    }
}

/// A name a binder introduces, with the reference levels its value has that
/// the AST dropped (none, for every binder but a `let` of a borrow).
type LevelScope = Vec<(String, Levels)>;

fn pattern_has_reference(pattern: &Pattern) -> bool {
    as_reference_pattern(pattern).is_some()
        || match pattern {
            Pattern::Constructor { inner, .. } => {
                inner.as_deref().is_some_and(pattern_has_reference)
            }
            Pattern::Alias { pattern, .. } => pattern_has_reference(pattern),
            Pattern::Tuple(elements) => elements.iter().any(pattern_has_reference),
            Pattern::Wildcard | Pattern::Binding(_) | Pattern::Literal(_) => false,
        }
}

/// Whether matching `pattern` cannot fail, whatever value of the matched
/// type it meets: names, `_`, aliases, tuples and reference patterns of
/// these.
fn cannot_fail(pattern: &Pattern) -> bool {
    if let Some((_, _, inner)) = as_reference_pattern(pattern) {
        return cannot_fail(inner);
    }
    match pattern {
        Pattern::Wildcard | Pattern::Binding(_) => true,
        Pattern::Alias { pattern, .. } => cannot_fail(pattern),
        Pattern::Tuple(elements) => elements.iter().all(cannot_fail),
        Pattern::Literal(_) | Pattern::Constructor { .. } => false,
    }
}

/// Whether `expr` holds a marker, or reads a name `scope` binds to a borrow
/// (shadowing aside, which only costs a descent).
fn touches_levels(expr: &PureExpr, scope: &LevelScope) -> bool {
    expr.any_recursive(|node| match node {
        PureExpr::Var(name, _) => scope
            .iter()
            .any(|(bound, levels)| bound == name && !levels.is_empty()),
        PureExpr::Match { arms, .. } => arms.iter().any(|arm| pattern_has_reference(&arm.pattern)),
        node => as_borrow(node).is_some(),
    })
}

impl ContractParser<'_> {
    /// Every kind of node `expr` holds as the text writes it, reading
    /// through the reference-level markers (a borrow is its operand's kinds,
    /// a reference pattern its inner pattern's: [`crate::contract_parser::PatternForm`]
    /// records the level itself).
    pub(in crate::contract_parser) fn written_kinds(
        &self,
        expr: &PureExpr,
    ) -> std::collections::BTreeSet<crate::formula::elaborate::NodeKind> {
        let unmarked = expr.rewrite_bottom_up(|node| match as_borrow(&node) {
            Some((operand, _)) => operand.clone(),
            None => match node {
                PureExpr::Match { scrutinee, arms } => PureExpr::Match {
                    scrutinee,
                    arms: arms
                        .into_iter()
                        .map(|arm| MatchArm {
                            pattern: unmark_pattern(arm.pattern),
                            body: arm.body,
                        })
                        .collect(),
                },
                node => node,
            },
        });
        crate::formula::elaborate::node_kinds(&unmarked)
    }

    fn reference_text(&self, index: usize) -> &str {
        self.references.get(index).map_or("", |reference| {
            self.input
                .get(reference.start..reference.end)
                .unwrap_or("")
                .trim()
        })
    }

    /// Record a reference level the text writes from `start` to here.
    fn record_reference(&mut self, start: usize) -> usize {
        let index = self.references.len();
        self.references.push(Reference {
            start,
            end: self.position,
        });
        index
    }

    /// `&operand` (`&mut operand`), whose `&` starts at `start` and whose
    /// operand the parser just consumed.
    pub(in crate::contract_parser) fn borrow(
        &mut self,
        start: usize,
        operand: PureExpr,
    ) -> PureExpr {
        let index = self.record_reference(start);
        borrow_marker(operand, index)
    }

    /// A reference pattern `&p` (`&mut p`) starting at `start` whose inner
    /// pattern the parser just consumed.
    pub(in crate::contract_parser) fn reference_pattern(
        &mut self,
        start: usize,
        inner: Pattern,
    ) -> Pattern {
        let index = self.record_reference(start);
        reference_marker(ReferenceSite::DerefPattern, index, inner)
    }

    /// A binding by reference starting at `start`: `ref name` (`ref mut
    /// name`), or `ref name @ subpattern`. Only `name` binds by reference;
    /// the subpattern matches the value itself. Matching `ref x @ p` against
    /// `v` is matching `x @ &p` against `&v`, which is the marker's reading:
    /// a binding by reference matches its inner pattern against a borrow of
    /// the value.
    pub(in crate::contract_parser) fn binding_by_reference(
        &mut self,
        start: usize,
        name: String,
        subpattern: Option<Pattern>,
    ) -> Pattern {
        let index = self.record_reference(start);
        let inner = match subpattern {
            None => Pattern::Binding(name),
            Some(subpattern) => Pattern::Alias {
                alias: name,
                pattern: Box::new(reference_marker(
                    ReferenceSite::DerefPattern,
                    index,
                    subpattern,
                )),
            },
        };
        reference_marker(ReferenceSite::ByReference, index, inner)
    }

    /// `^operand` (`final_value(operand)`), refused when `operand` is a
    /// borrow.
    pub(in crate::contract_parser) fn final_value(
        &self,
        operand: PureExpr,
        spelling: &str,
    ) -> Result<PureExpr, ParseError> {
        match as_borrow(&operand) {
            Some((_, index)) => Err(self.final_of_borrow(index, spelling, None)),
            None => Ok(PureExpr::Final(Arc::new(operand))),
        }
    }

    /// A call `ident(args)`, except that `view(e)` is the node `e@` is and
    /// `final_value(e)` the node `^e` is (refused of a borrow), whichever
    /// parser reads it: the view-syntax macro rewrites `e@` and `^e` to these
    /// calls, and sort inference reads the nodes, not a logic function.
    pub(in crate::contract_parser) fn call_or_reference_form(
        &self,
        ident: String,
        mut args: Vec<PureExpr>,
    ) -> Result<PureExpr, ParseError> {
        match (ident.as_str(), args.len()) {
            ("view", 1) => Ok(PureExpr::View(Arc::new(args.remove(0)))),
            ("final_value", 1) => self.final_value(args.remove(0), "final_value"),
            _ => Ok(PureExpr::LogicFnCall { name: ident, args }),
        }
    }

    fn final_of_borrow(&self, index: usize, spelling: &str, name: Option<&str>) -> ParseError {
        let borrow = self.reference_text(index);
        let of = match name {
            Some(name) => format!("`{name}`, bound to the borrow `{borrow}`,"),
            None => format!("the borrow `{borrow}`"),
        };
        ParseError {
            message: format!(
                "`{spelling}` of {of} has no reading: the contract logic drops the borrow, so it \
                 would read the final value of the borrowed operand itself"
            ),
            position: self.reference_start(index),
        }
    }

    /// `spelling` (`*` or `^`) of a value that is the borrow `index` in one
    /// branch of an `if` or `match` and not in another.
    fn uneven_borrow(&self, index: usize, spelling: &str) -> ParseError {
        ParseError {
            message: format!(
                "`{spelling}` of a value that is the borrow `{}` in one branch and not in another \
                 has no reading: the contract logic drops the borrow, so `{spelling}` would read \
                 that branch a reference level off",
                self.reference_text(index)
            ),
            position: self.reference_start(index),
        }
    }

    /// `^` of an operand whose resolution dropped the borrow `index`.
    fn final_over_dropped_borrow(&self, index: usize) -> ParseError {
        ParseError {
            message: format!(
                "`^` of an operand that holds the borrow `{}` has no reading: the contract logic \
                 drops the borrow, so the final value could be read a reference level off",
                self.reference_text(index)
            ),
            position: self.reference_start(index),
        }
    }

    fn reference_start(&self, index: usize) -> usize {
        self.references
            .get(index)
            .map_or(0, |reference| reference.start)
    }

    /// The borrow an annotation on `operand` would land on, as written: the
    /// value `operand` yields through `old`, a `let` body and every branch
    /// of an `if` or a `match`.
    pub(in crate::contract_parser) fn annotated_borrow(&self, operand: &PureExpr) -> Option<&str> {
        if let Some((_, index)) = as_borrow(operand) {
            return Some(self.reference_text(index));
        }
        match operand {
            PureExpr::Old(inner)
            | PureExpr::Let { body: inner, .. }
            | PureExpr::LetAssume { body: inner, .. }
            | PureExpr::LetObligation { body: inner, .. } => self.annotated_borrow(inner),
            PureExpr::Ite(_, then_expr, else_expr) => self
                .annotated_borrow(then_expr)
                .or_else(|| self.annotated_borrow(else_expr)),
            PureExpr::Match { arms, .. } => {
                arms.iter().find_map(|arm| self.annotated_borrow(&arm.body))
            }
            _ => None,
        }
    }

    /// `expr` as written, a borrow spelled as the text wrote it: for a
    /// refusal that quotes an operand before [`Self::resolve_references`]
    /// has removed its markers.
    pub(in crate::contract_parser) fn display(&self, expr: &PureExpr) -> String {
        expr.rewrite_bottom_up(|node| match as_borrow(&node) {
            Some((_, index)) => PureExpr::Var(self.reference_text(index).to_string(), None),
            None => match node {
                PureExpr::Match { scrutinee, arms } => PureExpr::Match {
                    scrutinee,
                    arms: arms
                        .into_iter()
                        .map(|arm| MatchArm {
                            pattern: self.display_pattern(arm.pattern),
                            body: arm.body,
                        })
                        .collect(),
                },
                node => node,
            },
        })
        .to_string()
    }

    fn display_pattern(&self, pattern: Pattern) -> Pattern {
        if let Some((_, index, _)) = as_reference_pattern(&pattern) {
            return Pattern::Binding(self.reference_text(index).to_string());
        }
        match pattern {
            Pattern::Constructor { name, inner } => Pattern::Constructor {
                name,
                inner: inner.map(|inner| Box::new(self.display_pattern(*inner))),
            },
            Pattern::Alias { alias, pattern } => Pattern::Alias {
                alias,
                pattern: Box::new(self.display_pattern(*pattern)),
            },
            Pattern::Tuple(elements) => Pattern::Tuple(
                elements
                    .into_iter()
                    .map(|element| self.display_pattern(element))
                    .collect(),
            ),
            Pattern::Wildcard | Pattern::Binding(_) | Pattern::Literal(_) => pattern,
        }
    }

    /// Take in the reference levels a parser of the text at `offset`
    /// recorded, and those its finished parse dropped.
    pub(in crate::contract_parser) fn absorb_references(
        &mut self,
        references: &[Reference],
        dropped: &[(usize, Dropped)],
        offset: usize,
    ) {
        let base = self.references.len();
        self.references
            .extend(references.iter().map(|reference| Reference {
                start: reference.start + offset,
                end: reference.end + offset,
            }));
        self.dropped_references
            .extend(dropped.iter().map(|&(index, how)| (index + base, how)));
    }

    fn drop_levels(&mut self, levels: &[usize], dropped: Dropped) {
        for &index in levels {
            self.drop_log.push(index);
            if !self
                .dropped_references
                .iter()
                .any(|&(recorded, _)| recorded == index)
            {
                self.dropped_references.push((index, dropped));
            }
        }
    }

    /// The written text of every reference level dropped as `dropped`.
    pub(in crate::contract_parser) fn dropped_texts(&self, dropped: Dropped) -> Vec<String> {
        self.dropped_references
            .iter()
            .filter(|&&(_, how)| how == dropped)
            .map(|&(index, _)| self.reference_text(index).to_string())
            .collect()
    }

    /// Remove every reference-level marker from a finished parse: `*` of a
    /// borrow, or of a name a `let` binds to one, reads through it, `^` of
    /// either refuses, and every other level is dropped and recorded.
    pub(in crate::contract_parser) fn resolve_references(
        &mut self,
        expr: &PureExpr,
    ) -> Result<PureExpr, ParseError> {
        if self.references.is_empty() {
            return Ok(expr.clone());
        }
        let mut scope = LevelScope::new();
        self.resolve_dropping(expr, &mut scope)
    }

    /// `expr` without markers, with the reference levels its value has that
    /// the AST dropped (a borrow's, or those of the name it is). A value
    /// flows out of a borrow, a name, `old`, the body of a `let`, and every
    /// branch of an `if` or a `match`; every other node's operands are
    /// dropped. A subtree that holds no marker and reads no name bound to a
    /// borrow is its own resolution.
    fn resolve_levels(
        &mut self,
        expr: &PureExpr,
        scope: &mut LevelScope,
    ) -> Result<(PureExpr, Levels), ParseError> {
        if !touches_levels(expr, scope) {
            return Ok((expr.clone(), Levels::none()));
        }
        if let Some((operand, index)) = as_borrow(expr) {
            let (operand, mut levels) = self.resolve_levels(operand, scope)?;
            levels.levels.push(vec![index]);
            return Ok((operand, levels));
        }
        match expr {
            PureExpr::Var(name, _) => Ok((expr.clone(), Self::levels_of(name, scope))),
            PureExpr::BinOp(left, op, right) => self.resolve_binop(left, *op, right, scope),
            PureExpr::Deref(operand) => self.resolve_deref(operand, scope),
            PureExpr::Final(operand) => self.resolve_final(operand, scope),
            PureExpr::Let { var, value, body } => self.resolve_let(var, value, body, scope),
            PureExpr::Ite(cond, then_expr, else_expr) => {
                self.resolve_ite(cond, then_expr, else_expr, scope)
            }
            PureExpr::Match { scrutinee, arms } => self.resolve_match(scrutinee, arms, scope),
            PureExpr::Old(_) | PureExpr::LetAssume { .. } | PureExpr::LetObligation { .. } => {
                self.resolve_passing(expr, scope)
            }
            _ => Ok((self.resolve_other(expr, scope)?, Levels::none())),
        }
    }

    /// Both operands' levels are dropped. Its own function, and a small one:
    /// a long chain of operators recurses through it once per operator.
    #[inline(never)]
    fn resolve_binop(
        &mut self,
        left: &PureExpr,
        op: crate::formula::BinOp,
        right: &PureExpr,
        scope: &mut LevelScope,
    ) -> Result<(PureExpr, Levels), ParseError> {
        let left = self.resolve_dropping(left, scope)?;
        let right = self.resolve_dropping(right, scope)?;
        Ok((
            PureExpr::BinOp(Arc::new(left), op, Arc::new(right)),
            Levels::none(),
        ))
    }

    #[inline(never)]
    fn levels_of(name: &str, scope: &LevelScope) -> Levels {
        scope
            .iter()
            .rev()
            .find(|(bound, _)| bound == name)
            .map_or_default(|(_, levels)| levels.clone())
    }

    /// `old(e)`, and the body of an assumption or obligation: the value is
    /// the operand's.
    #[inline(never)]
    fn resolve_passing(
        &mut self,
        expr: &PureExpr,
        scope: &mut LevelScope,
    ) -> Result<(PureExpr, Levels), ParseError> {
        Ok(match expr {
            PureExpr::Old(inner) => {
                let (inner, levels) = self.resolve_levels(inner, scope)?;
                (PureExpr::Old(Arc::new(inner)), levels)
            }
            PureExpr::LetAssume { assumption, body } => {
                let assumption = self.resolve_dropping(assumption, scope)?;
                let (body, levels) = self.resolve_levels(body, scope)?;
                (
                    PureExpr::LetAssume {
                        assumption: Arc::new(assumption),
                        body: Arc::new(body),
                    },
                    levels,
                )
            }
            PureExpr::LetObligation { obligation, body } => {
                let obligation = self.resolve_dropping(obligation, scope)?;
                let (body, levels) = self.resolve_levels(body, scope)?;
                (
                    PureExpr::LetObligation {
                        obligation: Arc::new(obligation),
                        body: Arc::new(body),
                    },
                    levels,
                )
            }
            _ => (self.resolve_other(expr, scope)?, Levels::none()),
        })
    }

    /// `*operand`: through the outermost level the operand's value has, else
    /// a dereference. A value that is a borrow in one branch and not in
    /// another has no reading: `*` would read each branch at a different
    /// level.
    #[inline(never)]
    fn resolve_deref(
        &mut self,
        operand: &PureExpr,
        scope: &mut LevelScope,
    ) -> Result<(PureExpr, Levels), ParseError> {
        let (operand, mut levels) = self.resolve_levels(operand, scope)?;
        if levels.levels.pop().is_some() {
            return Ok((operand, levels));
        }
        if let Some(&index) = levels.uneven.first() {
            return Err(self.uneven_borrow(index, "*"));
        }
        Ok((PureExpr::Deref(Arc::new(operand)), Levels::none()))
    }

    /// `^operand`, refused when the operand's value has a level the AST
    /// dropped (a borrow, a name bound to one, a branch that is one), or
    /// when resolving the operand dropped any borrow: the AST cannot say
    /// whether that borrow reaches the value `^` reads (`^id(&p)`).
    #[inline(never)]
    fn resolve_final(
        &mut self,
        operand: &PureExpr,
        scope: &mut LevelScope,
    ) -> Result<(PureExpr, Levels), ParseError> {
        let drops_before = self.drop_log.len();
        let (resolved, levels) = self.resolve_levels(operand, scope)?;
        if let Some(&index) = levels.levels.last().and_then(|level| level.first()) {
            let name = match operand {
                PureExpr::Var(name, _) => Some(name.as_str()),
                _ => None,
            };
            return Err(self.final_of_borrow(index, "^", name));
        }
        if let Some(&index) = levels.uneven.first() {
            return Err(self.uneven_borrow(index, "^"));
        }
        if let Some(&index) = self.drop_log.get(drops_before) {
            return Err(self.final_over_dropped_borrow(index));
        }
        Ok((PureExpr::Final(Arc::new(resolved)), Levels::none()))
    }

    #[inline(never)]
    fn resolve_let(
        &mut self,
        var: &str,
        value: &PureExpr,
        body: &PureExpr,
        scope: &mut LevelScope,
    ) -> Result<(PureExpr, Levels), ParseError> {
        let (value, levels) = self.resolve_levels(value, scope)?;
        scope.push((var.to_string(), levels));
        let body = self.resolve_levels(body, scope);
        scope.pop();
        let (body, levels) = body?;
        Ok((
            PureExpr::Let {
                var: var.to_string(),
                value: Arc::new(value),
                body: Arc::new(body),
            },
            levels,
        ))
    }

    #[inline(never)]
    fn resolve_ite(
        &mut self,
        cond: &PureExpr,
        then_expr: &PureExpr,
        else_expr: &PureExpr,
        scope: &mut LevelScope,
    ) -> Result<(PureExpr, Levels), ParseError> {
        let cond = self.resolve_dropping(cond, scope)?;
        let (then_expr, then_levels) = self.resolve_levels(then_expr, scope)?;
        let (else_expr, else_levels) = self.resolve_levels(else_expr, scope)?;
        Ok((
            PureExpr::Ite(Arc::new(cond), Arc::new(then_expr), Arc::new(else_expr)),
            self.merge_branches(vec![then_levels, else_levels]),
        ))
    }

    /// A first arm that cannot fail is the whole `match`, and binds as a
    /// `let` of its pattern does, reference patterns included (`match p {
    /// &t => .. }` binds `t` to `*p`). Otherwise each arm's pattern loses its
    /// reference patterns (recorded), and binds its names at no level.
    #[inline(never)]
    fn resolve_match(
        &mut self,
        scrutinee: &PureExpr,
        arms: &[MatchArm],
        scope: &mut LevelScope,
    ) -> Result<(PureExpr, Levels), ParseError> {
        if let Some(first) = arms.first() {
            if pattern_has_reference(&first.pattern) && cannot_fail(&first.pattern) {
                let bound = Self::desugar_let_pattern(
                    first.pattern.clone(),
                    scrutinee.clone(),
                    first.body.clone(),
                )?;
                return self.resolve_levels(&bound, scope);
            }
        }
        let scrutinee = self.resolve_dropping(scrutinee, scope)?;
        let mut resolved = Vec::with_capacity(arms.len());
        let mut branches = Vec::with_capacity(arms.len());
        for arm in arms {
            let pattern = self.strip_reference_patterns(&arm.pattern);
            let depth = scope.len();
            scope.extend(
                pattern
                    .bound_names()
                    .into_iter()
                    .map(|name| (name.to_string(), Levels::none())),
            );
            let body = self.resolve_levels(&arm.body, scope);
            scope.truncate(depth);
            let (body, levels) = body?;
            resolved.push(MatchArm { pattern, body });
            branches.push(levels);
        }
        Ok((
            PureExpr::Match {
                scrutinee: Arc::new(scrutinee),
                arms: resolved,
            },
            self.merge_branches(branches),
        ))
    }

    /// The levels a value with these branches has: each level every branch
    /// has, when the branches have as many. Branches at different levels
    /// drop theirs (recorded), and the value is uneven.
    fn merge_branches(&mut self, branches: Vec<Levels>) -> Levels {
        let mut uneven: Vec<usize> = branches
            .iter()
            .flat_map(|branch| branch.uneven.iter().copied())
            .collect();
        let depth = branches.first().map_or(0, |branch| branch.levels.len());
        if branches.iter().all(|branch| branch.levels.len() == depth) {
            let levels = (0..depth)
                .map(|at| {
                    branches
                        .iter()
                        .flat_map(|branch| branch.levels[at].iter().copied())
                        .collect()
                })
                .collect();
            return Levels { levels, uneven };
        }
        for branch in &branches {
            for level in &branch.levels {
                self.drop_levels(level, Dropped::Borrow);
                uneven.extend(level.iter().copied());
            }
        }
        Levels {
            levels: Vec::new(),
            uneven,
        }
    }

    /// Every node no value flows out of: each operand's levels are dropped.
    #[inline(never)]
    #[allow(clippy::too_many_lines)]
    fn resolve_other(
        &mut self,
        expr: &PureExpr,
        scope: &mut LevelScope,
    ) -> Result<PureExpr, ParseError> {
        Ok(match expr {
            PureExpr::UnOp(op, inner) => {
                PureExpr::UnOp(*op, Arc::new(self.resolve_dropping(inner, scope)?))
            }
            PureExpr::View(inner) => PureExpr::View(Arc::new(self.resolve_dropping(inner, scope)?)),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => self.resolve_method_call(receiver, method, args, scope)?,
            PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
                name: name.clone(),
                args: self.resolve_all(args, scope)?,
            },
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let (body, triggers) = self.resolve_under_binder(var, body, triggers, scope)?;
                PureExpr::Forall {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: Arc::new(body),
                    triggers,
                }
            }
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let (body, triggers) = self.resolve_under_binder(var, body, triggers, scope)?;
                PureExpr::Exists {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: Arc::new(body),
                    triggers,
                }
            }
            PureExpr::Closure { params, body } => {
                let depth = scope.len();
                scope.extend(
                    params
                        .iter()
                        .map(|(name, _)| (name.clone(), Levels::none())),
                );
                let body = self.resolve_dropping(body, scope);
                scope.truncate(depth);
                PureExpr::Closure {
                    params: params.clone(),
                    body: Arc::new(body?),
                }
            }
            // Resolved by `resolve_levels`, and leaves.
            PureExpr::Var(..)
            | PureExpr::Bool(_)
            | PureExpr::Int(_)
            | PureExpr::Float(_)
            | PureExpr::Deref(_)
            | PureExpr::Final(_)
            | PureExpr::Old(_)
            | PureExpr::BinOp(..)
            | PureExpr::Let { .. }
            | PureExpr::Ite(..)
            | PureExpr::Match { .. }
            | PureExpr::LetAssume { .. }
            | PureExpr::LetObligation { .. } => self.resolve_dropping(expr, scope)?,
        })
    }

    /// `receiver.method(args)`. A receiver whose value has a reference level
    /// the AST drops (`(&a).m()`, `r.m()` with `r` bound to `&a` or by `ref`)
    /// is a reference to Rust's method lookup, which starts at that
    /// reference's type and takes a method applying to it (the prelude's
    /// blanket `Invariant for &T`) before any method of the referent; every
    /// resolver would type the dropped receiver as the referent
    /// (method_call_borrowed_receiver_*_granted.rs). No reading of the call
    /// rests on that: it becomes the refusal marker, whatever it names.
    #[inline(never)]
    fn resolve_method_call(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        scope: &mut LevelScope,
    ) -> Result<PureExpr, ParseError> {
        let (receiver, levels) = self.resolve_levels(receiver, scope)?;
        let args = self.resolve_all(args, scope)?;
        if levels.is_empty() {
            return Ok(PureExpr::MethodCall {
                receiver: Arc::new(receiver),
                method: method.to_string(),
                args,
            });
        }
        for level in &levels.levels {
            self.drop_levels(level, Dropped::Borrow);
        }
        let mut call_args = Vec::with_capacity(args.len() + 1);
        call_args.push(receiver);
        call_args.extend(args);
        Ok(PureExpr::LogicFnCall {
            name: crate::logic::identity::logic_fn_unresolved_marker(method),
            args: call_args,
        })
    }

    /// `expr` without markers, any level its value has dropped.
    fn resolve_dropping(
        &mut self,
        expr: &PureExpr,
        scope: &mut LevelScope,
    ) -> Result<PureExpr, ParseError> {
        let (resolved, levels) = self.resolve_levels(expr, scope)?;
        for level in &levels.levels {
            self.drop_levels(level, Dropped::Borrow);
        }
        Ok(resolved)
    }

    fn resolve_all(
        &mut self,
        exprs: &[PureExpr],
        scope: &mut LevelScope,
    ) -> Result<Vec<PureExpr>, ParseError> {
        exprs
            .iter()
            .map(|expr| self.resolve_dropping(expr, scope))
            .collect()
    }

    fn resolve_under_binder(
        &mut self,
        var: &str,
        body: &PureExpr,
        triggers: &[Vec<PureExpr>],
        scope: &mut LevelScope,
    ) -> Result<(PureExpr, Vec<Vec<PureExpr>>), ParseError> {
        scope.push((var.to_string(), Levels::none()));
        let resolved = self.resolve_dropping(body, scope).and_then(|body| {
            let triggers = triggers
                .iter()
                .map(|group| self.resolve_all(group, scope))
                .collect::<Result<Vec<_>, _>>()?;
            Ok((body, triggers))
        });
        scope.pop();
        resolved
    }

    /// `pattern` with every reference pattern replaced by its inner pattern,
    /// each recorded: outside a `let` the AST has no node that reads through
    /// the reference.
    pub(in crate::contract_parser) fn strip_reference_patterns(
        &mut self,
        pattern: &Pattern,
    ) -> Pattern {
        if let Some((_, index, inner)) = as_reference_pattern(pattern) {
            self.drop_levels(&[index], Dropped::Pattern);
            return self.strip_reference_patterns(inner);
        }
        match pattern {
            Pattern::Constructor { name, inner } => Pattern::Constructor {
                name: name.clone(),
                inner: inner
                    .as_deref()
                    .map(|inner| Box::new(self.strip_reference_patterns(inner))),
            },
            Pattern::Alias { alias, pattern } => Pattern::Alias {
                alias: alias.clone(),
                pattern: Box::new(self.strip_reference_patterns(pattern)),
            },
            Pattern::Tuple(elements) => Pattern::Tuple(
                elements
                    .iter()
                    .map(|element| self.strip_reference_patterns(element))
                    .collect(),
            ),
            Pattern::Wildcard | Pattern::Binding(_) | Pattern::Literal(_) => pattern.clone(),
        }
    }
}
