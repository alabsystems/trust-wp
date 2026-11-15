// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract expression parser
//!
//! Parses contract strings (e.g., "x > 0", "result == x + 1") into
//! `PureExpr` AST nodes for verification condition generation.

use std::{error::Error, fmt, iter::Peekable, str::Chars, sync::Arc};

use crate::formula::{PureExpr, SpannedExpr};

mod helpers;
pub mod machine_arith;
mod spanned;
pub mod spelled_types;
mod unspanned;

#[cfg(test)]
mod tests;

/// Internal wrapper used to preserve turbofish generic arguments until the
/// driver can classify type-only generics vs. const generics. (#1635)
pub const TURBOFISH_ARG_WRAPPER_NAME: &str = "__trust_wp_turbofish_arg";

/// The syntactic position of a type the clause text writes (or elides).
///
/// A cast is lowered to the exact integer arithmetic of Rust's `as`, or the
/// clause is refused (see `helpers::casts`); an ascription or a `let`
/// annotation to an integer type or `bool` is kept as the sort of its operand.
/// Every other written type is mapped to an SMT sort where the parser can and
/// otherwise dropped: `(e : T)` for any other `T` and an aliased or tuple
/// binder `forall<v: Wd>` leave no trace of `T` in the [`PureExpr`], and a
/// machine-integer binder `forall<v: u8>` leaves only its range (D-203).
/// Consumers whose verdict depends on a type the AST does not carry (trait
/// refinement, the pure-expr bundle claim decoder) read these records and
/// refuse it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WrittenTypeSite {
    /// `expr as T`
    Cast,
    /// `expr : T`
    Ascription,
    /// `forall<v: T>` / `exists<v: T>`; elided for `forall<v>`.
    QuantifierBinder,
    /// `|p: T|`; elided for `|p|` and destructuring parameters.
    ClosureParam,
    /// `let p: T = ..`
    LetBinding,
    /// A literal type suffix: `255u8`, `1int`, `1.5f32`. The literal's value
    /// is kept (a value outside the suffix's type is refused) and the suffix
    /// dropped, although the suffix fixes the literal's type and so the
    /// meaning of the operators around it (`255u8 + 1u8 == 0u8` holds,
    /// `255u16 + 1u16 == 0u16` does not).
    LiteralSuffix,
}

crate::formula::listed_enum::listed_enum! {
    /// A form of pattern the text writes, which the AST desugars or keeps as
    /// a [`crate::formula::Pattern`] of another shape: recorded by the parser
    /// for a census of what a clause writes ([`parse_contract_census`]).
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum PatternForm {
        /// `_`
        Wildcard,
        /// `x`
        Binding,
        /// `mut x`
        MutBinding,
        /// `true`, `0`
        Literal,
        /// `(p, q)`
        Tuple,
        /// A tuple pattern inside a tuple pattern.
        NestedTuple,
        /// `(p,)`
        OneTuple,
        /// `(p)`: `p` parenthesized.
        Parenthesized,
        /// `Some(p)`, `None`
        Constructor,
        /// `S { a, b: p }`
        Struct,
        /// `..` in a constructor or struct pattern.
        Rest,
        /// `x @ p`
        Alias,
        /// `ref x`
        Ref,
        /// `ref mut x`
        RefMut,
        /// `ref x @ p`
        RefAlias,
        /// `&p`
        Reference,
        /// `&mut p`
        MutReference,
        /// `box p`
        Box,
        /// `p | q`: one `match` arm per alternative, sharing the body.
        Or,
    }
}

/// One type written (or elided) in clause text; see [`WrittenTypeSite`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WrittenType {
    pub site: WrittenTypeSite,
    /// The type text as written (trimmed), or `None` when the binder or
    /// parameter has no annotation. A destructuring closure parameter is
    /// recorded as elided.
    pub text: Option<String>,
}

/// Error during contract parsing
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "parse error at position {}: {}",
            self.position, self.message
        )
    }
}

impl Error for ParseError {}

/// Contract expression parser
// Grammar restrictions, call retention, and arithmetic nesting are independent
// contexts with different scopes; they do not form one parser state machine.
#[allow(clippy::struct_excessive_bools)]
pub(crate) struct ContractParser<'a> {
    input: &'a str,
    chars: Peekable<Chars<'a>>,
    position: usize,
    preserve_stmt_exprs: bool,
    /// Whether the text is a logic function's body, whose every evaluated
    /// call owes its callee's precondition: elaboration may drop no subterm
    /// that calls something (`resolve_aliases_keeping_calls`).
    keeps_evaluated_calls: bool,
    stmt_expr_counter: usize,
    /// When true, suppress struct literal parsing for uppercase identifiers
    /// followed by `{`. Mirrors Rust's `RESTRICTION_NO_STRUCT_LITERAL` for
    /// if/while/for conditions where `Ident {` would be ambiguous with the
    /// branch block. (#2331)
    no_struct_literals: bool,
    /// Every written or elided type the parse consumed, in source order
    /// (including types consumed by branches the parser later backtracked
    /// out of). Recorded unconditionally; read by
    /// [`parse_contract_written_types`].
    written_types: Vec<WrittenType>,
    /// Every statement a block drops from the AST, as written: an expression
    /// statement (`lemma(x);`), a `use` item, `let _ = e;` and a `let` whose
    /// pattern binds nothing. Recorded like `written_types`; not recorded
    /// when `preserve_stmt_exprs` keeps an expression statement.
    discarded_statements: Vec<String>,
    /// Fresh-name counter for the `let` a 64-bit cast binds its operand to.
    cast_counter: usize,
    /// Fresh-name counter for the parameter (`$cpN`) a destructuring closure
    /// parameter is.
    closure_param_counter: usize,
    /// The integer suffix the most recent integer literal carried, for the
    /// range check of that literal.
    last_int_suffix: Option<&'static str>,
    /// Every name an ascription or `let` annotation gave a sort, with that
    /// sort and where the annotation starts: the position a scope
    /// disagreement is reported at.
    annotated_names: Vec<(String, crate::formula::ExprSort, usize)>,
    /// Every `Int` or `bool` annotation the AST keeps no trace of, as
    /// written: one on an operand whose sort the parser neither records nor
    /// reads off its syntax (`(*p : Int)`, `let t: Int = *p`).
    unchecked_annotations: Vec<String>,
    /// Every reference level the text writes: a borrow, a binding by
    /// reference, a reference pattern (`helpers/borrows.rs`).
    references: Vec<helpers::borrows::Reference>,
    /// The reference levels a finished parse dropped, each once, by index
    /// into `references`.
    dropped_references: Vec<(usize, helpers::borrows::Dropped)>,
    /// Every time a reference level was dropped, by index into
    /// `references`, repeats included: `^` refuses an operand whose
    /// resolution dropped any.
    drop_log: Vec<usize>,
    /// Every pattern form the parse read, repeats included.
    pattern_forms: Vec<PatternForm>,
    /// Every kind of node the finished parses held as written, before any
    /// desugaring `finish` does: taken only for [`parse_contract_census`].
    census: Option<std::collections::BTreeSet<crate::formula::elaborate::NodeKind>>,
    /// The names a bundle claim's summary facts relate: `finish` binds them
    /// to the binders the claim opens with AS WRITTEN, before alias
    /// resolution moves any quantifier (`formula::elaborate::facts`).
    fact_names: Option<std::collections::HashSet<String>>,
    /// What each arithmetic operator of this text is read as (D-232).
    arith: machine_arith::TextArith,
    /// A generic argument's parser: its operators are counted by the parser
    /// that owns the whole text.
    arith_nested: bool,
    /// Every arithmetic operator built from the text, in parse order.
    written_sites: Vec<machine_arith::WrittenSite>,
}

/// What a parse consumed that its [`PureExpr`] does not carry.
#[non_exhaustive]
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ContractElisions {
    /// Every written or elided type, in source order.
    pub written_types: Vec<WrittenType>,
    /// Every statement dropped from a block, as written (trimmed).
    pub discarded_statements: Vec<String>,
    /// Every `Int` or `bool` annotation dropped because its operand carries
    /// no sort the parser records or checks (a dereference, a call, a
    /// `match`), described as written: the AST reads such an operand at
    /// whatever sort its consumer infers, so the annotation states nothing
    /// anyone checks.
    pub unchecked_annotations: Vec<String>,
    /// Every borrow (`&e`, `&mut e`, and a `let`'s `ref x`) the AST drops,
    /// as written. One a `*` reads through is not dropped (`*&e` is `e`, and
    /// `let r = &e; *r` reads `e`); any other use keeps `e` where the text
    /// has a reference to it, so a consumer that reads sorts reads it one
    /// reference level off.
    pub dropped_borrows: Vec<String>,
    /// Every reference pattern (`&p`, `&mut p`, `ref x`, `ref mut x`, `ref x
    /// @ p`) the AST drops, as written: in a `match` arm, a `let … else`, an
    /// `if let` or a closure parameter the AST has no pattern node for it, so
    /// the binding matches the value a reference level off. A plain `let`
    /// models one (`let &t = p` binds `t` to `*p`, `let ref t = e` binds a
    /// borrow of `e`).
    pub dropped_reference_patterns: Vec<String>,
}

impl<'a> ContractParser<'a> {
    /// Create a new parser for the given input
    pub(crate) fn new(input: &'a str) -> Self {
        Self {
            input,
            chars: input.chars().peekable(),
            position: 0,
            preserve_stmt_exprs: false,
            keeps_evaluated_calls: false,
            stmt_expr_counter: 0,
            no_struct_literals: false,
            written_types: Vec::new(),
            discarded_statements: Vec::new(),
            cast_counter: 0,
            closure_param_counter: 0,
            last_int_suffix: None,
            annotated_names: Vec::new(),
            unchecked_annotations: Vec::new(),
            references: Vec::new(),
            dropped_references: Vec::new(),
            drop_log: Vec::new(),
            pattern_forms: Vec::new(),
            census: None,
            fact_names: None,
            arith: machine_arith::TextArith::for_input(input),
            arith_nested: false,
            written_sites: Vec::new(),
        }
    }

    /// A finished parse of `expr`: its reference levels resolved (refused
    /// where one has no reading), refused if an annotation disagrees with
    /// its name's binder, its aliases substituted and projections of
    /// branches pushed into the branches (`formula::elaborate`), else
    /// normalized.
    fn finish(&mut self, expr: PureExpr) -> Result<PureExpr, ParseError> {
        if self.census.is_some() {
            let written = self.written_kinds(&expr);
            self.census.get_or_insert_default().extend(written);
        }
        let expr = self.resolve_references(&expr)?;
        self.check_annotations_agree_with_scope(&expr)?;
        let expr = match &self.fact_names {
            Some(names) => {
                crate::formula::elaborate::bind_facts_to_the_written_prefix(&expr, names)
            }
            None => expr,
        };
        let expr = if self.keeps_evaluated_calls {
            crate::formula::elaborate::resolve_aliases_keeping_calls(&expr)
        } else {
            crate::formula::elaborate::resolve_aliases(&expr)
        };
        Ok(normalize_parsed_expr(expr))
    }

    /// What the parse consumed that its AST does not carry.
    fn elisions(self) -> ContractElisions {
        ContractElisions {
            dropped_borrows: self.dropped_texts(helpers::borrows::Dropped::Borrow),
            dropped_reference_patterns: self.dropped_texts(helpers::borrows::Dropped::Pattern),
            written_types: self.written_types,
            discarded_statements: self.discarded_statements,
            unchecked_annotations: self.unchecked_annotations,
        }
    }

    /// Parse the entire input as an expression.
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if the input contains:
    /// - Syntax errors (unmatched parentheses, invalid operators)
    /// - Unexpected characters after a valid expression
    /// - Invalid tokens
    pub(crate) fn parse(mut self) -> Result<PureExpr, ParseError> {
        self.parse_in_place()
    }

    /// [`Self::parse`], keeping the parser and what it recorded.
    pub(crate) fn parse_in_place(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        let expr = self.parse_expr()?;
        self.skip_whitespace();
        if self.chars.peek().is_some() {
            return Err(self.error("unexpected characters after expression"));
        }
        self.check_written_arith()?;
        let expr = self.settle_wraps(expr)?;
        self.finish(expr)
    }

    /// Parse the entire input as a block body (statements + trailing expression).
    ///
    /// Handles Creusot-style multi-statement `proof_assert!` blocks:
    /// ```text
    /// lemma_call();
    /// lemma_call2();
    /// assertion_expr
    /// ```
    ///
    /// Statement expressions (followed by `;`) are parsed and discarded (they
    /// serve as lemma invocation hints in Creusot but have no logical value in
    /// trust-wp's current architecture). The trailing expression without `;` is
    /// returned as the block's value.
    ///
    /// Falls back to single-expression parsing when no semicolons are present.
    pub(crate) fn parse_as_block(mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        let expr = self.parse_top_level_body()?;
        self.skip_whitespace();
        if self.chars.peek().is_some() {
            return Err(self.error("unexpected characters after expression"));
        }
        self.check_written_arith()?;
        let expr = self.settle_wraps(expr)?;
        self.finish(expr)
    }

    /// Parse the entire input as a block body and retain leading statements.
    pub(crate) fn parse_as_block_with_leading_exprs(
        mut self,
    ) -> Result<(Vec<PureExpr>, PureExpr), ParseError> {
        self.preserve_stmt_exprs = true;
        self.keeps_evaluated_calls = true;
        self.skip_whitespace();
        let expr = if self.peek() == Some('{') {
            self.try_consume("{");
            let parsed = self.parse_block_body_with_leading_exprs()?;
            self.skip_whitespace();
            if !self.try_consume("}") {
                return Err(self.error("expected '}'"));
            }
            parsed
        } else {
            self.parse_top_level_body_with_leading_exprs()?
        };
        self.skip_whitespace();
        if self.chars.peek().is_some() {
            return Err(self.error("unexpected characters after expression"));
        }
        self.check_written_arith()?;
        let leading = expr
            .0
            .into_iter()
            .map(|leading| {
                let leading = self.settle_wraps(leading)?;
                self.finish(leading)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let trailing = self.settle_wraps(expr.1)?;
        Ok((leading, self.finish(trailing)?))
    }

    /// Parse the entire input as an expression with source location tracking.
    ///
    /// Returns a [`SpannedExpr`] that records the span of the full expression
    /// within the input string.
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
    /// or unexpected characters.
    pub(crate) fn parse_spanned(mut self) -> Result<SpannedExpr, ParseError> {
        self.skip_whitespace();
        let expr = self.parse_expr_spanned()?;
        self.skip_whitespace();
        if self.chars.peek().is_some() {
            return Err(self.error("unexpected characters after expression"));
        }
        self.check_written_arith()?;
        let settled = self.settle_wraps(expr.expr)?;
        let expr = SpannedExpr {
            expr: self.finish(settled)?,
            span: expr.span,
        };
        Ok(expr)
    }

    /// Consume a type annotation at `site` and record its text.
    pub(crate) fn consume_written_type(
        &mut self,
        site: WrittenTypeSite,
    ) -> Result<Option<crate::formula::ExprSort>, ParseError> {
        self.consume_written_type_text(site).map(|(sort, _)| sort)
    }

    /// Consume a type annotation at `site`, record its text, and return the
    /// sort it maps to together with that text.
    pub(crate) fn consume_written_type_text(
        &mut self,
        site: WrittenTypeSite,
    ) -> Result<(Option<crate::formula::ExprSort>, String), ParseError> {
        let start = self.position;
        let sort = self.consume_type_annotation()?;
        let text = self.input[start..self.position].trim().to_string();
        self.refuse_shadowed_type(&text, start)?;
        self.written_types.push(WrittenType {
            site,
            text: Some(text.clone()),
        });
        Ok((sort, text))
    }

    /// Refuse a type that spells a name the crate under verification gives
    /// another meaning than the one the parser reads it with (D-202), binds
    /// to a type holding a machine integer the parser cannot see through
    /// (D-205), or a path through a module or a crate to an item the parser
    /// cannot see (D-206) (`spelled_types`).
    pub(crate) fn refuse_shadowed_type(&self, text: &str, at: usize) -> Result<(), ParseError> {
        if let Some(name) = spelled_types::first_shadowed(text) {
            return Err(Self::shadowed_type_error(text, &name, at));
        }
        if let Some(name) = spelled_types::first_machine_int_alias(text) {
            return Err(ParseError {
                message: format!(
                    "`{text}` spells `{name}`, which this crate binds to a type holding a machine \
                     integer (an alias, an import, an associated type or an impl's `Self`); a \
                     clause is read by the name it writes, so that integer's range is not known \
                     here and it is refused"
                ),
                position: at,
            });
        }
        match spelled_types::first_module_path(text) {
            Some(path) => Err(ParseError {
                message: format!(
                    "`{text}` names the type `{path}` by a path through a module or a crate; a \
                     clause is read by the names it writes, not through Rust's paths, so what \
                     that item is (an alias of a machine integer, whose range a binder must \
                     state, among others) is not known here and it is refused"
                ),
                position: at,
            }),
            None => Ok(()),
        }
    }

    /// `refuse_shadowed_type` for a path: only its head (or a qualified
    /// path's types) is read as a type.
    pub(crate) fn refuse_shadowed_path(&self, path: &str, at: usize) -> Result<(), ParseError> {
        match spelled_types::shadowed_path_head(path) {
            Some(name) => Err(Self::shadowed_type_error(path, &name, at)),
            None => Ok(()),
        }
    }

    fn shadowed_type_error(text: &str, name: &str, at: usize) -> ParseError {
        ParseError {
            message: format!(
                "`{text}` spells `{name}`, which this crate declares or imports with another \
                 meaning; a clause is read by the name it writes, not through Rust's scopes, so \
                 it is refused"
            ),
            position: at,
        }
    }

    /// Record a statement a block drops from the AST, written from `start`
    /// to the current position.
    pub(crate) fn note_discarded_statement(&mut self, start: usize) {
        let text = self.input[start..self.position].trim().to_string();
        self.discarded_statements.push(text);
    }

    /// Record a literal type suffix the parser consumed and discarded.
    pub(crate) fn note_literal_suffix(&mut self, suffix: &str) {
        self.written_types.push(WrittenType {
            site: WrittenTypeSite::LiteralSuffix,
            text: Some(suffix.to_string()),
        });
    }

    /// Record that a binder or parameter at `site` has no written type.
    pub(crate) fn note_elided_type(&mut self, site: WrittenTypeSite) {
        self.written_types.push(WrittenType { site, text: None });
    }

    pub(crate) fn wrap_stmt_expr(&mut self, value: PureExpr, body: PureExpr) -> PureExpr {
        let idx = self.stmt_expr_counter;
        self.stmt_expr_counter = self.stmt_expr_counter.saturating_add(1);
        PureExpr::Let {
            var: format!("$stmt{idx}"),
            value: Arc::new(value),
            body: Arc::new(body),
        }
    }
}

fn normalize_parsed_expr(expr: PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Var(name, sort) => {
            let name = normalize_qualified_path_spacing(name);
            PureExpr::Var(name, sort)
        }
        PureExpr::LogicFnCall { name, args } => {
            let name = normalize_qualified_path_spacing(name);
            PureExpr::LogicFnCall { name, args }
        }
        node => node,
    })
}

fn normalize_qualified_path_spacing(name: String) -> String {
    if name.starts_with('<') && name.contains(">as ") {
        name.replace(">as ", "> as ")
    } else {
        name
    }
}

/// Parse a contract expression string into a [`PureExpr`] AST.
///
/// # Errors
///
/// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
/// or unexpected characters.
pub fn parse_contract(input: &str) -> Result<PureExpr, ParseError> {
    ContractParser::new(input).parse()
}

/// Parse a contract clause exactly as [`parse_contract_spanned`] does and
/// return every type the text writes or elides (casts, ascriptions, binder,
/// closure-parameter and `let` annotations, literal suffixes). The AST
/// carries a cast as Rust's `as` and an integer or `bool` annotation as a
/// sort; every other written type it does not carry.
///
/// # Errors
///
/// Returns a [`ParseError`] exactly when [`parse_contract_spanned`] does.
pub fn parse_contract_written_types(input: &str) -> Result<Vec<WrittenType>, ParseError> {
    let mut parser = ContractParser::new(input);
    parser.skip_whitespace();
    let expr = parser.parse_expr_spanned()?;
    parser.skip_whitespace();
    if parser.chars.peek().is_some() {
        return Err(parser.error("unexpected characters after expression"));
    }
    parser.check_written_arith()?;
    let expr = parser.settle_wraps(expr.expr)?;
    parser.finish(expr)?;
    Ok(parser.written_types)
}

/// Parse a contract clause exactly as [`parse_contract`] does, and return
/// with its AST everything the parse consumed that the AST does not carry
/// ([`ContractElisions`]).
///
/// # Errors
///
/// Returns a [`ParseError`] exactly when [`parse_contract`] does.
pub fn parse_contract_with_elisions(
    input: &str,
) -> Result<(PureExpr, ContractElisions), ParseError> {
    parse_with_elisions(ContractParser::new(input))
}

/// [`parse_contract_with_elisions`] for a logic function's body read as one
/// expression: like [`parse_contract_body_with_leading_exprs`], it drops no
/// subterm that evaluates a call.
///
/// # Errors
///
/// Returns a [`ParseError`] exactly when [`parse_contract`] does.
pub fn parse_logic_body_expr_with_elisions(
    input: &str,
) -> Result<(PureExpr, ContractElisions), ParseError> {
    let mut parser = ContractParser::new(input);
    parser.keeps_evaluated_calls = true;
    parse_with_elisions(parser)
}

fn parse_with_elisions(
    mut parser: ContractParser<'_>,
) -> Result<(PureExpr, ContractElisions), ParseError> {
    parser.skip_whitespace();
    let expr = parser.parse_expr()?;
    parser.skip_whitespace();
    if parser.chars.peek().is_some() {
        return Err(parser.error("unexpected characters after expression"));
    }
    parser.check_written_arith()?;
    let expr = parser.settle_wraps(expr)?;
    let expr = parser.finish(expr)?;
    Ok((expr, parser.elisions()))
}

/// Parse a bundle claim exactly as [`parse_contract_with_elisions`] does,
/// with every binder of a name in `fact_names` renamed apart except the
/// opening universal quantifiers' first binding of it, decided on the claim
/// as written: a summary fact relating those names is about the obligation's
/// own values, and no other binder of them
/// ([`crate::formula::elaborate::bind_facts_to_the_written_prefix`]).
///
/// # Errors
///
/// Returns a [`ParseError`] exactly when [`parse_contract`] does.
pub fn parse_claim_binding_facts(
    input: &str,
    fact_names: &std::collections::HashSet<String>,
) -> Result<(PureExpr, ContractElisions), ParseError> {
    let mut parser = ContractParser::new(input);
    parser.fact_names = Some(fact_names.clone());
    parser.skip_whitespace();
    let expr = parser.parse_expr()?;
    parser.skip_whitespace();
    if parser.chars.peek().is_some() {
        return Err(parser.error("unexpected characters after expression"));
    }
    parser.check_written_arith()?;
    let expr = parser.settle_wraps(expr)?;
    let expr = parser.finish(expr)?;
    Ok((expr, parser.elisions()))
}

/// Every kind of node a contract clause writes, as [`parse_contract`] reads
/// it: each [`crate::formula::PureExpr`], operator and pattern variant of the
/// parse as written (before `finish` substitutes aliases away or reads a
/// pattern through a reference), and every [`PatternForm`] it wrote. A
/// generated oracle counts its cases by these.
///
/// # Errors
///
/// Returns a [`ParseError`] exactly when [`parse_contract`] does.
pub fn parse_contract_census(
    input: &str,
) -> Result<std::collections::BTreeSet<crate::formula::elaborate::NodeKind>, ParseError> {
    let mut parser = ContractParser::new(input);
    parser.census = Some(std::collections::BTreeSet::new());
    parser.parse_in_place()?;
    let mut census = parser.census.take().unwrap_or_default();
    census.extend(
        parser
            .pattern_forms
            .iter()
            .map(|&form| crate::formula::elaborate::NodeKind::Form(form)),
    );
    Ok(census)
}

/// Parse a block-style contract body into a [`PureExpr`] AST.
///
/// Handles multi-statement input such as Creusot `proof_assert!` blocks:
/// ```text
/// lemma_call();
/// lemma_call2();
/// assertion_expr
/// ```
///
/// Leading statement expressions (terminated by `;`) are parsed and discarded.
/// The trailing expression is returned as the block value. If the input contains
/// no semicolons, this behaves identically to [`parse_contract`].
///
/// # Errors
///
/// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
/// or unexpected characters.
pub fn parse_contract_body(input: &str) -> Result<PureExpr, ParseError> {
    ContractParser::new(input).parse_as_block()
}

/// Parse a block-style contract body and retain leading expression statements.
///
/// # Errors
///
/// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
/// or unexpected characters.
pub fn parse_contract_body_with_leading_exprs(
    input: &str,
) -> Result<(Vec<PureExpr>, PureExpr), ParseError> {
    ContractParser::new(input).parse_as_block_with_leading_exprs()
}

/// Parse a contract expression string into a [`SpannedExpr`] AST with source locations.
///
/// This is the preferred entry point when source location information is needed
/// for error reporting. The returned [`SpannedExpr`] records the span of the
/// full expression within the input string.
///
/// # Errors
///
/// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
/// or unexpected characters.
pub fn parse_contract_spanned(input: &str) -> Result<SpannedExpr, ParseError> {
    ContractParser::new(input).parse_spanned()
}
