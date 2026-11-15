// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantifier parsing (`forall`, `exists`), type annotations, triggers,
//! and comparison operators.

use std::sync::Arc;

use super::super::{ContractParser, ParseError, WrittenTypeSite};
use crate::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

/// The sort of a collection iterator type the parser reads by its path
/// (`hash_map::IntoIter<K, V>`), if `type_path` is one.
pub(in crate::contract_parser) fn collection_iterator_sort(
    type_path: &[String],
) -> Option<ExprSort> {
    let canonical_name = match type_path {
        [module, ty]
            if module == "hash_map" && matches!(ty.as_str(), "IntoIter" | "Iter" | "IterMut") =>
        {
            Some(format!("std::collections::hash_map::{ty}"))
        }
        [module, ty] if module == "hash_set" && matches!(ty.as_str(), "IntoIter" | "Iter") => {
            Some(format!("std::collections::hash_set::{ty}"))
        }
        [std, collections, module, ty]
            if std == "std"
                && collections == "collections"
                && module == "hash_map"
                && matches!(ty.as_str(), "IntoIter" | "Iter" | "IterMut") =>
        {
            Some(format!("std::collections::hash_map::{ty}"))
        }
        [std, collections, module, ty]
            if std == "std"
                && collections == "collections"
                && module == "hash_set"
                && matches!(ty.as_str(), "IntoIter" | "Iter") =>
        {
            Some(format!("std::collections::hash_set::{ty}"))
        }
        [std, collections, hash, map_or_set, ty]
            if std == "std"
                && collections == "collections"
                && hash == "hash"
                && map_or_set == "map"
                && matches!(ty.as_str(), "IntoIter" | "Iter" | "IterMut") =>
        {
            Some(format!("std::collections::hash::map::{ty}"))
        }
        [std, collections, hash, map_or_set, ty]
            if std == "std"
                && collections == "collections"
                && hash == "hash"
                && map_or_set == "set"
                && matches!(ty.as_str(), "IntoIter" | "Iter") =>
        {
            Some(format!("std::collections::hash::set::{ty}"))
        }
        _ => None,
    }?;

    Some(ExprSort::Datatype(intern_sort_name(&canonical_name)))
}

/// A machine integer type, the range of values a binder of it takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MachineInt {
    bits: u32,
    signed: bool,
}

impl MachineInt {
    /// `low <= value && value < high`, the type's values. A bound past `i64`
    /// is spelled as a product of 32-bit powers (`PureExpr::Int` is an `i64`).
    /// No bound is computed past `i128`: a 128-bit type's `high` (2^127,
    /// 2^128) is none, and the shift or negation that computed it overflowed
    /// (quantifier_binder_128_bit_machine_int_range_overflows.rs).
    fn range_of(self, value: &PureExpr) -> PureExpr {
        let (low, high) = if self.signed {
            (
                int_constant(i128::MIN >> (128 - self.bits)),
                power_of_two(self.bits - 1),
            )
        } else {
            (int_constant(0), power_of_two(self.bits))
        };
        let value = || Arc::new(value.clone());
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(Arc::new(low), BinOp::Le, value())),
            BinOp::And,
            Arc::new(PureExpr::BinOp(value(), BinOp::Lt, Arc::new(high))),
        )
    }
}

/// `2^exponent` (`exponent <= 128`) as an integer expression.
fn power_of_two(exponent: u32) -> PureExpr {
    if exponent < 127 {
        return int_constant(1_i128 << exponent);
    }
    PureExpr::BinOp(
        Arc::new(int_constant(1_i128 << (exponent - 64))),
        BinOp::Mul,
        Arc::new(int_constant(1_i128 << 64)),
    )
}

/// `value` as an integer expression: a literal where it fits an `i64`, else
/// `high * 2^32 + low` with `0 <= low < 2^32`.
fn int_constant(value: i128) -> PureExpr {
    if let Ok(small) = i64::try_from(value) {
        return PureExpr::Int(small);
    }
    let two_pow_32 = 1_i128 << 32;
    let high = value.div_euclid(two_pow_32);
    let low = value.rem_euclid(two_pow_32);
    PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(int_constant(high)),
            BinOp::Mul,
            Arc::new(PureExpr::Int(1_i64 << 32)),
        )),
        BinOp::Add,
        Arc::new(int_constant(low)),
    )
}

/// The machine integer `name` is, by its spelling (a shadowed spelling is
/// refused before this reads it, `spelled_types`). `usize`/`isize` are 64
/// bits wide, as `usize::MAX` is read.
fn machine_int(name: &str) -> Option<MachineInt> {
    let (bits, signed) = match name {
        "u8" => (8, false),
        "u16" => (16, false),
        "u32" => (32, false),
        "u64" | "usize" => (64, false),
        "u128" => (128, false),
        "i8" => (8, true),
        "i16" => (16, true),
        "i32" => (32, true),
        "i64" | "isize" => (64, true),
        "i128" => (128, true),
        _ => return None,
    };
    Some(MachineInt { bits, signed })
}

/// What a binder's written type says of the values it ranges over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BinderRange {
    /// A machine integer: its range is stated on the body.
    MachineInt(MachineInt),
    /// A reference to a machine integer: the range of the value it points
    /// at, and of a `&mut`'s final value, is stated on the body.
    Reference { int: MachineInt, mutable: bool },
    /// A type that holds a machine integer anywhere else (`Seq<u8>`,
    /// `(u8, bool)`, `&&u8`): the sort it maps to keeps no range for it, and
    /// the binder would range over values the type does not have. The
    /// quantifier is refused.
    Holds,
}

impl BinderRange {
    /// `value` is a value of this type, as a formula; `None` for
    /// [`BinderRange::Holds`].
    fn of(self, value: &PureExpr) -> Option<PureExpr> {
        let shared = || Arc::new(value.clone());
        match self {
            Self::MachineInt(int) => Some(int.range_of(value)),
            Self::Reference { int, mutable } => {
                let current = int.range_of(&PureExpr::Deref(shared()));
                Some(if mutable {
                    let last = int.range_of(&PureExpr::Final(shared()));
                    PureExpr::BinOp(Arc::new(current), BinOp::And, Arc::new(last))
                } else {
                    current
                })
            }
            Self::Holds => None,
        }
    }
}

/// The range a binder's written type states, if any.
fn binder_range(text: &str) -> Option<BinderRange> {
    let text = text.trim();
    if let Some(own) = machine_int(text) {
        return Some(BinderRange::MachineInt(own));
    }
    if let Some(referent) = text.strip_prefix('&').map(str::trim_start) {
        let (mutable, referent) = match referent.strip_prefix("mut") {
            Some(rest) if rest.starts_with(char::is_whitespace) => (true, rest.trim()),
            _ => (false, referent.trim()),
        };
        if let Some(int) = machine_int(referent) {
            return Some(BinderRange::Reference { int, mutable });
        }
    }
    text.split(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
        .any(|word| machine_int(word).is_some())
        .then_some(BinderRange::Holds)
}

fn type_annotation_sort(
    type_path: &[String],
    has_generics: bool,
    is_dyn: bool,
) -> Option<ExprSort> {
    if is_dyn {
        return None;
    }

    if let Some(sort) = collection_iterator_sort(type_path) {
        return Some(sort);
    }

    let [type_name] = type_path else {
        return None;
    };

    // Conservative generic-parameter heuristic: single-letter uppercase
    // names (`T`, `E`, etc.) map to Int fallback sort. This avoids
    // classifying custom nominal types like `FooType` as generics. (#1752)
    let mut type_name_chars = type_name.chars();
    let is_generic_type_param = matches!(
        (type_name_chars.next(), type_name_chars.next()),
        (Some(c), None) if c.is_ascii_uppercase()
    );

    match type_name.as_str() {
        "bool" | "Bool" => Some(ExprSort::Bool),
        "Int" | "i8" | "i16" | "i32" | "i64" | "i128" | "u8" | "u16" | "u32" | "u64" | "u128"
        | "isize" | "usize" => Some(ExprSort::Int),
        "Seq" => Some(ExprSort::Seq),
        // Vec<T> maps to Seq in SMT (logical view of collections)
        "Vec" if has_generics => Some(ExprSort::Seq),
        // Creusot `Mapping<K, V>` (Why3 `map.Map.map`) is a total function
        // value. Annotate it with the canonical Mapping datatype sort (the same
        // sort the encoder's type-name table and the driver's ADT analysis
        // use), so `forall<f: Mapping<T, U>> .. f.get(x) ..` binds `f` at the
        // Mapping carrier instead of the Int fallback. Sort choice only.
        "Mapping" if has_generics => Some(ExprSort::Datatype(intern_sort_name("Mapping"))),
        _ if is_generic_type_param => Some(ExprSort::TypeParam(intern_sort_name(type_name))),
        _ => None,
    }
}

impl ContractParser<'_> {
    /// Parse quantifier: `<var: Type> [#[trigger(...)]]* body`
    ///
    /// Called after consuming `forall` or `exists` keyword.
    ///
    /// # Syntax
    ///
    /// Basic: `forall<x: Int> body` or `exists<x: Int> body`
    ///
    /// With triggers: `forall<x: Int> #[trigger(f(x), g(x))] body`
    ///
    /// Multiple trigger groups: `forall<x: Int> #[trigger(f(x))] #[trigger(g(x))] body`
    ///
    /// Each `#[trigger(...)]` creates one trigger pattern. Multiple expressions
    /// within the same trigger form a multi-trigger (all must match).
    /// Multiple `#[trigger]` annotations provide alternative instantiation patterns.
    pub(in crate::contract_parser) fn parse_quantifier(
        &mut self,
        is_forall: bool,
    ) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();

        // Expect '<'
        if !self.try_consume("<") {
            let qname = if is_forall { "forall" } else { "exists" };
            return Err(self.error(&format!("expected '<' after '{qname}'")));
        }

        // Parse one or more comma-separated variable bindings.
        // Supported forms:
        //   forall<x: Int>        — single variable with type (sort preserved)
        //   forall<x: bool>       — single variable with Bool sort
        //   exists<c>             — single variable, type elided (sort = None)
        //   forall<a, b>          — multiple variables, types elided
        //   exists<s1: F, r: T>   — multiple variables with types
        //   exists<r: &mut T>     — generic reference annotation (Int fallback)
        let mut vars: Vec<(String, Option<ExprSort>, Option<BinderRange>)> = Vec::new();

        loop {
            self.skip_whitespace();
            let var = self
                .try_parse_simple_identifier()
                .ok_or_else(|| self.error("expected variable name in quantifier"))?;

            self.skip_whitespace();

            // Optional type annotation: `: Type`
            let (sort, range) = if self.try_consume(":") {
                self.skip_whitespace();
                let (sort, text) =
                    self.consume_written_type_text(WrittenTypeSite::QuantifierBinder)?;
                (sort, binder_range(&text))
            } else {
                self.note_elided_type(WrittenTypeSite::QuantifierBinder);
                (None, None)
            };

            vars.push((var, sort, range));

            self.skip_whitespace();

            // Check for ',' (more variables) or '>' (end of binding list)
            if self.try_consume(",") {
                continue;
            }
            break;
        }

        self.skip_whitespace();

        // Expect '>'
        if !self.try_consume(">") {
            return Err(self.error("expected '>' after type in quantifier"));
        }

        self.skip_whitespace();

        // Parse optional trigger annotations: #[trigger(expr, ...)]
        let triggers = self.parse_trigger_annotations()?;

        self.skip_whitespace();

        // Parse body (the entire remaining expression)
        let body = self.parse_expr()?;

        // For multi-variable quantifiers, nest them: forall<a, b> body
        // becomes Forall { var: a, body: Forall { var: b, body } }
        let mut result = body;
        for (var, var_sort, range) in vars.into_iter().rev() {
            // The binder's sort has every integer where its type has a
            // range: the range is a premise of `forall` and a conjunct of
            // `exists` (quantifier_binder_machine_int_read_unbounded_granted.rs).
            let bound = PureExpr::Var(var.clone(), None);
            if let Some(range) = range.and_then(|range| range.of(&bound)) {
                let op = if is_forall {
                    BinOp::Implies
                } else {
                    BinOp::And
                };
                result = PureExpr::BinOp(Arc::new(range), op, Arc::new(result));
            }
            let refused = range == Some(BinderRange::Holds);
            let binder_var = var.clone();
            result = if is_forall {
                PureExpr::Forall {
                    var,
                    var_sort,
                    body: Arc::new(result),
                    triggers: triggers.clone(),
                }
            } else {
                PureExpr::Exists {
                    var,
                    var_sort,
                    body: Arc::new(result),
                    triggers: triggers.clone(),
                }
            };
            if refused {
                // Refused where the quantifier is read, not here: the proc
                // macros parse every clause at compile time, and a parse
                // error there fails the user's build.
                result = PureExpr::LogicFnCall {
                    name: crate::logic::identity::logic_fn_unresolved_marker(&format!(
                        "{binder_var}_binder_range"
                    )),
                    args: vec![result],
                };
            }
        }

        Ok(result)
    }

    /// Consume a type annotation in a quantifier binding, returning the
    /// corresponding `ExprSort` when the type maps to a known SMT sort.
    ///
    /// Handles simple types (`Int`, `u32`, `T`), reference types (`&mut T`, `&T`),
    /// pointer types (`*const T`, `*mut T`), and generic types (`Vec<T>`).
    ///
    /// Returns `Some(ExprSort)` for recognized SMT-mapped types:
    /// - `bool` / `Bool` → `ExprSort::Bool`
    /// - `Int` / `i8`..`i64` / `u8`..`u64` / `isize` / `usize` → `ExprSort::Int`
    /// - `Seq` / `Vec` / `[T]` → `ExprSort::Seq`
    /// - Generic type parameters like `T` / `E` → `ExprSort::Int` (fallback)
    /// - All others (pointers, tuples, unknown custom types) → `None`
    pub(in crate::contract_parser) fn consume_type_annotation(
        &mut self,
    ) -> Result<Option<ExprSort>, ParseError> {
        self.skip_whitespace();

        // Handle reference types: `&T`, `&mut T`, `&[T]`
        // Preserve the wrapper so quantifier and closure binders can
        // distinguish shared and mutable references. (#2141)
        if self.try_consume("&") {
            self.skip_whitespace();
            let is_mut = self.try_consume_keyword("mut");
            self.skip_whitespace();
            let inner = self.consume_type_annotation()?;
            return Ok(inner.map(|sort| {
                if is_mut {
                    ExprSort::MutRef(Box::new(sort))
                } else {
                    ExprSort::Ref(Box::new(sort))
                }
            }));
        }

        // Handle raw pointer types: `*const T`, `*mut T`
        if self.try_consume("*") {
            self.skip_whitespace();
            if !(self.try_consume_keyword("const") || self.try_consume_keyword("mut")) {
                return Err(self.error("expected 'const' or 'mut' in pointer type"));
            }
            self.skip_whitespace();
            self.consume_type_annotation()?;
            return Ok(None);
        }

        // Handle slice types: `[T]` — maps to Seq in SMT
        if self.peek() == Some('[') {
            self.advance(); // consume '['
            self.consume_type_annotation()?;
            self.skip_whitespace();
            if !self.try_consume("]") {
                return Err(self.error("expected ']' in slice type"));
            }
            return Ok(Some(ExprSort::Seq));
        }

        // Handle tuple / unit types: `()`, `(T,)`, `(T, U)`
        if self.peek() == Some('(') {
            self.advance(); // consume '('
            self.skip_whitespace();
            if self.try_consume(")") {
                // Unit type `()` — singleton type, quantifiers over it are eliminable
                return Ok(Some(ExprSort::Unit));
            }
            // At least one element: parse comma-separated types
            self.consume_type_annotation()?;
            loop {
                self.skip_whitespace();
                if self.try_consume(")") {
                    break;
                }
                if !self.try_consume(",") {
                    return Err(self.error("expected ',' or ')' in tuple type"));
                }
                self.skip_whitespace();
                // Allow trailing comma: `(T,)`
                if self.peek() == Some(')') {
                    self.advance();
                    break;
                }
                self.consume_type_annotation()?;
            }
            return Ok(None);
        }

        // Handle `dyn Trait` object types (#657) — no SMT sort mapping
        let is_dyn = self.try_consume_keyword("dyn");
        if is_dyn {
            self.skip_whitespace();
        }

        // Must start with an identifier
        let type_name = self
            .try_parse_simple_identifier()
            .ok_or_else(|| self.error("expected type name in quantifier"))?;

        // Handle path segments: `K::DeepModelTy`, `crate::module::Type`
        let mut type_path = vec![type_name.clone()];
        while self.try_consume_path_separator() {
            let segment = self
                .try_parse_simple_identifier()
                .ok_or_else(|| self.error("expected identifier after '::' in type path"))?;
            type_path.push(segment);
        }
        self.skip_whitespace();

        // Handle generic parameters: `<T>`, `<K, V>`
        // We need to handle nested `<>` for types like `HashMap<K, V>`
        let has_generics = self.peek() == Some('<');
        if has_generics {
            self.consume_balanced_angles()?;
        }

        // Map recognized simple type names to ExprSort.
        // Path-qualified types (K::DeepModelTy) and dyn types are not mapped.
        let sort = type_annotation_sort(&type_path, has_generics, is_dyn);

        Ok(sort)
    }

    /// Consume balanced angle brackets `<...>`, handling nesting.
    pub(in crate::contract_parser) fn consume_balanced_angles(&mut self) -> Result<(), ParseError> {
        if !self.try_consume("<") {
            return Err(self.error("expected '<'"));
        }
        let mut depth = 1u32;
        while depth > 0 {
            match self.peek() {
                Some('<') => {
                    depth = depth.saturating_add(1);
                    self.advance();
                }
                Some('>') => {
                    depth -= 1;
                    self.advance();
                }
                Some(_) => {
                    self.advance();
                }
                None => return Err(self.error("unexpected end of input in type annotation")),
            }
        }
        Ok(())
    }

    /// Try to consume a comparison operator and return its corresponding AST operator.
    pub(in crate::contract_parser) fn try_parse_comparison_op(&mut self) -> Option<BinOp> {
        if self.try_consume("<=") {
            Some(BinOp::Le)
        } else if self.try_consume(">=") {
            Some(BinOp::Ge)
        } else if self.try_consume("<") {
            Some(BinOp::Lt)
        } else if self.try_consume(">") {
            Some(BinOp::Gt)
        } else {
            None
        }
    }

    /// Parse trigger annotations: `#[trigger(expr1, expr2)] #[trigger(expr3)]`
    ///
    /// Returns a vector of trigger groups. Each group is a multi-trigger
    /// (all expressions must match for instantiation).
    pub(in crate::contract_parser) fn parse_trigger_annotations(
        &mut self,
    ) -> Result<Vec<Vec<PureExpr>>, ParseError> {
        let mut triggers = Vec::new();

        loop {
            self.skip_whitespace();

            // Check for #[trigger
            if !self.try_consume("#[trigger(") {
                break;
            }

            // Parse comma-separated expressions until closing )]
            let mut trigger_exprs = Vec::new();

            loop {
                self.skip_whitespace();

                // Check for closing )]
                if self.try_consume(")]") {
                    break;
                }

                // Skip comma if not first expression
                if !trigger_exprs.is_empty() {
                    if !self.try_consume(",") {
                        return Err(self.error("expected ',' or ')]' in trigger"));
                    }
                    self.skip_whitespace();
                }

                // Parse the full trigger expression.
                let expr = self.parse_expr()?;
                trigger_exprs.push(expr);
            }

            if trigger_exprs.is_empty() {
                return Err(self.error("trigger must contain at least one expression"));
            }

            triggers.push(trigger_exprs);
        }

        Ok(triggers)
    }
}
