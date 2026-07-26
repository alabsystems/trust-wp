// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Primary expression parsing: literals, variables, parenthesized groups,
//! quantifiers, match/if, old(), macros, and character literals.

use std::sync::Arc;

use super::super::{ContractParser, ParseError};
use crate::formula::{internal::tuple_lowering::tuple_logic_fn_name, PureExpr};

impl ContractParser<'_> {
    /// Parse primary expressions (literals, variables, parenthesized expressions)
    #[allow(clippy::too_many_lines)]
    pub(super) fn parse_primary(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();

        // Parenthesized expression or unit value ()
        if self.try_consume("(") {
            self.skip_whitespace();
            // Unit value: () — empty tuple / unit type
            if self.try_consume(")") {
                return Ok(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(0),
                    args: vec![],
                });
            }
            let first = self.parse_expr()?;
            self.skip_whitespace();
            if self.try_consume(",") {
                self.skip_whitespace();
                if self.try_consume(")") {
                    // Singleton tuple sugar: `(x,)` lowers to `x`.
                    return Ok(first);
                }
                // Multi-element tuples are lowered to synthetic logic-function calls:
                // `(x, y)` -> `__trust_wp_tuple2(x, y)`.
                let mut items = vec![first];
                loop {
                    let item = self.parse_expr()?;
                    items.push(item);
                    self.skip_whitespace();
                    if self.try_consume(",") {
                        self.skip_whitespace();
                        if self.try_consume(")") {
                            break;
                        }
                        continue;
                    }
                    if self.try_consume(")") {
                        break;
                    }
                    return Err(self.error("expected ',' or ')' in tuple expression"));
                }
                return Ok(PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(items.len()),
                    args: items,
                });
            }
            if !self.try_consume(")") {
                return Err(self.error("expected ')'"));
            }
            return Ok(first);
        }

        // Boolean literals
        if self.try_consume_keyword("true") {
            return Ok(PureExpr::Bool(true));
        }
        if self.try_consume_keyword("false") {
            return Ok(PureExpr::Bool(false));
        }

        // old(expr) - captures value at function entry (for postconditions).
        // `old` followed by `(` is the Old keyword; bare `old` (e.g., as a
        // match binding name in `Some(old) => old == ...`) falls through to
        // the identifier path. (#967)
        {
            let saved_pos = self.position;
            if self.try_consume_keyword("old") {
                self.skip_whitespace();
                if self.try_consume("(") {
                    let inner = self.parse_expr()?;
                    if !self.try_consume(")") {
                        return Err(self.error("expected ')' after old expression"));
                    }
                    return Ok(PureExpr::Old(Arc::new(inner)));
                }
                // No '(' after 'old' — backtrack and treat as identifier
                self.position = saved_pos;
                self.chars = self.input[self.position..].chars().peekable();
            }
        }

        // Universal quantifier: forall<x: Type> body
        if self.try_consume_keyword("forall") {
            return self.parse_quantifier(true);
        }

        // Existential quantifier: exists<x: Type> body
        if self.try_consume_keyword("exists") {
            return self.parse_quantifier(false);
        }

        // Match expression: match expr { pattern => body, ... }
        if self.try_consume_keyword("match") {
            return self.parse_match();
        }

        // If-then-else expression: if cond { then } else { else }
        if self.try_consume_keyword("if") {
            return self.parse_if_else();
        }

        // Block expression: { stmt; stmt; expr }
        if self.peek() == Some('{') {
            return self.parse_block();
        }

        // Character literal: 'c' — parsed as integer (Unicode codepoint). (#1513)
        if self.peek() == Some('\'') {
            return self.parse_char_literal();
        }

        // Numeric literal (integer or float, including negative, hex)
        if let Some(num) = self.try_parse_number()? {
            return Ok(num);
        }

        // Fully-qualified associated type/const path: `<Type as Trait>::CONST`
        // e.g., `<I3<T> as Nat>::VALUE`, `<T as ::std::mem::SizedTypeProperties>::IS_ZST`
        if let Some(qualified) = self.try_parse_qualified_path() {
            // After parsing the qualified path, check for a function call `(args...)`.
            // Logic function bodies like `<Self as Foo>::f()` serialize the qualified
            // call via `quote!(...).to_string()`. (#352)
            self.skip_whitespace();
            if self.try_consume("(") {
                let args = self.parse_argument_list()?;
                if !self.try_consume(")") {
                    return Err(self.error("expected ')' after qualified path call arguments"));
                }
                return Ok(PureExpr::LogicFnCall {
                    name: qualified,
                    args,
                });
            }
            // Otherwise return as a Var with the full path string.
            // Postfix `@` (view) and further `::segment` continuations
            // are handled by the caller through `parse_postfix`.
            return Ok(PureExpr::Var(qualified, None));
        }

        // Identifier (variable, path like i32::MIN, or logic function call)
        if let Some(ident) = self.try_parse_identifier() {
            let turbofish_args = self.try_parse_turbofish_args()?;

            self.skip_whitespace();
            // Check for logic function call: identifier(args...)
            if self.try_consume("(") {
                let mut args = turbofish_args.unwrap_or_default();
                args.extend(self.parse_argument_list()?);
                if !self.try_consume(")") {
                    return Err(self.error("expected ')' after function arguments"));
                }
                // Recognize `view(expr)` as a structural View node rather than
                // a LogicFnCall. The `@` postfix operator (e.g., `y@`) is
                // transformed to `view(y)` by the view-syntax macro, but the
                // contract parser only produces `PureExpr::View` for the native
                // `@` syntax. Without this, `view(y)` falls through to the
                // LogicFnCall catch-all in sort inference, which fires the
                // demoting `SortFallbackToIntFromLogicFn` counter and causes
                // invariant/postcondition proofs to be demoted to Unknown.
                // (#2671)
                if ident == "view" && args.len() == 1 {
                    return Ok(PureExpr::View(Arc::new(args.remove(0))));
                }
                // Similarly, `final_value(expr)` from `^expr` syntax should
                // produce a structural Final node. (#2671)
                if ident == "final_value" && args.len() == 1 {
                    return Ok(PureExpr::Final(Arc::new(args.remove(0))));
                }
                return Ok(PureExpr::LogicFnCall { name: ident, args });
            }
            // Macro-style call: identifier!(...), identifier![...], identifier!{...}
            if let Some(open) = self.peek_macro_invocation_delimiter() {
                let close = match open {
                    '(' => ')',
                    '[' => ']',
                    '{' => '}',
                    // Defensive: peek_macro_invocation_delimiter only returns '(', '[', or '{'.
                    _ => return Err(self.error("unexpected macro delimiter")),
                };
                self.advance(); // '!'
                self.skip_whitespace();
                self.advance(); // opening delimiter
                                // `pearlite!{ ... }` is a transparent wrapper around a logic
                                // expression block. Parse brace bodies as block statements so
                                // `let` bindings and trailing expressions are supported.
                if ident == "pearlite" && close == '}' {
                    let expr = self.parse_block_body()?;
                    if self.peek() != Some(close) {
                        return Err(
                            self.error(&format!("expected '{close}' after macro arguments"))
                        );
                    }
                    self.advance(); // closing delimiter
                    return Ok(expr);
                }
                // `proof_assert!(...)` is used in Creusot for inline hints. Its body
                // can be a Pearlite block — multi-statement with `let` bindings and a
                // trailing assertion expression (e.g., 04_skip.rs). Parse the body as
                // a block so we accept these forms. The full assertion expression is
                // returned as the single arg; lemma/let-statements are discarded by
                // the block-body parser (#2171-adjacent: parser support for laws).
                if ident == "proof_assert" && close == ')' {
                    self.skip_whitespace();
                    let expr = self.parse_block_body()?;
                    self.skip_whitespace();
                    if self.peek() != Some(close) {
                        return Err(
                            self.error(&format!("expected '{close}' after macro arguments"))
                        );
                    }
                    self.advance(); // closing delimiter
                    return Ok(PureExpr::LogicFnCall {
                        name: ident,
                        args: vec![expr],
                    });
                }
                let args = self.parse_argument_list_with_closing(close)?;
                if self.peek() != Some(close) {
                    return Err(self.error(&format!("expected '{close}' after macro arguments")));
                }
                self.advance(); // closing delimiter
                                // pearlite! with paren/bracket delimiters is also transparent.
                if ident == "pearlite" && args.len() == 1 {
                    let mut pearlite_args = args;
                    return Ok(pearlite_args.remove(0));
                }
                return Ok(PureExpr::LogicFnCall { name: ident, args });
            }
            // Struct literal expression: `TypeName { field: expr, ... }`
            // Only parse when the identifier looks like a type/constructor name
            // (starts with uppercase or contains `::`) to avoid ambiguity with
            // block expressions after lowercase variable names.
            // Suppressed inside if-conditions (no_struct_literals) to match
            // Rust's restriction: `if x == NULL { body }` is not a struct
            // literal. (#2331)
            if self.peek() == Some('{') && !self.no_struct_literals {
                let is_type_name =
                    ident.contains("::") || ident.chars().next().is_some_and(char::is_uppercase);
                if is_type_name {
                    return self.parse_struct_literal(ident);
                }
            }
            return Ok(PureExpr::Var(ident, None));
        }

        // Closure expression: |param1: Type1, param2: Type2| body
        // In primary expression position, `|` starts a closure (including `||`
        // for zero-param closures). Bitwise/logical OR are binary operators
        // handled at higher precedence levels, not in parse_primary.
        if self.peek() == Some('|') {
            return self.parse_closure();
        }

        Err(self.error("expected expression"))
    }

    /// Parse a character literal: `'c'` — returned as `PureExpr::Int` with the
    /// character's Unicode codepoint value. (#1513)
    ///
    /// Supports single characters, escape sequences (`\n`, `\t`, `\\`, `\'`),
    /// and Unicode escapes (`\u{XXXX}`).
    pub(in crate::contract_parser) fn parse_char_literal(
        &mut self,
    ) -> Result<PureExpr, ParseError> {
        if !self.try_consume("'") {
            return Err(self.error("expected character literal"));
        }
        let ch = if self.peek() == Some('\\') {
            self.advance(); // consume backslash
            match self.peek() {
                Some('n') => {
                    self.advance();
                    '\n'
                }
                Some('t') => {
                    self.advance();
                    '\t'
                }
                Some('r') => {
                    self.advance();
                    '\r'
                }
                Some('\\') => {
                    self.advance();
                    '\\'
                }
                Some('\'') => {
                    self.advance();
                    '\''
                }
                Some('0') => {
                    self.advance();
                    '\0'
                }
                Some('u') => {
                    self.advance(); // consume 'u'
                    if !self.try_consume("{") {
                        return Err(self.error("expected '{' after \\u in character literal"));
                    }
                    let mut hex = String::new();
                    while let Some(c) = self.peek() {
                        if !c.is_ascii_hexdigit() {
                            break;
                        }
                        hex.push(c);
                        self.advance();
                    }
                    if !self.try_consume("}") {
                        return Err(self.error("expected '}' after \\u{...} in character literal"));
                    }
                    let code = u32::from_str_radix(&hex, 16)
                        .map_err(|_| self.error("invalid Unicode escape"))?;
                    char::from_u32(code).ok_or_else(|| self.error("invalid Unicode codepoint"))?
                }
                _ => return Err(self.error("unknown escape sequence in character literal")),
            }
        } else {
            match self.peek() {
                Some(c) => {
                    self.advance();
                    c
                }
                None => return Err(self.error("unterminated character literal")),
            }
        };
        if !self.try_consume("'") {
            return Err(self.error("expected closing ' for character literal"));
        }
        Ok(PureExpr::Int(ch as i64))
    }
}
