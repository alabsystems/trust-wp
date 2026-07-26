// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match-arm pattern parsing.

use super::super::{ContractParser, ParseError};
use crate::formula::{Pattern, PureExpr};

impl ContractParser<'_> {
    /// Parse a pattern in a match arm
    #[allow(clippy::too_many_lines)]
    pub(in crate::contract_parser) fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        self.skip_whitespace();

        // Handle `ref` and `ref mut` qualifiers (#1513) — these are consumed
        // and discarded since contract logic bindings are always by-value.
        // e.g., `Some(ref mut v)` → `Some(v)`, `ref x` → `x`
        if self.try_consume_keyword("ref") {
            self.skip_whitespace();
            self.try_consume_keyword("mut");
            self.skip_whitespace();
            // Parse the inner pattern (usually just a binding)
            return self.parse_pattern();
        }

        // Handle bare `mut` qualifier — consumed and discarded
        if self.try_consume_keyword("mut") {
            self.skip_whitespace();
            return self.parse_pattern();
        }

        // Creusot examples use Rust's box-pattern syntax in logic matches
        // (`Some(box Node { .. })`, `CPN(_, box l, box r)`). Box is
        // transparent in trust-wp's logical model, so parse the inner pattern.
        if self.try_consume_keyword("box") {
            self.skip_whitespace();
            return self.parse_pattern();
        }

        // Reference patterns: `&pattern` and `&mut pattern`. Creusot's logic
        // model treats references transparently in match arms (e.g.,
        // `Bdd(&If { childt, childf, .. }, _)` in bdd.rs). Consume the `&`
        // (and optional `mut`) and parse the inner pattern.
        if self.peek() == Some('&') {
            self.advance(); // consume '&'
            self.skip_whitespace();
            self.try_consume_keyword("mut");
            self.skip_whitespace();
            return self.parse_pattern();
        }

        // Wildcard: _
        if self.try_consume("_") {
            // Make sure it's not _identifier (like _unused or __x)
            // Valid identifier chars after _ are alphanumeric or underscore
            if self.peek().is_some_and(|c| c.is_alphanumeric() || c == '_') {
                // It's an identifier starting with _, backtrack
                self.position -= 1;
                self.chars = self.input[self.position..].chars().peekable();
            } else {
                return Ok(Pattern::Wildcard);
            }
        }

        // Try boolean literal
        if self.try_consume_keyword("true") {
            return Ok(Pattern::Literal(PureExpr::Bool(true)));
        }
        if self.try_consume_keyword("false") {
            return Ok(Pattern::Literal(PureExpr::Bool(false)));
        }

        // Character-literal patterns (`'c'`, `'\n'`, `'\u{XXXX}'`, …) are
        // unsupported, matching Creusot's documented behavior: a `match` on
        // `char` aborts with "match on char is currently unsupported"
        // (reference/creusot/tests/should_fail/unsupported/char_pattern.rs).
        //
        // The underlying reason is the Pearlite limitation that
        // `pattern_contains_int_literal` already enforces: a char-literal
        // pattern can only lower to an integer-literal match on the Unicode
        // codepoint, and Pearlite does not support matching `Int` literals.
        // Accepting the lowered `Pattern::Literal(Int)` and silently treating
        // it as a codepoint match would be unsound w.r.t. the supported
        // pattern-matching semantics, so we fail closed here.
        //
        // We still drive the full char-literal parser first so malformed char
        // literals (unterminated, unknown escape) surface their own precise
        // parse errors rather than this rejection. (char-pattern soundness
        // 2026-06-02)
        if self.peek() == Some('\'') {
            let _lit = self.parse_char_literal()?;
            return Err(self.error(
                "match on char is currently unsupported (Pearlite cannot match \
                 char/Int literals; consider using if-then-else with an equality \
                 comparison instead)",
            ));
        }

        // Try integer literal
        if let Some(n) = self.try_parse_integer()? {
            return Ok(Pattern::Literal(PureExpr::Int(n)));
        }

        // Try tuple pattern: (pat1, pat2, ...)
        if self.peek() == Some('(') {
            self.try_consume("(");
            self.skip_whitespace();
            let mut elements = Vec::new();
            if self.peek() != Some(')') {
                elements.push(self.parse_pattern()?);
                self.skip_whitespace();
                while self.try_consume(",") {
                    self.skip_whitespace();
                    if self.peek() == Some(')') {
                        break; // trailing comma
                    }
                    elements.push(self.parse_pattern()?);
                    self.skip_whitespace();
                }
            }
            if !self.try_consume(")") {
                return Err(self.error("expected ')' after tuple pattern"));
            }
            return Ok(Pattern::Tuple(elements));
        }

        // Try identifier (could be variable binding or constructor)
        // Use try_parse_identifier to handle qualified paths like OwnResult::Ok (#939)
        if let Some(name) = self.try_parse_identifier() {
            self.skip_whitespace();

            // Alias pattern: `node @ Node { .. }`. Bind the alias to the
            // whole scrutinee while retaining inner-pattern bindings.
            if self.try_consume("@") {
                let pattern = self.parse_pattern()?;
                return Ok(Pattern::Alias {
                    alias: name,
                    pattern: Box::new(pattern),
                });
            }

            // Check if it's a constructor with inner pattern(s): Some(x), Cons(a, l).
            // Also handles tuple-struct rest patterns `Foo(x, ..)`, `Foo(..)`,
            // `Foo(.., last)` — `..` matches zero or more positional fields and
            // is consumed/discarded (unmentioned fields become wildcards).
            if self.try_consume("(") {
                self.skip_whitespace();
                let inner = if self.peek() == Some(')') {
                    // Normalize explicit zero-arg syntax (e.g., Nil()) to unit constructor.
                    None
                } else {
                    let mut constructor_args: Vec<Pattern> = Vec::new();
                    // Each iteration parses one positional element, OR consumes
                    // a `..` rest token (which contributes nothing to the args).
                    loop {
                        if self.try_consume("..") {
                            // Rest pattern: skip; allow optional trailing comma.
                            self.skip_whitespace();
                            if self.try_consume(",") {
                                self.skip_whitespace();
                                if self.peek() == Some(')') {
                                    break;
                                }
                                continue;
                            }
                            break;
                        }
                        constructor_args.push(self.parse_pattern()?);
                        self.skip_whitespace();
                        if !self.try_consume(",") {
                            break;
                        }
                        self.skip_whitespace();
                        if self.peek() == Some(')') {
                            break;
                        }
                    }
                    if constructor_args.is_empty() {
                        // `Foo(..)` — no captured bindings; treat as unit constructor.
                        None
                    } else if constructor_args.len() == 1 {
                        Some(Box::new(
                            constructor_args
                                .pop()
                                .expect("constructor_args is non-empty by length check"),
                        ))
                    } else {
                        Some(Box::new(Pattern::Tuple(constructor_args)))
                    }
                };
                self.skip_whitespace();
                if !self.try_consume(")") {
                    return Err(self.error("expected ')' after constructor pattern"));
                }
                return Ok(Pattern::Constructor { name, inner });
            }

            // Check if it's a struct constructor pattern with braces: `Sum::B { b }`,
            // `Pair { a, b }`, `Sum::B { b: pat }`, `B { field: true, .. }`.
            // Field names are encoded into the constructor name using the
            // `TypeName{field1,field2}` convention so the driver's rewrite pass
            // can reorder to canonical field order. Rest pattern `..` is consumed
            // and discarded (all unmentioned fields are wildcards). (#1819)
            if self.peek() == Some('{') {
                self.advance(); // consume '{'
                self.skip_whitespace();
                let mut field_names = Vec::new();
                let mut field_patterns = Vec::new();
                let mut has_rest = false;
                while self.peek() != Some('}') {
                    // Handle `..` rest-pattern — consume and stop field parsing
                    if self.try_consume("..") {
                        has_rest = true;
                        self.skip_whitespace();
                        // Allow trailing comma after `..`
                        self.try_consume(",");
                        self.skip_whitespace();
                        break;
                    }
                    // Parse field: either `name: pattern` or shorthand `name` (binds name)
                    let field_name = self
                        .try_parse_simple_identifier()
                        .ok_or_else(|| self.error("expected field name in struct pattern"))?;
                    self.skip_whitespace();
                    let field_pat = if self.try_consume(":") {
                        self.skip_whitespace();
                        self.parse_pattern()?
                    } else {
                        // Shorthand: `{ b }` means `{ b: b }`
                        Pattern::Binding(field_name.clone())
                    };
                    field_names.push(field_name);
                    field_patterns.push(field_pat);
                    self.skip_whitespace();
                    if !self.try_consume(",") {
                        break;
                    }
                    self.skip_whitespace();
                }
                if !self.try_consume("}") {
                    return Err(self.error("expected '}' after struct pattern"));
                }
                let inner = if field_patterns.is_empty() {
                    None
                } else if field_patterns.len() == 1 {
                    Some(Box::new(
                        field_patterns
                            .pop()
                            .expect("field_patterns is non-empty by length check"),
                    ))
                } else {
                    Some(Box::new(Pattern::Tuple(field_patterns)))
                };
                // Encode field names into constructor name so the driver can
                // reorder to canonical order. Skip when rest pattern `..` is
                // present (incomplete field list makes reordering ambiguous).
                let ctor_name = if has_rest || field_names.is_empty() {
                    name
                } else {
                    crate::formula::named_struct_ctor_name(&name, &field_names)
                };
                return Ok(Pattern::Constructor {
                    name: ctor_name,
                    inner,
                });
            }

            // Check if it's a unit constructor (like None) or variable binding.
            // Qualified paths (e.g., OwnResult::Ok) are always constructors.
            // For simple names, use uppercase first letter as heuristic.
            let is_constructor =
                name.contains("::") || name.chars().next().is_some_and(char::is_uppercase);
            if is_constructor {
                return Ok(Pattern::Constructor { name, inner: None });
            }

            // Otherwise it's a variable binding
            return Ok(Pattern::Binding(name));
        }

        Err(self.error("expected pattern"))
    }
}
