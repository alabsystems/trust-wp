// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match-arm pattern parsing.

use super::super::{ContractParser, ParseError, PatternForm};
use crate::formula::{Pattern, PureExpr};

impl ContractParser<'_> {
    /// Parse a pattern (a `let`, a `match` arm, `if let`, a closure
    /// parameter). A name bound twice in one pattern is refused, as rustc
    /// refuses it (E0416): each binding of it would read a different value.
    pub(in crate::contract_parser) fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        self.skip_whitespace();
        let start = self.position;
        let pattern = self.parse_subpattern()?;
        let mut seen = std::collections::HashSet::new();
        if let Some(name) = pattern
            .bound_names()
            .into_iter()
            .find(|name| !seen.insert(*name))
        {
            return Err(ParseError {
                message: format!("identifier `{name}` is bound more than once in the same pattern"),
                position: start,
            });
        }
        Ok(pattern)
    }

    #[allow(clippy::too_many_lines)]
    fn parse_subpattern(&mut self) -> Result<Pattern, ParseError> {
        self.skip_whitespace();

        // A binding by reference, `ref x` / `ref mut x`, optionally with a
        // subpattern: `ref x @ p`. Only `x` binds by reference, one level
        // above the matched value; `p` matches the value itself
        // (`helpers/borrows.rs`). Rust writes a name after `ref`, and nothing
        // else.
        let start = self.position;
        if self.try_consume_keyword("ref") {
            self.skip_whitespace();
            let form = if self.try_consume_keyword("mut") {
                PatternForm::RefMut
            } else {
                PatternForm::Ref
            };
            self.skip_whitespace();
            let name = self
                .try_parse_simple_identifier()
                .filter(|name| name != "_")
                .ok_or_else(|| {
                    self.error(
                        "expected an identifier after `ref`: a binding by reference binds a name",
                    )
                })?;
            self.skip_whitespace();
            let subpattern = if self.try_consume("@") {
                self.pattern_forms.push(PatternForm::RefAlias);
                Some(self.parse_subpattern()?)
            } else {
                self.pattern_forms.push(form);
                None
            };
            return Ok(self.binding_by_reference(start, name, subpattern));
        }

        // Handle bare `mut` qualifier — consumed and discarded
        if self.try_consume_keyword("mut") {
            self.pattern_forms.push(PatternForm::MutBinding);
            self.skip_whitespace();
            return self.parse_subpattern();
        }

        // Creusot examples use Rust's box-pattern syntax in logic matches
        // (`Some(box Node { .. })`, `CPN(_, box l, box r)`). Box is
        // transparent in trust-wp's logical model, so parse the inner pattern.
        if self.try_consume_keyword("box") {
            self.pattern_forms.push(PatternForm::Box);
            self.skip_whitespace();
            return self.parse_subpattern();
        }

        // Reference patterns: `&pattern` and `&mut pattern` match the inner
        // pattern against the referent, one level below the matched value
        // (`helpers/borrows.rs`), as in `Bdd(&If { childt, childf, .. }, _)`.
        if self.peek() == Some('&') {
            self.advance(); // consume '&'
            self.skip_whitespace();
            let form = if self.try_consume_keyword("mut") {
                PatternForm::MutReference
            } else {
                PatternForm::Reference
            };
            self.pattern_forms.push(form);
            self.skip_whitespace();
            let inner = self.parse_subpattern()?;
            return Ok(self.reference_pattern(start, inner));
        }

        // Wildcard: _
        if self.try_consume("_") {
            // Make sure it's not _identifier (like _unused or __x)
            // Valid identifier chars after _ are alphanumeric or underscore
            if self.peek().is_some_and(|c| c.is_alphanumeric() || c == '_') {
                // It's an identifier starting with _, backtrack
                self.position = self.position.saturating_sub(1);
                self.chars = self.input[self.position..].chars().peekable();
            } else {
                self.pattern_forms.push(PatternForm::Wildcard);
                return Ok(Pattern::Wildcard);
            }
        }

        // Try boolean literal
        if self.try_consume_keyword("true") {
            self.pattern_forms.push(PatternForm::Literal);
            return Ok(Pattern::Literal(PureExpr::Bool(true)));
        }
        if self.try_consume_keyword("false") {
            self.pattern_forms.push(PatternForm::Literal);
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
            self.pattern_forms.push(PatternForm::Literal);
            return Ok(Pattern::Literal(PureExpr::Int(n)));
        }

        // A tuple pattern `(p1, p2, ..)` or `()`. `(p)` is `p` parenthesized,
        // as in Rust, and `(p,)` matches what `p` matches: the logic reads a
        // one-element tuple as its element (`(x,)` is `x`, primary.rs), and a
        // one-element tuple pattern read as a tuple bound `p` to a field the
        // value does not have (`match (x,) { (v,) => v == x }` was refuted).
        if self.peek() == Some('(') {
            self.try_consume("(");
            self.skip_whitespace();
            let mut elements = Vec::new();
            let mut comma = false;
            if self.peek() != Some(')') {
                elements.push(self.parse_subpattern()?);
                self.skip_whitespace();
                while self.try_consume(",") {
                    comma = true;
                    self.skip_whitespace();
                    if self.peek() == Some(')') {
                        break; // trailing comma
                    }
                    elements.push(self.parse_subpattern()?);
                    self.skip_whitespace();
                }
            }
            if !self.try_consume(")") {
                return Err(self.error("expected ')' after tuple pattern"));
            }
            if elements.len() == 1 {
                self.pattern_forms.push(if comma {
                    PatternForm::OneTuple
                } else {
                    PatternForm::Parenthesized
                });
                return Ok(elements.remove(0));
            }
            self.pattern_forms.push(PatternForm::Tuple);
            if elements
                .iter()
                .any(|element| matches!(element, Pattern::Tuple(_)))
            {
                self.pattern_forms.push(PatternForm::NestedTuple);
            }
            return Ok(Pattern::Tuple(elements));
        }

        // Try identifier (could be variable binding or constructor)
        // Use try_parse_identifier to handle qualified paths like OwnResult::Ok (#939)
        let path_at = self.position;
        if let Some(name) = self.try_parse_identifier() {
            self.refuse_shadowed_path(&name, path_at)?;
            self.skip_whitespace();

            // Alias pattern: `node @ Node { .. }`. Bind the alias to the
            // whole scrutinee while retaining inner-pattern bindings.
            if self.try_consume("@") {
                self.pattern_forms.push(PatternForm::Alias);
                let pattern = self.parse_subpattern()?;
                return Ok(Pattern::Alias {
                    alias: name,
                    pattern: Box::new(pattern),
                });
            }

            // Check if it's a constructor with inner pattern(s): Some(x), Cons(a, l).
            // Also handles tuple-struct rest patterns `Foo(x, ..)` and `Foo(..)`:
            // a TRAILING `..` matches zero or more positional fields and is
            // consumed/discarded (unmentioned fields become wildcards). A `..`
            // with further elements after it — `Foo(.., last)`, `Foo(a, .., b)`
            // — is refused, see below.
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
                            self.pattern_forms.push(PatternForm::Rest);
                            // Rest pattern: skip; allow optional trailing comma.
                            self.skip_whitespace();
                            if self.try_consume(",") {
                                self.skip_whitespace();
                                if self.peek() == Some(')') {
                                    break;
                                }
                                // An element after `..` sits at an index only
                                // the constructor's declared arity can give
                                // (`Foo(.., last)` names the LAST field). This
                                // parser cannot see a declaration, and the
                                // positional encoding it emits has no way to
                                // say "counted from the end", so binding
                                // `last` at the next written index — what
                                // dropping the `..` would do — reads a
                                // different field than the one the pattern
                                // denotes. Refuse rather than guess.
                                return Err(self.error(&format!(
                                    "a `..` rest pattern followed by further positional \
                                     fields in `{name}(..)` is not supported: their \
                                     positions depend on the constructor's declared arity, \
                                     which specification text cannot see"
                                )));
                            }
                            break;
                        }
                        constructor_args.push(self.parse_subpattern()?);
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
                self.pattern_forms.push(PatternForm::Constructor);
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
                        self.pattern_forms.push(PatternForm::Rest);
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
                        self.parse_subpattern()?
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
                // Encode field names into the constructor name so the driver
                // can place each one at its DECLARED index.
                //
                // A `..` rest pattern is encoded too, with a trailing `..`
                // marker. Dropping the field list for rest patterns — which is
                // what this did until s82 — does not make the reordering
                // ambiguous, it makes it INVISIBLE: the driver then sees a
                // bare `E::C` with a shorter argument list and positions the
                // first NAMED field at index 0, so `E::C { b: bb, .. }` binds
                // `bb` to the field declared first. Carrying the names lets
                // the driver place them and pad the rest with wildcards, and
                // lets it REFUSE when it cannot.
                let ctor_name = if field_names.is_empty() {
                    name
                } else {
                    let mut encoded = field_names.clone();
                    if has_rest {
                        encoded.push(crate::formula::NAMED_CTOR_REST_MARKER.to_string());
                    }
                    crate::formula::named_struct_ctor_name(&name, &encoded)
                };
                self.pattern_forms.push(PatternForm::Struct);
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
                self.pattern_forms.push(PatternForm::Constructor);
                return Ok(Pattern::Constructor { name, inner: None });
            }

            // Otherwise it's a variable binding
            self.pattern_forms.push(PatternForm::Binding);
            return Ok(Pattern::Binding(name));
        }

        Err(self.error("expected pattern"))
    }
}
