// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A reference level is part of what the text says: a pattern that matches
//! through a reference, a binding by reference, and a borrow a `let` binds are
//! each read at their level, or recorded, or refused. Every parser reads them
//! alike: the spanned parser, and the one a generic argument is parsed by.

use super::*;

fn elisions(input: &str) -> ContractElisions {
    parse_contract_with_elisions(input).expect("parses").1
}

/// `let &t = p` binds `t` to `*p`, and `let ref t = e` binds a borrow of `e`,
/// which `*t` reads through. Each pattern was consumed and `t` bound to `p`
/// itself, so `forall<p: &Int> { let &t = p; *t + 1 > *t }` read `*t` as `*p`
/// and verified, and with a disjointness fact on `p`, `q` so did `{ let &t =
/// p; let &u = q; t != u }` over two `&&Int`s, whose referents may be equal.
#[test]
fn a_reference_pattern_in_a_let_is_read_at_its_level() {
    for (input, expected) in [
        ("{ let &t = p; t + 1 > t }", "*p + 1 > *p"),
        ("{ let &mut t = p; t + 1 > t }", "*p + 1 > *p"),
        ("{ let & t = p; *t > 0 }", "**p > 0"),
        ("{ let &&t = p; t > 0 }", "**p > 0"),
        ("{ let &t = &v; t > 0 }", "v > 0"),
        ("{ let ref t = p; *t > 0 }", "p > 0"),
        ("{ let ref mut t = p; **t > 0 }", "*p > 0"),
        ("{ let ref t = p; ^*t > 0 }", "^p > 0"),
        ("{ let r = &v; let &t = r; t > 0 }", "v > 0"),
        ("{ let (&a, b) = pair; a + b > 0 }", "*pair.0 + pair.1 > 0"),
        (
            "{ let &(a, b) = pair; a + b > 0 }",
            "(*pair).0 + (*pair).1 > 0",
        ),
        ("{ let x @ &t = p; t > 0 && x == p }", "*p > 0 && p == p"),
    ] {
        let parsed = parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
        let expected = parse_contract(expected).expect("parses");
        assert_eq!(
            inline_lets(&parsed),
            inline_lets(&expected),
            "{input} reads {parsed}"
        );
        assert_eq!(
            parse_contract_spanned(input).expect("parses").expr,
            parsed,
            "{input} (spanned)"
        );
        assert!(
            elisions(input).dropped_borrows.is_empty(),
            "{input}: {:?}",
            elisions(input)
        );
    }
    // A binding by reference read other than through `*` keeps the borrowed
    // value where the text has a reference to it.
    assert_eq!(
        elisions("{ let ref t = p; t == q }").dropped_borrows,
        ["ref t"]
    );
    assert_eq!(
        elisions("{ let (ref a, b) = pair; a == b }").dropped_borrows,
        ["ref a"]
    );
    // A `let` whose reference pattern binds nothing drops the statement.
    assert_eq!(
        elisions("{ let &_ = p; true }").discarded_statements,
        ["let &_ = p;"]
    );
}

/// `let &t = v` of a value that is no reference dereferences it, which the
/// claim side refuses naming the dereference; the parser only reads the level.
#[test]
fn a_reference_pattern_reads_through_what_it_matches() {
    let parsed = parse_contract("forall<v: Int> { let &t = v; t > 0 }").expect("parses");
    assert!(
        parsed.any_recursive(|node| matches!(node, PureExpr::Deref(_))),
        "{parsed}"
    );
}

/// Outside a `let` the AST has no node for a reference pattern in an arm
/// that can fail: it is kept as its inner pattern and recorded, so a
/// consumer that reads sorts can refuse it. The driver reads the pattern as
/// before.
#[test]
fn a_reference_pattern_outside_a_let_is_recorded() {
    for (input, recorded) in [
        ("match p { Some(&t) => t > 0, None => true }", vec!["&t"]),
        (
            "match p { Some(ref t) => *t > 0, None => true }",
            vec!["ref t"],
        ),
        (
            "match p { Some(ref mut t) => true, None => true }",
            vec!["ref mut t"],
        ),
        ("{ let Some(&t) = o else { true }; t > 0 }", vec!["&t"]),
    ] {
        let parsed = parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
        let text = parsed.to_string();
        assert!(
            !text.contains("__trust_wp_borrow") && !text.contains('#'),
            "{input} leaves a marker: {text}"
        );
        assert_eq!(
            elisions(input).dropped_reference_patterns,
            recorded,
            "{input}"
        );
        assert_eq!(
            parse_contract_spanned(input).expect("parses").expr,
            parsed,
            "{input} (spanned)"
        );
    }
    // The inner pattern is what the AST keeps.
    assert_eq!(
        parse_contract("match p { Some(&t) => t > 0, _ => true }").expect("parses"),
        parse_contract("match p { Some(t) => t > 0, _ => true }").expect("parses")
    );
}

/// A reference pattern in an arm that cannot fail, an `if let` whose pattern
/// cannot fail, or a closure parameter binds as a `let` of the pattern does:
/// `&t` matches `t` against the referent. Kept as its inner pattern, `t` was
/// the reference itself.
#[test]
fn a_reference_pattern_that_cannot_fail_binds_the_referent() {
    for (input, expected) in [
        ("match p { &t => t > 0 }", "let t = *p; (t > 0)"),
        (
            "match p { &mut t => t > 0, _ => false }",
            "let t = *p; (t > 0)",
        ),
        (
            "if let &t = p { t > 0 } else { true }",
            "let t = *p; (t > 0)",
        ),
        (
            "(|(&a, b)| a > b)",
            "|$cp0| let a = *__trust_wp_tuple_get_0($cp0); let b = __trust_wp_tuple_get_1($cp0); \
             (a > b)",
        ),
    ] {
        let parsed = parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
        assert_eq!(parsed.to_string(), expected, "{input}");
        assert!(
            elisions(input).dropped_reference_patterns.is_empty(),
            "{input}"
        );
        assert_eq!(
            parse_contract_spanned(input).expect("parses").expr,
            parsed,
            "{input} (spanned)"
        );
    }
}

/// `*` of a name a `let` binds to a borrow reads the borrowed value, through
/// every level the borrow has: `let r = &v; *r` is `v`, and `**(& &v)` is `v`
/// (it was `*v`, a reference level off, which native replay alone proved of a
/// `v: &Int`).
#[test]
fn a_borrow_is_read_through_at_every_level() {
    for (input, expected) in [
        ("**(& &v) + 1 > **(& &v)", "v + 1 > v"),
        ("*(*(& &v)) > 0", "v > 0"),
        ("{ let r = &v; *r + 1 > *r }", "v + 1 > v"),
        ("{ let r = & &v; **r > 0 }", "v > 0"),
        ("{ let r = &v; let s = &r; **s > 0 }", "v > 0"),
        ("{ let r = &v; old(*r) > 0 }", "old(v) > 0"),
        (
            "*(if c { &a } else { &b }) > 0",
            "(if c { a } else { b }) > 0",
        ),
        (
            "{ let r = &v; forall<r: Int> *r > 0 }",
            "forall<r: Int> *r > 0",
        ),
    ] {
        let parsed = parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
        assert_eq!(
            inline_lets(&parsed),
            inline_lets(&parse_contract(expected).expect("parses")),
            "{input} reads {parsed}"
        );
        assert!(
            elisions(input).dropped_borrows.is_empty(),
            "{input}: {:?}",
            elisions(input)
        );
    }
    // A borrow a `*` reads only partly through is recorded once.
    assert_eq!(
        elisions("{ let r = & &v; *r == v }").dropped_borrows,
        ["&v"]
    );
    // Branches at different levels have no single reading through `*`.
    for input in [
        "*(if c { &a } else { b }) > 0",
        "*(if c { a } else { &b }) > 0",
        "*(match x { A => &a, _ => b }) > 0",
        "{ let r = if c { &a } else { b }; *r > 0 }",
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(
            err.message
                .contains("in one branch and not in another has no reading"),
            "{input}: {err}"
        );
    }
    // A branch's borrow no `*` reads through is dropped and recorded.
    assert_eq!(
        elisions("f(if c { &a } else { b }) > 0").dropped_borrows,
        ["&a"]
    );
    // A shadowing binder is not the borrow.
    assert_eq!(
        elisions("{ let r = &v; forall<r: &Int> *r > 0 }").dropped_borrows,
        Vec::<String>::new()
    );
}

/// A method call's receiver whose reference level the AST drops is a
/// reference to Rust's method lookup, which starts at the reference's type;
/// read as its referent it would select the referent's method
/// (method_call_borrowed_receiver_*_granted.rs). The call is the refusal
/// marker, receiver first; a receiver read through its borrow, and one with
/// no borrow, stay method calls.
#[test]
fn a_method_call_on_a_dropped_borrow_is_refused() {
    use crate::logic::identity::is_refused_logic_fn_marker;
    for input in [
        "(&a).m()",
        "(&mut a).m(b)",
        "{ let r = &a; r.m() }",
        "{ let ref r = a; r.m() }",
        "(if c { &a } else { &b }).m()",
    ] {
        let parsed = parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
        let refused = inline_lets(&parsed).any_recursive(|node| {
            matches!(node, PureExpr::LogicFnCall { name, .. } if is_refused_logic_fn_marker(name))
        });
        assert!(refused, "{input} reads {parsed}");
        assert!(
            !inline_lets(&parsed).any_recursive(|node| matches!(node, PureExpr::MethodCall { .. })),
            "{input} reads {parsed}"
        );
        assert_eq!(
            parse_contract_spanned(input).expect("parses").expr,
            parsed,
            "{input} (spanned)"
        );
    }
    for input in ["(*&a).m()", "{ let r = &a; (*r).m() }", "a.m()", "(*a).m()"] {
        let parsed = parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
        assert!(
            inline_lets(&parsed).any_recursive(|node| matches!(node, PureExpr::MethodCall { .. })),
            "{input} reads {parsed}"
        );
    }
}

/// A borrow is a reference, never an integer or a `bool`: an annotation that
/// says it is one was put on the borrowed operand, a reference level off.
#[test]
fn an_integer_annotation_on_a_borrow_is_refused() {
    for input in [
        "(&p : Int) > 0",
        "{ let t: Int = &p; t > 0 }",
        "(old(&p) : bool)",
        "((if c { &a } else { &b }) : Int) > 0",
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(err.message.contains("on the borrow `&"), "{input}: {err}");
    }
    // An annotation it cannot check names the operand as written.
    assert_eq!(
        elisions("(f(&x) : Int) > 0").unchecked_annotations,
        ["type ascription `: Int` on `f(&x)`"]
    );
}

/// The spanned parser built `final_value(e)` and `view(e)` as logic-function
/// calls where the unspanned parser builds the `^e` and `e@` nodes, so
/// `final_value(&p)` was recorded as a dropped borrow there but not refused.
#[test]
fn both_parsers_read_final_value_and_view_as_nodes() {
    for input in [
        "final_value(p) == ^p",
        "view(b) + 1 > b@",
        "old(final_value(p)) > 0",
    ] {
        assert_eq!(
            parse_contract_spanned(input).expect("parses").expr,
            parse_contract(input).expect("parses"),
            "{input}"
        );
    }
    let err = parse_contract_spanned("final_value(&p) > 0").unwrap_err();
    assert!(
        err.message.contains("`final_value` of the borrow `&p`"),
        "{err}"
    );
}

/// A generic argument was parsed by a parser of its own whose records were
/// thrown away, and whose refusal made the argument a type: what a const
/// argument writes is the clause's, as anywhere else in it.
#[test]
fn a_generic_argument_is_parsed_like_the_rest_of_the_clause() {
    let written = elisions("f::<{ (x : u8) }>(y) > 0").written_types;
    assert!(
        written
            .iter()
            .any(|written| written.text.as_deref() == Some("u8")),
        "{written:?}"
    );
    assert_eq!(
        elisions("f::<{ lemma(x); 1 }>(y) > 0").discarded_statements,
        ["lemma(x);"]
    );
    for (input, named) in [
        ("f::<{ 256u8 }>(y) > 0", "256"),
        ("f::<300u8>(y) > 0", "300"),
        (
            "forall<v: bool> f::<{ (v : Int) }>(y) > 0",
            "`v` is annotated at sort Int where it is bound at sort Bool",
        ),
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(err.message.contains(named), "{input}: {err}");
    }
    // A type argument stays a type.
    for input in [
        "f::<T>(y) > 0",
        "f::<Vec<u8>>(y) > 0",
        "f::<[u8; 4]>(y) > 0",
    ] {
        parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
    }
    // The argument's own counters continue the clause's: two 64-bit casts
    // bind two names.
    let parsed = parse_contract("(a + b) as u64 == f::<{ (c + d) as u64 }>(y)").expect("parses");
    let mut names = Vec::new();
    parsed.for_each_recursive(|node| {
        if let PureExpr::Let { var, .. } = node {
            names.push(var.clone());
        }
    });
    names.sort();
    names.dedup();
    assert_eq!(names.len(), 2, "{parsed}");
}

/// A const generic argument (a block, a literal) is an expression whatever
/// characters it holds. One holding `&`, `*`, `[`, `'` or a `<` past its
/// start was made a type placeholder, which the driver drops: `addn::<{ 2 *
/// 3 }>(x) == addn::<{ 1 * 3 }>(x)` read `addn(x) == addn(x)` and verified,
/// `f::<{ ^&p }>` and `f::<{ 1 +* }>` parsed, and `f::<{ &p }>` recorded no
/// borrow.
#[test]
fn a_const_generic_argument_is_an_expression() {
    let argument = |input: &str| {
        let parsed = parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
        let mut arguments = Vec::new();
        parsed.for_each_recursive(|node| {
            if let PureExpr::LogicFnCall { name, args } = node {
                if name == TURBOFISH_ARG_WRAPPER_NAME {
                    arguments.extend(args.iter().cloned());
                }
            }
        });
        assert_eq!(arguments.len(), 1, "{input}: {parsed}");
        arguments.remove(0)
    };
    for (input, expected) in [
        ("f::<{ 2 * 3 }>(x) > 0", "2 * 3"),
        ("f::<{ a[0] }>(x) > 0", "a[0]"),
        ("f::<{ *p }>(x) > 0", "*p"),
        (
            "f::<{ if c { 1 } else { 2 } }>(x) > 0",
            "if c { 1 } else { 2 }",
        ),
        ("f::<-1>(x) > 0", "-1"),
    ] {
        assert_eq!(
            argument(input),
            parse_contract(expected).expect("parses"),
            "{input}"
        );
    }
    for (input, named) in [
        ("f::<{ ^&p }>(p) > 0", "`^` of the borrow `&p`"),
        ("f::<{ 1 +* }>(p) > 0", "generic argument `{ 1 +* }`"),
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(err.message.contains(named), "{input}: {err}");
    }
    assert_eq!(elisions("f::<{ &p }>(p) > 0").dropped_borrows, ["&p"]);
    // A type argument stays a placeholder.
    for input in ["f::<&T>(x) > 0", "f::<[u8; 4]>(x) > 0", "f::<'a>(x) > 0"] {
        assert!(
            matches!(
                argument(input),
                PureExpr::Var(_, Some(crate::formula::ExprSort::TypeParam(_)))
            ),
            "{input}"
        );
    }
}

/// In `ref x @ p` only `x` binds by reference: `p` matches the value itself.
/// The whole alias was read as a binding by reference, so every name `p`
/// binds was a borrow of what it matches, one level off (`*t` read the
/// value, where `t` is the value and `*t` has no reading of an integer).
/// Rust writes a name after `ref`, nothing else.
#[test]
fn a_binding_by_reference_binds_only_its_name() {
    for (input, expected) in [
        ("{ let ref a @ t = p; *t > 0 }", "*p > 0"),
        ("{ let ref a @ t = p; *a == t }", "p == p"),
        ("{ let ref mut a @ t = p; **a == *t }", "*p == *p"),
        (
            "{ let ref a @ b @ t = p; *a == t && b == t }",
            "p == p && p == p",
        ),
        ("{ let ref a @ ref b @ t = p; *a == *b }", "p == p"),
        (
            "{ let (ref a @ t, u) = (p, q); *a == t && u > 0 }",
            "p == p && q > 0",
        ),
    ] {
        let parsed = parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
        assert_eq!(
            tuple_beta(&inline_lets(&parsed)),
            tuple_beta(&inline_lets(&parse_contract(expected).expect("parses"))),
            "{input} reads {parsed}"
        );
        assert_eq!(
            parse_contract_spanned(input).expect("parses").expr,
            parsed,
            "{input} (spanned)"
        );
    }
    parse_contract("match p { ref Some(t) => t > 0, _ => true }").unwrap_err();
    // Outside a `let` the alias keeps its subpattern, and the level is
    // recorded once.
    assert_eq!(
        elisions("match p { ref a @ Some(t) => t > 0, _ => true }").dropped_reference_patterns,
        ["ref a @ Some(t)"]
    );
    for input in [
        "{ let ref (t) = p; t > 0 }",
        "{ let ref &t = p; t > 0 }",
        "{ let ref mut (a, b) = p; a > 0 }",
        "{ let ref _ = p; true }",
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(
            err.message.contains("expected an identifier after `ref`"),
            "{input}: {err}"
        );
    }
}

/// A pattern binds each name once, as rustc requires (E0416): the desugaring
/// bound the name twice, and read the second binding.
#[test]
fn a_name_bound_twice_in_one_pattern_is_refused() {
    for input in [
        "{ let (t, t) = (a, 0); t == 0 }",
        "{ let t @ Some(t) = o; t == t }",
        "{ let ref t @ t = p; true }",
        "match p { (a, a) => a > 0 }",
        "if let S { a, b: a } = s { a > 0 } else { true }",
        "(|(a, a)| a > 0)",
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(
            err.message
                .contains("is bound more than once in the same pattern"),
            "{input}: {err}"
        );
    }
}

/// A pattern reads the value it matches once, before any name it binds: an
/// alias's subpattern was matched against the value after the alias rebound
/// its names (`let x @ y = x + 1` read `y` as the new `x` plus one), and each
/// field of a tuple read the value inside the fields bound before it (`let
/// (a, b) = (b, a)` read the new `b` as the new `a`).
#[test]
fn a_pattern_reads_the_value_before_the_names_it_binds() {
    for (input, expected) in [
        ("{ let x @ y = x + 1; y == x }", "x + 1 == x + 1"),
        ("{ let x @ y = x + 1; y > 0 }", "x + 1 > 0"),
        ("{ let (a, b) = (b, a); a - b }", "b - a"),
        ("{ let (a, (b, c)) = (c, (a, b)); a + b * c }", "c + a * b"),
        (
            "{ let S(a, b) = S(b, a); a - b }",
            "__trust_wp_tuple_get_0(S(b, a)) - __trust_wp_tuple_get_1(S(b, a))",
        ),
        ("{ let (a, b) = (x, y); a - b }", "x - y"),
    ] {
        let parsed = parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}"));
        let expected = parse_contract(expected).expect("parses");
        assert_eq!(
            tuple_beta(&inline_lets(&parsed)),
            tuple_beta(&inline_lets(&expected)),
            "{input} reads {parsed}"
        );
    }
    // A value that reads no name the pattern binds is read in place.
    let parsed = parse_contract("{ let (a, b) = (x, y); a - b }").expect("parses");
    assert!(!parsed.to_string().contains("$let"), "{parsed}");
}

/// `*` or `^` of an `if` or `match` one branch of which is a borrow and
/// another not has no reading: `*` would read the branches at two levels,
/// and `^(if c { &p } else { q })` was read as `^(if c { p } else { q })`,
/// the final value of `p`, and verified. `^` of an operand that drops a
/// borrow anywhere is refused too: the AST cannot say whether the borrow
/// reaches the value `^` reads (`^id(&p)` read `^id(p)`).
#[test]
fn a_reference_level_in_a_branch_is_read_or_refused() {
    for (input, named) in [
        (
            "^(if c { &p } else { q }) > 0",
            "`^` of a value that is the borrow `&p` in one branch",
        ),
        (
            "^(if c { q } else { &p }) > 0",
            "`^` of a value that is the borrow `&p` in one branch",
        ),
        (
            "^(match x { A => &p, _ => q }) > 0",
            "`^` of a value that is the borrow `&p` in one branch",
        ),
        (
            "^(match 0 { _ => &p }) > 0",
            "`^` of the borrow `&p` has no reading",
        ),
        (
            "^(if c { &p } else { &q }) > 0",
            "`^` of the borrow `&p` has no reading",
        ),
        (
            "{ let r = if c { &p } else { q }; ^r > 0 }",
            "`^` of a value that is the borrow `&p`",
        ),
        (
            "^{ let r = &p; r } > 0",
            "`^` of the borrow `&p` has no reading",
        ),
        (
            "*(if c { &a } else { b }) > 0",
            "`*` of a value that is the borrow `&a` in one branch",
        ),
        (
            "^id(&p) > 0",
            "`^` of an operand that holds the borrow `&p`",
        ),
        (
            "^((&p, 0).0) > 0",
            "`^` of an operand that holds the borrow `&p`",
        ),
        (
            "final_value(g(&mut p)) > 0",
            "`^` of an operand that holds the borrow `&mut p`",
        ),
    ] {
        for parse in [
            |input: &str| parse_contract(input).map(|_| ()),
            |input: &str| parse_contract_spanned(input).map(|_| ()),
        ] {
            let err = parse(input).unwrap_err();
            assert!(err.message.contains(named), "{input}: {err}");
        }
    }
    // Controls: a level every branch has is read through, and `^` of an
    // operand no borrow reaches is read.
    for (input, expected) in [
        (
            "*(if c { &a } else { &b }) > 0",
            "(if c { a } else { b }) > 0",
        ),
        (
            "*(match x { A => &a, _ => &b }) > 0",
            "(match x { A => a, _ => b }) > 0",
        ),
        ("^*&p > 0", "^p > 0"),
        (
            "^(if c { p } else { q }) > 0",
            "^(if c { p } else { q }) > 0",
        ),
        (
            "^(if *&c { p } else { q }) > 0",
            "^(if c { p } else { q }) > 0",
        ),
    ] {
        assert_eq!(
            parse_contract(input).unwrap_or_else(|e| panic!("{input}: {e}")),
            parse_contract(expected).expect("parses"),
            "{input}"
        );
    }
}

/// `tuple_get_N(tupleK(..))` reduced, for comparing a desugared pattern to
/// what it reads.
fn tuple_beta(expr: &PureExpr) -> PureExpr {
    expr.substitute(&std::collections::HashMap::new())
}

/// A long clause with a borrow is resolved without exhausting the stack.
#[test]
fn a_deep_clause_with_a_borrow_resolves() {
    let chain = (0..2000)
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(" + ");
    let input = format!("*&v + {chain} > 0");
    let (_, elisions) = parse_contract_with_elisions(&input).expect("parses");
    assert_eq!(elisions.dropped_borrows, Vec::<String>::new());
    for input in [
        format!("{chain} + f(&v) > 0"),
        format!("f(&v) + {chain} > 0"),
    ] {
        let (_, elisions) = parse_contract_with_elisions(&input).expect("parses");
        assert_eq!(elisions.dropped_borrows, ["&v"]);
    }
}

/// `let` bodies inlined, for comparing a desugared binding to what it reads.
fn inline_lets(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Let { var, value, body } => {
            let mut substitution = std::collections::HashMap::new();
            substitution.insert(var, value.as_ref().clone());
            body.substitute_capture_avoiding(
                &substitution,
                &crate::formula::CaptureAvoidingSubstOptions::default(),
            )
        }
        node => node,
    })
}
