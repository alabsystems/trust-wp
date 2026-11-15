// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A cast is Rust's `as`, never its operand; an annotation keeps its
//! operand's value and states its sort; a literal outside its suffix's type,
//! a refutable `let` and a statement a block drops are refused or recorded.

use super::*;

/// Evaluate the integer arithmetic a lowered cast is made of, in `i128`,
/// with Euclidean `div`/`mod`. Shares nothing with the parser.
fn eval(expr: &PureExpr, env: &mut Vec<(String, i128)>) -> i128 {
    match expr {
        PureExpr::Int(value) => i128::from(*value),
        PureExpr::Var(name, _) => {
            env.iter()
                .rev()
                .find(|(bound, _)| bound == name)
                .unwrap_or_else(|| panic!("`{name}` is bound"))
                .1
        }
        PureExpr::UnOp(UnOp::Neg, inner) => -eval(inner, env),
        PureExpr::BinOp(left, op, right) => {
            let (left, right) = (eval(left, env), eval(right, env));
            match op {
                BinOp::Add => left + right,
                BinOp::Sub => left - right,
                BinOp::Mul => left * right,
                BinOp::Div => left.div_euclid(right),
                BinOp::Mod => left.rem_euclid(right),
                other => panic!("a lowered cast has no {other:?}"),
            }
        }
        PureExpr::Let { var, value, body } => {
            let value = eval(value, env);
            env.push((var.clone(), value));
            let result = eval(body, env);
            env.pop();
            result
        }
        other => panic!("a lowered cast has no {other:?}"),
    }
}

/// Rust's own `as`, from an `i128` source.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn rust_as(value: i128, target: &str) -> i128 {
    match target {
        "u8" => i128::from(value as u8),
        "u16" => i128::from(value as u16),
        "u32" => i128::from(value as u32),
        "u64" => i128::from(value as u64),
        "i8" => i128::from(value as i8),
        "i16" => i128::from(value as i16),
        "i32" => i128::from(value as i32),
        "i64" => i128::from(value as i64),
        other => panic!("`{other}` is not a modeled target"),
    }
}

fn cast_sources() -> Vec<i64> {
    let mut values = vec![
        0,
        1,
        -1,
        2,
        -2,
        127,
        128,
        -128,
        -129,
        255,
        256,
        -256,
        32_767,
        32_768,
        -32_768,
        -32_769,
        65_535,
        65_536,
        i64::from(i32::MAX),
        i64::from(i32::MAX) + 1,
        i64::from(i32::MIN),
        i64::from(i32::MIN) - 1,
        i64::from(u32::MAX),
        i64::from(u32::MAX) + 1,
        -i64::from(u32::MAX),
        -(1 << 32) - 1,
        i64::MAX,
        i64::MAX - 1,
        i64::MIN,
        i64::MIN + 1,
    ];
    // xorshift64: the same spread on every run.
    let mut state = 0x6361_7374_5f74_6573_u64;
    for _ in 0..200 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        values.push(i64::from_ne_bytes(state.to_ne_bytes()));
    }
    values
}

#[test]
fn every_modeled_cast_is_rusts_as_exactly() {
    for target in ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"] {
        for value in cast_sources() {
            // A literal operand is duplicated; a compound one is `let`-bound.
            for text in [
                format!("({value}) as {target}"),
                format!("(({value}) + 0) as {target}"),
            ] {
                let lowered = parse_ok(&text);
                assert_eq!(
                    eval(&lowered, &mut Vec::new()),
                    rust_as(i128::from(value), target),
                    "{text} lowered to {lowered:?}"
                );
            }
        }
    }
}

#[test]
fn a_cast_of_a_name_is_arithmetic_over_the_name() {
    let x = || Arc::new(PureExpr::Var("x".into(), None));
    let int = |value: i64| Arc::new(PureExpr::Int(value));
    assert_eq!(
        parse_ok("x as u8"),
        PureExpr::BinOp(x(), BinOp::Mod, int(256))
    );
    assert_eq!(
        parse_ok("x as i8"),
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(x(), BinOp::Add, int(128))),
                BinOp::Mod,
                int(256),
            )),
            BinOp::Sub,
            int(128),
        )
    );
    // The value, not the operand: `(x as u8) == x` is not `x == x`.
    assert_ne!(parse_ok("(x as u8) == x"), parse_ok("x == x"));
    // Nested and chained casts compose; a compound 64-bit operand is bound
    // once rather than duplicated.
    let chained = parse_ok("x as u64 as i8 as u32");
    let mut env = vec![("x".to_string(), -300)];
    assert_eq!(
        eval(&chained, &mut env),
        rust_as(rust_as(rust_as(-300, "u64"), "i8"), "u32")
    );
    assert!(matches!(
        parse_ok("(x + 1) as i64"),
        PureExpr::Let { ref var, .. } if var == "$cast0"
    ));
    // Unary minus binds tighter than `as`: `-1 as u8` is `(-1) as u8`.
    assert_eq!(eval(&parse_ok("-1 as u8"), &mut Vec::new()), 255);
    // Spanned and plain parses agree.
    for input in ["x as u64 == (y + 1) as i32", "(x as i8)@ == 3"] {
        assert_eq!(parse_ok(input), parse_spanned_ok(input).expr, "{input}");
    }
}

#[test]
fn a_cast_the_parser_cannot_model_is_refused_by_name() {
    for (input, named) in [
        ("x as usize == 0", "cast `as usize`"),
        ("x as isize == 0", "cast `as isize`"),
        ("x as u128 == 0", "cast `as u128`"),
        ("x as i128 == 0", "cast `as i128`"),
        ("x as f64 == 0", "cast `as f64`"),
        ("x as f32 == 0", "cast `as f32`"),
        ("x as char == 'a'", "cast `as char`"),
        ("x as bool", "cast `as bool`"),
        ("x as Int == 0", "cast `as Int`"),
        ("(x as Wd)@ == 0", "cast `as Wd`"),
        (
            "x as std::primitive::u8 == 0",
            "cast `as std::primitive::u8`",
        ),
    ] {
        for err in [
            parse_contract(input).unwrap_err(),
            parse_contract_spanned(input).unwrap_err(),
        ] {
            assert!(err.message.contains(named), "{input}: {err}");
        }
    }
}

#[test]
fn an_annotation_states_its_operands_sort() {
    // Pushed to the names that yield the value.
    assert_eq!(
        parse_ok("(if c { x } else { old(y) } : Int)"),
        PureExpr::Ite(
            Arc::new(PureExpr::Var("c".into(), None)),
            Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
            Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
                "y".into(),
                Some(ExprSort::Int)
            )))),
        )
    );
    // An operand whose syntax has the other sort is refused, not coerced.
    for (input, named) in [
        (
            "((x > 0) : Int) == ((x > 0) : Int)",
            "type ascription `: Int`",
        ),
        ("((x + 1) : bool)", "type ascription `: bool`"),
        ("(true : u8) == 1", "type ascription `: u8`"),
        ("{ let t: bool = x + 1; t }", "`let` annotation `: bool`"),
        ("{ let t: Int = x > 0; t }", "`let` annotation `: Int`"),
        (
            "(300 : u8) == 300",
            "type ascription `: u8` on the literal 300",
        ),
        (
            "(-1 : u64) < 0",
            "type ascription `: u64` on the literal -1",
        ),
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(err.message.contains(named), "{input}: {err}");
    }
    // A `let` annotation reads the value at its sort; the name bound to the
    // name `b` is `b`.
    assert_eq!(
        parse_ok("{ let t: bool = b; t }"),
        PureExpr::Var("b".into(), Some(ExprSort::Bool))
    );
    assert_eq!(
        parse_ok("{ let t: bool = b || c; t }"),
        PureExpr::Let {
            var: "t".into(),
            value: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("b".into(), None)),
                crate::formula::BinOp::Or,
                Arc::new(PureExpr::Var("c".into(), None))
            )),
            body: Arc::new(PureExpr::Var("t".into(), None)),
        }
    );
    // Any other type leaves the operand as written, for consumers that read
    // the written type itself.
    assert_eq!(parse_ok("(x : Wd)"), PureExpr::Var("x".into(), None));
}

#[test]
fn a_literal_its_suffix_cannot_hold_is_refused() {
    for input in [
        "256u8 == 0",
        "-1u8 < 0",
        "128i8 == 0",
        "-129i8 == 0",
        "0x100u8 == 0",
        "65536u16 == 0",
        "4294967296u32 == 0",
        "-1usize == 0",
        "-1u64 == 0",
        "-1u128 == 0",
        "match x { 256u8 => true, _ => false }",
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(
            err.message.contains("outside the range of"),
            "{input}: {err}"
        );
    }
    for (input, value) in [
        ("255u8", 255),
        ("-128i8", -128),
        ("127i8", 127),
        ("0xFFu8", 255),
        ("4294967295u32", 4_294_967_295),
        ("-9223372036854775808i64", i64::MIN),
        ("9223372036854775807u64", i64::MAX),
        ("-5int", -5),
        ("3u128", 3),
        ("9223372036854775807u128", i64::MAX),
        ("-3i128", -3),
    ] {
        assert_eq!(parse_ok(input), PureExpr::Int(value), "{input}");
    }
}

#[test]
fn a_refutable_let_is_refused_and_a_dropped_statement_recorded() {
    for input in [
        "{ let 5 = x; true }",
        "{ let (0, y) = t; y }",
        "{ let Some(0) = o; true }",
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(err.message.contains("literal pattern"), "{input}: {err}");
    }
    // `let ... else` keeps the test.
    assert!(matches!(
        parse_ok("{ let 5 = x else { false }; true }"),
        PureExpr::Match { .. }
    ));
    let dropped = |input: &str| {
        parse_contract_with_elisions(input)
            .unwrap_or_else(|err| panic!("{input}: {err}"))
            .1
            .discarded_statements
    };
    assert_eq!(dropped("{ false; true }"), vec!["false;"]);
    assert_eq!(
        dropped("{ proof_assert!(x > 0); lemma(x); x > 0 }"),
        vec!["proof_assert!(x > 0);", "lemma(x);"]
    );
    assert_eq!(dropped("{ let _ = f(x); true }"), vec!["let _ = f(x);"]);
    assert_eq!(dropped("{ use a::b; true }"), vec!["use a::b;"]);
    assert_eq!(dropped("{ let t = x; t > 0 }"), Vec::<String>::new());
    assert_eq!(dropped("x + 1 > x"), Vec::<String>::new());
}

/// Measured: an annotation on a bound name was checked only against the
/// name's syntax, so `forall<v: bool> (v : Int) + 1 > (v : Int)` parsed with
/// `v` carried at `Int` under a `bool` binder, and the native bundle path
/// verified it (and the four shapes below it) at exit 0. An annotation must
/// agree with the sort its name already has in scope — declared by a
/// quantifier or closure binder, or the sort of the value a `let` binds —
/// and one that does not is refused naming the name, by every entry point.
#[test]
fn an_annotation_agrees_with_the_sort_its_name_has_in_scope() {
    for (input, named) in [
        (
            "forall<v: bool> (v : Int) + 1 > (v : Int)",
            "`v` is annotated at sort Int where it is bound at sort Bool",
        ),
        (
            "forall<v: Int> (v : bool) || true",
            "`v` is annotated at sort Bool where it is bound at sort Int",
        ),
        (
            "forall<v: bool> { let t: Int = v; t + 1 > t }",
            "`v` is annotated at sort Int where it is bound at sort Bool",
        ),
        (
            "forall<v: Int> { let t = (v : bool); t || true }",
            "`v` is annotated at sort Bool where it is bound at sort Int",
        ),
        (
            "forall<x: Int> ((x : bool) == (x : bool)) && (x + 1 > x)",
            "`x` is annotated at sort Bool where it is bound at sort Int",
        ),
        (
            "exists<v: u8> (v : bool)",
            "`v` is annotated at sort Bool where it is bound at sort Int",
        ),
        (
            "forall<p: &T> (p : Int) > 0",
            "`p` is annotated at sort Int where it is bound at sort &TypeParam(T)",
        ),
        // A `let` name has its value's sort, however the value states it.
        (
            "{ let t = x > 0; (t : Int) + 1 > 0 }",
            "`t` is annotated at sort Int where it is bound at sort Bool",
        ),
        (
            "forall<v: bool> { let t = v; (t : Int) > 0 }",
            "`t` is annotated at sort Int where it is bound at sort Bool",
        ),
        (
            "forall<v: bool> { let t = old(v); (if c { t } else { t } : Int) > 0 }",
            "`t` is annotated at sort Int where it is bound at sort Bool",
        ),
        // The innermost binder is the one that counts.
        (
            "forall<v: Int> forall<v: bool> (v : Int) > 0",
            "`v` is annotated at sort Int where it is bound at sort Bool",
        ),
        (
            "|v: bool| (v : Int) > 0",
            "`v` is annotated at sort Int where it is bound at sort Bool",
        ),
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(err.message.contains(named), "{input}: {err}");
        for other in [
            parse_contract_spanned(input).map(|_| ()),
            parse_contract_body(input).map(|_| ()),
            parse_contract_with_elisions(input).map(|_| ()),
            parse_contract_written_types(input).map(|_| ()),
        ] {
            assert_eq!(other.unwrap_err().message, err.message, "{input}");
        }
    }
    // Reported at the annotation.
    let input = "forall<v: bool> (v : Int) > 0";
    assert_eq!(
        parse_contract(input).unwrap_err().position,
        input.find(": Int").expect("the annotation")
    );
    // Controls: an annotation agreeing with the binder, a binder that fixes
    // no sort, an inner binder shadowing an outer one, and a free name.
    for input in [
        "forall<v: Int> (v : Int) + 1 > v",
        "forall<v: u8> (v : Int) >= 0",
        "forall<v: bool> (v : bool) == v",
        "forall<v: Int> { let t: Int = v; t + 1 > t }",
        "forall<v: bool> { let t = (v : bool); t || !t }",
        "forall<v> (v : Int) > 0",
        "forall<v: bool> forall<v: Int> (v : Int) > 0",
        "forall<v: bool> match o { Some(v) => (v : Int) > 0, None => v }",
        "forall<v: bool> (|v: Int| (v : Int) > 0)",
        "forall<v: bool> { let v = 1; (v : Int) > 0 }",
        "(x : Int) + 1 > x",
    ] {
        parse_ok(input);
    }
}

/// `*` of a borrow is the borrowed value, parenthesized or not: reading
/// through it reads `e` at its own sort. `*&e` was a dereference of `e`,
/// which the claim-side readers took for the referent of whatever `e` is
/// (`forall<v: bool> *&v + 1 > *&v` verified), and `*(&v)` still was (a
/// `forall<v: &Int> *(&v) + 1 > *(&v)` verified). A dereference of anything
/// else stays one.
#[test]
fn a_dereference_of_a_borrow_is_the_borrowed_value() {
    for (input, expected) in [
        ("*&v + 1 > *&v", "v + 1 > v"),
        ("*&mut v == v", "v == v"),
        ("* & v", "v"),
        ("*&*&v", "v"),
        ("forall<v: bool> *&v || true", "forall<v: bool> v || true"),
        ("*(&v) + 1 > *(&v)", "v + 1 > v"),
        ("*((&mut v)) == * ( & v )", "v == v"),
        ("**(&p)", "*p"),
        ("*(&(&v))", "v"),
    ] {
        assert_eq!(
            parse_contract(input).expect("parses"),
            parse_contract(expected).expect("parses"),
            "{input}"
        );
        assert_eq!(
            parse_contract_spanned(input).expect("parses").expr,
            parse_contract(expected).expect("parses"),
            "{input} (spanned)"
        );
    }
    // A borrow that is only part of the operand is no borrow of it.
    for input in ["*v", "&*v", "*(&v)[0]", "*(&v + 1)", "*(&v).len()"] {
        assert!(
            matches!(parse_contract(input).expect("parses"), PureExpr::Deref(_)),
            "{input}"
        );
    }
}

/// `^` of a borrow reads the final value of a reference the AST never forms:
/// the borrow is dropped, so `^&p` read as `^p` and `forall<p: &mut Int>
/// (0 < 1 ==> ^&p + 1 > ^&p)` verified, though `^` of the shared reference
/// `&p` has no reading and the final value of a reborrow `&mut p` is a
/// reference. Every spelling is refused, in both parsers.
#[test]
fn the_final_value_of_a_borrow_is_refused() {
    for (input, named) in [
        ("^&p + 1 > ^&p", "`^` of the borrow `&p`"),
        ("^(&p)", "`^` of the borrow `&p`"),
        ("^(&mut p) == ^p", "`^` of the borrow `&mut p`"),
        ("^& &p", "`^` of the borrow `& &p`"),
        ("^&*p", "`^` of the borrow `&*p`"),
        ("^&mut *p", "`^` of the borrow `&mut *p`"),
        ("old(^&p) > 0", "`^` of the borrow `&p`"),
        ("final_value(&p) > 0", "`final_value` of the borrow `&p`"),
        (
            "final_value( &mut p ) > ^p",
            "`final_value` of the borrow `&mut p`",
        ),
        ("^*(& &p)", "`^` of the borrow `&p`"),
        ("{ let r = &p; ^r }", "`^` of `r`, bound to the borrow `&p`"),
        (
            "{ let r = &mut p; ^r > 0 }",
            "`^` of `r`, bound to the borrow `&mut p`",
        ),
        (
            "{ let ref t = p; ^t > 0 }",
            "`^` of `t`, bound to the borrow `ref t`",
        ),
        (
            "{ let ref mut t = p; old(^t) > 0 }",
            "`^` of `t`, bound to the borrow `ref mut t`",
        ),
        ("{ let r = & &p; ^*r > 0 }", "`^` of the borrow `&p`"),
        (
            "{ let r = &p; let s = r; ^s > 0 }",
            "`^` of `s`, bound to the borrow `&p`",
        ),
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(err.message.contains(named), "{input}: {err}");
        let err = parse_contract_spanned(input).unwrap_err();
        assert!(err.message.contains(named), "{input} (spanned): {err}");
    }
    // `^` of a dereferenced borrow is `^` of the borrowed reference.
    assert_eq!(
        parse_contract("^*&mut p").expect("parses"),
        parse_contract("^p").expect("parses")
    );
}

/// A borrow no `*` reads through is recorded: the AST keeps its operand, a
/// reference level below the borrow (`let r = &p; ^r` read `^p`).
#[test]
fn a_borrow_the_ast_drops_is_recorded() {
    let dropped = |input: &str| {
        parse_contract_with_elisions(input)
            .expect("parses")
            .1
            .dropped_borrows
    };
    assert_eq!(dropped("{ let r = &p; r == q }"), ["&p"]);
    assert_eq!(dropped("{ let r = &p; *r == r }"), ["&p"]);
    assert_eq!(dropped("result == &mut r.0"), ["&mut r.0"]);
    assert_eq!(dropped("*(&(&v)) == v"), ["&v"]);
    assert_eq!(dropped("f(&x, &mut y)"), ["&x", "&mut y"]);
    for input in [
        "*&v == v",
        "*(&v) + 1 > *( &mut v )",
        "**&p",
        "x && y",
        "{ let r = &p; *r > 0 }",
        "{ let r = &p; true }",
    ] {
        assert!(dropped(input).is_empty(), "{input}");
    }
}

/// A `let` of `*p` binds the sort `p` references, so an annotation that says
/// otherwise disagrees with it: `forall<p: &bool> { let t = *p; (t : Int) + 1
/// > (t : Int) }` read `t` as an integer.
#[test]
fn a_let_of_a_dereference_has_the_referent_sort() {
    for (input, named) in [
        (
            "forall<p: &bool> { let t = *p; (t : Int) + 1 > (t : Int) }",
            "`t` is annotated at sort Int where it is bound at sort Bool",
        ),
        (
            "forall<p: &mut bool> { let t = *p; (t : Int) > 0 }",
            "`t` is annotated at sort Int where it is bound at sort Bool",
        ),
        (
            "forall<p: &&Int> { let t = **p; (t : bool) }",
            "`t` is annotated at sort Bool where it is bound at sort Int",
        ),
        (
            "forall<p: &mut Int> { let t = ^p; (t : bool) }",
            "`t` is annotated at sort Bool where it is bound at sort Int",
        ),
    ] {
        let err = parse_contract(input).unwrap_err();
        assert!(err.message.contains(named), "{input}: {err}");
    }
    for input in [
        "forall<p: &Int> { let t = *p; (t : Int) + 1 > t }",
        "forall<p: &bool> { let t = *p; (t : bool) || true }",
        // `^` of a shared reference fixes no sort here; the claim side
        // refuses it.
        "forall<p: &Int> { let t = ^p; (t : bool) }",
    ] {
        parse_ok(input);
    }
}
