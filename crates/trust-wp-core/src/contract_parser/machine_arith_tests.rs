// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{BTreeMap, HashMap};

use super::*;
use crate::contract_parser::{parse_contract, parse_contract_spanned};

fn typed(kinds: &[(ArithOp, OpReading, usize)]) -> TextReading {
    TextReading {
        kinds: kinds
            .iter()
            .map(|(op, reading, typed)| {
                (
                    *op,
                    KindReading {
                        reading: reading.clone(),
                        typed: Some(*typed),
                    },
                )
            })
            .collect::<BTreeMap<_, _>>(),
    }
}

fn u32_ty() -> MachineInt {
    MachineInt::new(32, false).unwrap()
}

fn with<R>(texts: &[(&str, TextReading)], f: impl FnOnce() -> R) -> R {
    install_for_thread(
        texts
            .iter()
            .map(|(text, reading)| ((*text).to_string(), reading.clone()))
            .collect::<HashMap<_, _>>(),
    );
    let out = f();
    clear_for_thread();
    out
}

#[test]
fn nothing_installed_reads_every_operator_mathematically() {
    let expr = parse_contract("a + b >= a").unwrap();
    assert!(!expr.to_string().contains("ite"));
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Ge, _)));
}

/// `cond ==> body` conjuncts of a lifted comparison, in order.
fn lifted_cases(expr: &PureExpr) -> Vec<(PureExpr, PureExpr)> {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            let mut cases = lifted_cases(left);
            cases.extend(lifted_cases(right));
            cases
        }
        PureExpr::BinOp(cond, BinOp::Implies, body) => {
            vec![(cond.as_ref().clone(), body.as_ref().clone())]
        }
        other => panic!("not a lifted comparison: {other:?}"),
    }
}

fn holds_ite(expr: &PureExpr) -> bool {
    let mut found = false;
    let _ = expr.rewrite_bottom_up(|node| {
        found |= matches!(node, PureExpr::Ite(..) | PureExpr::Let { .. });
        node
    });
    found
}

#[test]
fn a_machine_sum_wraps() {
    let text = "a + b >= a";
    let expr = with(
        &[(
            text,
            typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 1)]),
        )],
        || parse_contract(text).unwrap(),
    );
    // An unsigned sum leaves the range only upward: two cases, each a
    // comparison at that case's value, and no `ite` of integers.
    let cases = lifted_cases(&expr);
    assert_eq!(cases.len(), 2, "{expr:?}");
    assert!(matches!(cases[0].0, PureExpr::BinOp(_, BinOp::Gt, _)));
    assert!(matches!(
        &cases[0].1,
        PureExpr::BinOp(left, BinOp::Ge, _) if matches!(left.as_ref(), PureExpr::BinOp(_, BinOp::Sub, _))
    ));
    assert!(matches!(cases[1].0, PureExpr::BinOp(_, BinOp::Le, _)));
    assert!(!holds_ite(&expr), "{expr:?}");
}

#[test]
fn a_signed_sum_has_three_cases() {
    let text = "a + b > a";
    let i8_ty = MachineInt::new(8, true).unwrap();
    let expr = with(
        &[(
            text,
            typed(&[(ArithOp::Add, OpReading::Wrapping(i8_ty), 1)]),
        )],
        || parse_contract(text).unwrap(),
    );
    assert_eq!(lifted_cases(&expr).len(), 3, "{expr:?}");
}

#[test]
fn a_sum_outside_any_comparison_is_a_term() {
    let text = "p(a + b)";
    let expr = with(
        &[(
            text,
            typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 1)]),
        )],
        || parse_contract(text).unwrap(),
    );
    let PureExpr::LogicFnCall { args, .. } = &expr else {
        panic!("{expr:?}")
    };
    assert!(matches!(args[0], PureExpr::Ite(..)), "{expr:?}");
}

#[test]
fn a_sum_under_old_inside_a_comparison_is_a_term() {
    let text = "old(a + b) >= 0u32";
    let expr = with(
        &[(
            text,
            typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 1)]),
        )],
        || parse_contract(text).unwrap(),
    );
    assert!(holds_ite(&expr), "{expr:?}");
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Ge, _)), "{expr:?}");
}

#[test]
fn the_placeholder_cannot_be_spelled() {
    let error = parse_contract("__trust_wp_spec_wrap_add_u32(x) > 0").unwrap_err();
    assert!(error.message.contains("reserved"), "{error}");
}

#[test]
fn spanned_and_unspanned_parses_agree() {
    let text = "result == x + 1";
    let reading = typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 1)]);
    let (plain, spanned) = with(&[(text, reading)], || {
        (
            parse_contract(text).unwrap(),
            parse_contract_spanned(text).unwrap().into_expr(),
        )
    });
    assert_eq!(plain, spanned);
}

#[test]
fn an_int_sum_stays_mathematical() {
    let text = "a@ + b@ >= a@";
    let expr = with(
        &[(text, typed(&[(ArithOp::Add, OpReading::Mathematical, 1)]))],
        || parse_contract(text).unwrap(),
    );
    assert_eq!(expr, parse_contract(text).unwrap());
}

#[test]
fn a_count_the_type_check_does_not_hold_is_refused() {
    // Two `+` in the text, one in the type check: the second has no type.
    let text = "a + b + c >= a";
    let error = with(
        &[(
            text,
            typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 1)]),
        )],
        || parse_contract(text).unwrap_err(),
    );
    assert!(error.message.contains("D-232"), "{error}");
}

#[test]
fn an_untyped_text_keeps_only_int_syntax() {
    let error = with(&[], || parse_contract("a + b >= a").unwrap_err());
    assert!(error.message.contains("no type check"), "{error}");
    let ok = with(&[], || {
        parse_contract("a@ + 1 > a@ && s.len() - 1 >= 0").unwrap()
    });
    assert_eq!(
        ok,
        parse_contract("a@ + 1 > a@ && s.len() - 1 >= 0").unwrap()
    );
}

#[test]
fn an_untyped_text_keeps_boolean_negation() {
    let ok = with(&[], || parse_contract("!b && !(x@ > 0)").unwrap());
    assert_eq!(ok, parse_contract("!b && !(x@ > 0)").unwrap());
}

#[test]
fn a_refused_kind_refuses_the_clause() {
    let text = "a << 1u32 >= a";
    let error = with(
        &[(
            text,
            typed(&[(ArithOp::Shl, OpReading::Refused("a shift".into()), 1)]),
        )],
        || parse_contract(text).unwrap_err(),
    );
    assert!(error.message.contains("a shift"), "{error}");
}

#[test]
fn a_literal_the_type_has_no_value_for_is_refused() {
    let text = "a + 5000000000 > a";
    let error = with(
        &[(
            text,
            typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 1)]),
        )],
        || parse_contract(text).unwrap_err(),
    );
    assert!(error.message.contains("not a value of `u32`"), "{error}");
}

#[test]
fn a_negated_literal_is_not_an_operator() {
    let text = "a@ == - 1";
    let expr = with(&[(text, typed(&[]))], || parse_contract(text).unwrap());
    assert_eq!(expr, parse_contract(text).unwrap());
}

#[test]
fn a_nested_sum_is_split_innermost_first() {
    let text = "a + b + c >= a";
    let expr = with(
        &[(
            text,
            typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 2)]),
        )],
        || parse_contract(text).unwrap(),
    );
    // Two cases for `a + b`, each split again for the outer sum.
    let outer = lifted_cases(&expr);
    assert_eq!(outer.len(), 2, "{expr:?}");
    for (_, body) in &outer {
        assert_eq!(lifted_cases(body).len(), 2, "{body:?}");
    }
    assert!(!holds_ite(&expr), "{expr:?}");
}

#[test]
fn constants_beyond_i64_are_sums_of_i64_literals() {
    let modulus = constant(1_i128 << 64);
    fn eval(expr: &PureExpr) -> i128 {
        match expr {
            PureExpr::Int(v) => i128::from(*v),
            PureExpr::BinOp(l, BinOp::Add, r) => eval(l) + eval(r),
            other => panic!("{other:?}"),
        }
    }
    assert_eq!(eval(&modulus), 1_i128 << 64);
    assert_eq!(eval(&constant(-(1_i128 << 63))), -(1_i128 << 63));
    assert_eq!(eval(&constant(5)), 5);
}

#[test]
fn merging_disagreeing_readings_refuses_the_kind() {
    let a = typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 1)]);
    let b = typed(&[(
        ArithOp::Add,
        OpReading::Wrapping(MachineInt::new(64, false).unwrap()),
        1,
    )]);
    let merged = a.merge(&b);
    assert!(matches!(
        merged.kinds[&ArithOp::Add].reading,
        OpReading::Refused(_)
    ));
    assert_eq!(a.merge(&a.clone()), a);
}

#[test]
fn a_text_also_written_untyped_keeps_only_what_holds_at_any_type() {
    let text = "a + b >= a";
    let wrapping = typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 1)]);
    let error = with(&[(text, wrapping.with_untyped_occurrence())], || {
        parse_contract(text).unwrap_err()
    });
    assert!(error.message.contains("also written"), "{error}");
    let int = typed(&[(ArithOp::Add, OpReading::Mathematical, 1)]);
    let error = with(&[(text, int.with_untyped_occurrence())], || {
        parse_contract(text).unwrap_err()
    });
    assert!(error.message.contains("no type check"), "{error}");
    let views = "a@ + b@ >= a@";
    let expr = with(&[(views, int.with_untyped_occurrence())], || {
        parse_contract(views).unwrap()
    });
    assert_eq!(expr, parse_contract(views).unwrap());
}

#[test]
fn program_source_reads_every_operator_mathematically() {
    let text = "a + b";
    let reading = typed(&[(ArithOp::Add, OpReading::Wrapping(u32_ty()), 1)]);
    let (program, logic) = with(&[(text, reading)], || {
        (
            read_as_program(|| parse_contract(text).unwrap()),
            parse_contract(text).unwrap(),
        )
    });
    assert_eq!(program, parse_contract(text).unwrap());
    assert_ne!(program, logic);
    let untyped = with(&[], || read_as_program(|| parse_contract("x + y").unwrap()));
    assert_eq!(untyped, parse_contract("x + y").unwrap());
}

fn eval_int(expr: &PureExpr, x: i128) -> i128 {
    match expr {
        PureExpr::Int(v) => i128::from(*v),
        PureExpr::Var(..) => x,
        PureExpr::UnOp(UnOp::Neg, inner) => -eval_int(inner, x),
        PureExpr::BinOp(l, op, r) => {
            let (l, r) = (eval_int(l, x), eval_int(r, x));
            match op {
                BinOp::Add => l + r,
                BinOp::Sub => l - r,
                BinOp::Mul => l * r,
                BinOp::Div => l.div_euclid(r),
                BinOp::Mod => l.rem_euclid(r),
                other => panic!("{other:?}"),
            }
        }
        PureExpr::Ite(c, t, e) => {
            let PureExpr::BinOp(cl, BinOp::Lt, cr) = c.as_ref() else {
                panic!("{c:?}")
            };
            if eval_int(cl, x) < eval_int(cr, x) {
                eval_int(t, x)
            } else {
                eval_int(e, x)
            }
        }
        other => panic!("{other:?}"),
    }
}

/// `x <op> amount` on `ty`, parsed and evaluated at `x`.
fn shifted(op: &str, amount: &str, ty: MachineInt, x: i128) -> i128 {
    let text = format!("x {op} {amount}");
    let kind = if op == "<<" {
        ArithOp::Shl
    } else {
        ArithOp::Shr
    };
    let expr = with(
        &[(text.as_str(), typed(&[(kind, OpReading::Wrapping(ty), 1)]))],
        || parse_contract(&text).unwrap(),
    );
    eval_int(&expr, x)
}

#[test]
fn a_literal_shift_is_the_oracles_bit_vector_shift() {
    let u8_ty = MachineInt::new(8, false).unwrap();
    let i8_ty = MachineInt::new(8, true).unwrap();
    for x in 0..=255_i128 {
        for k in [0_i64, 1, 3, 7, 8, 9, 256, 257] {
            let amount = (i128::from(k)).rem_euclid(256);
            let shl = if amount >= 8 { 0 } else { (x << amount) & 0xff };
            let shr = if amount >= 8 { 0 } else { x >> amount };
            assert_eq!(shifted("<<", &k.to_string(), u8_ty, x), shl, "{x} << {k}");
            assert_eq!(shifted(">>", &k.to_string(), u8_ty, x), shr, "{x} >> {k}");
        }
    }
    for x in -128..=127_i128 {
        for k in [0_i64, 1, 7, 8, 300] {
            let amount = (i128::from(k)).rem_euclid(256);
            let bits = u8::try_from(x.rem_euclid(256)).unwrap();
            let shl = if amount >= 8 {
                0
            } else {
                i128::from((bits << amount) as i8)
            };
            let shr = if amount >= 8 {
                if x < 0 {
                    -1
                } else {
                    0
                }
            } else {
                i128::from((bits as i8) >> amount)
            };
            assert_eq!(shifted("<<", &k.to_string(), i8_ty, x), shl, "{x} << {k}");
            assert_eq!(shifted(">>", &k.to_string(), i8_ty, x), shr, "{x} >> {k}");
        }
    }
}

#[test]
fn a_shift_by_an_amount_that_is_no_literal_is_refused() {
    let text = "x << y";
    let error = with(
        &[(
            text,
            typed(&[(ArithOp::Shl, OpReading::Wrapping(u32_ty()), 1)]),
        )],
        || parse_contract(text).unwrap_err(),
    );
    assert!(error.message.contains("not a literal"), "{error}");
}
