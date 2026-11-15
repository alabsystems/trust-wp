// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The census a generated oracle counts its cases by: every kind of node a
//! clause writes, as written, and every pattern form.

use crate::{
    contract_parser::{parse_contract, parse_contract_census, PatternForm},
    formula::{
        elaborate::{ExprKind, NodeKind, PatternKind},
        BinOp, UnOp,
    },
};

fn census(text: &str) -> std::collections::BTreeSet<NodeKind> {
    parse_contract_census(text).unwrap_or_else(|e| panic!("{text}: {e}"))
}

/// The census reads the clause as written: a `match` whose first arm cannot
/// fail is still a `match`, and a pattern a `let` desugars is still counted
/// by its form, although the AST the parse hands on has neither.
#[test]
fn the_census_counts_what_the_text_writes() {
    let written = census("match (x, b) { (w, true) => w > 0, (_, false) => true }");
    for kind in [
        NodeKind::Expr(ExprKind::Match),
        NodeKind::Pattern(PatternKind::Tuple),
        NodeKind::Pattern(PatternKind::Literal),
        NodeKind::Pattern(PatternKind::Wildcard),
        NodeKind::Pattern(PatternKind::Binding),
        NodeKind::BinOp(BinOp::Gt),
        NodeKind::Form(PatternForm::Tuple),
        NodeKind::Form(PatternForm::Literal),
        NodeKind::Form(PatternForm::Wildcard),
        NodeKind::Form(PatternForm::Binding),
    ] {
        assert!(written.contains(&kind), "{kind}: {written:?}");
    }
    let aliased = census("match p { q => *q == old(*p) }");
    assert!(
        aliased.contains(&NodeKind::Expr(ExprKind::Match)),
        "{aliased:?}"
    );
    assert!(!matches!(
        parse_contract("match p { q => *q == old(*p) }").expect("parses"),
        crate::formula::PureExpr::Match { .. }
    ));
    for (text, form) in [
        ("{ let ref a @ c = x; *a == c }", PatternForm::RefAlias),
        ("{ let ref a = x; *a == x }", PatternForm::Ref),
        ("{ let ref mut a = p; **a == 0 }", PatternForm::RefMut),
        ("{ let &a = r; a == 0 }", PatternForm::Reference),
        ("{ let &mut a = p; a == 0 }", PatternForm::MutReference),
        ("{ let (a) = x; a == x }", PatternForm::Parenthesized),
        ("{ let (a,) = (x,); a == x }", PatternForm::OneTuple),
        (
            "{ let (a, (c, d)) = (x, (y, x)); a == d }",
            PatternForm::NestedTuple,
        ),
        ("{ let mut a = x; a == x }", PatternForm::MutBinding),
        ("{ let box a = x; a == x }", PatternForm::Box),
        (
            "match o { Some(..) => true, None => false }",
            PatternForm::Rest,
        ),
        ("match s { S { a: u, .. } => u == 0 }", PatternForm::Struct),
        ("match x { a @ c => a == c }", PatternForm::Alias),
        ("match b { true | false => x == x }", PatternForm::Or),
    ] {
        assert!(
            census(text).contains(&NodeKind::Form(form)),
            "{text}: {form:?}"
        );
    }
    assert!(census("!(0 < -x)").contains(&NodeKind::UnOp(UnOp::Not)));
    assert!(census("(300 as u8) == 44").contains(&NodeKind::BinOp(BinOp::Mod)));
    assert!(census("(5 as i64) == 5").contains(&NodeKind::BinOp(BinOp::Div)));
    assert!(census("|r: i32| r == 0").contains(&NodeKind::Expr(ExprKind::Closure)));
}

/// Every list is written from its enum's variants, so a new variant is in the
/// list the oracle counts over.
#[test]
fn every_kind_is_listed() {
    let all = NodeKind::all();
    let unique: std::collections::BTreeSet<_> = all.iter().copied().collect();
    assert_eq!(unique.len(), all.len());
    assert_eq!(
        all.len(),
        ExprKind::ALL.len()
            + BinOp::ALL.len()
            + UnOp::ALL.len()
            + PatternKind::ALL.len()
            + PatternForm::ALL.len()
    );
    for kind in ExprKind::ALL {
        assert!(all.contains(&NodeKind::Expr(*kind)));
    }
}
