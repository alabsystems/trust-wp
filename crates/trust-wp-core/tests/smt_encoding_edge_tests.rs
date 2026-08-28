// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::{
    formula::{BinOp, Formula, PureExpr},
    smt::{expr_to_smt, formula_to_smt, SmtGenerator},
};

#[test]
fn expr_to_smt_old_view_of_deref_uses_old_current_view_name() {
    let expr = PureExpr::Old(Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(
        Arc::new(PureExpr::Var("v".to_string(), None)),
    )))));

    assert_eq!(expr_to_smt(&expr), "old_v_current_view");
}

#[test]
fn expr_to_smt_old_method_call_prefixes_receiver_and_arguments() {
    let expr = PureExpr::Old(Arc::new(PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("xs".to_string(), None)),
        method: "custom".to_string(),
        args: vec![PureExpr::Var("i".to_string(), None)],
    }));

    assert_eq!(expr_to_smt(&expr), "(custom old_xs old_i)");
}

#[test]
fn formula_to_smt_forall_with_trigger_patterns() {
    let formula = Formula::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(Formula::Pure(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ))),
        triggers: vec![vec![
            Formula::Pure(PureExpr::LogicFnCall {
                name: "f".to_string(),
                args: vec![PureExpr::Var("i".to_string(), None)],
            }),
            Formula::Pure(PureExpr::LogicFnCall {
                name: "g".to_string(),
                args: vec![PureExpr::Var("i".to_string(), None)],
            }),
        ]],
    };

    assert_eq!(
        formula_to_smt(&formula),
        "(forall ((i Int)) (! (> i 0) :pattern ((logic_f i) (logic_g i))))"
    );
}

#[test]
fn generator_declares_old_current_view_for_old_view_of_deref() {
    let expr = PureExpr::Old(Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(
        Arc::new(PureExpr::Var("v".to_string(), None)),
    )))));

    let mut generator = SmtGenerator::new();
    generator.declare_vars_in_expr(&expr);

    assert!(generator
        .output()
        .contains("(declare-const old_v_current_view Seq)"));
}

#[test]
fn generator_formula_declares_free_trigger_vars_but_not_bound_names() {
    let formula = Formula::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(Formula::True),
        triggers: vec![vec![Formula::Pure(PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![
                PureExpr::Var("i".to_string(), None),
                PureExpr::Var("y".to_string(), None),
            ],
        })]],
    };

    let mut generator = SmtGenerator::new();
    generator.declare_vars_in_formula(&formula);
    let output = generator.output();

    assert!(output.contains("(declare-const y Int)"));
    assert!(!output.contains("(declare-const i Int)"));
}

// ---------------------------------------------------------------------------
// generate_vc must emit a query a solver will actually read
// ---------------------------------------------------------------------------
//
// These pin the three ways the rendered query used to name things it never
// declared, each of which made the whole artifact unparseable — `--emit-smt`
// promises "the SMT-LIB2 queries", and text no solver accepts is not that.

/// The printer spells the mathematical view of `x` `x_view`, so that is the
/// name the declaration block has to carry. Declaring `x` instead left every
/// query that mentions a view — which is every query with an integer
/// parameter, because the driver injects `x@`-based range preconditions —
/// referring to an unknown constant.
#[test]
fn generate_vc_declares_the_view_name_the_printer_emits() {
    let x_view = PureExpr::View(Arc::new(PureExpr::Var(
        "x".to_string(),
        Some(trust_wp_core::formula::ExprSort::Int),
    )));
    let requires = vec![PureExpr::BinOp(
        Arc::new(x_view),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];

    let mut generator = SmtGenerator::new();
    generator.generate_vc("f", &requires, &ensures, None);
    let output = generator.output();

    assert!(output.contains("(declare-const x_view Int)"), "{output}");
    // The view of a scalar is that scalar, not a sequence: the range
    // preconditions compare it with integers.
    assert!(!output.contains("(declare-const x_view Seq)"), "{output}");
}

/// A quantifier's bound variable is introduced by the quantifier. Declaring it
/// as a free constant as well would change what the query says.
#[test]
fn generate_vc_does_not_declare_quantifier_bound_variables() {
    let ensures = vec![PureExpr::Forall {
        var: "k".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("k".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        )),
        triggers: Vec::new(),
    }];

    let mut generator = SmtGenerator::new();
    generator.generate_vc("f", &[], &ensures, None);
    let output = generator.output();

    assert!(output.contains("(declare-const n Int)"), "{output}");
    assert!(!output.contains("(declare-const k "), "{output}");
}

/// Logic functions and type-invariant predicates are applied by name in the
/// body. An SMT-LIB query has to declare them before it uses them.
#[test]
fn generate_vc_declares_the_symbols_it_applies() {
    let ensures = vec![PureExpr::LogicFnCall {
        name: "inv".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    }];

    let mut generator = SmtGenerator::new();
    generator.generate_vc("f", &[], &ensures, None);
    let output = generator.output();

    let declared = output
        .lines()
        .find(|line| line.starts_with("(declare-fun logic_inv"))
        .unwrap_or_else(|| panic!("logic_inv must be declared:\n{output}"));
    // Applied where a formula is expected, over one integer argument.
    assert!(declared.ends_with("(Int) Bool)"), "{declared}");
}

/// The driver wraps a divided term in `LetAssume` so the divisor guard travels
/// with the value. The printer renders that as `(=> guard body)`, which is
/// ill-sorted when `body` is a term — `(=> Bool Int)`. The guard belongs in an
/// assertion of its own.
#[test]
fn generate_vc_lifts_a_divisor_guard_out_of_the_term_that_carried_it() {
    let guard = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("d".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        )),
    );
    let guarded_quotient = PureExpr::LetAssume {
        assumption: Arc::new(guard),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Div,
            Arc::new(PureExpr::Var("d".to_string(), None)),
        )),
    };

    let mut generator = SmtGenerator::new();
    generator.generate_vc("f", &[], &[], Some(&guarded_quotient));
    let output = generator.output();

    assert!(output.contains("(assert (not (= d 0)))"), "{output}");
    assert!(output.contains("(assert (= result (div n d)))"), "{output}");
    // The ill-sorted implication must be gone entirely.
    assert!(!output.contains("(=> (not (= d 0))"), "{output}");
}

/// A `LetObligation` in term position is hoisted too, and is labelled.
///
/// `LetObligation` marks something the full encoder *checks*; the rendered
/// query can only assume it, so the marker is the reader's only clue that this
/// file is weaker than the real check. It is emitted by the driver's MIR
/// lowering, never by the surface contract grammar, so no end-to-end corpus
/// reaches it — this test is the branch's only cover.
#[test]
fn generate_vc_labels_a_hoisted_obligation_as_an_obligation() {
    let obligation = PureExpr::BinOp(
        Arc::new(PureExpr::Var("y".to_string(), None)),
        BinOp::Ne,
        Arc::new(PureExpr::Int(0)),
    );
    let guarded = PureExpr::LetObligation {
        obligation: Arc::new(obligation),
        // A bare `Var` is not formula-shaped, which is what puts the node in
        // term position and so makes it eligible for hoisting.
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };

    let mut generator = SmtGenerator::new();
    generator.generate_vc("f", &[], &[], Some(&guarded));
    let output = generator.output();

    assert!(output.contains("; obligation:"), "{output}");
    assert!(output.contains("(assert (not (= y 0)))"), "{output}");
    assert!(output.contains("(assert (= result x))"), "{output}");
    // The obligation must not be left in the term it guarded.
    assert!(!output.contains("(=> (not (= y 0))"), "{output}");
}

/// One name applied at two signatures cannot be declared once, and the query
/// says so rather than declaring the first and staying quiet.
///
/// `method_smt_name` passes user method names through unqualified, so two
/// receiver types sharing a method name share an SMT symbol. A query that
/// parses and is wrong is the worst outcome for a debug artifact.
#[test]
fn generate_vc_notes_a_symbol_applied_at_two_signatures() {
    let one_arg = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
            method: "foo".to_string(),
            args: vec![PureExpr::Int(1)],
        }),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let no_args = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("b".to_string(), None)),
            method: "foo".to_string(),
            args: vec![],
        }),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );

    let mut generator = SmtGenerator::new();
    generator.generate_vc(
        "f",
        std::slice::from_ref(&one_arg),
        std::slice::from_ref(&no_args),
        None,
    );
    let output = generator.output();

    // Only the first signature is declared; the note is what makes the second
    // one visible.
    assert!(
        output.contains("(declare-fun foo (Int Int) Int)"),
        "{output}"
    );
    assert!(
        output.contains("NOTE: `foo` is applied at more than one signature here"),
        "{output}"
    );
}

/// A variable that shares its name with an applied symbol must stay a
/// variable.
///
/// Symbol collection skips any name already in `declared_vars`, so the
/// variable declarations have to be emitted first. With the two phases
/// reversed `(declare-const foo Int)` silently becomes
/// `(declare-fun foo (Int) Int)` — a query that parses and asks a different
/// question. This pins the phase order.
#[test]
fn generate_vc_declares_variables_before_it_collects_applied_symbols() {
    let requires = PureExpr::BinOp(
        Arc::new(PureExpr::Var("foo".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
            method: "foo".to_string(),
            args: vec![],
        }),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );

    let mut generator = SmtGenerator::new();
    generator.generate_vc(
        "f",
        std::slice::from_ref(&requires),
        std::slice::from_ref(&ensures),
        None,
    );
    let output = generator.output();

    assert!(output.contains("(declare-const foo Int)"), "{output}");
    assert!(!output.contains("(declare-fun foo"), "{output}");
    assert!(!output.contains("; Uninterpreted symbols"), "{output}");
}

/// ...but a `LetAssume` standing for a formula still means the implication it
/// prints as, and must be left alone.
#[test]
fn generate_vc_leaves_a_formula_position_assumption_as_an_implication() {
    let assumed = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("d".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
    };

    let mut generator = SmtGenerator::new();
    generator.generate_vc("f", &[], std::slice::from_ref(&assumed), None);
    let output = generator.output();

    assert!(output.contains("(=> (> d 0) (> result 0))"), "{output}");
}

// ---------------------------------------------------------------------------
// a query that cannot decide the obligation must say so
// ---------------------------------------------------------------------------
//
// This generator is a weakest-precondition rendering; it does not model
// mutation. For a `&mut` parameter the postcondition talks about
// `<param>_final`, which nothing else in the query constrains, so the file is
// satisfiable whatever was really proved — `swap`, `abs_mut` and
// `increment_ref` in `examples/mut_borrow.rs` all emit `sat` while two of the
// three verify. `--help` sends people here to read the obligation, and a
// debug artifact that quietly reports the opposite verdict is worse than none.

/// A symbol only the postcondition mentions is named in the emitted file.
#[test]
fn a_final_value_the_query_cannot_pin_down_is_called_out() {
    // ensures: v_final >= 0, with nothing constraining v_final.
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("v_final".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];

    let mut generator = SmtGenerator::new();
    generator.generate_vc("abs_mut", &[], &ensures, None);
    let output = generator.output();

    assert!(output.contains("WARNING"), "no warning emitted:\n{output}");
    assert!(output.contains("`v_final`"), "{output}");
    // It has to be legible as SMT-LIB: a comment, not bare prose.
    for line in output.lines().filter(|l| l.contains("WARNING")) {
        assert!(line.starts_with(';'), "warning is not a comment: {line}");
    }
}

/// Two loose symbols read as a sentence, and the order is stable so the file
/// can be diffed between runs.
#[test]
fn several_unpinned_symbols_are_listed_in_a_stable_order() {
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("b_final".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("a_final".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )),
    )];

    let mut generator = SmtGenerator::new();
    generator.generate_vc("swap", &[], &ensures, None);
    let output = generator.output();
    assert!(
        output.contains("`a_final` and `b_final`"),
        "expected a sorted, readable list:\n{output}"
    );
}

/// And a faithful query stays quiet. `result` is pinned by the generator's own
/// `(= result <body>)`, which is not part of the body expression it is handed
/// — missing that made every function with a return value look broken.
#[test]
fn a_query_that_does_decide_the_obligation_carries_no_warning() {
    let x = PureExpr::Var("x".to_string(), None);
    let requires = vec![PureExpr::BinOp(
        Arc::new(x.clone()),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Gt,
        Arc::new(x.clone()),
    )];
    let body = PureExpr::BinOp(Arc::new(x), BinOp::Add, Arc::new(PureExpr::Int(1)));

    let mut generator = SmtGenerator::new();
    generator.generate_vc("increment", &requires, &ensures, Some(&body));
    let output = generator.output();

    assert!(
        !output.contains("WARNING"),
        "a faithful query was flagged:\n{output}"
    );

    // With no body, `result` genuinely is unconstrained, and that is worth the
    // same warning for the same reason.
    let mut generator = SmtGenerator::new();
    generator.generate_vc("increment", &requires, &ensures, None);
    assert!(generator.output().contains("`result`"));
}
