// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The library facade takes its logic functions from its caller and
//! withdraws none of them, so a definition that reads `^q` reaches the
//! encoder as written, where its `&mut` parameter is one value and `^q ==
//! *q` holds of every `q`. The encoder's door decides which definitions read
//! a final value itself, to a fixed point over their bodies, so this lane
//! refuses what the driver's withdrawal refuses (D-108, D-109).

use std::{collections::HashMap, sync::Arc};

use trust_wp_lib::{
    verify_mut_borrow, BinOp, LogicFnDef, LogicMode, MutBorrowBundle, PureExpr, VerificationBundle,
    VerificationResult,
};

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn call(name: &str, arg: &str) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args: vec![var(arg)],
    }
}

/// `#[logic(open, prophetic)] fn unchanged(q: &mut i32) -> bool { ^q == *q }`
fn unchanged() -> LogicFnDef {
    LogicFnDef::new(
        "unchanged".to_string(),
        "c::unchanged".to_string(),
        vec!["q".to_string()],
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(var("q")))),
            BinOp::Eq,
            Arc::new(PureExpr::Deref(Arc::new(var("q")))),
        ),
    )
    .with_mode(LogicMode::Prophetic)
}

/// `#[logic(open, prophetic)] fn wrapper(q: &mut i32) -> bool { unchanged(q) }`
fn wrapper() -> LogicFnDef {
    LogicFnDef::new(
        "wrapper".to_string(),
        "c::wrapper".to_string(),
        vec!["q".to_string()],
        call("unchanged", "q"),
    )
    .with_mode(LogicMode::Prophetic)
}

/// `#[logic(open, prophetic)] fn settled(q: &mut i32) -> bool { resolve(q) }`
fn settled() -> LogicFnDef {
    LogicFnDef::new(
        "settled".to_string(),
        "c::settled".to_string(),
        vec!["q".to_string()],
        call("resolve", "q"),
    )
    .with_mode(LogicMode::Prophetic)
}

/// `#[requires(*p != 5)] #[ensures(ensures)] fn set5(p: &mut i32) { *p = 5 }`
/// over the logic functions `defs`.
fn set5(ensures: PureExpr, defs: Vec<LogicFnDef>) -> MutBorrowBundle {
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(var("p")))),
        BinOp::Ne,
        Arc::new(PureExpr::Int(5)),
    )];
    let mut base = VerificationBundle::new(requires, vec![ensures]);
    base.logic_fns = defs;
    MutBorrowBundle::new(base, HashMap::from([("p".to_string(), PureExpr::Int(5))]))
}

/// FALSE: `p` is left at 5 and it was not 5. Each spelling of the claim
/// verified through the library before the door read the definitions: the
/// function itself, a function calling it, a function reading `resolve`.
#[test]
fn a_final_reading_logic_function_from_the_library_is_not_the_current_value() {
    for (goal, defs) in [
        (call("unchanged", "p"), vec![unchanged()]),
        (call("wrapper", "p"), vec![wrapper(), unchanged()]),
        (call("c::wrapper", "p"), vec![unchanged(), wrapper()]),
        (call("settled", "p"), vec![settled()]),
    ] {
        let result = verify_mut_borrow(&set5(goal.clone(), defs));
        assert!(
            !matches!(result, Ok(VerificationResult::Verified(_))),
            "a false `{goal}` of `*p = 5` verified through the library: {result:?}"
        );
    }
}

/// The lane is not vacuous: the true `^p == 5` of the same body verifies
/// beside a definition that reads a final value and that the goal does not
/// name.
#[test]
fn a_goal_not_naming_a_final_reader_keeps_its_reading() {
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(var("p")))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );
    let result = verify_mut_borrow(&set5(ensures, vec![unchanged()]));
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "the true `^p == 5` of `*p = 5`: {result:?}"
    );
}
