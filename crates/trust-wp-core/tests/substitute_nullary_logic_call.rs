// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use trust_wp_core::formula::PureExpr;

#[test]
fn substitute_rewrites_nullary_logic_call_name() {
    let expr = PureExpr::LogicFnCall {
        name: "err".to_string(),
        args: vec![],
    };
    let mut substitutions = HashMap::new();
    substitutions.insert("err".to_string(), PureExpr::Bool(true));

    let result = expr.substitute(&substitutions);
    assert_eq!(result, PureExpr::Bool(true));
}

#[test]
fn substitute_filtered_rewrites_nullary_logic_call_name() {
    let expr = PureExpr::LogicFnCall {
        name: "err".to_string(),
        args: vec![],
    };
    let mut substitutions = HashMap::new();
    substitutions.insert("err".to_string(), PureExpr::Bool(true));
    let filter: HashSet<&str> = ["err"].into_iter().collect();

    let result = expr.substitute_filtered(&filter, &substitutions);
    assert_eq!(result, PureExpr::Bool(true));
}
