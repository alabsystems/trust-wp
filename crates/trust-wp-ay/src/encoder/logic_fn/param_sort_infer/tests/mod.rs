// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::{
    formula::{Pattern, PureExpr},
    logic::LogicFnDef,
};

use super::*;
use crate::tests::helpers::{int, logic_fn_call, match_expr, method_call, var};

mod cross_fn_seq;
mod param_datatypes;
mod seq_like;

fn ctor_pattern(name: &str, inner: Option<Pattern>) -> Pattern {
    Pattern::Constructor {
        name: name.to_string(),
        inner: inner.map(Box::new),
    }
}

fn simple_logic_fn(name: &str, params: Vec<&str>, body: PureExpr) -> LogicFnDef {
    LogicFnDef::new(
        name.to_string(),
        format!("crate::specs::{name}"),
        params.into_iter().map(String::from).collect(),
        body,
    )
}
