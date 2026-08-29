// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Tests for unknown method call fallback to logic function encoding

pub(super) use super::*;

mod ext_eq_tseitin;
mod routing;
mod seq_receiver_uf;
mod set_arity;
mod sort_hint_regressions;

fn register_open_logic_fn(encoder: &mut AYEncoder, name: &str, params: &[&str]) {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let logic_fn = LogicFnDef::new(
        name.to_string(),
        name.to_string(),
        params.iter().map(|p| (*p).to_string()).collect(),
        bool_expr(true),
    )
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("registration should succeed");
}
