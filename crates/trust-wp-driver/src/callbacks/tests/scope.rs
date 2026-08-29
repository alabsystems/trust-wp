// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- OpenSelf scoping (#519) ---

#[test]
fn test_scope_open_self_same_module_upgrades_to_open() {
    use trust_wp_core::logic::LogicFnDef;

    let lf = LogicFnDef::new(
        "helper".into(),
        "mymod::specs::helper".into(),
        vec![],
        PureExpr::Int(1),
    )
    .with_mode(LogicMode::OpenSelf);

    let scoped = scope_logic_fn_modes(&[lf], "mymod::specs::caller_fn");
    assert_eq!(scoped.len(), 1);
    assert_eq!(
        scoped[0],
        LogicMode::Open,
        "OpenSelf same module should upgrade to Open"
    );
}

#[test]
fn test_scope_open_self_different_module_same_crate_stays_opaque() {
    use trust_wp_core::logic::LogicFnDef;

    // OpenSelf = same-module visibility, so a sibling module remains opaque.
    let lf = LogicFnDef::new(
        "helper".into(),
        "mymod::specs::helper".into(),
        vec![],
        PureExpr::Int(1),
    )
    .with_mode(LogicMode::OpenSelf);

    let scoped = scope_logic_fn_modes(&[lf], "mymod::other::caller_fn");
    assert_eq!(scoped.len(), 1);
    assert_eq!(
        scoped[0],
        LogicMode::Default,
        "OpenSelf from different module in the same crate should stay opaque"
    );
}

#[test]
fn test_scope_open_self_different_crate_downgrades() {
    use trust_wp_core::logic::LogicFnDef;

    // OpenSelf remains opaque outside the defining module, including other crates.
    let lf = LogicFnDef::new(
        "helper".into(),
        "other_crate::specs::helper".into(),
        vec![],
        PureExpr::Int(1),
    )
    .with_mode(LogicMode::OpenSelf);

    let scoped = scope_logic_fn_modes(&[lf], "mymod::caller_fn");
    assert_eq!(scoped.len(), 1);
    assert_eq!(
        scoped[0],
        LogicMode::Default,
        "OpenSelf from different crate should be downgraded to Default"
    );
}

#[test]
fn test_scope_preserves_open_and_prophetic() {
    use trust_wp_core::logic::LogicFnDef;

    let open_fn = LogicFnDef::new(
        "open_fn".into(),
        "a::b::open_fn".into(),
        vec![],
        PureExpr::Int(1),
    )
    .with_mode(LogicMode::Open);

    let prophetic_fn = LogicFnDef::new(
        "prophetic_fn".into(),
        "e::f::prophetic_fn".into(),
        vec![],
        PureExpr::Int(3),
    )
    .with_mode(LogicMode::Prophetic);

    let scoped = scope_logic_fn_modes(&[open_fn, prophetic_fn], "x::y::caller");
    assert_eq!(scoped[0], LogicMode::Open, "Open stays Open");
    assert_eq!(scoped[1], LogicMode::Prophetic, "Prophetic stays Prophetic");
}

#[test]
fn test_scope_open_self_mixed_same_and_different() {
    use trust_wp_core::logic::LogicFnDef;

    let same_module = LogicFnDef::new(
        "visible".into(),
        "mymod::visible".into(),
        vec![],
        PureExpr::Int(1),
    )
    .with_mode(LogicMode::OpenSelf);

    let different_module = LogicFnDef::new(
        "hidden".into(),
        "other::hidden".into(),
        vec![],
        PureExpr::Int(2),
    )
    .with_mode(LogicMode::OpenSelf);

    let scoped = scope_logic_fn_modes(&[same_module, different_module], "mymod::caller");
    assert_eq!(
        scoped[0],
        LogicMode::Open,
        "Same module OpenSelf should upgrade to Open"
    );
    assert_eq!(
        scoped[1],
        LogicMode::Default,
        "Different module OpenSelf should downgrade to Default"
    );
}

// --- Default mode scoping (#540) ---

#[test]
fn test_scope_default_same_module_upgrades_to_open() {
    use trust_wp_core::logic::LogicFnDef;

    let lf = LogicFnDef::new(
        "helper".into(),
        "mymod::specs::helper".into(),
        vec![],
        PureExpr::Int(1),
    )
    .with_mode(LogicMode::Default);

    let scoped = scope_logic_fn_modes(&[lf], "mymod::specs::caller_fn");
    assert_eq!(scoped.len(), 1);
    assert_eq!(
        scoped[0],
        LogicMode::Open,
        "Default same module should upgrade to Open (Creusot semantics)"
    );
}

#[test]
fn test_scope_default_different_module_stays_opaque() {
    use trust_wp_core::logic::LogicFnDef;

    let lf = LogicFnDef::new(
        "helper".into(),
        "mymod::specs::helper".into(),
        vec![],
        PureExpr::Int(1),
    )
    .with_mode(LogicMode::Default);

    let scoped = scope_logic_fn_modes(&[lf], "mymod::other::caller_fn");
    assert_eq!(scoped.len(), 1);
    assert_eq!(
        scoped[0],
        LogicMode::Default,
        "Default from different module should stay Default (opaque)"
    );
}

#[test]
fn test_scope_default_and_open_self_both_upgrade_same_module() {
    use trust_wp_core::logic::LogicFnDef;

    let default_fn = LogicFnDef::new(
        "bare_logic".into(),
        "mymod::bare_logic".into(),
        vec![],
        PureExpr::Int(1),
    )
    .with_mode(LogicMode::Default);

    let open_self_fn = LogicFnDef::new(
        "explicit_self".into(),
        "mymod::explicit_self".into(),
        vec![],
        PureExpr::Int(2),
    )
    .with_mode(LogicMode::OpenSelf);

    let scoped = scope_logic_fn_modes(&[default_fn, open_self_fn], "mymod::caller");
    assert_eq!(
        scoped[0],
        LogicMode::Open,
        "Default same module upgrades to Open"
    );
    assert_eq!(
        scoped[1],
        LogicMode::Open,
        "OpenSelf same module upgrades to Open"
    );
}

#[test]
fn test_scope_default_cross_module_with_open() {
    use trust_wp_core::logic::LogicFnDef;

    let default_fn = LogicFnDef::new(
        "helper".into(),
        "other::helper".into(),
        vec![],
        PureExpr::Int(1),
    )
    .with_mode(LogicMode::Default);

    let open_fn = LogicFnDef::new(
        "always_open".into(),
        "other::always_open".into(),
        vec![],
        PureExpr::Int(2),
    )
    .with_mode(LogicMode::Open);

    let scoped = scope_logic_fn_modes(&[default_fn, open_fn], "mymod::caller");
    assert_eq!(
        scoped[0],
        LogicMode::Default,
        "Default cross-module stays opaque"
    );
    assert_eq!(
        scoped[1],
        LogicMode::Open,
        "Open stays Open regardless of module"
    );
}
