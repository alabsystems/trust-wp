// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{ExprSort, PureExpr};

#[test]
fn closure_display_keeps_typed_parameter_sorts() {
    let closure = PureExpr::Closure {
        params: vec![
            ("x".to_string(), Some(ExprSort::Bool)),
            ("y".to_string(), Some(ExprSort::Seq)),
            ("z".to_string(), None),
        ],
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };

    assert_eq!(format!("{closure}"), "|x: Bool, y: Seq, z| x");
}
