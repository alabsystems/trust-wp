// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compatibility shim for closure capture types that now live in `trust-wp-core`.

#[cfg(test)]
pub(crate) use trust_wp_core::closure::CaptureField;
pub(crate) use trust_wp_core::closure::CaptureKind;
pub use trust_wp_core::closure::ClosureCaptureInfo;

/// Construct a [`ClosureCaptureInfo`] without depending on its private fields.
#[macro_export]
macro_rules! closure_capture_info {
    (
        def_id: $def_id:expr,
        captures: $captures:expr,
        param_name: $param_name:expr,
        body_expr: $body_expr:expr,
        param_names: $param_names:expr,
        ensures_exprs: $ensures_exprs:expr,
        requires_exprs: $requires_exprs:expr $(,)?
    ) => {
        $crate::ClosureCaptureInfo::new($def_id, $captures)
            .with_param_name($param_name)
            .with_body_expr($body_expr)
            .with_param_names($param_names)
            .with_ensures_exprs($ensures_exprs)
            .with_requires_exprs($requires_exprs)
    };
    // Backward-compatible form without requires_exprs
    (
        def_id: $def_id:expr,
        captures: $captures:expr,
        param_name: $param_name:expr,
        body_expr: $body_expr:expr,
        param_names: $param_names:expr,
        ensures_exprs: $ensures_exprs:expr $(,)?
    ) => {
        $crate::ClosureCaptureInfo::new($def_id, $captures)
            .with_param_name($param_name)
            .with_body_expr($body_expr)
            .with_param_names($param_names)
            .with_ensures_exprs($ensures_exprs)
    };
}
