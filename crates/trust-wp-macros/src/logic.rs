// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function attribute processing
//!
//! This module handles the `#[logic]` attribute for pure specification functions.
//! Logic functions:
//! - Exist only for verification (erased at compile time)
//! - Must be pure (no side effects, no mutable parameters)
//! - Can use unbounded `Int` arithmetic
//! - Can be called from contracts and ghost blocks

use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::{FnArg, ItemFn, Pat, ReturnType, Signature, Type};

/// Error type for logic function validation failures.
#[derive(Debug)]
pub(crate) struct LogicValidationError {
    pub(crate) span: Span,
    pub(crate) message: String,
}

/// Openness mode for `#[logic]` / `#[predicate]` functions.
///
/// In Creusot semantics:
/// - Default (no attribute argument): body is opaque to callers
/// - `open`: body is visible/inlined for all callers
/// - `open(self)`: body is visible only within the same module/type
/// - `prophetic`: function may reference final values of mutable borrows
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LogicMode {
    /// Default: body is opaque to callers (only contract is visible)
    Default,
    /// `#[logic(open)]`: body is visible to all callers
    Open,
    /// `#[logic(open(self))]`: body visible within same module/type
    OpenSelf,
    /// `#[logic(prophetic)]`: may reference final values (`^v`)
    Prophetic,
}

impl LogicMode {
    /// Returns the doc marker suffix for this mode.
    ///
    /// Combined with a base prefix (e.g., "trust-wp:logic:") to produce
    /// the full doc marker string embedded in the function's attributes.
    pub(crate) fn marker_suffix(self) -> &'static str {
        match self {
            LogicMode::Default => "",
            LogicMode::Open => "open:",
            LogicMode::OpenSelf => "open_self:",
            LogicMode::Prophetic => "prophetic:",
        }
    }
}

/// Parse the attribute argument of `#[logic(...)]` or `#[predicate(...)]`.
///
/// Returns the logic mode, or a compile error if the argument is invalid.
///
/// # Valid forms
///
/// - `#[logic]` → `LogicMode::Default`
/// - `#[logic(open)]` → `LogicMode::Open`
/// - `#[logic(open(self))]` → `LogicMode::OpenSelf`
/// - `#[logic(prophetic)]` → `LogicMode::Prophetic`
/// - `#[logic(law)]` → `LogicMode::Open` (axiom-visible alias)
pub(crate) fn parse_logic_attr(attr: &TokenStream) -> Result<LogicMode, LogicValidationError> {
    parse_logic_mode_str(&attr.to_string()).map_err(|mut e| {
        // Override call_site span with the first token of the attribute for
        // more precise error location (#1676).
        e.span = crate::marker_attrs::first_token_span(attr);
        e
    })
}

/// Return whether the `#[logic(...)]`/`#[predicate(...)]` attribute includes
/// Creusot's `law` marker.
pub(crate) fn logic_attr_contains_law(attr: &TokenStream) -> bool {
    attr.to_string()
        .replace(' ', "")
        .split(',')
        .any(|part| part == "law")
}

/// Return whether the `#[logic(...)]`/`#[predicate(...)]` attribute includes
/// Creusot's explicit `opaque` marker.
pub(crate) fn logic_attr_contains_opaque(attr: &TokenStream) -> bool {
    attr.to_string()
        .replace(' ', "")
        .split(',')
        .any(|part| part == "opaque")
}

pub(crate) fn logic_attr_contains_sealed(attr: &TokenStream) -> bool {
    attr.to_string()
        .replace(' ', "")
        .split(',')
        .any(|part| part == "sealed")
}

pub(crate) fn logic_attr_contains_open_crate(attr: &TokenStream) -> bool {
    attr.to_string()
        .replace(' ', "")
        .split(',')
        .any(|part| part == "open(crate)")
}

pub(crate) fn logic_attr_contains_open_super(attr: &TokenStream) -> bool {
    attr.to_string()
        .replace(' ', "")
        .split(',')
        .any(|part| part == "open(super)")
}

/// Parse a logic mode from a string (the text between parentheses in `#[logic(...)]`).
///
/// Separated from `parse_logic_attr` for testability (`proc_macro::TokenStream`
/// cannot be constructed outside proc macro context).
fn parse_logic_mode_str(attr_text: &str) -> Result<LogicMode, LogicValidationError> {
    let trimmed = attr_text.trim();

    if trimmed.is_empty() {
        return Ok(LogicMode::Default);
    }

    // Normalize spaces and handle compound attributes (e.g., "prophetic, open")
    let normalized = trimmed.replace(' ', "");

    // Split on commas for compound attributes like `prophetic, open`
    let parts: Vec<&str> = normalized.split(',').map(str::trim).collect();

    // Determine the mode from parts. Priority: prophetic > open variants > law > opaque
    let mut mode = LogicMode::Default;
    for part in &parts {
        match *part {
            "open" => {
                if mode != LogicMode::Prophetic {
                    mode = LogicMode::Open;
                }
            }
            "open(self)" => {
                if mode != LogicMode::Prophetic {
                    mode = LogicMode::OpenSelf;
                }
            }
            "open(crate)" | "open(super)" => {
                // Creusot visibility scopes: open(crate), open(super) — treat
                // both as Open since trust-wp does not yet track module-level
                // visibility for logic function bodies.
                if mode != LogicMode::Prophetic {
                    mode = LogicMode::Open;
                }
            }
            "prophetic" => mode = LogicMode::Prophetic,
            "opaque" => { /* Default is already opaque */ }
            "law" => {
                // Creusot compatibility: `#[logic(law)]` marks axioms.
                // Axioms require body visibility, so treat it as open.
                if mode != LogicMode::Prophetic {
                    mode = LogicMode::Open;
                }
            }
            "inline" => { /* Creusot hint; ignore */ }
            "sealed" => { /* Creusot hint; ignore */ }
            "" => {}
            _ => {
                return Err(LogicValidationError {
                    span: Span::call_site(),
                    message: format!(
                        "unknown attribute argument `{trimmed}`. \
                         Expected combinations of: `open`, `open(self)`, `open(super)`, `open(crate)`, `prophetic`, `opaque`, `law`"
                    ),
                });
            }
        }
    }

    Ok(mode)
}

/// Validates that a function is suitable for the `#[logic]` attribute.
///
/// # Requirements
///
/// - No `&mut` parameters (unless prophetic mode — Creusot allows `&mut`
///   in prophetic logic functions to model final/prophecy values via `^x`)
/// - Body must be parseable as an expression (validated by driver)
///
/// # Returns
///
/// `Ok(())` if valid, or `Err` with a diagnostic message.
pub(crate) fn validate_logic_function(
    func: &ItemFn,
    mode: LogicMode,
) -> Result<(), LogicValidationError> {
    validate_logic_signature(&func.sig, mode)
}

/// Validates a function signature for logic function constraints.
///
/// Works for both free functions (`ItemFn`) and trait method declarations
/// (`TraitItemFn`), since both share a `Signature`.
///
/// Creusot allows `&mut` parameters in all logic modes. At the logical level,
/// `&mut T` provides both current (`*x`) and final (`^x`) values. Prophetic
/// mode controls `^x` access, not whether `&mut` params are accepted.
pub(crate) fn validate_logic_signature(
    sig: &Signature,
    _mode: LogicMode,
) -> Result<(), LogicValidationError> {
    // Creusot allows &mut parameters in ALL logic function modes.
    // At the logical level, &mut T provides both current (*x) and final (^x)
    // values. Prophetic mode controls ^x access, not parameter mutability.
    // Only reject `mut` binding patterns (e.g., `mut x: T`), which are
    // meaningless in logic context.
    for arg in &sig.inputs {
        if let FnArg::Typed(pat_type) = arg {
            if is_mutable_binding(&pat_type.pat) {
                let span = get_pattern_span(&pat_type.pat);
                return Err(LogicValidationError {
                    span,
                    message: "logic functions cannot have mutable parameter bindings".to_string(),
                });
            }
        }
    }

    // Check for async functions (not allowed in logic)
    if sig.asyncness.is_some() {
        return Err(LogicValidationError {
            span: sig.fn_token.span,
            message: "logic functions cannot be async".to_string(),
        });
    }

    // Check for unsafe functions (not allowed in logic)
    if sig.unsafety.is_some() {
        return Err(LogicValidationError {
            span: sig.fn_token.span,
            message: "logic functions cannot be unsafe".to_string(),
        });
    }

    Ok(())
}

/// Validates that a function marked with `#[predicate]` returns `bool`.
pub(crate) fn validate_predicate_function(func: &ItemFn) -> Result<(), LogicValidationError> {
    validate_predicate_signature(&func.sig)
}

/// Validates that a signature has a `bool` return type (for `#[predicate]`).
pub(crate) fn validate_predicate_signature(sig: &Signature) -> Result<(), LogicValidationError> {
    if !is_bool_return_type(&sig.output) {
        return Err(LogicValidationError {
            span: sig.ident.span(),
            message: "predicate functions must return bool".to_string(),
        });
    }
    Ok(())
}

/// Check if a function return type is exactly `bool`.
fn is_bool_return_type(output: &ReturnType) -> bool {
    let ReturnType::Type(_, ty) = output else {
        return false;
    };

    match ty.as_ref() {
        Type::Path(type_path) => type_path.qself.is_none() && type_path.path.is_ident("bool"),
        _ => false,
    }
}

/// Check if a pattern is a mutable binding (mut x).
fn is_mutable_binding(pat: &Pat) -> bool {
    match pat {
        Pat::Ident(ident) => ident.mutability.is_some(),
        _ => false,
    }
}

/// Get the span of a pattern for error reporting.
fn get_pattern_span(pat: &Pat) -> Span {
    match pat {
        Pat::Ident(ident) => ident.ident.span(),
        _ => Span::call_site(),
    }
}

#[cfg(test)]
mod tests {
    use syn::parse_quote;

    use super::*;

    #[test]
    fn test_valid_logic_function() {
        let func: ItemFn = parse_quote! {
            fn max(a: Int, b: Int) -> Int {
                if a >= b { a } else { b }
            }
        };
        validate_logic_function(&func, LogicMode::Default).unwrap();
    }

    #[test]
    fn test_valid_with_ref_param() {
        let func: ItemFn = parse_quote! {
            fn len(s: &Seq<Int>) -> Int {
                s.len()
            }
        };
        validate_logic_function(&func, LogicMode::Default).unwrap();
    }

    #[test]
    fn test_allow_mut_ref_param() {
        // Creusot allows &mut params in all logic modes — they provide
        // both current (*x) and final (^x) values at the logical level.
        let func: ItemFn = parse_quote! {
            fn bor(v: &mut Vec<i32>) -> i32 {
                v.len() as i32
            }
        };
        validate_logic_function(&func, LogicMode::Default).unwrap();
    }

    #[test]
    fn test_prophetic_allows_mut_ref_param() {
        let func: ItemFn = parse_quote! {
            fn bor_value(x: &mut i32) -> i32 {
                *x
            }
        };
        validate_logic_function(&func, LogicMode::Prophetic).unwrap();
    }

    #[test]
    fn test_prophetic_allows_mut_self() {
        let method: syn::TraitItemFn = parse_quote! {
            fn observe(&mut self) -> Int;
        };
        validate_logic_signature(&method.sig, LogicMode::Prophetic).unwrap();
    }

    #[test]
    fn test_reject_mutable_binding() {
        let func: ItemFn = parse_quote! {
            fn bad(mut x: i32) -> i32 {
                x
            }
        };
        let err = validate_logic_function(&func, LogicMode::Default).unwrap_err();
        assert!(err.message.contains("mutable"));
    }

    #[test]
    fn test_reject_async() {
        let func: ItemFn = parse_quote! {
            async fn bad() -> i32 {
                42
            }
        };
        let err = validate_logic_function(&func, LogicMode::Default).unwrap_err();
        assert!(err.message.contains("async"));
    }

    #[test]
    fn test_reject_unsafe() {
        let func: ItemFn = parse_quote! {
            unsafe fn bad() -> i32 {
                42
            }
        };
        let err = validate_logic_function(&func, LogicMode::Default).unwrap_err();
        assert!(err.message.contains("unsafe"));
    }

    #[test]
    fn test_valid_predicate_function() {
        let func: ItemFn = parse_quote! {
            fn is_positive(x: Int) -> bool {
                x > 0
            }
        };
        validate_predicate_function(&func).unwrap();
    }

    #[test]
    fn test_reject_predicate_without_return_type() {
        let func: ItemFn = parse_quote! {
            fn bad(x: Int) {
                let _ = x;
            }
        };
        let err = validate_predicate_function(&func).unwrap_err();
        assert!(err.message.contains("return bool"));
    }

    #[test]
    fn test_reject_predicate_non_bool_return() {
        let func: ItemFn = parse_quote! {
            fn bad(x: Int) -> Int {
                x
            }
        };
        let err = validate_predicate_function(&func).unwrap_err();
        assert!(err.message.contains("return bool"));
    }

    #[test]
    fn test_validate_logic_signature_trait_method() {
        let method: syn::TraitItemFn = parse_quote! {
            fn logical(&self) -> Int;
        };
        validate_logic_signature(&method.sig, LogicMode::Default).unwrap();
    }

    #[test]
    fn test_validate_logic_signature_trait_method_allow_mut_self() {
        // Creusot allows &mut self in logic functions — logical reborrows.
        let method: syn::TraitItemFn = parse_quote! {
            fn observe(&mut self) -> Int;
        };
        validate_logic_signature(&method.sig, LogicMode::Default).unwrap();
    }

    #[test]
    fn test_validate_predicate_signature_trait_method() {
        let method: syn::TraitItemFn = parse_quote! {
            fn is_valid(&self) -> bool;
        };
        validate_predicate_signature(&method.sig).unwrap();
    }

    #[test]
    fn test_validate_predicate_signature_trait_method_reject_non_bool() {
        let method: syn::TraitItemFn = parse_quote! {
            fn bad(&self) -> Int;
        };
        let err = validate_predicate_signature(&method.sig).unwrap_err();
        assert!(err.message.contains("return bool"));
    }

    #[test]
    fn test_parse_logic_attr_empty() {
        let mode = parse_logic_mode_str("").unwrap();
        assert_eq!(mode, LogicMode::Default);
    }

    #[test]
    fn test_parse_logic_attr_open() {
        let mode = parse_logic_mode_str("open").unwrap();
        assert_eq!(mode, LogicMode::Open);
    }

    #[test]
    fn test_parse_logic_attr_open_self() {
        let mode = parse_logic_mode_str("open(self)").unwrap();
        assert_eq!(mode, LogicMode::OpenSelf);
    }

    #[test]
    fn test_parse_logic_attr_open_self_spaced() {
        // proc_macro tokenizer may insert spaces: "open (self)"
        let mode = parse_logic_mode_str("open (self)").unwrap();
        assert_eq!(mode, LogicMode::OpenSelf);
    }

    #[test]
    fn test_parse_logic_attr_prophetic() {
        let mode = parse_logic_mode_str("prophetic").unwrap();
        assert_eq!(mode, LogicMode::Prophetic);
    }

    #[test]
    fn test_parse_logic_attr_opaque() {
        // Creusot uses #[logic(opaque)] — maps to Default (already opaque)
        let mode = parse_logic_mode_str("opaque").unwrap();
        assert_eq!(mode, LogicMode::Default);
    }

    #[test]
    fn test_parse_logic_attr_rejects_unknown() {
        let err = parse_logic_mode_str("typo").unwrap_err();
        assert!(err.message.contains("unknown attribute argument"));
        assert!(err.message.contains("typo"));
    }

    #[test]
    fn test_parse_logic_attr_accepts_law() {
        // `#[logic(law)]` is a Creusot axiom marker; map to Open so axioms are emitted.
        let mode = parse_logic_mode_str("law").unwrap();
        assert_eq!(mode, LogicMode::Open);
    }

    #[test]
    fn test_parse_logic_attr_law_allows_more_specific_open_self() {
        let mode = parse_logic_mode_str("law, open(self)").unwrap();
        assert_eq!(mode, LogicMode::OpenSelf);
    }

    #[test]
    fn test_parse_logic_attr_law_does_not_override_prophetic() {
        let mode = parse_logic_mode_str("prophetic, law").unwrap();
        assert_eq!(mode, LogicMode::Prophetic);
    }

    #[test]
    fn test_logic_mode_marker_suffix() {
        assert_eq!(LogicMode::Default.marker_suffix(), "");
        assert_eq!(LogicMode::Open.marker_suffix(), "open:");
        assert_eq!(LogicMode::OpenSelf.marker_suffix(), "open_self:");
        assert_eq!(LogicMode::Prophetic.marker_suffix(), "prophetic:");
    }

    #[test]
    fn test_logic_mode_doc_markers() {
        // Verify complete marker strings match expected format
        let logic_open = format!("trust-wp:logic:{}", LogicMode::Open.marker_suffix());
        assert_eq!(logic_open, "trust-wp:logic:open:");

        let pred_open = format!(
            "trust-wp:logic:{}predicate",
            LogicMode::Open.marker_suffix()
        );
        assert_eq!(pred_open, "trust-wp:logic:open:predicate");

        let logic_default = format!("trust-wp:logic:{}", LogicMode::Default.marker_suffix());
        assert_eq!(logic_default, "trust-wp:logic:");
    }

    // ---- Prophetic compound attribute tests (#2683) ----
    //
    // Creusot's compat tests use `#[logic(prophetic, open)]` on Resolve and
    // Invariant impls. Verify all prophetic compound attribute combinations.

    #[test]
    fn test_parse_logic_attr_prophetic_open() {
        // Used in partially_opaque.rs: `#[logic(prophetic, open)]`
        let mode = parse_logic_mode_str("prophetic, open").unwrap();
        assert_eq!(mode, LogicMode::Prophetic, "prophetic overrides open");
    }

    #[test]
    fn test_parse_logic_attr_open_prophetic() {
        // Reversed order should produce the same result
        let mode = parse_logic_mode_str("open, prophetic").unwrap();
        assert_eq!(
            mode,
            LogicMode::Prophetic,
            "prophetic overrides open regardless of order"
        );
    }

    #[test]
    fn test_parse_logic_attr_prophetic_open_self() {
        let mode = parse_logic_mode_str("prophetic, open(self)").unwrap();
        assert_eq!(mode, LogicMode::Prophetic, "prophetic overrides open(self)");
    }

    #[test]
    fn test_parse_logic_attr_prophetic_opaque() {
        // Unusual combination: prophetic + opaque. Prophetic takes priority.
        let mode = parse_logic_mode_str("prophetic, opaque").unwrap();
        assert_eq!(mode, LogicMode::Prophetic, "prophetic overrides opaque");
    }

    #[test]
    fn test_parse_logic_attr_prophetic_inline() {
        // Creusot hint: inline is ignored, prophetic preserved
        let mode = parse_logic_mode_str("prophetic, inline").unwrap();
        assert_eq!(
            mode,
            LogicMode::Prophetic,
            "inline is ignored, prophetic preserved"
        );
    }

    #[test]
    fn test_parse_logic_attr_prophetic_marker_roundtrip() {
        // Verify the prophetic marker suffix roundtrips through trust-wp-core parsing
        let suffix = LogicMode::Prophetic.marker_suffix();
        assert_eq!(suffix, "prophetic:");

        let full_marker = format!("trust-wp:logic:{suffix}");
        assert_eq!(full_marker, "trust-wp:logic:prophetic:");

        // The marker is parsed by trust-wp-core's LogicMode::from_marker_suffix
        // which strips the "trust-wp:logic:" prefix before matching.
    }
}
