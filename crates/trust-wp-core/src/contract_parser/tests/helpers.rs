// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Parse a contract expression, panicking with a diagnostic message on failure.
#[track_caller]
pub(super) fn parse_ok(input: &str) -> PureExpr {
    parse_contract(input).unwrap_or_else(|e| panic!("parse_contract({input:?}) failed: {e}"))
}

/// Parse a contract body (block expression), panicking with a diagnostic on failure.
#[track_caller]
pub(super) fn parse_body_ok(input: &str) -> PureExpr {
    parse_contract_body(input)
        .unwrap_or_else(|e| panic!("parse_contract_body({input:?}) failed: {e}"))
}

/// Parse a contract with span info, panicking with a diagnostic on failure.
#[track_caller]
pub(super) fn parse_spanned_ok(input: &str) -> SpannedExpr {
    parse_contract_spanned(input)
        .unwrap_or_else(|e| panic!("parse_contract_spanned({input:?}) failed: {e}"))
}
