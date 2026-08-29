// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Serialization helpers for verification bundles.
//!
//! The tRust verify-bundle request/result boundary is JSON-serializable for
//! debugging, replay, and cross-process communication. The older
//! [`VerificationBundle`] helpers remain fail-closed until the lower-level
//! expression/result internals gain serde support.

use crate::{
    bundle::VerificationBundle, error::TrustWpLibError, VerifyBundleRequest, VerifyBundleResult,
};

/// Serialize a verification bundle to JSON.
///
/// # Errors
///
/// Returns `TrustWpLibError::InvalidBundle` until Phase 1a adds serde support
/// to the inner types (`PureExpr`, `ExprSort`, etc.).
pub fn serialize_bundle(_bundle: &VerificationBundle) -> Result<String, TrustWpLibError> {
    Err(TrustWpLibError::InvalidBundle(
        "serde support pending: inner types need #[derive(Serialize, Deserialize)] (Phase 1a)"
            .into(),
    ))
}

/// Deserialize a verification bundle from JSON.
///
/// # Errors
///
/// Returns `TrustWpLibError::InvalidBundle` until Phase 1a adds serde support
/// to the inner types (`PureExpr`, `ExprSort`, etc.).
pub fn deserialize_bundle(_json: &str) -> Result<VerificationBundle, TrustWpLibError> {
    Err(TrustWpLibError::InvalidBundle(
        "serde support pending: inner types need #[derive(Serialize, Deserialize)] (Phase 1a)"
            .into(),
    ))
}

/// Serialize a tRust verify-bundle request to pretty JSON.
///
/// # Errors
///
/// Returns [`TrustWpLibError::Serialization`] if JSON serialization fails.
pub fn serialize_verify_bundle_request(
    request: &VerifyBundleRequest,
) -> Result<String, TrustWpLibError> {
    serde_json::to_string_pretty(request).map_err(TrustWpLibError::from)
}

/// Deserialize a tRust verify-bundle request from JSON.
///
/// # Errors
///
/// Returns [`TrustWpLibError::Serialization`] if the payload is not a valid
/// `VerifyBundleRequest`.
pub fn deserialize_verify_bundle_request(
    json: &str,
) -> Result<VerifyBundleRequest, TrustWpLibError> {
    serde_json::from_str(json).map_err(TrustWpLibError::from)
}

/// Serialize a tRust verify-bundle result to pretty JSON.
///
/// # Errors
///
/// Returns [`TrustWpLibError::Serialization`] if JSON serialization fails.
pub fn serialize_verify_bundle_result(
    result: &VerifyBundleResult,
) -> Result<String, TrustWpLibError> {
    serde_json::to_string_pretty(result).map_err(TrustWpLibError::from)
}

/// Deserialize a tRust verify-bundle result from JSON.
///
/// # Errors
///
/// Returns [`TrustWpLibError::Serialization`] if the payload is not a valid
/// `VerifyBundleResult`.
pub fn deserialize_verify_bundle_result(json: &str) -> Result<VerifyBundleResult, TrustWpLibError> {
    serde_json::from_str(json).map_err(TrustWpLibError::from)
}
