// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error types for trust-wp-lib operations.

use trust_wp_ay::EncodingError;
use trust_wp_core::verify_bundle::TrustTmirAdapterError;

#[cfg(feature = "trust-ir-native")]
use crate::trust_ir_native::TrustIrNativeBundleError;

/// Errors from trust-wp-lib operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TrustWpLibError {
    /// Verification encoding failed.
    #[error("encoding error: {0}")]
    Encoding(#[from] EncodingError),

    /// Serialization/deserialization failed.
    #[error("serialization error: {0}")]
    Serialization(#[from] serde_json::Error),

    /// Trust/tMIR adapter preparation failed.
    #[error("Trust/tMIR adapter error: {0}")]
    TrustTmirAdapter(#[from] TrustTmirAdapterError),

    /// trust-ir native bundle preparation failed.
    #[cfg(feature = "trust-ir-native")]
    #[error("trust-ir native bundle error: {0}")]
    TrustIrNativeBundle(#[from] TrustIrNativeBundleError),

    /// Bundle validation failed (e.g., missing required fields).
    #[error("invalid bundle: {0}")]
    InvalidBundle(String),
}
