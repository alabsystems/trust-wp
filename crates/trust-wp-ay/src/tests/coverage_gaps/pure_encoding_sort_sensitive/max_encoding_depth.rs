// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── MAX_ENCODING_DEPTH guard ─────────────────────────────────────────

/// Deeply nested expressions hit the depth guard (MAX_ENCODING_DEPTH = 128).
/// Uses a spawned thread with larger stack to avoid actual stack overflow
/// while testing the encoder's guard.
#[test]
#[timeout(30000)]
fn max_encoding_depth_returns_error() {
    let handle = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024) // 8 MB stack
        .spawn(|| {
            let mut encoder = AYEncoder::new();
            let mut expr = bool_expr(true);
            for _ in 0..130 {
                expr = not(expr);
            }
            encoder.encode_pure(&expr)
        })
        .expect("thread spawn");

    let result = handle.join().expect("thread join");
    assert!(
        result.is_err(),
        "130-level nesting should hit MAX_ENCODING_DEPTH (128)"
    );
}
