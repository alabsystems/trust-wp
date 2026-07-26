// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Allow cfg(trust_wp) - this is set by trust-wp-driver during verification
#![allow(unexpected_cfgs)]

//! Ghost erasure check test fixtures.
//!
//! This module contains test cases for the MIR-level ghost erasure soundness
//! check as defined in #1768.
//!
//! ## Checks Tested
//!
//! 1. **Ghost-returning function from ghost-only body → Allowed**
//! 2. **Normal ghost block usage without leaks → Allowed**
//! 3. **Ghost-derived runtime branch (`SwitchInt`) → Error**
//!
//! ## How to Run
//!
//! These fixtures are tested via the integration test in trust-wp-driver:
//!
//! ```bash
//! cargo test -p trust-wp-driver --test ghost_erasure_check
//! ```
//!
//! The integration test compiles these fixtures through trust-wp-rustc and
//! verifies that the two pass cases succeed and the `should_fail_switchint`
//! fixture produces the expected validation error.

// Note: The fixture binaries are compiled separately rather than as modules of
// this lib so each erasure scenario is checked in isolation.
