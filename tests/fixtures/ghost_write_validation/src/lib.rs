// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Allow cfg(trust_wp) - this is set by trust-wp-driver during verification
#![allow(unexpected_cfgs)]

//! Ghost block write validation test fixtures.
//!
//! This module contains test cases for ghost block write validation rules
//! as defined in `designs/2026-02-01-ghost-code.md` Section D2.
//!
//! ## Validation Rules Tested
//!
//! 1. **Writing to non-ghost variable in ghost block → Error**
//! 2. **Compound assignment to non-ghost variable → Error**
//! 3. **Field/index write on non-ghost variable → Error**
//! 4. **Deref write through non-ghost pointer → Error**
//! 5. **Writing to local (ghost-block-scoped) variable → Allowed**
//!
//! ## How to Run
//!
//! These fixtures are tested via the integration test in trust-wp-driver:
//!
//! ```bash
//! # Run the ghost write validation integration test
//! cargo test -p trust-wp-driver --test ghost_write_validation
//! ```
//!
//! The integration test compiles these fixtures through trust-wp-rustc and
//! verifies that should_pass cases succeed and should_fail cases produce
//! the expected validation errors.

// Note: The should_pass.rs and should_fail.rs are compiled as separate binaries.
// They are NOT modules of this lib to ensure isolated compilation.
