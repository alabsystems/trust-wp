// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Allow cfg(trust_wp) - this is set by trust-wp-driver during verification
#![allow(unexpected_cfgs)]

//! Ghost block move validation test fixtures.
//!
//! This module contains test cases for ghost block move validation rules
//! as defined in `designs/2026-02-01-ghost-code.md` Section D3.
//!
//! ## Validation Rules Tested
//!
//! 1. **Moving non-Copy, non-Ghost value into ghost block → Error**
//! 2. **Moving Ghost<T> value → Allowed**
//! 3. **Copying Copy value → Allowed**
//!
//! ## How to Run
//!
//! These fixtures are tested via the integration test in trust-wp-driver:
//!
//! ```bash
//! # Run the ghost move validation integration test
//! cargo test -p trust-wp-driver --test ghost_move_validation
//! ```
//!
//! The integration test compiles these fixtures through trust-wp-rustc and
//! verifies that should_pass cases succeed and should_fail cases produce
//! the expected validation errors.
//!
//! ## Expected Results
//!
//! ### should_pass.rs - All functions should verify successfully
//! - `move_ghost_in_ghost` - Ghost<T> can be moved
//! - `copy_in_ghost` - Copy types can be used freely
//! - `borrow_in_ghost` - Borrowing is allowed
//! - `move_local_in_ghost` - Local variables can be moved
//! - `shared_ref_in_ghost` - Shared references are Copy
//! - `array_copy_in_ghost` - Arrays of Copy are Copy
//!
//! ### should_fail.rs - All functions should produce validation errors
//! - `move_non_copy_in_ghost` - Error: "cannot move non-ghost value"
//! - `multiple_moves_in_ghost` - Multiple errors
//! - `nested_ghost_moves` - Error for outer variable
//! - `move_in_call` - Error for function argument
//! - `move_in_struct` - Error for struct field
//! - `move_in_tuple` - Error for tuple element
//! - `move_in_match` - Error for match scrutinee
//! - `move_string` - String is non-Copy
//! - `move_box` - Box is non-Copy

// Note: The should_pass.rs and should_fail.rs are compiled as separate binaries.
// They are NOT modules of this lib to ensure isolated compilation.
//
// Rationale: When testing ghost move validation, we need to check that:
// - should_pass compiles successfully with trust-wp-rustc
// - should_fail produces expected validation errors
//
// If both were modules here, compiling any target would also compile
// the failing module, making it impossible to test the passing case.
