// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic trait-recursion fixtures (ledger impl_arg + terminates trio).
//!
//! Each binary is tested in isolation — see the [[bin]] entries in Cargo.toml.
//! The should_fail_* binaries pin the four ledgered false-accepts (creusot
//! tests/should_fail/recursive_types/impl_arg.rs and terminates/trait_where.rs
//! / trait_impl_where.rs / trait_where_supertrait.rs); the should_pass_*
//! binaries prove legitimate trait-bounded logic functions are not
//! over-rejected.
