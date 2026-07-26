// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unspanned expression parsing for contract attributes.
//!
//! Primary expressions, character literals, block/let lowering, and pattern
//! desugaring. Operator-precedence descent lives in `precedence.rs`; postfix
//! parsing (view `@`, method calls, indexing) lives in `postfix.rs`.

mod blocks;
mod postfix;
mod precedence;
mod primary;
