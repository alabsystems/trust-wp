// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

//! Fixture crate for dropped-contract-clause guard regressions (#814).
//!
//! This crate provides binaries with malformed contract clauses that should be
//! rejected by `parse_and_extract_contract` rather than silently dropped.
