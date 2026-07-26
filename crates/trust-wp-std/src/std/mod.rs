// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Specifications for Rust standard library types
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides specifications for std types that can be used
//! with trust-wp's verification. These are organized to mirror std's structure.

pub mod boxed;
pub mod builtin_registry;
pub mod cell;
pub mod char;
pub mod clone;
pub mod cmp;
pub mod collections;
pub mod default;
pub mod duration;
mod extern_specs;
pub mod hash;
pub mod instant;
pub mod iter;
pub mod lookup_registry;
pub mod mem;
pub mod num;
pub mod ops;
pub mod option;
pub mod primitives;
pub mod ptr;
pub mod result;
pub mod slice;
pub mod string;
pub mod sync;
#[cfg(test)]
pub(crate) mod test_shim;
pub mod thread;
pub mod vec;
