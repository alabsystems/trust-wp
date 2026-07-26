// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic types for specifications
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides logical types used in specifications:
//! - `Seq<T>` - Logical sequences for modeling collections
//! - `Int` - Unbounded integers for avoiding overflow concerns
//! - `View` - Trait for converting runtime types to logical models
//! - `FMap<K, V>` - Finite maps for ghost code
//! - `FSet<T>` - Finite sets for ghost code
//! - `Mapping<A, B>` - Total functions for ghost code
//! - `ra` - Resource algebras for separation logic

pub mod fmap;
pub mod fset;
mod int;
pub mod mapping;
mod model;
pub mod ops;
mod ord;
pub mod ra;
pub mod real;
pub mod seq;
pub mod such_that;
mod well_founded;

pub use fmap::FMap;
pub use fset::FSet;
pub use int::Int;
pub use mapping::Mapping;
pub use model::{view, DeepModel, View};
pub use ord::OrdLogic;
pub use ra::{Ag, Excl, Frac, Id, UnitRA, RA};
pub use seq::Seq;
pub use such_that::{dead, such_that, unreachable};
pub use well_founded::WellFounded;
