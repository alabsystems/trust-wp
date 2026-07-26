// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic operator traits used by Creusot-compatible specifications.
//!
//! This mirrors the `creusot_std::logic::ops` surface so compatibility tests
//! can import and implement traits like `IndexLogic`.

use super::Int;
use crate::logic;

// All `*Logic` traits below are logic-mode by definition — every operation
// is a specification predicate. Implementers override with `#[logic(open)]`
// to match Creusot. The trait/impl consistency checker enforces the marker
// on impl methods.

/// Trait for indexing operations (`container[index]`) in logic code.
pub trait IndexLogic<I: ?Sized> {
    type Item;

    #[logic(open)]
    fn index_logic(self, idx: I) -> Self::Item;
}

/// Trait for addition (`+`) in logic code.
pub trait AddLogic<Rhs = Self> {
    type Output;

    #[logic(open)]
    fn add(self, other: Rhs) -> Self::Output;
}

/// Trait for subtraction (`-`) in logic code.
pub trait SubLogic<Rhs = Self> {
    type Output;

    #[logic(open)]
    fn sub(self, other: Rhs) -> Self::Output;
}

/// Trait for multiplication (`*`) in logic code.
pub trait MulLogic<Rhs = Self> {
    type Output;

    #[logic(open)]
    fn mul(self, other: Rhs) -> Self::Output;
}

/// Trait for division (`/`) in logic code.
pub trait DivLogic<Rhs = Self> {
    type Output;

    #[logic(open)]
    fn div(self, other: Rhs) -> Self::Output;
}

/// Trait for remainder (`%`) in logic code.
pub trait RemLogic<Rhs = Self> {
    type Output;

    #[logic(open)]
    fn rem(self, other: Rhs) -> Self::Output;
}

/// Trait for unary negation (`-x`) in logic code.
pub trait NegLogic {
    type Output;

    #[logic(open)]
    fn neg(self) -> Self::Output;
}

/// Trait for bit extraction helpers in logic code.
pub trait NthBitLogic {
    #[logic(open)]
    fn nth_bit(self, n: Int) -> bool;
}

/// Trait used by Creusot for overloading final-value (`^`) syntax.
pub trait Fin {
    type Target: ?Sized;

    #[logic(prophetic)]
    fn fin<'a>(self) -> &'a Self::Target;
}

impl<T: ?Sized> Fin for &mut T {
    type Target = T;

    fn fin<'a>(self) -> &'a T {
        let _ = self;
        super::dead()
    }
}
