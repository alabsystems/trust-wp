// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `extern_spec!` declarations for standard library types.
//!
//! These generate hidden stub functions with `trust-wp:extern_spec:target=...`
//! doc markers that trust-wp-driver discovers during verification. Discovered
//! extern specs take priority over the hardcoded `std_specs` table.
//!
//! Reference: Creusot `creusot-std/src/std/` `extern_spec` blocks.

// Clone trait impls for primitives use `&self` which is correct for the API
// contract but triggers trivially_copy_pass_by_ref for small Copy types.
#![allow(clippy::trivially_copy_pass_by_ref)]

// -- Vec<T> ------------------------------------------------------------------

crate::extern_spec! {
    impl<T> std::vec::Vec::<T> {
        #[ensures(result@.len() == 0)]
        fn new() -> std::vec::Vec::<T>;

        #[ensures(result@ == self@.len())]
        fn len(&self) -> usize;

        #[ensures(result == (self@.len() == 0))]
        fn is_empty(&self) -> bool;

        #[ensures((^self)@ == self@.push_back(value))]
        fn push(&mut self, value: T);

        #[ensures((^self)@.len() == 0)]
        fn clear(&mut self);

        #[ensures(result@ >= self@.len())]
        fn capacity(&self) -> usize;
    }
}

// Methods intentionally NOT in the extern_spec block above (stronger specs
// exist in the hardcoded std_specs table in trust-wp-driver, and extern_specs
// take priority, so weaker extern_specs would shadow them — see #1999):
//   with_capacity, pop, insert, remove, reserve, reserve_exact,
//   shrink_to_fit, shrink_to
//
// `Vec::get` / `get_mut` are provided through the built-in registry and the
// hardcoded std-spec tables instead of `extern_spec!`: those methods come from
// `[T]` via Deref, so the macro's `Vec::<T>::get(...)` stub expansion does not
// resolve on stable Rust.

crate::extern_spec! {
    impl<T, I> core::ops::Index<I> for std::vec::Vec::<T>
    where
        I: core::slice::SliceIndex<[T]> + crate::std::slice::SliceIndexSpec<T>,
    {
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, result))]
        fn index(&self, ix: I) -> &I::Output;
    }
}

crate::extern_spec! {
    impl<T, I> core::ops::IndexMut<I> for std::vec::Vec::<T>
    where
        I: core::slice::SliceIndex<[T]> + crate::std::slice::SliceIndexSpec<T>,
    {
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, result))]
        #[ensures(ix.has_value((^self)@, ^result))]
        #[ensures(ix.resolve_elsewhere(self@, (^self)@))]
        #[ensures((^self)@.len() == self@.len())]
        fn index_mut(&mut self, ix: I) -> &mut I::Output;
    }
}

// -- Slice [T] ---------------------------------------------------------------
// `len`, `is_empty`, `first`, `last` use `extern_spec!` directly.
// `index`, `index_mut` use generic `SliceIndexSpec`-based extern_specs (#1609).
// Remaining methods (`get`, `get_mut`, `contains`, `binary_search`) stay in
// fallback `std_specs` tables (lookup_registry::PTR_SLICE).

crate::extern_spec! {
    impl<T> [T] {
        #[ensures(result@ == self@.len())]
        fn len(&self) -> usize;

        #[ensures(result == (self@.len() == 0))]
        fn is_empty(&self) -> bool;

        #[ensures(match result {
            Some(v) => self@.len() > 0 && *v == self@.index_logic(0),
            None => self@.len() == 0,
        })]
        fn first(&self) -> Option<&T>;

        #[ensures(match result {
            Some(v) => self@.len() > 0 && *v == self@[self@.len() - 1],
            None => self@.len() == 0,
        })]
        fn last(&self) -> Option<&T>;
    }
}

crate::extern_spec! {
    impl<T, I> core::ops::Index<I> for [T]
    where
        I: core::slice::SliceIndex<[T]> + crate::std::slice::SliceIndexSpec<T>,
    {
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, result))]
        fn index(&self, ix: I) -> &I::Output;
    }
}

crate::extern_spec! {
    impl<T, I> core::ops::IndexMut<I> for [T]
    where
        I: core::slice::SliceIndex<[T]> + crate::std::slice::SliceIndexSpec<T>,
    {
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, result))]
        #[ensures(ix.has_value((^self)@, ^result))]
        #[ensures(ix.resolve_elsewhere(self@, (^self)@))]
        #[ensures((^self)@.len() == self@.len())]
        fn index_mut(&mut self, ix: I) -> &mut I::Output;
    }
}

// -- Option<T> ---------------------------------------------------------------

crate::extern_spec! {
    impl<T> core::option::Option::<T> {
        #[ensures(result == self.is_some())]
        fn is_some(&self) -> bool;

        #[ensures(result == !self.is_some())]
        fn is_none(&self) -> bool;

        #[requires(self.is_some())]
        #[ensures(Some(result) == old(self))]
        fn unwrap(self) -> T;

        #[requires(self.is_some())]
        #[ensures(Some(result) == old(self))]
        fn expect(self, msg: &str) -> T;

        fn as_ref(&self) -> Option<&T>;

        fn as_mut(&mut self) -> Option<&mut T>;

        #[ensures(result == old(*self))]
        fn take(&mut self) -> Option<T>;

        #[ensures(result == old(*self))]
        fn replace(&mut self, value: T) -> Option<T>;

        #[ensures(self.is_none() ==> result.is_none())]
        fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U>;

        #[ensures(self.is_none() ==> result.is_none())]
        fn and_then<U, F: FnOnce(T) -> Option<U>>(self, f: F) -> Option<U>;

        #[ensures(self.is_none() ==> result == default)]
        fn unwrap_or(self, default: T) -> T;
    }
}

// -- Result<T, E> ------------------------------------------------------------

crate::extern_spec! {
    impl<T, E> core::result::Result::<T, E> {
        #[ensures(result == self.is_ok())]
        fn is_ok(&self) -> bool;

        #[ensures(result == !self.is_ok())]
        fn is_err(&self) -> bool;

        fn ok(self) -> Option<T>;

        fn err(self) -> Option<E>;

        fn as_ref(&self) -> Result<&T, &E>;

        fn as_mut(&mut self) -> Result<&mut T, &mut E>;

        #[ensures(self.is_err() ==> result.is_err())]
        fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Result<U, E>;

        #[ensures(self.is_err() ==> result.is_err())]
        fn and_then<U, F: FnOnce(T) -> Result<U, E>>(self, f: F) -> Result<U, E>;

        #[ensures(self.is_err() ==> result == default)]
        fn unwrap_or(self, default: T) -> T;
    }
}

crate::extern_spec! {
    impl<T, E: std::fmt::Debug> core::result::Result::<T, E> {
        #[requires(self.is_ok())]
        #[ensures(Ok(result) == old(self))]
        fn unwrap(self) -> T;

        #[requires(self.is_ok())]
        #[ensures(Ok(result) == old(self))]
        fn expect(self, msg: &str) -> T;
    }
}

crate::extern_spec! {
    impl<T: std::fmt::Debug, E> core::result::Result::<T, E> {
        #[requires(self.is_err())]
        #[ensures(Err(result) == old(self))]
        fn unwrap_err(self) -> E;
    }
}

// -- Clone for primitive types -----------------------------------------------

crate::extern_spec! {
    impl core::clone::Clone for bool {
        #[ensures(result == *self)]
        fn clone(&self) -> bool;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for i8 {
        #[ensures(result == *self)]
        fn clone(&self) -> i8;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for i16 {
        #[ensures(result == *self)]
        fn clone(&self) -> i16;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for i32 {
        #[ensures(result == *self)]
        fn clone(&self) -> i32;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for i64 {
        #[ensures(result == *self)]
        fn clone(&self) -> i64;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for i128 {
        #[ensures(result == *self)]
        fn clone(&self) -> i128;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for isize {
        #[ensures(result == *self)]
        fn clone(&self) -> isize;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for u8 {
        #[ensures(result == *self)]
        fn clone(&self) -> u8;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for u16 {
        #[ensures(result == *self)]
        fn clone(&self) -> u16;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for u32 {
        #[ensures(result == *self)]
        fn clone(&self) -> u32;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for u64 {
        #[ensures(result == *self)]
        fn clone(&self) -> u64;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for u128 {
        #[ensures(result == *self)]
        fn clone(&self) -> u128;
    }
}

crate::extern_spec! {
    impl core::clone::Clone for usize {
        #[ensures(result == *self)]
        fn clone(&self) -> usize;
    }
}

// -- Default for primitive types ---------------------------------------------

crate::extern_spec! {
    impl core::default::Default for bool {
        #[ensures(result == false)]
        fn default() -> bool;
    }
}

crate::extern_spec! {
    impl core::default::Default for i32 {
        #[ensures(result == 0)]
        fn default() -> i32;
    }
}

crate::extern_spec! {
    impl core::default::Default for u32 {
        #[ensures(result == 0)]
        fn default() -> u32;
    }
}

crate::extern_spec! {
    impl core::default::Default for usize {
        #[ensures(result == 0)]
        fn default() -> usize;
    }
}

crate::extern_spec! {
    impl core::default::Default for isize {
        #[ensures(result == 0)]
        fn default() -> isize;
    }
}

crate::extern_spec! {
    impl core::default::Default for u8 {
        #[ensures(result == 0)]
        fn default() -> u8;
    }
}

crate::extern_spec! {
    impl core::default::Default for i8 {
        #[ensures(result == 0)]
        fn default() -> i8;
    }
}

crate::extern_spec! {
    impl core::default::Default for u16 {
        #[ensures(result == 0)]
        fn default() -> u16;
    }
}

crate::extern_spec! {
    impl core::default::Default for i16 {
        #[ensures(result == 0)]
        fn default() -> i16;
    }
}

crate::extern_spec! {
    impl core::default::Default for u64 {
        #[ensures(result == 0)]
        fn default() -> u64;
    }
}

crate::extern_spec! {
    impl core::default::Default for i64 {
        #[ensures(result == 0)]
        fn default() -> i64;
    }
}

crate::extern_spec! {
    impl core::default::Default for i128 {
        #[ensures(result == 0i128)]
        fn default() -> i128;
    }
}

crate::extern_spec! {
    impl core::default::Default for u128 {
        #[ensures(result == 0u128)]
        fn default() -> u128;
    }
}

// -- Option<T> combinators ---------------------------------------------------
// These combinators have no driver-table entries and are commonly used.
// Adding them as extern_specs provides the first coverage for these methods.

crate::extern_spec! {
    impl<T> core::option::Option::<T> {
        #[ensures(self.is_some() ==> result == self)]
        #[ensures(self.is_none() ==> result == optb)]
        fn or(self, optb: core::option::Option::<T>) -> core::option::Option::<T>;

        #[ensures(self.is_none() ==> result.is_none())]
        #[ensures(self.is_some() ==> result == optb)]
        fn and<U>(self, optb: core::option::Option::<U>) -> core::option::Option::<U>;

        #[ensures(self.is_none() ==> result.is_none())]
        #[ensures(other.is_none() ==> result.is_none())]
        #[ensures(self.is_some() && other.is_some() ==> result.is_some())]
        fn zip<U>(self, other: core::option::Option::<U>) -> core::option::Option::<(T, U)>;
    }
}

// `unwrap_or_default` requires `T: Default` — separate impl block.
crate::extern_spec! {
    impl<T: core::default::Default> core::option::Option::<T> {
        #[ensures(self.is_some() ==> Some(result) == self)]
        #[ensures(self.is_none() ==> result == T::default())]
        fn unwrap_or_default(self) -> T;
    }
}

// -- Result<T, E> combinators ------------------------------------------------
// These combinators have no driver-table entries and are commonly used.

crate::extern_spec! {
    impl<T, E> core::result::Result::<T, E> {
        #[ensures(self.is_err() ==> result.is_err())]
        #[ensures(self.is_ok() ==> result == res)]
        fn and<U>(self, res: core::result::Result::<U, E>) -> core::result::Result::<U, E>;

        #[ensures(self.is_ok() ==> result.is_ok())]
        #[ensures(self.is_err() ==> result == res)]
        fn or<F>(self, res: core::result::Result::<T, F>) -> core::result::Result::<T, F>;
    }
}

// `Result::unwrap_or_default` requires `T: Default` — separate impl block.
crate::extern_spec! {
    impl<T: core::default::Default, E: core::fmt::Debug> core::result::Result::<T, E> {
        #[ensures(self.is_ok() ==> Ok(result) == old(self))]
        #[ensures(self.is_err() ==> result == T::default())]
        fn unwrap_or_default(self) -> T;
    }
}

// -- String ------------------------------------------------------------------

crate::extern_spec! {
    impl std::string::String {
        #[ensures(result.len() == 0)]
        fn new() -> std::string::String;

        #[ensures(result@ >= self@.len())]
        #[ensures(self@.len() == 1 ==> result@ == self@.index_logic(0).to_utf8().len())]
        fn len(&self) -> usize;

        #[ensures(result == (self.len() == 0))]
        fn is_empty(&self) -> bool;

        #[ensures((^self).len() == 0)]
        fn clear(&mut self);

        #[ensures(result >= self.len())]
        fn capacity(&self) -> usize;
    }
}
