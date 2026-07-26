// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for raw pointer types (`*const T`, `*mut T`)
//!
//! Provides logical methods for reasoning about pointers in specifications.
//!
//! Reference: Creusot `creusot-std/src/std/ptr.rs`

use core::{convert::TryFrom, marker::PhantomData};

use crate::{ghost::Ghost, logic::Int, trusted};

/// Extension trait providing logical methods for raw pointers.
///
/// `Ext`-suffixed traits add new specification-only capabilities with no
/// runtime std counterpart (see [crate-level naming convention](crate)).
///
/// In Creusot, `addr_logic` is a built-in that maps to the SMT pointer
/// address model. Here we provide a runtime stub that returns the actual
/// pointer address, which the trust-wp driver can intercept for verification.
pub trait PointerExt<T: ?Sized>: Sized {
    /// Logical address of the pointer.
    ///
    /// In specification context, this returns the abstract address used for
    /// separation logic reasoning. At runtime, returns the actual address.
    fn addr_logic(self) -> usize;

    /// True if the pointer is null (`addr_logic` == 0).
    #[trusted]
    #[allow(clippy::wrong_self_convention)]
    fn is_null_logic(self) -> bool {
        self.addr_logic() == 0
    }
}

impl<T: ?Sized> PointerExt<T> for *const T {
    fn addr_logic(self) -> usize {
        self.cast::<()>() as usize
    }
}

impl<T: ?Sized> PointerExt<T> for *mut T {
    fn addr_logic(self) -> usize {
        self.cast_const().cast::<()>() as usize
    }
}

/// Extension trait for sized pointer offset operations.
///
/// See [`PointerExt`] for the base trait and [naming convention](crate).
pub trait SizedPointerExt<T>: PointerExt<T> {
    /// Logical pointer offset.
    ///
    /// Returns a pointer whose `addr_logic` is offset by
    /// `offset * size_of::<T>()` from `self.addr_logic()`.
    fn offset_logic(self, offset: Int) -> Self;
}

fn offset_addr_logic<T>(addr: usize, offset: Int) -> usize {
    let addr = i128::try_from(addr).expect("pointer address must fit in i128");
    let size = i128::try_from(core::mem::size_of::<T>()).expect("type size must fit in i128");
    let delta = offset
        .0
        .checked_mul(size)
        .expect("pointer offset multiplication overflow");
    let target = addr
        .checked_add(delta)
        .expect("pointer offset addition overflow");
    usize::try_from(target).expect("pointer offset produced a negative address")
}

impl<T> SizedPointerExt<T> for *const T {
    fn offset_logic(self, offset: Int) -> Self {
        offset_addr_logic::<T>(self.addr_logic(), offset) as *const T
    }
}

impl<T> SizedPointerExt<T> for *mut T {
    fn offset_logic(self, offset: Int) -> Self {
        offset_addr_logic::<T>(self.addr_logic(), offset) as *mut T
    }
}

/// Extension methods for slice raw pointers.
pub trait SlicePointerExt<T>: PointerExt<[T]> {
    /// Remove slice metadata and keep only the data pointer.
    fn thin(self) -> *const T;

    /// Get the logical slice length carried by the wide pointer.
    fn len_logic(self) -> usize;
}

impl<T> SlicePointerExt<T> for *const [T] {
    fn thin(self) -> *const T {
        self.cast::<T>()
    }

    fn len_logic(self) -> usize {
        self.len()
    }
}

impl<T> SlicePointerExt<T> for *mut [T] {
    fn thin(self) -> *const T {
        self.cast::<T>()
    }

    fn len_logic(self) -> usize {
        self.cast_const().len()
    }
}

/// Lightweight ghost witness used by permission-aware pointer arithmetic.
pub struct PtrLive<'a, T>(PhantomData<&'a T>);

impl<T> Clone for PtrLive<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for PtrLive<'_, T> {}

/// Pointer offsets with lightweight live-range witnesses.
pub trait PtrAddExt<'a, T>: Sized {
    /// Wrapper around pointer addition with a ghost witness.
    ///
    /// # Safety
    ///
    /// Callers must uphold the same validity requirements as the underlying
    /// raw-pointer addition operation.
    unsafe fn add_live(self, offset: usize, live: Ghost<PtrLive<'a, T>>) -> Self;

    /// Wrapper around pointer offset with a ghost witness.
    ///
    /// # Safety
    ///
    /// Callers must uphold the same validity requirements as the underlying
    /// raw-pointer offset operation.
    unsafe fn offset_live(self, offset: isize, live: Ghost<PtrLive<'a, T>>) -> Self;
}

impl<'a, T> PtrAddExt<'a, T> for *const T {
    unsafe fn add_live(self, offset: usize, live: Ghost<PtrLive<'a, T>>) -> Self {
        let _ = live;
        // SAFETY: callers of `add_live` must satisfy the same safety contract
        // as the underlying pointer primitive.
        unsafe { self.add(offset) }
    }

    unsafe fn offset_live(self, offset: isize, live: Ghost<PtrLive<'a, T>>) -> Self {
        let _ = live;
        // SAFETY: callers of `offset_live` must satisfy the same safety
        // contract as the underlying pointer primitive.
        unsafe { self.offset(offset) }
    }
}

impl<'a, T> PtrAddExt<'a, T> for *mut T {
    unsafe fn add_live(self, offset: usize, live: Ghost<PtrLive<'a, T>>) -> Self {
        let _ = live;
        // SAFETY: callers of `add_live` must satisfy the same safety contract
        // as the underlying pointer primitive.
        unsafe { self.add(offset) }
    }

    unsafe fn offset_live(self, offset: isize, live: Ghost<PtrLive<'a, T>>) -> Self {
        let _ = live;
        // SAFETY: callers of `offset_live` must satisfy the same safety
        // contract as the underlying pointer primitive.
        unsafe { self.offset(offset) }
    }
}

/// Specification constants for driver lookup.
#[doc(hidden)]
pub mod specs {
    /// Contract for `<*const T>::addr`
    pub const ADDR: &str = r"
        ensures: result == self.addr_logic()
    ";

    /// Contract for `<*const T>::is_null`
    pub const IS_NULL: &str = r"
        ensures: result == self.is_null_logic()
    ";

    /// Contract for `core::ptr::null` and `core::ptr::null_mut`.
    ///
    /// Both return a pointer with `addr_logic() == 0`. The address-equals-zero
    /// postcondition lets impls that `Default for *mut ()` or similar wrappers
    /// (e.g. `Elem(std::ptr::null_mut())` in `union_find_*`) discharge their
    /// fail-closed opaque-call obligation rather than getting a synthetic
    /// `requires(false)`.
    pub const NULL_PTR: &str = r"
        params:
        ensures: result.addr_logic() == 0
    ";

    /// Contract for `core::ptr::addr_eq`.
    ///
    /// Returns true iff both pointers carry the same logical address. This is
    /// the underlying spec for `Elem::eq` shims that compare `*mut ()` via
    /// address rather than provenance.
    pub const ADDR_EQ: &str = r"
        ensures: result == (p.addr_logic() == q.addr_logic())
    ";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ghost::Ghost;

    #[test]
    fn test_const_ptr_addr_logic() {
        let x: i32 = 42;
        let p: *const i32 = &raw const x;
        let addr = p.addr_logic();
        assert!(addr != 0);
        assert_eq!(addr, p as usize);
    }

    #[test]
    fn test_mut_ptr_addr_logic() {
        let mut x: i32 = 42;
        let p: *mut i32 = &raw mut x;
        let addr = p.addr_logic();
        assert!(addr != 0);
        assert_eq!(addr, p as usize);
    }

    #[test]
    fn test_null_ptr_is_null_logic() {
        let p: *const i32 = core::ptr::null();
        assert!(p.is_null_logic());
    }

    #[test]
    fn test_slice_ptr_addr_logic() {
        let arr: [usize; 3] = [1, 2, 3];
        let p: *const [usize] = &arr as &[usize];
        let addr = p.addr_logic();
        assert!(addr != 0);
    }

    #[test]
    fn test_const_ptr_offset_logic() {
        let arr = [10_i32, 20, 30];
        let base = arr.as_ptr();
        let plus_two = base.offset_logic(Int::from(2_usize));
        assert_eq!(plus_two.addr_logic(), base.wrapping_add(2).addr_logic());

        let back_one = plus_two.offset_logic(Int::from(-1_i32));
        assert_eq!(back_one.addr_logic(), base.wrapping_add(1).addr_logic());
    }

    #[test]
    fn test_mut_ptr_offset_logic() {
        let mut arr = [10_i32, 20, 30];
        let base = arr.as_mut_ptr();
        let plus_one = base.offset_logic(Int::from(1_usize));
        assert_eq!(plus_one.addr_logic(), base.wrapping_add(1).addr_logic());

        let back_one = plus_one.offset_logic(Int::from(-1_i32));
        assert_eq!(back_one.addr_logic(), base.addr_logic());
    }

    #[test]
    fn test_slice_pointer_ext_const() {
        let arr = [1_i32, 2, 3];
        let ptr: *const [i32] = &arr;
        assert_eq!(ptr.thin(), arr.as_ptr());
        assert_eq!(ptr.len_logic(), arr.len());
    }

    #[test]
    fn test_slice_pointer_ext_mut() {
        let mut arr = [1_i32, 2, 3];
        let ptr: *mut [i32] = &mut arr;
        assert_eq!(ptr.thin(), arr.as_ptr());
        assert_eq!(ptr.len_logic(), arr.len());
    }

    #[test]
    fn test_const_ptr_add_live() {
        let arr = [10_i32, 20, 30];
        let base = arr.as_ptr();
        let next = unsafe { base.add_live(1, Ghost::conjure()) };
        assert_eq!(next.addr_logic(), base.wrapping_add(1).addr_logic());
    }

    #[test]
    fn test_mut_ptr_offset_live() {
        let mut arr = [10_i32, 20, 30];
        let base = arr.as_mut_ptr();
        let next = unsafe { base.offset_live(1, Ghost::conjure()) };
        assert_eq!(next.addr_logic(), base.wrapping_add(1).addr_logic());
    }
}
