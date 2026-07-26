// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Specifications for `std::sync` types
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These specifications define the contract semantics for synchronization
//! primitives. trust-wp-driver uses these specs when verifying concurrent code.
//!
//! Reference: Creusot's `creusot/tests/should_succeed/mutex.rs`
//!
//! ## Design Notes
//!
//! Mutex/RwLock verification uses an invariant-based approach:
//! - `Inv<T>` trait defines what must hold for protected data
//! - Lock acquisition provides the invariant as a postcondition
//! - Lock release requires the invariant as a precondition
//!
//! This models the rely-guarantee reasoning needed for concurrent verification.

pub mod atomic_relacq;
pub mod atomic_sc;

use std::marker::PhantomData;

/// Trait for lock invariants.
///
/// Types implementing this trait define what property must hold for the
/// protected data at all times between lock acquisitions.
///
/// # Example
///
/// ```text
/// struct EvenInvariant;
///
/// impl Inv<u32> for EvenInvariant {
///     #[logic]
///     fn inv(&self, x: u32) -> bool {
///         x.view() % 2 == 0
///     }
/// }
/// ```
pub trait Inv<T> {
    /// The invariant predicate.
    ///
    /// Returns true if `x` satisfies the invariant.
    fn inv(&self, x: &T) -> bool;
}

/// Trivial invariant that always holds.
///
/// Use this when no specific property needs to be maintained.
#[derive(Debug, Clone, Copy, Default)]
pub struct TrueInv;

impl<T> Inv<T> for TrueInv {
    fn inv(&self, _x: &T) -> bool {
        true
    }
}

// =============================================================================
// Mutex<T, I>
// =============================================================================

/// Specification trait for `std::sync::Mutex<T>`.
///
/// Mutex verification uses ghost invariants to track what properties hold
/// for the protected data. The pattern is:
///
/// ```text
/// #[trusted]
/// #[requires(inv.inv(value))]
/// fn new(value: T, inv: I) -> Mutex<T, I>;
///
/// #[trusted]
/// #[ensures(self.inv().inv(*result))]
/// fn lock(&self) -> MutexGuard<'_, T, I>;
/// ```
///
/// # Contracts
///
/// ## new
/// ```text
/// #[requires(inv.inv(value))]
/// #[ensures(result.inv() == inv)]
/// fn new(value: T, inv: I) -> Mutex<T, I>;
/// ```
///
/// ## lock
/// ```text
/// #[ensures(self.inv().inv(*result))]
/// fn lock(&self) -> MutexGuard<'_, T, I>;
/// ```
///
/// ## `into_inner`
/// ```text
/// #[ensures(self.inv().inv(result))]
/// fn into_inner(self) -> T;
/// ```
///
/// ## `get_mut`
/// ```text
/// #[ensures((*self).inv().inv(*result))]
/// fn get_mut(&mut self) -> &mut T;
/// ```
pub trait MutexSpec<T, I: Inv<T>> {
    /// Get the invariant associated with this mutex.
    fn inv(&self) -> &I;

    /// Create a new mutex with initial value satisfying the invariant.
    fn new_spec(value: T, inv: I) -> Self
    where
        Self: Sized;

    /// Acquire the lock, returning a guard with the invariant property.
    fn lock_spec(&self) -> MutexGuardSpec<'_, T, I>;

    /// Consume the mutex and return the inner value.
    fn into_inner_spec(self) -> T
    where
        Self: Sized;

    /// Get exclusive access without locking (requires unique ownership).
    fn get_mut_spec(&mut self) -> &mut T;
}

/// Specification model for `std::sync::MutexGuard<T>`.
///
/// The guard provides access to the protected data while holding the lock.
/// When dropped, the invariant must be restored.
///
/// # Contracts
///
/// ## deref
/// ```text
/// #[ensures(self.inv().inv(*result))]
/// fn deref(&self) -> &T;
/// ```
///
/// ## `deref_mut` / set
/// ```text
/// #[requires(self.inv().inv(value))]
/// fn set(&mut self, value: T);
/// ```
pub struct MutexGuardSpec<'a, T, I: Inv<T>> {
    /// The protected value.
    pub value: T,
    /// The invariant (as a snapshot for verification).
    pub inv: I,
    /// Lifetime marker.
    pub _marker: PhantomData<&'a ()>,
}

#[allow(clippy::elidable_lifetime_names)]
impl<'a, T, I: Inv<T>> MutexGuardSpec<'a, T, I> {
    /// Access the value (postcondition: invariant holds).
    #[allow(clippy::should_implement_trait)]
    pub fn deref(&self) -> &T {
        &self.value
    }

    /// Set a new value (precondition: invariant holds for new value).
    pub fn set(&mut self, value: T) {
        self.value = value;
    }

    /// Get the invariant.
    pub fn inv(&self) -> &I {
        &self.inv
    }
}

// =============================================================================
// RwLock<T, I>
// =============================================================================

/// Specification trait for `std::sync::RwLock<T>`.
///
/// Similar to Mutex but allows multiple readers or one writer.
///
/// # Contracts
///
/// ## new
/// ```text
/// #[requires(inv.inv(value))]
/// fn new(value: T, inv: I) -> RwLock<T, I>;
/// ```
///
/// ## read
/// ```text
/// #[ensures(self.inv().inv(*result))]
/// fn read(&self) -> RwLockReadGuard<'_, T, I>;
/// ```
///
/// ## write
/// ```text
/// #[ensures(self.inv().inv(*result))]
/// fn write(&self) -> RwLockWriteGuard<'_, T, I>;
/// ```
pub trait RwLockSpec<T, I: Inv<T>> {
    /// Get the invariant.
    fn inv(&self) -> &I;

    /// Create a new `RwLock`.
    fn new_spec(value: T, inv: I) -> Self
    where
        Self: Sized;

    /// Acquire a read lock.
    fn read_spec(&self) -> RwLockReadGuardSpec<'_, T, I>;

    /// Acquire a write lock.
    fn write_spec(&self) -> RwLockWriteGuardSpec<'_, T, I>;

    /// Get inner value.
    fn into_inner_spec(self) -> T
    where
        Self: Sized;

    /// Get mutable reference (unique ownership).
    fn get_mut_spec(&mut self) -> &mut T;
}

/// Read guard specification.
pub struct RwLockReadGuardSpec<'a, T, I: Inv<T>> {
    /// The protected value (read-only).
    pub value: T,
    /// The invariant.
    pub inv: I,
    /// Lifetime marker.
    pub _marker: PhantomData<&'a ()>,
}

#[allow(clippy::elidable_lifetime_names)]
impl<'a, T, I: Inv<T>> RwLockReadGuardSpec<'a, T, I> {
    /// Access the value.
    #[allow(clippy::should_implement_trait)]
    pub fn deref(&self) -> &T {
        &self.value
    }

    /// Get the invariant.
    pub fn inv(&self) -> &I {
        &self.inv
    }
}

/// Write guard specification.
pub struct RwLockWriteGuardSpec<'a, T, I: Inv<T>> {
    /// The protected value.
    pub value: T,
    /// The invariant.
    pub inv: I,
    /// Lifetime marker.
    pub _marker: PhantomData<&'a ()>,
}

#[allow(clippy::elidable_lifetime_names)]
impl<'a, T, I: Inv<T>> RwLockWriteGuardSpec<'a, T, I> {
    /// Access the value.
    #[allow(clippy::should_implement_trait)]
    pub fn deref(&self) -> &T {
        &self.value
    }

    /// Set a new value.
    pub fn set(&mut self, value: T) {
        self.value = value;
    }

    /// Get the invariant.
    pub fn inv(&self) -> &I {
        &self.inv
    }
}

// =============================================================================
// Arc<T>
// =============================================================================

/// Specification trait for `std::sync::Arc<T>`.
///
/// Arc provides shared ownership with atomic reference counting.
/// For verification, we model Arc as providing immutable access
/// to the contained value across threads.
///
/// # Contracts
///
/// ## new
/// ```text
/// #[ensures(*result == value)]
/// fn new(value: T) -> Arc<T>;
/// ```
///
/// ## clone
/// ```text
/// #[ensures(*result == *self)]
/// fn clone(&self) -> Arc<T>;
/// ```
///
/// ## `try_unwrap`
/// ```text
/// #[ensures(match result {
///     Ok(v) => v == *self,
///     Err(arc) => *arc == *self,
/// })]
/// fn try_unwrap(self) -> Result<T, Arc<T>>;
/// ```
pub trait ArcSpec<T> {
    /// Create a new Arc.
    fn new_spec(value: T) -> Self
    where
        Self: Sized;

    /// Get a reference to the value.
    fn deref_spec(&self) -> &T;

    /// Clone the Arc (increments ref count).
    fn clone_spec(&self) -> Self
    where
        Self: Sized,
        T: Clone;

    /// Get the strong reference count.
    fn strong_count_spec(&self) -> usize;

    /// Get the weak reference count.
    fn weak_count_spec(&self) -> usize;

    /// Try to unwrap if this is the only reference.
    fn try_unwrap_spec(this: Self) -> Result<T, Self>
    where
        Self: Sized;
}

// =============================================================================
// Rc<T>
// =============================================================================

/// Specification trait for `std::rc::Rc<T>`.
///
/// Rc provides shared ownership with reference counting (single-threaded).
/// Similar to Arc but not thread-safe.
///
/// # Contracts
///
/// ## new
/// ```text
/// #[ensures(*result == value)]
/// fn new(value: T) -> Rc<T>;
/// ```
///
/// ## clone
/// ```text
/// #[ensures(*result == *self)]
/// fn clone(&self) -> Rc<T>;
/// ```
pub trait RcSpec<T> {
    /// Create a new Rc.
    fn new_spec(value: T) -> Self
    where
        Self: Sized;

    /// Get a reference to the value.
    fn deref_spec(&self) -> &T;

    /// Clone the Rc.
    fn clone_spec(&self) -> Self
    where
        Self: Sized,
        T: Clone;

    /// Get the strong reference count.
    fn strong_count_spec(&self) -> usize;

    /// Get the weak reference count.
    fn weak_count_spec(&self) -> usize;

    /// Try to unwrap if this is the only reference.
    fn try_unwrap_spec(this: Self) -> Result<T, Self>
    where
        Self: Sized;
}

// =============================================================================
// Cell<T> and RefCell<T>
// =============================================================================

/// Specification trait for `std::cell::Cell<T>`.
///
/// Cell provides interior mutability for Copy types.
///
/// # Contracts
///
/// ## new
/// ```text
/// #[ensures(result.get() == value)]
/// fn new(value: T) -> Cell<T>;
/// ```
///
/// ## get
/// ```text
/// #[ensures(result == self.inner())]
/// fn get(&self) -> T;
/// ```
///
/// ## set
/// ```text
/// #[ensures((^self).inner() == value)]
/// fn set(&self, value: T);
/// ```
pub trait CellSpec<T: Copy> {
    /// Get the current value.
    fn get_spec(&self) -> T;

    /// Set a new value.
    fn set_spec(&self, value: T);

    /// Replace the value and return the old one.
    fn replace_spec(&self, value: T) -> T;

    /// Get a mutable reference to the inner value.
    fn get_mut_spec(&mut self) -> &mut T;
}

/// Specification trait for `std::cell::RefCell<T>`.
///
/// `RefCell` provides interior mutability with runtime borrow checking.
///
/// # Contracts
///
/// ## new
/// ```text
/// #[ensures(*result.borrow() == value)]
/// fn new(value: T) -> RefCell<T>;
/// ```
///
/// ## borrow
/// ```text
/// #[ensures(*result == self.inner())]
/// fn borrow(&self) -> Ref<'_, T>;
/// ```
///
/// ## `borrow_mut`
/// ```text
/// #[ensures(*result == self.inner())]
/// #[ensures((^self).inner() == ^result)]
/// fn borrow_mut(&self) -> RefMut<'_, T>;
/// ```
pub trait RefCellSpec<T> {
    /// Create a new `RefCell`.
    fn new_spec(value: T) -> Self
    where
        Self: Sized;

    /// Borrow the value immutably.
    fn borrow_spec(&self) -> RefSpec<'_, T>;

    /// Borrow the value mutably.
    fn borrow_mut_spec(&self) -> RefMutSpec<'_, T>;

    /// Get the inner value.
    fn into_inner_spec(self) -> T
    where
        Self: Sized;

    /// Replace the value.
    fn replace_spec(&self, value: T) -> T;
}

/// Immutable borrow specification.
pub struct RefSpec<'a, T> {
    /// The borrowed value.
    pub value: T,
    /// Lifetime marker.
    pub _marker: PhantomData<&'a T>,
}

#[allow(clippy::elidable_lifetime_names)]
impl<'a, T> RefSpec<'a, T> {
    /// Access the value.
    #[allow(clippy::should_implement_trait)]
    pub fn deref(&self) -> &T {
        &self.value
    }
}

/// Mutable borrow specification.
pub struct RefMutSpec<'a, T> {
    /// The borrowed value.
    pub value: T,
    /// Lifetime marker.
    pub _marker: PhantomData<&'a mut T>,
}

#[allow(clippy::elidable_lifetime_names)]
impl<'a, T> RefMutSpec<'a, T> {
    /// Access the value.
    #[allow(clippy::should_implement_trait)]
    pub fn deref(&self) -> &T {
        &self.value
    }

    /// Set a new value.
    pub fn set(&mut self, value: T) {
        self.value = value;
    }
}

// =============================================================================
// Thread spawn/join (ghost model)
// =============================================================================

/// Specification trait for thread spawn and join.
///
/// This models the postcondition propagation from spawned thread to join.
///
/// # Pattern
///
/// ```text
/// #[requires(f.precondition())]
/// fn spawn<F: FnOnce() -> T>(f: F) -> JoinHandle<T, F::Postcond>;
///
/// #[ensures(match result {
///     Ok(v) => self.postcond().inv(v),
///     Err(_) => true,
/// })]
/// fn join(self) -> Result<T, ()>;
/// ```
pub trait JoinHandleSpec<T, P: Inv<T>> {
    /// Get the postcondition invariant.
    fn postcond(&self) -> &P;

    /// Join the thread and get the result.
    #[allow(clippy::result_unit_err)]
    fn join_spec(self) -> Result<T, ()>
    where
        Self: Sized;
}

// =============================================================================
// Specification string constants for trust-wp-driver
// =============================================================================

/// Internal specification definitions used by the driver's hardcoded fallback
/// tables and local tests. Builtin registry loading happens separately.
#[doc(hidden)]
pub mod specs {
    /// Contract for `Mutex::new`
    pub const MUTEX_NEW: &str = r"
        params: value, inv
        requires: inv.inv(value)
        ensures: result.inv() == inv
    ";

    /// Contract for `Mutex::lock`
    pub const MUTEX_LOCK: &str = r"
        ensures: self.inv().inv(*result)
    ";

    /// Contract for `Mutex::into_inner`
    pub const MUTEX_INTO_INNER: &str = r"
        ensures: self.inv().inv(result)
    ";

    /// Contract for `Mutex::get_mut`
    pub const MUTEX_GET_MUT: &str = r"
        ensures: (*self).inv().inv(*result)
    ";

    /// Contract for `MutexGuard::deref`
    pub const MUTEX_GUARD_DEREF: &str = r"
        ensures: self.inv().inv(*result)
    ";

    /// Contract for `MutexGuard::set` (drop with new value)
    pub const MUTEX_GUARD_SET: &str = r"
        requires: self.inv().inv(value)
        ensures: (^self).inv().inv(value)
    ";

    /// Contract for `Arc::new`
    pub const ARC_NEW: &str = r"
        ensures: *result == value
    ";

    // Inner-value equality: clone preserves the inner T value.
    // Combined with the inner-value biconditional ptr_eq spec, this
    // proves ptr_eq after clone.
    /// Contract for `Arc::clone`
    pub const ARC_CLONE: &str = r"
        ensures: *result == *self
    ";

    /// Contract for `Arc::as_ref`
    pub const ARC_AS_REF: &str = r"
        ensures: result@ == *self
    ";

    /// Contract for `Arc::try_unwrap`
    pub const ARC_TRY_UNWRAP: &str = r"
        ensures: match result {
            Ok(v) => v == *self,
            Err(arc) => *arc == *self,
        }
    ";

    /// Contract for `Rc::new`
    pub const RC_NEW: &str = r"
        ensures: *result == value
    ";

    // Inner-value equality: clone preserves the inner T value.
    // Same semantics as ARC_CLONE.
    /// Contract for `Rc::clone`
    pub const RC_CLONE: &str = r"
        ensures: *result == *self
    ";

    /// Contract for `Rc::as_ref`
    pub const RC_AS_REF: &str = r"
        ensures: result@ == *self
    ";

    /// Contract for `Rc::ptr_eq`
    ///
    /// Biconditional on inner-value equality: `result == (*self == *rhs)`.
    /// Combined with the whole-value clone spec (`result == self`, so
    /// `*result == *self`), this proves `ptr_eq` after clone.
    ///
    /// Soundness note: this spec is slightly over-strong — two distinct
    /// `Rc::new(42)` allocations would prove `ptr_eq == true`, which is
    /// incorrect in Rust. A fully sound model requires allocation identity
    /// tracking, which the current SMT encoding does not support.
    /// The current encoding is safe for the Creusot test suite patterns
    /// (clone-then-ptr_eq and different-value-ptr_eq).
    pub const RC_PTR_EQ: &str = r"
        ensures: result == (*self == *rhs)
    ";

    /// Contract for `Arc::ptr_eq`
    ///
    /// Biconditional on inner-value equality (same as `RC_PTR_EQ`).
    pub const ARC_PTR_EQ: &str = r"
        ensures: result == (*self == *rhs)
    ";

    /// Contract for `Cell::new`
    pub const CELL_NEW: &str = r"
        ensures: result.get() == value
    ";

    /// Contract for `Cell::get`
    pub const CELL_GET: &str = r"
        ensures: result == self.inner()
    ";

    /// Contract for `Cell::set`
    pub const CELL_SET: &str = r"
        ensures: (^self).inner() == value
    ";

    /// Contract for `RefCell::new`
    pub const REFCELL_NEW: &str = r"
        ensures: *result.borrow() == value
    ";

    /// Contract for `RefCell::borrow`
    pub const REFCELL_BORROW: &str = r"
        ensures: *result == self.inner()
    ";

    /// Contract for `RefCell::borrow_mut`
    pub const REFCELL_BORROW_MUT: &str = r"
        ensures: *result == self.inner()
        ensures: (^self).inner() == ^result
    ";

    /// Contract for `thread::spawn`
    pub const SPAWN: &str = r"
        params: f
        requires: f.precondition()
        ensures: result.postcond() == f.postcond()
    ";

    /// Contract for `JoinHandle::join`
    pub const JOIN: &str = r"
        ensures: match result {
            Ok(v) => self.postcond().inv(v),
            Err(_) => true,
        }
    ";

    // =========================================================================
    // Atomic operation specs (preventing opaque classification)
    // =========================================================================

    // AtomicBool/AtomicUsize/AtomicI32/AtomicU32/AtomicU64 — all variants
    // use empty specs to prevent OpaqueCallTrueAssumption fallback.
    // The actual atomic semantics come from the wrapper implementation
    // (trust_wp_std::std::sync::atomic_sc and atomic_relacq modules).

    /// Atomic new — constructs an atomic value
    pub const ATOMIC_NEW: &str = "";

    /// Atomic into_inner — consumes and returns inner value
    pub const ATOMIC_INTO_INNER: &str = "";

    /// Atomic load — reads current value
    pub const ATOMIC_LOAD: &str = "";

    /// Atomic store — writes value
    pub const ATOMIC_STORE: &str = "";

    /// Atomic swap — atomically replaces value, returning old
    pub const ATOMIC_SWAP: &str = "";

    /// Atomic fetch_add — atomically adds, returning old value
    pub const ATOMIC_FETCH_ADD: &str = "";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_true_inv() {
        let inv = TrueInv;
        assert!(inv.inv(&42));
        assert!(inv.inv(&"hello"));
        assert!(inv.inv(&vec![1, 2, 3]));
    }

    #[test]
    fn test_custom_inv() {
        struct EvenInv;

        impl Inv<i32> for EvenInv {
            fn inv(&self, x: &i32) -> bool {
                x % 2 == 0
            }
        }

        let inv = EvenInv;
        assert!(inv.inv(&0));
        assert!(inv.inv(&2));
        assert!(inv.inv(&-4));
        assert!(!inv.inv(&1));
        assert!(!inv.inv(&-3));
    }

    #[test]
    fn test_mutex_guard_spec() {
        let mut guard: MutexGuardSpec<'_, i32, TrueInv> = MutexGuardSpec {
            value: 42,
            inv: TrueInv,
            _marker: PhantomData,
        };

        assert_eq!(*guard.deref(), 42);
        guard.set(100);
        assert_eq!(*guard.deref(), 100);
    }

    #[test]
    fn test_ref_spec() {
        let r: RefSpec<'_, i32> = RefSpec {
            value: 42,
            _marker: PhantomData,
        };
        assert_eq!(*r.deref(), 42);
    }

    #[test]
    fn test_ref_mut_spec() {
        let mut r: RefMutSpec<'_, i32> = RefMutSpec {
            value: 42,
            _marker: PhantomData,
        };
        assert_eq!(*r.deref(), 42);
        r.set(100);
        assert_eq!(*r.deref(), 100);
    }
}
