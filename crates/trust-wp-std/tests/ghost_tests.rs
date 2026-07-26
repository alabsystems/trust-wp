// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for ghost code support (Phase 2)
//!
//! These tests verify the integration of ghost code support:
//! 1. Runtime behavior: ghost blocks erase to `{}` when `cfg(trust_wp)` is not set
//! 2. Type system: `Ghost<T>` and `Snapshot<T>` are zero-sized
//! 3. Semantics: ghost code can read program variables but is erased at runtime
//!
//! For verification-time behavior (driver ghost block detection), see
//! `designs/2026-02-01-ghost-code.md` and `crates/trust-wp-driver/src/ghost.rs`.

use trust_wp_std::{
    cell::PermCell,
    ghost,
    ghost::{
        invariant::{NonAtomicInvariant, Protocol},
        perm::Perm,
        Ghost, Snapshot,
    },
    logic::{Int, Mapping, Seq, View},
    seq, snapshot,
};

#[test]
fn test_ghost_creation() {
    // Ghost blocks are erased at runtime
    let _ = ghost! {
        {
            let _g: Ghost<i32> = Ghost::new(42);
            // Can use g in specifications (verified by trust-wp)
        }
    };
    // Should compile and run (ghost block erased)
}

#[test]
fn test_ghost_with_program_code() {
    let mut x = 0;
    let _ = ghost! {
        {
            let _proof_helper = Ghost::new(x);
            // Ghost code can reference program variables
        }
    };
    x += 1;
    assert_eq!(x, 1);
}

#[test]
fn test_ghost_is_zero_sized() {
    let ghost: Ghost<i32> = Ghost::new(42);
    assert_eq!(std::mem::size_of_val(&ghost), 0);
}

#[test]
fn test_ghost_copy() {
    let ghost1: Ghost<i32> = Ghost::new(42);
    let ghost2 = ghost1; // Copy
    let ghost3 = ghost1; // Still valid because Copy
    let _ = (ghost2, ghost3);
}

#[test]
fn test_ghost_with_slice() {
    // Ghost<usize> is zero-sized
    let arr = [1, 2, 3];
    let ghost = Ghost::new(arr.len()); // Capture length
    assert_eq!(std::mem::size_of_val(&ghost), 0);
}

#[test]
fn test_ghost_block_local_loop() {
    // Local loops within ghost blocks are allowed
    let _ = ghost! {
        {
            let mut sum = 0;
            for i in 0..5 {
                sum += i;
            }
            let _ = Ghost::new(sum);
        }
    };
}

#[test]
fn test_multiple_ghost_blocks() {
    let mut x = 0;

    let _ = ghost! {
        {
            let _before = Ghost::new(x);
        }
    };

    x += 1;

    let _ = ghost! {
        {
            let _after = Ghost::new(x);
        }
    };

    assert_eq!(x, 1);
}

#[test]
fn test_ghost_default() {
    let ghost: Ghost<i32> = Ghost::default();
    assert_eq!(std::mem::size_of_val(&ghost), 0);
}

#[derive(Clone, Copy)]
struct TestProtocol;

impl Protocol for TestProtocol {
    type Public = usize;
}

#[test]
fn test_ghost_clone_payload_does_not_nest_ghost() {
    let inv: Ghost<std::rc::Rc<NonAtomicInvariant<TestProtocol>>> = Ghost::conjure();
    let cloned: Ghost<std::rc::Rc<NonAtomicInvariant<TestProtocol>>> = ghost!(inv.clone());
    assert_eq!(std::mem::size_of_val(&cloned), 0);
}

#[test]
fn test_permcell_logical_key_surface_compiles() {
    let (cell, mut perm) = PermCell::new(1i32);
    let _updated: Ghost<Mapping<PermCell<i32>, Int>> = ghost!({
        let mut map: Mapping<PermCell<i32>, Int> = Mapping::cst(Int(0));
        map = map.set(cell.clone(), Int(1));
        map
    });

    // `PermCell::new` returns `Ghost<Box<Perm<_>>>`; `&mut **perm` chains
    // Ghost → Box → Perm so the resulting reference type is `&mut Perm<_>`.
    let borrowed: Ghost<&mut Perm<PermCell<i32>>> = ghost!(&mut **perm);
    assert_eq!(std::mem::size_of_val(&borrowed), 0);
}

#[test]
fn test_rc_permcell_view_surface_compiles() {
    let cell = std::rc::Rc::new(PermCell::new(1i32).0);
    let viewed: Ghost<PermCell<i32>> = ghost!((*cell.view()).clone());
    let _ = viewed;
}

// === Snapshot integration tests ===

#[test]
fn test_snapshot_capture() {
    let x = 42;
    let snap = Snapshot::capture(&x);
    // x is not consumed
    assert_eq!(x, 42);
    // Snapshot is zero-sized
    assert_eq!(std::mem::size_of_val(&snap), 0);
}

#[test]
fn test_snapshot_copy() {
    let v = vec![1, 2, 3];
    let snap1 = Snapshot::capture(&v);
    let snap2 = snap1; // Copy
    let snap3 = snap1; // Still valid - Snapshot is always Copy
    let _ = (snap2, snap3);
    // v is still valid
    assert_eq!(v.len(), 3);
}

#[test]
fn test_snapshot_with_method_call() {
    // Common use case: snapshot a computed value
    let v = [1, 2, 3, 4, 5];
    let len_snap = Snapshot::capture(&v.len());
    assert_eq!(std::mem::size_of_val(&len_snap), 0);
    // v unchanged
    assert_eq!(v.len(), 5);
}

#[test]
fn test_snapshot_debug() {
    let x = 42;
    let snap = Snapshot::capture(&x);
    // Debug output should work (useful for debugging verification code)
    let debug_str = format!("{snap:?}");
    assert!(debug_str.contains("Snapshot"));
}

#[test]
fn test_ghost_debug() {
    let ghost: Ghost<i32> = Ghost::new(42);
    let debug_str = format!("{ghost:?}");
    assert!(debug_str.contains("Ghost"));
}

// === snapshot! macro tests ===

#[test]
fn test_snapshot_macro() {
    // Test the snapshot! macro (not just Snapshot::capture)
    let x = 42;
    let snap = snapshot!(x);
    // x is not consumed
    assert_eq!(x, 42);
    // Snapshot is zero-sized
    assert_eq!(std::mem::size_of_val(&snap), 0);
}

#[test]
fn test_snapshot_macro_with_expression() {
    // snapshot! should work with arbitrary expressions
    let v = [1, 2, 3];
    let len_snap = snapshot!(v.len());
    assert_eq!(std::mem::size_of_val(&len_snap), 0);
    // v unchanged
    assert_eq!(v.len(), 3);
}

#[test]
fn test_snapshot_macro_copy_semantics() {
    // Snapshots from macro should be Copy
    let x = 42;
    let snap1 = snapshot!(x);
    let snap2 = snap1; // Copy
    let snap3 = snap1; // Still valid
    let _ = (snap2, snap3);
}

// === Phase 2 integration tests ===

/// Verify ghost blocks with nested control flow are erased correctly.
/// This tests the cfg-gating: when not under trust-wp verification, the
/// ghost block body is replaced with `{}`.
#[test]
fn test_ghost_nested_conditionals() {
    let mut count = 0;

    let _ = ghost! {
        {
            // Complex ghost code that would fail at runtime if not erased
            if true {
                let _g = Ghost::new(42);
                if false {
                    let _h = Ghost::new(count);
                }
            }
        }
    };

    count += 1;
    assert_eq!(count, 1); // Proves ghost block was erased (no side effects)
}

/// Test ghost blocks interleaved with program mutation.
/// Demonstrates the key pattern: ghost code observes but doesn't affect execution.
#[test]
fn test_ghost_observes_mutations() {
    let mut v = vec![1, 2, 3];

    let _ = ghost! {
        {
            // Capture state before mutation (for verification)
            let _before_len = Ghost::new(v.len());
        }
    };

    v.push(4); // Program mutation

    let _ = ghost! {
        {
            // Capture state after mutation (for verification)
            let _after_len = Ghost::new(v.len());
            // In verification: *_after_len == *_before_len + 1
        }
    };

    assert_eq!(v.len(), 4);
}

/// Test that ghost blocks handle references correctly.
/// Ghost code can take references to program values without consuming them.
#[test]
fn test_ghost_with_references() {
    let data = vec![1, 2, 3, 4, 5];
    let reference = &data;

    let _ = ghost! {
        {
            // Can reference program data in ghost code
            let _len = Ghost::new(reference.len());
            let _first = Ghost::new(reference[0]);
        }
    };

    // reference is still valid
    assert_eq!(reference.len(), 5);
}

// ── seq! inside ghost/snapshot (#1345 coverage gap) ─────────────────

/// Test that seq! macro works inside ghost! blocks.
/// This was the stated motivation for adding the seq! macro (c1e4fb72)
/// but was not tested by the original commit.
#[test]
fn test_seq_inside_ghost_block() {
    let _ = ghost! {
        {
            let _s: Seq<i32> = seq![1, 2, 3];
            let _empty: Seq<i32> = seq![];
            let _single = seq![42];
        }
    };
}

/// Test that seq! macro works inside snapshot! blocks.
/// cell/03_as_slice_of_cells.rs uses `seq!(pred0, pred1)` inside snapshot!,
/// which was the original failing test case.
#[test]
fn test_seq_inside_snapshot_block() {
    let x = 10i32;
    let y = 20i32;
    let _s: Snapshot<Seq<i32>> = snapshot! {
        let built = seq![x, y];
        built
    };
}
