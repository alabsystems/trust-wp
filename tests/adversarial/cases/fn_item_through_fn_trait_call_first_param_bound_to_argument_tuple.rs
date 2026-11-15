//@ expect: reject
//@ also-verified: g, h
//@ mechanism: a fn item of two or more parameters called through `Fn::call`, `FnMut::call_mut` or
//@ mechanism: `FnOnce::call_once` gets its parameters as ONE tuple after the receiver (the `rust-call`
//@ mechanism: ABI). The lane that states the item's own spec at such a call
//@ mechanism: (`resolve_effective_spec`, and its twin in the substitution pass) binds the item's
//@ mechanism: parameter names to the arguments after the receiver one by one, so the first parameter
//@ mechanism: is bound to the whole tuple and the others to nothing. `g`'s `x.1` is read at the call
//@ mechanism: as field 1 of `((1, 2), 3)`, which is 3, not as `x.1`, which is 2; `h`'s `requires`
//@ mechanism: `x.1 == 3` is discharged the same way. D-180 untuples this call for a closure with its
//@ mechanism: own contract; the fn-item lane beside it was not changed. Found probing sideways from
//@ mechanism: D-180.
//@ accept-means: a caller was credited with a postcondition, or discharged a precondition, read at
//@ accept-means: the whole argument tuple instead of at the parameter the clause names.
//@ WHY THE CONTRACT IS FALSE: `g((1, 2), 3)` returns `x.1`, which is 2, and each `via_*` host claims
//@ WHY THE CONTRACT IS FALSE: 3; `h((1, 2), 3)` violates `x.1 == 3` and returns `2 - 2`, which is 0,
//@ WHY THE CONTRACT IS FALSE: and `requires_discharged` claims 1.
//@ fixed-by: OPEN: committed RED. The fn-item lane must bind parameter `i` to field `i` of the
//@ fixed-by: argument tuple, as `untupled_closure_call_args` does for a closure, or bind none.
//@ teeth: LIVE at the head D-181 was reviewed at: ACCEPTED, exit 0, every function `verified` (`via_call`,
//@ teeth: `via_call_mut`, `via_call_once`, `requires_discharged`), and the `call`, `call_mut` and `call_once` spellings alone the same.
//@ teeth: The TRUE twin (fn_item_through_fn_trait_call_first_param_bound_to_argument_tuple_control.rs,
//@ teeth: which claims 2) is FAILED, so the clause IS read at the tuple. The same at the campaign tip
//@ teeth: the branch that carries D-180 merged (ACCEPTED, exit 0; the twin FAILED).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(fn_traits, unboxed_closures)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == x.1)]
pub fn g(x: (u32, u32), y: u32) -> u32 {
    let _ = y;
    x.1
}

#[requires(x.1 == 3u32)]
#[ensures(result == 1u32)]
pub fn h(x: (u32, u32), y: u32) -> u32 {
    let _ = y;
    x.1 - 2u32
}

#[ensures(result == 3u32)]
pub fn via_call() -> u32 {
    Fn::call(&g, ((1u32, 2u32), 3u32))
}

#[ensures(result == 3u32)]
pub fn via_call_mut() -> u32 {
    let mut f = g;
    FnMut::call_mut(&mut f, ((1u32, 2u32), 3u32))
}

#[ensures(result == 3u32)]
pub fn via_call_once() -> u32 {
    FnOnce::call_once(g, ((1u32, 2u32), 3u32))
}

#[ensures(result == 1u32)]
pub fn requires_discharged() -> u32 {
    Fn::call(&h, ((1u32, 2u32), 3u32))
}
