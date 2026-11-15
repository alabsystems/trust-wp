//@ expect: reject
//@ mechanism: a writing guard dropped IN PLACE behind a standard cell's accessor: `*cell.get_mut() = None`
//@ mechanism: and `*cell.try_borrow_mut()? = None` (the `RefMut` spelling) on a `RefCell<Option<G>>`, and
//@ mechanism: `*m.get_mut()? = None` on a `Mutex<Option<G>>`. The assignment drops the old `G` through the
//@ mechanism: accessor's `&mut`, and `G::drop` sets `c` to 5; the cell itself is forgotten. D-140 reads
//@ mechanism: the accessor call as a hand-off (it is handed mutable access to a value whose glue may
//@ mechanism: write) and the assignment's `Drop` of the place as another. Found probing D-140's standard
//@ mechanism: types sideways; this pins that the cells stay rejected when their accessors are modelled.
//@ accept-means: a host is reported `verified` although the in-place drop behind the cell set `c` to 5.
//@ WHY THE CONTRACT IS FALSE: every host returns 5; compiled and run as a plain program each prints 5.
//@ fixed-by: n/a: rejected before and after D-140.
//@ teeth: UNVERIFIED as a gate of D-140: with its hand-off disabled the `RefCell` hosts are refused on
//@ teeth: the unmodelled logic method `borrow` and the `Mutex` hosts on `inv`; with it the `RefCell` hosts
//@ teeth: are `unknown` on the hand-off's fail-closed read first. It pins the spellings, not the gate.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::cell::RefCell;
use std::sync::Mutex;

pub struct G<'a>(pub &'a mut u32);
impl Drop for G<'_> {
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

#[ensures(result@ == 0)]
pub fn refcell_get_mut() -> u32 {
    let mut c = 0u32;
    {
        let mut cell = RefCell::new(Some(G(&mut c)));
        *cell.get_mut() = None;
        std::mem::forget(cell);
    }
    c
}

#[ensures(result@ == 0)]
pub fn refcell_try_borrow_mut() -> u32 {
    let mut c = 0u32;
    {
        let cell = RefCell::new(Some(G(&mut c)));
        if let Ok(mut r) = cell.try_borrow_mut() {
            *r = None;
        }
        std::mem::forget(cell);
    }
    c
}

#[ensures(result@ == 0)]
pub fn mutex_get_mut() -> u32 {
    let mut c = 0u32;
    {
        let mut m = Mutex::new(Some(G(&mut c)));
        if let Ok(g) = m.get_mut() {
            *g = None;
        }
        std::mem::forget(m);
    }
    c
}
