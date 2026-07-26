// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Completeness pin for the nested-reborrow transfer encoding: the reference
//! rusthorn `inc_max_3` program must keep verifying after the collapsed
//! body-fact strip (its proof rests solely on the exact expiry resolutions).

#![allow(unexpected_cfgs)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[ensures(^mma == *mmb && ^mmb == *mma)]
fn swap<'a, 'b>(mma: &'a mut &'b mut u32, mmb: &'a mut &'b mut u32) {
    std::mem::swap(mma, mmb);
}

#[requires(*ma <= 1_000_000u32 && *mb <= 1_000_000u32 && *mc <= 1_000_000u32)]
#[ensures(^ma != ^mb && ^mb != ^mc && ^mc != ^ma)]
fn inc_max_3<'a>(mut ma: &'a mut u32, mut mb: &'a mut u32, mut mc: &'a mut u32) {
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    if *mb < *mc {
        swap(&mut mb, &mut mc);
    }
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    *ma += 2;
    *mb += 1;
}

fn main() {
    let (mut a, mut b, mut c) = (3u32, 2u32, 1u32);
    inc_max_3(&mut a, &mut b, &mut c);
}
