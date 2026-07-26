// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp::{ensures, proof_assert};

#[ensures(result == (x.1, x.0))]
fn swap_refs<'a, T>(x: (&'a mut T, &'a mut T)) -> (&'a mut T, &'a mut T) {
    (x.1, x.0)
}

fn projected_deref_write_verify() {
    let (mut a, mut b) = (0u32, 0u32);
    let p = swap_refs((&mut a, &mut b));

    *p.0 = 10u32;

    proof_assert!(b == 10u32);
    proof_assert!(a == 0u32);
}

fn main() {
    projected_deref_write_verify();
}
