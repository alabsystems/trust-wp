//@ expect: reject
//@ mechanism: a STANDARD-LIBRARY destructor that calls a method of its type argument: `BufWriter<W>`
//@ mechanism: flushes its buffer through `W::write` when dropped, and `Splice<I>` drains the rest of
//@ mechanism: `I` through `I::next`. Both user methods write through the `&mut` their value holds. The
//@ mechanism: drop-glue scan walked a standard type only through the values it OWNS (its type
//@ mechanism: arguments' own glue), and neither `W` nor `I` has any, so neither drop was a hand-off.
//@ accept-means: a `proof_assert!` is credited although the standard destructor ran a user method that
//@ accept-means: set the asserted local to 5.
//@ WHY THE CONTRACT IS FALSE: at each assertion `c` is 5: the `BufWriter` was dropped with one
//@ WHY THE CONTRACT IS FALSE: buffered byte and wrote it through `W::write`; the `Splice` was dropped
//@ WHY THE CONTRACT IS FALSE: and pulled from `It::next`.
//@ fixed-by: D-140: a type parameter of a standard `Drop` impl that is not `#[may_dangle]`
//@ fixed-by: (`tcx.destructor_constraints`), instantiated with a type that holds write access or
//@ fixed-by: reaches interior mutability, makes the glue one that may write
//@ fixed-by: (`drop_glue_writes::std_dtor_may_call_user_code`).
//@ teeth: MEASURED: with D-140's hand-off disabled, and with the hand-off but standard types walked
//@ teeth: only through their type arguments, both assertions are `verified`; with D-140 both FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::io::Write;

pub struct W<'a>(pub &'a mut u32);

impl Write for W<'_> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        *self.0 = 5;
        Ok(buf.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub fn buf_writer() {
    let mut c = 0u32;
    {
        let mut b = std::io::BufWriter::new(W(&mut c));
        let _ = b.write(b"x");
    }
    proof_assert!(c@ == 0);
}

pub struct It<'a>(pub &'a mut u32);

impl Iterator for It<'_> {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        *self.0 = 5;
        None
    }
}

pub fn splice() {
    let mut c = 0u32;
    let mut v: Vec<u32> = Vec::new();
    {
        let _s = v.splice(0..0, It(&mut c));
    }
    proof_assert!(c@ == 0);
}
