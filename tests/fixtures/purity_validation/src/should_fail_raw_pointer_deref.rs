// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(dead_code, unexpected_cfgs)]

pub unsafe fn read_raw(ptr: *const i32) -> i32 {
    *ptr
}

fn main() {}
