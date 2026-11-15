//@ expect: verify
//@ mechanism: control for sp12/sp16: #[derive(PartialEq, DeepModel)] eq is logical equality over u32 fields, must still verify a == a
use creusot_std::prelude::*;
#[derive(Clone, Copy, PartialEq, DeepModel)]
pub struct S(pub u32);
#[ensures(result)]
pub fn f() -> bool { let a = S(1); a == a }
