// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A generated soundness oracle over the driver lane, and a census that the
//! generated corpus covers every kind of node the contract parser writes.
//!
//! Each case is a function of one fixed signature (a `&mut i32`, integers, a
//! `bool`, an `Option<i32>`, a struct, a shared reference and a `Vec`) with a
//! body from a small set the evaluator below runs, and a generated
//! postcondition. The evaluator shares no code with trust-wp: it reads each
//! postcondition as contract-syntax.md says (a clause that names a `&mut`
//! parameter inside `old(..)` reads `*p` and `p@` outside `old` as the value
//! `p` is left with, unless it writes `^p` outside `old`; otherwise `*p` is
//! the entry value and `^p` the final one) at every point of a grid inside
//! the precondition. Two properties hold for every case:
//!
//! 1. a postcondition some grid point falsifies is never verified;
//! 2. every kind of node the parser writes ([`NodeKind::all`], each list
//!    written from the AST enums' own variants, so a new variant is a new
//!    kind) is written by at least [`COVERAGE`] verified true cases and by at
//!    least [`COVERAGE`] false or refused ones, counted over the census the
//!    parser takes of each clause as written ([`parse_contract_census`]).
//!
//! A kind no driver clause can spell (`box p`, which rustc refuses outside
//! nightly) is counted over bundle claims the native verifier decides, each
//! true or false by construction (`bundle_claims`).

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    path::{Path, PathBuf},
};

use ntest::timeout;
use trust_wp_core::{
    contract_parser::parse_contract_census,
    formula::{elaborate::NodeKind, BinOp, UnOp},
    verify_bundle::{
        BundleClaim, BundleClaimFormat, BundleDigest, BundleObligation, BundleObligationKind,
        BundleProducer, BundleSummaryFact, BundleSummaryFactKind, BundleTarget,
        NativeTrustWpBundleVerifier, VerifyBundleEngine, VerifyBundleRequest, VerifyBundleStatus,
    },
};
use trust_wp_test_utils::{nested_cargo, trust_wp_rustc_fixture_target_dir, trust_wp_rustc_path};

/// How many verified true cases, and how many false or refused ones, must
/// write each kind.
const COVERAGE: usize = 3;

// ---- The program each case verifies -----------------------------------------

/// A point of the grid the evaluator reads every case at.
#[derive(Debug, Clone)]
struct Point {
    x: i128,
    y: i128,
    b: bool,
    /// `*p` at entry.
    p0: i128,
    o: Option<i128>,
    sa: i128,
    sb: i128,
    /// `*r`.
    r: i128,
    v: Vec<i128>,
}

fn grid() -> Vec<Point> {
    let mut points = Vec::new();
    for x in [-7, 0, 3] {
        for y in [-2, 5] {
            for b in [false, true] {
                for p0 in [-5, 0, 9] {
                    for o in [None, Some(-3), Some(4)] {
                        for (sa, sb) in [(1, -2), (0, 5)] {
                            for r in [-1, 6] {
                                for v in [vec![], vec![3], vec![1, 2]] {
                                    points.push(Point {
                                        x,
                                        y,
                                        b,
                                        p0,
                                        o,
                                        sa,
                                        sb,
                                        r,
                                        v,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    points
}

/// The body a case's function runs, which the evaluator runs too.
#[derive(Debug, Clone, Copy)]
enum Body {
    IncP,
    SetPToX,
    IncPIfB,
    DoubleP,
    AddSomeToP,
    /// `p` left with `x + 1` through two shadowing `let`s of the parameter's
    /// name: the clause's `x` is the parameter, never a body binding (D-237).
    ShadowIncP,
    /// The parameter `x` copied, then shadowed in an inner block (which
    /// stores `y`) and again after it: the result is the parameter.
    ShadowParam,
}

impl Body {
    fn rust(self) -> &'static str {
        match self {
            Self::IncP => "*p += 1; x + y",
            Self::SetPToX => "*p = x; y",
            Self::IncPIfB => "if b { *p += 1; } x",
            Self::DoubleP => "*p = *p + *p; *r",
            Self::AddSomeToP => "let w = match o { Some(w) => w, None => 0 }; *p += w; w",
            Self::ShadowIncP => "let x = *p; let x = x + 1; *p = x; y",
            Self::ShadowParam => "let w = x; { let x = y; *p = x; } let x = 0i32; w + x",
        }
    }

    /// `*p` when the function returns, and its result.
    fn run(self, point: &Point) -> (i128, i128) {
        match self {
            Self::IncP => (point.p0 + 1, point.x + point.y),
            Self::SetPToX => (point.x, point.y),
            Self::IncPIfB => (point.p0 + i128::from(point.b), point.x),
            Self::DoubleP => (point.p0 * 2, point.r),
            Self::AddSomeToP => {
                let w = point.o.unwrap_or(0);
                (point.p0 + w, w)
            }
            Self::ShadowIncP => (point.p0 + 1, point.y),
            Self::ShadowParam => (point.y, point.x),
        }
    }
}

const PRECONDITION: &str = "*p < 100 && *p > -100 && x < 100 && x > -100 && y < 100 && \
     y > -100 && *r < 100 && *r > -100 && s.a < 100 && s.a > -100 && \
     match o { Some(w) => w < 100 && w > -100, None => true }";

const PRELUDE: &str = "#![feature(stmt_expr_attributes, proc_macro_hygiene)]
#![allow(unused)]
use std::cell::{Cell, RefCell};
use trust_wp::prelude::*;
use trust_wp::resolve::{structural_resolve, Resolve};

pub struct S {
    pub a: i32,
    pub b: i32,
}

pub struct HC {
    pub c: Cell<i32>,
}

pub struct HB {
    pub c: Box<Cell<i32>>,
}

pub struct HR {
    pub c: RefCell<i32>,
}

pub struct SC<'a> {
    pub c: &'a Cell<i32>,
}

pub struct SR<'a> {
    pub c: &'a RefCell<i32>,
}

pub struct HM<'a> {
    pub m: &'a mut i32,
    pub v: i32,
}

pub struct H1<'a> {
    pub m: &'a mut i32,
}

pub struct N1<'a>(pub &'a mut i32);

#[logic(open, prophetic)]
fn unchanged<T>(q: &mut T) -> bool {
    pearlite! { ^q == *q }
}

#[logic(open, prophetic)]
fn settled<T>(q: &mut T) -> bool {
    pearlite! { resolve(q) }
}

#[logic(open)]
fn add1(v: Int) -> Int {
    v + 1
}

pub trait Tag {
    const TAG: i32;
}

impl Tag for u8 {
    const TAG: i32 = 1;
}

impl Tag for u16 {
    const TAG: i32 = 2;
}

#[logic(open)]
fn tag<T: Tag>() -> i32 {
    T::TAG
}

#[logic(open)]
fn addn<const N: i32>(v: i32) -> i32 {
    v + N
}
";

// ---- Terms ------------------------------------------------------------------

/// An integer-valued term, spelled at `Int` (`x@`, `(*p)@`, a literal).
#[derive(Debug, Clone)]
enum I {
    Lit(i64),
    X,
    Y,
    R,
    SA,
    Result,
    /// `(*p)@`
    DerefP,
    /// `p@`
    ViewP,
    /// `(^p)@`
    FinalP,
    /// `(*q)@` of a name bound to `p`.
    DerefAlias(String),
    Old(Box<I>),
    Add(Box<I>, Box<I>),
    Sub(Box<I>, Box<I>),
    MulK(Box<I>, i64),
    Neg(Box<I>),
    DivK(Box<I>, i64),
    RemK(Box<I>, i64),
    Ite(Box<Bo>, Box<I>, Box<I>),
    /// A name bound to an `i32` (`w@`) or to an `Int` (`i`).
    Name(String, bool),
    /// `(*a)@` of a name bound to a borrow of an `i32` name.
    DerefName(String),
    MatchO(String, Box<I>, Box<I>),
    Add1(Box<I>),
    /// `v@.len()`
    Len,
    /// `v@.push_back(x).len()`
    PushLen,
    /// `(k as u8)@`
    CastU8(i64),
    /// `(k as i64)@`
    CastI64(i64),
    /// `(*(if b { p } else { p }))@`
    DerefBranch,
}

/// A boolean-valued term.
#[derive(Debug, Clone)]
enum Bo {
    Lit(bool),
    B,
    Cmp(BinOp, I, I),
    Not(Box<Bo>),
    And(Box<Bo>, Box<Bo>),
    Or(Box<Bo>, Box<Bo>),
    Implies(Box<Bo>, Box<Bo>),
    Ite(Box<Bo>, Box<Bo>, Box<Bo>),
    Let(String, I, Box<Bo>),
    MutLet(String, I, Box<Bo>),
    MatchO(String, Box<Bo>, Box<Bo>),
    IfLetSome(String, Box<Bo>, Box<Bo>),
    MatchB(Box<Bo>, Box<Bo>),
    /// `match (x, b) { (w, true) => .., (_, false) => .. }`
    MatchTuple(String, Box<Bo>, Box<Bo>),
    /// `match o { Some(..) => .., None => .. }`
    MatchRest(Box<Bo>, Box<Bo>),
    /// `match s { S { a: u, .. } => .. }` or with every field.
    MatchStruct(String, Option<String>, Box<Bo>),
    /// A `let` of a pattern form, see [`LetForm`].
    LetForm(LetForm, Box<Bo>),
    /// `match p { q => .. }` over the `&mut` parameter.
    MatchP(String, Box<Bo>),
    /// `match x { a @ c => .. }`
    MatchAlias(Box<Bo>),
    Forall(String, I, Box<Bo>),
    Exists(String, I, Box<Bo>),
    /// `o.is_none() == (o == None)`, or `!=` for the false twin.
    IsNone(bool),
    IsSome,
    /// `(A op B) == C` over `i32`, or `u32` for a shift.
    Bits(BinOp, i64, i64, i64),
    FloatEq(f64, f64),
    /// `tag::<A>() == tag::<B>()` for type arguments `u8`/`u16`: equal
    /// exactly when the types are.
    TagEq(&'static str, &'static str),
    /// `addn::<{ A }>(x) == addn::<{ B }>(x)` for const blocks `A`, `B`.
    AddnEq(&'static str, &'static str),
    /// `READ == old(*p) + d` over `i32`, `READ` one of the spellings of the
    /// `&mut` parameter's referent in [`RAW_READS`] (the measured ones).
    RawState(usize, i64),
    /// `o == None` (`true`) or `o != None`.
    ONone(bool),
    /// `match b { true | false => .. }`
    MatchOrB(Box<Bo>),
    /// `match (x, b) { (w, true) | (w, false) => .. }`: `w` is `x`.
    MatchOrTuple(String, Box<Bo>),
    /// `match o { Some(_) | None => .. }`
    MatchOrO(Box<Bo>),
}

/// Reads of `*p` through a binder, a branch or a tuple field, each spelled
/// as a measured case spelled it, with `{}` where `*p == old(*p) + d`'s
/// comparison goes.
const RAW_READS: [&str; 13] = [
    "match p { q => *q {} }",
    "match p { p => *p {} }",
    "{ let q = p; *q {} }",
    "(if let q = p { *q {} } else { true })",
    "match (p, 0) { (q, _) => *q {} }",
    "*(if true { p } else { p }) {}",
    "*(if old(*p) > 1000 { p } else { p }) {}",
    "*(match 0 { _ => p }) {}",
    "*(match b { true => p, false => p }) {}",
    "*(p, 0).0 {}",
    "match p { q => q@ == old(q@) + {} }",
    // Reads the state rule cannot place: refused.
    "{ let t = (p, 0); *t.0 {} }",
    "match Some(p) { Some(q) => *q {}, None => true }",
];

/// The pattern forms a `let` writes, each binding names the body reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LetForm {
    /// `let (a, (c, d)) = (x, (y, x));`
    NestedTuple,
    /// `let a @ c = x;`
    Alias,
    /// `let ref a = x;` (`a` read as `(*a)@`)
    Ref,
    /// `let ref mut a = p;` (`a` read as `(**a)@`)
    RefMut,
    /// `let ref a @ c = x;`
    RefAlias,
    /// `let &a = r;`
    Reference,
    /// `let &mut a = p;`
    MutReference,
    /// `let (a) = x;`
    Parenthesized,
    /// `let (a,) = (x,);`
    OneTuple,
    /// `let _ = x;` then the body.
    Wildcard,
}

/// The values a case's names are bound to.
#[derive(Debug, Clone, Default)]
struct Env {
    ints: BTreeMap<String, i128>,
}

/// How the clause reads `*p`: see the module documentation.
#[derive(Debug, Clone, Copy)]
struct Reading {
    old_dialect: bool,
    explicit_final: bool,
}

struct At<'a> {
    point: &'a Point,
    p1: i128,
    result: i128,
    reading: Reading,
    in_old: bool,
}

impl At<'_> {
    fn deref_p(&self) -> i128 {
        if !self.in_old && self.reading.old_dialect && !self.reading.explicit_final {
            self.p1
        } else {
            self.point.p0
        }
    }

    fn old(&self) -> Self {
        At {
            point: self.point,
            p1: self.p1,
            result: self.result,
            reading: self.reading,
            in_old: true,
        }
    }
}

fn trunc_div(a: i128, b: i128) -> i128 {
    a / b
}

fn trunc_rem(a: i128, b: i128) -> i128 {
    a % b
}

impl I {
    fn render(&self) -> String {
        match self {
            Self::Lit(k) => {
                if *k < 0 {
                    format!("({k})")
                } else {
                    k.to_string()
                }
            }
            Self::X => "x@".into(),
            Self::Y => "y@".into(),
            Self::R => "(*r)@".into(),
            Self::SA => "s.a@".into(),
            Self::Result => "result@".into(),
            Self::DerefP => "(*p)@".into(),
            Self::ViewP => "p@".into(),
            Self::FinalP => "(^p)@".into(),
            Self::DerefAlias(q) => format!("(*{q})@"),
            Self::Old(inner) => format!("old({})", inner.render()),
            Self::Add(a, b) => format!("({} + {})", a.render(), b.render()),
            Self::Sub(a, b) => format!("({} - {})", a.render(), b.render()),
            Self::MulK(a, k) => format!("({} * {})", a.render(), I::Lit(*k).render()),
            Self::Neg(a) => format!("(-{})", a.render()),
            Self::DivK(a, k) => format!("({} / {})", a.render(), I::Lit(*k).render()),
            Self::RemK(a, k) => format!("({} % {})", a.render(), I::Lit(*k).render()),
            Self::Ite(c, t, e) => format!(
                "(if {} {{ {} }} else {{ {} }})",
                c.render(),
                t.render(),
                e.render()
            ),
            Self::Name(name, machine) => {
                if *machine {
                    format!("{name}@")
                } else {
                    name.clone()
                }
            }
            Self::DerefName(name) => format!("(*{name})@"),
            Self::MatchO(w, some, none) => format!(
                "(match o {{ Some({w}) => {}, None => {} }})",
                some.render(),
                none.render()
            ),
            Self::Add1(a) => format!("add1({})", a.render()),
            Self::Len => "v@.len()".into(),
            Self::PushLen => "v@.push_back(x).len()".into(),
            Self::CastU8(k) => format!("({k}i32 as u8)@"),
            Self::CastI64(k) => format!("({k}i32 as i64)@"),
            Self::DerefBranch => "(*(if b { p } else { p }))@".into(),
        }
    }

    fn eval(&self, env: &Env, at: &At<'_>) -> i128 {
        let point = at.point;
        match self {
            Self::Lit(k) => i128::from(*k),
            Self::X => point.x,
            Self::Y => point.y,
            Self::R => point.r,
            Self::SA => point.sa,
            Self::Result => at.result,
            Self::DerefP | Self::ViewP | Self::DerefAlias(_) | Self::DerefBranch => at.deref_p(),
            Self::FinalP => at.p1,
            Self::Old(inner) => inner.eval(env, &at.old()),
            Self::Add(a, b) => a.eval(env, at) + b.eval(env, at),
            Self::Sub(a, b) => a.eval(env, at) - b.eval(env, at),
            Self::MulK(a, k) => a.eval(env, at) * i128::from(*k),
            Self::Neg(a) => -a.eval(env, at),
            Self::DivK(a, k) => trunc_div(a.eval(env, at), i128::from(*k)),
            Self::RemK(a, k) => trunc_rem(a.eval(env, at), i128::from(*k)),
            Self::Ite(c, t, e) => {
                if c.eval(env, at) {
                    t.eval(env, at)
                } else {
                    e.eval(env, at)
                }
            }
            Self::Name(name, _) | Self::DerefName(name) => env.ints[name],
            Self::MatchO(w, some, none) => match point.o {
                Some(value) => {
                    let mut inner = env.clone();
                    inner.ints.insert(w.clone(), value);
                    some.eval(&inner, at)
                }
                None => none.eval(env, at),
            },
            Self::Add1(a) => a.eval(env, at) + 1,
            Self::Len => point.v.len() as i128,
            Self::PushLen => point.v.len() as i128 + 1,
            Self::CastU8(k) => i128::from(*k as u8),
            Self::CastI64(k) => i128::from(*k),
        }
    }

    /// Whether the term reads `p`'s referent (for the dialect).
    fn reads_p(&self) -> bool {
        match self {
            Self::DerefP | Self::ViewP | Self::FinalP | Self::DerefAlias(_) | Self::DerefBranch => {
                true
            }
            Self::Old(a)
            | Self::MulK(a, _)
            | Self::Neg(a)
            | Self::DivK(a, _)
            | Self::RemK(a, _) => a.reads_p(),
            Self::Add1(a) => a.reads_p(),
            Self::Add(a, b) | Self::Sub(a, b) | Self::MatchO(_, a, b) => a.reads_p() || b.reads_p(),
            Self::Ite(c, t, e) => c.reads_p() || t.reads_p() || e.reads_p(),
            _ => false,
        }
    }

    fn scan(&self, in_old: bool, reading: &mut Reading) {
        match self {
            Self::Old(inner) => {
                if inner.reads_p() {
                    reading.old_dialect = true;
                }
                inner.scan(true, reading);
            }
            Self::FinalP if !in_old => reading.explicit_final = true,
            Self::MulK(a, _)
            | Self::Neg(a)
            | Self::DivK(a, _)
            | Self::RemK(a, _)
            | Self::Add1(a) => {
                a.scan(in_old, reading);
            }
            Self::Add(a, b) | Self::Sub(a, b) | Self::MatchO(_, a, b) => {
                a.scan(in_old, reading);
                b.scan(in_old, reading);
            }
            Self::Ite(c, t, e) => {
                c.scan(in_old, reading);
                t.scan(in_old, reading);
                e.scan(in_old, reading);
            }
            _ => {}
        }
    }
}

/// The value of a const block the generator writes: `k` or `a * b`.
fn const_block(text: &str) -> i64 {
    text.split('*')
        .map(|factor| factor.trim().parse::<i64>().expect("a literal factor"))
        .product()
}

fn cmp_spelling(op: BinOp) -> &'static str {
    match op {
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        other => panic!("no spelling for {other:?}"),
    }
}

fn cmp_holds(op: BinOp, a: i128, b: i128) -> bool {
    match op {
        BinOp::Eq => a == b,
        BinOp::Ne => a != b,
        BinOp::Lt => a < b,
        BinOp::Le => a <= b,
        BinOp::Gt => a > b,
        BinOp::Ge => a >= b,
        other => panic!("not a comparison: {other:?}"),
    }
}

impl LetForm {
    const ALL: [Self; 10] = [
        Self::NestedTuple,
        Self::Alias,
        Self::Ref,
        Self::RefMut,
        Self::RefAlias,
        Self::Reference,
        Self::MutReference,
        Self::Parenthesized,
        Self::OneTuple,
        Self::Wildcard,
    ];

    /// The `let` statement.
    fn statement(self) -> &'static str {
        match self {
            Self::NestedTuple => "let (a, (c, d)) = (x, (y, x));",
            Self::Alias => "let a @ c = x;",
            Self::Ref => "let ref a = x;",
            Self::RefMut => "let ref mut a = p;",
            Self::RefAlias => "let ref a @ c = x;",
            Self::Reference => "let &a = r;",
            Self::MutReference => "let &mut a = p;",
            Self::Parenthesized => "let (a) = x;",
            Self::OneTuple => "let (a,) = (x,);",
            Self::Wildcard => "let _ = x;",
        }
    }

    /// The term the body reads `a` through, and its value.
    fn a(self) -> I {
        match self {
            Self::NestedTuple | Self::Alias | Self::Parenthesized | Self::OneTuple => {
                I::Name("a".into(), true)
            }
            Self::Ref | Self::RefAlias => I::DerefName("a".into()),
            Self::RefMut => I::DerefAlias("*a".into()),
            Self::Reference => I::Name("a".into(), true),
            Self::MutReference => I::Name("a".into(), true),
            Self::Wildcard => I::X,
        }
    }

    /// The names the statement binds, with their values.
    fn bind(self, env: &Env, at: &At<'_>) -> Env {
        let point = at.point;
        let mut env = env.clone();
        match self {
            Self::NestedTuple => {
                env.ints.insert("a".into(), point.x);
                env.ints.insert("c".into(), point.y);
                env.ints.insert("d".into(), point.x);
            }
            Self::Alias | Self::RefAlias => {
                env.ints.insert("a".into(), point.x);
                env.ints.insert("c".into(), point.x);
            }
            Self::Ref | Self::Parenthesized | Self::OneTuple => {
                env.ints.insert("a".into(), point.x);
            }
            Self::Reference => {
                env.ints.insert("a".into(), point.r);
            }
            // `*p` at the `let`: the clause's state outside `old`.
            Self::MutReference => {
                env.ints.insert("a".into(), at.deref_p());
            }
            Self::RefMut | Self::Wildcard => {}
        }
        env
    }

    fn reads_p(self) -> bool {
        matches!(self, Self::RefMut | Self::MutReference)
    }
}

impl Bo {
    fn render(&self) -> String {
        match self {
            Self::Lit(value) => value.to_string(),
            Self::B => "b".into(),
            Self::Cmp(op, a, b) => format!("({} {} {})", a.render(), cmp_spelling(*op), b.render()),
            Self::Not(inner) => format!("!{}", inner.render_atom()),
            Self::And(a, b) => format!("({} && {})", a.render(), b.render()),
            Self::Or(a, b) => format!("({} || {})", a.render(), b.render()),
            Self::Implies(a, b) => format!("({} ==> {})", a.render(), b.render()),
            Self::Ite(c, t, e) => format!(
                "(if {} {{ {} }} else {{ {} }})",
                c.render(),
                t.render(),
                e.render()
            ),
            Self::Let(name, value, body) => {
                format!("{{ let {name} = {}; {} }}", value.render(), body.render())
            }
            Self::MutLet(name, value, body) => {
                format!(
                    "{{ let mut {name} = {}; {} }}",
                    value.render(),
                    body.render()
                )
            }
            Self::MatchO(w, some, none) => format!(
                "(match o {{ Some({w}) => {}, None => {} }})",
                some.render(),
                none.render()
            ),
            Self::IfLetSome(w, some, none) => format!(
                "(if let Some({w}) = o {{ {} }} else {{ {} }})",
                some.render(),
                none.render()
            ),
            Self::MatchB(t, f) => format!(
                "(match b {{ true => {}, false => {} }})",
                t.render(),
                f.render()
            ),
            Self::MatchTuple(w, t, f) => format!(
                "(match (x, b) {{ ({w}, true) => {}, (_, false) => {} }})",
                t.render(),
                f.render()
            ),
            Self::MatchRest(some, none) => format!(
                "(match o {{ Some(..) => {}, None => {} }})",
                some.render(),
                none.render()
            ),
            Self::MatchStruct(u, w, body) => match w {
                None => format!("(match s {{ S {{ a: {u}, .. }} => {} }})", body.render()),
                Some(w) => format!(
                    "(match s {{ S {{ a: {u}, b: {w} }} => {} }})",
                    body.render()
                ),
            },
            Self::LetForm(form, body) => format!("{{ {} {} }}", form.statement(), body.render()),
            Self::MatchP(q, body) => format!("(match p {{ {q} => {} }})", body.render()),
            Self::MatchAlias(body) => format!("(match x {{ a @ c => {} }})", body.render()),
            Self::Forall(i, value, body) => format!(
                "(forall<{i}: Int> {i} == {} ==> {})",
                value.render(),
                body.render()
            ),
            Self::Exists(i, value, body) => format!(
                "(exists<{i}: Int> {i} == {} && {})",
                value.render(),
                body.render()
            ),
            Self::IsNone(true) => "(o.is_none() == (o == None))".into(),
            Self::IsNone(false) => "(o.is_none() == (o != None))".into(),
            Self::IsSome => "(o.is_some() == (o != None))".into(),
            Self::Bits(op, a, b, c) => {
                let ty = if matches!(op, BinOp::Shl | BinOp::Shr) {
                    "u32"
                } else {
                    "i32"
                };
                format!("(({a}{ty} {} {b}{ty}) == {c}{ty})", cmp_spelling(*op))
            }
            Self::FloatEq(a, b) => format!("({a:?}f64 == {b:?}f64)"),
            Self::TagEq(a, b) => format!("(tag::<{a}>() == tag::<{b}>())"),
            Self::ONone(true) => "(o == None)".into(),
            Self::ONone(false) => "(o != None)".into(),
            Self::RawState(at, d) => {
                let shape = RAW_READS[*at];
                if shape.ends_with("+ {} }") {
                    format!("({})", shape.replace("{}", &d.to_string()))
                } else {
                    let comparison = if *d == 0 {
                        "== old(*p)".to_string()
                    } else {
                        format!("== old(*p) + {d}")
                    };
                    format!("({})", shape.replace("{}", &comparison))
                }
            }
            Self::AddnEq(a, b) => format!("(addn::<{{ {a} }}>(x) == addn::<{{ {b} }}>(x))"),
            Self::MatchOrB(body) => format!("(match b {{ true | false => {} }})", body.render()),
            Self::MatchOrTuple(w, body) => format!(
                "(match (x, b) {{ ({w}, true) | ({w}, false) => {} }})",
                body.render()
            ),
            Self::MatchOrO(body) => format!("(match o {{ Some(_) | None => {} }})", body.render()),
        }
    }

    /// Whether the term reads `p`'s referent.
    fn reads_p(&self) -> bool {
        match self {
            Self::Cmp(_, a, b) => a.reads_p() || b.reads_p(),
            Self::Let(_, value, body) | Self::MutLet(_, value, body) => {
                value.reads_p() || body.reads_p()
            }
            Self::Forall(_, value, body) | Self::Exists(_, value, body) => {
                value.reads_p() || body.reads_p()
            }
            Self::LetForm(form, body) => form.reads_p() || body.reads_p(),
            Self::MatchP(..) | Self::RawState(..) => true,
            Self::Not(inner)
            | Self::MatchStruct(_, _, inner)
            | Self::MatchAlias(inner)
            | Self::MatchOrB(inner)
            | Self::MatchOrTuple(_, inner)
            | Self::MatchOrO(inner) => inner.reads_p(),
            Self::And(a, b)
            | Self::Or(a, b)
            | Self::Implies(a, b)
            | Self::MatchO(_, a, b)
            | Self::IfLetSome(_, a, b)
            | Self::MatchB(a, b)
            | Self::MatchTuple(_, a, b)
            | Self::MatchRest(a, b) => a.reads_p() || b.reads_p(),
            Self::Ite(c, t, e) => c.reads_p() || t.reads_p() || e.reads_p(),
            _ => false,
        }
    }

    fn render_atom(&self) -> String {
        let text = self.render();
        if text.starts_with('(') {
            text
        } else {
            format!("({text})")
        }
    }

    fn eval(&self, env: &Env, at: &At<'_>) -> bool {
        let point = at.point;
        match self {
            Self::Lit(value) => *value,
            Self::B => point.b,
            Self::Cmp(op, a, b) => cmp_holds(*op, a.eval(env, at), b.eval(env, at)),
            Self::Not(inner) => !inner.eval(env, at),
            Self::And(a, b) => a.eval(env, at) && b.eval(env, at),
            Self::Or(a, b) => a.eval(env, at) || b.eval(env, at),
            Self::Implies(a, b) => !a.eval(env, at) || b.eval(env, at),
            Self::Ite(c, t, e) => {
                if c.eval(env, at) {
                    t.eval(env, at)
                } else {
                    e.eval(env, at)
                }
            }
            Self::Let(name, value, body) | Self::MutLet(name, value, body) => {
                let mut inner = env.clone();
                inner.ints.insert(name.clone(), value.eval(env, at));
                body.eval(&inner, at)
            }
            Self::MatchO(w, some, none) | Self::IfLetSome(w, some, none) => match point.o {
                Some(value) => {
                    let mut inner = env.clone();
                    inner.ints.insert(w.clone(), value);
                    some.eval(&inner, at)
                }
                None => none.eval(env, at),
            },
            Self::MatchB(t, f) => {
                if point.b {
                    t.eval(env, at)
                } else {
                    f.eval(env, at)
                }
            }
            Self::MatchTuple(w, t, f) => {
                if point.b {
                    let mut inner = env.clone();
                    inner.ints.insert(w.clone(), point.x);
                    t.eval(&inner, at)
                } else {
                    f.eval(env, at)
                }
            }
            Self::MatchRest(some, none) => {
                if point.o.is_some() {
                    some.eval(env, at)
                } else {
                    none.eval(env, at)
                }
            }
            Self::MatchStruct(u, w, body) => {
                let mut inner = env.clone();
                inner.ints.insert(u.clone(), point.sa);
                if let Some(w) = w {
                    inner.ints.insert(w.clone(), point.sb);
                }
                body.eval(&inner, at)
            }
            Self::LetForm(form, body) => body.eval(&form.bind(env, at), at),
            Self::MatchP(_, body) => body.eval(env, at),
            Self::MatchAlias(body) => {
                let mut inner = env.clone();
                inner.ints.insert("a".into(), point.x);
                inner.ints.insert("c".into(), point.x);
                body.eval(&inner, at)
            }
            Self::Forall(i, value, body) | Self::Exists(i, value, body) => {
                let mut inner = env.clone();
                inner.ints.insert(i.clone(), value.eval(env, at));
                body.eval(&inner, at)
            }
            Self::IsNone(holds) => *holds,
            Self::IsSome => true,
            Self::Bits(op, a, b, c) => {
                let (a, b, c) = (*a, *b, *c);
                match op {
                    BinOp::BitAnd => (a as i32 & b as i32) == c as i32,
                    BinOp::BitOr => (a as i32 | b as i32) == c as i32,
                    BinOp::BitXor => (a as i32 ^ b as i32) == c as i32,
                    BinOp::Shl => (a as u32).checked_shl(b as u32) == Some(c as u32),
                    BinOp::Shr => (a as u32).checked_shr(b as u32) == Some(c as u32),
                    other => panic!("not a bit operator: {other:?}"),
                }
            }
            #[allow(clippy::float_cmp)]
            Self::FloatEq(a, b) => a == b,
            Self::TagEq(a, b) => a == b,
            Self::ONone(is_none) => point.o.is_none() == *is_none,
            // Every spelling reads `p`'s referent in the clause's state: the
            // value `p` is left with (the clause reads `old(*p)`).
            Self::RawState(_, d) => at.p1 == point.p0 + i128::from(*d),
            Self::AddnEq(a, b) => const_block(a) == const_block(b),
            Self::MatchOrB(body) | Self::MatchOrO(body) => body.eval(env, at),
            Self::MatchOrTuple(w, body) => {
                let mut inner = env.clone();
                inner.ints.insert(w.clone(), point.x);
                body.eval(&inner, at)
            }
        }
    }

    fn scan(&self, in_old: bool, reading: &mut Reading) {
        match self {
            Self::RawState(..) => reading.old_dialect = true,
            Self::Cmp(_, a, b) => {
                a.scan(in_old, reading);
                b.scan(in_old, reading);
            }
            Self::Let(_, value, body) | Self::MutLet(_, value, body) => {
                value.scan(in_old, reading);
                body.scan(in_old, reading);
            }
            Self::Forall(_, value, body) | Self::Exists(_, value, body) => {
                value.scan(in_old, reading);
                body.scan(in_old, reading);
            }
            Self::Not(inner)
            | Self::LetForm(_, inner)
            | Self::MatchP(_, inner)
            | Self::MatchAlias(inner)
            | Self::MatchStruct(_, _, inner)
            | Self::MatchOrB(inner)
            | Self::MatchOrTuple(_, inner)
            | Self::MatchOrO(inner) => inner.scan(in_old, reading),
            Self::And(a, b)
            | Self::Or(a, b)
            | Self::Implies(a, b)
            | Self::MatchO(_, a, b)
            | Self::IfLetSome(_, a, b)
            | Self::MatchB(a, b)
            | Self::MatchTuple(_, a, b)
            | Self::MatchRest(a, b) => {
                a.scan(in_old, reading);
                b.scan(in_old, reading);
            }
            Self::Ite(c, t, e) => {
                c.scan(in_old, reading);
                t.scan(in_old, reading);
                e.scan(in_old, reading);
            }
            _ => {}
        }
    }
}

// ---- The generator ------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn pick<T: Clone>(&mut self, items: &[T]) -> T {
        items[self.below(items.len())].clone()
    }

    fn small(&mut self) -> i64 {
        self.pick(&[-2, -1, 0, 1, 2, 3, 7])
    }
}

/// A plain integer term over the parameters and the result.
fn plain(rng: &mut Rng, depth: usize) -> I {
    if depth == 0 {
        return match rng.below(7) {
            0 => I::Lit(rng.small()),
            1 => I::X,
            2 => I::Y,
            3 => I::R,
            4 => I::SA,
            5 => I::Result,
            _ => I::Old(Box::new(I::X)),
        };
    }
    match rng.below(5) {
        0 => I::Add(
            Box::new(plain(rng, depth - 1)),
            Box::new(plain(rng, depth - 1)),
        ),
        1 => I::Sub(
            Box::new(plain(rng, depth - 1)),
            Box::new(plain(rng, depth - 1)),
        ),
        2 => I::MulK(Box::new(plain(rng, depth - 1)), rng.pick(&[-1, 2, 3])),
        3 => I::Neg(Box::new(plain(rng, depth - 1))),
        _ => plain(rng, 0),
    }
}

fn cmp(op: BinOp, a: I, b: I) -> Bo {
    Bo::Cmp(op, a, b)
}

fn add(a: I, k: i64) -> I {
    I::Add(Box::new(a), Box::new(I::Lit(k)))
}

/// `a == b + k`, true for `k` the offset the evaluator reads, false for
/// another: the verified case and its false twin come from one template.
fn eq_off(a: I, b: I, k: i64) -> Bo {
    cmp(BinOp::Eq, a, add(b, k))
}

/// `*p`'s final value spelled two ways, when the body gives it one: with
/// `old((*p)@)` for the entry value (the pre-Creusot dialect), and with
/// `(*p)@` (Creusot's).
fn final_of_p(body: Body) -> Option<(I, I)> {
    let old_p = || I::Old(Box::new(I::DerefP));
    match body {
        Body::IncP => Some((add(old_p(), 1), add(I::DerefP, 1))),
        Body::SetPToX => Some((I::X, I::X)),
        Body::DoubleP => Some((
            I::MulK(Box::new(old_p()), 2),
            I::MulK(Box::new(I::DerefP), 2),
        )),
        Body::ShadowIncP => Some((add(old_p(), 1), add(I::DerefP, 1))),
        Body::ShadowParam => Some((I::Y, I::Y)),
        Body::IncPIfB | Body::AddSomeToP => None,
    }
}

/// The result a body returns, spelled over the parameters.
fn result_of(body: Body) -> I {
    match body {
        Body::IncP => I::Add(Box::new(I::X), Box::new(I::Y)),
        Body::SetPToX => I::Y,
        Body::IncPIfB => I::X,
        Body::DoubleP => I::R,
        Body::AddSomeToP => I::MatchO(
            "w".into(),
            Box::new(I::Name("w".into(), true)),
            Box::new(I::Lit(0)),
        ),
        Body::ShadowIncP => I::Y,
        Body::ShadowParam => I::X,
    }
}

/// Reads of `p`'s referent, each at the state the clause gives it: the
/// pre-Creusot dialect through `*p`, `p@`, a `match` binder, a branch, a
/// `let &mut` and a `let ref mut`, and Creusot's `^p`. `k` offsets the
/// right side: 0 is the body's true final value. With `unchanged`, the right
/// side is the entry value instead (`*q == old(*q)`), the claim every
/// reading at the wrong state proved.
fn state_templates(body: Body, k: i64, unchanged: bool) -> Vec<Bo> {
    let Some((final_old, final_entry)) = final_of_p(body) else {
        return Vec::new();
    };
    let (final_old, final_entry) = if unchanged {
        (I::Old(Box::new(I::DerefP)), I::DerefP)
    } else {
        (final_old, final_entry)
    };
    let q = || I::DerefAlias("q".into());
    let offset = |term: &I| add(term.clone(), k);
    vec![
        cmp(BinOp::Eq, I::DerefP, offset(&final_old)),
        cmp(BinOp::Eq, I::ViewP, offset(&final_old).clone()),
        cmp(BinOp::Eq, I::FinalP, offset(&final_entry)),
        Bo::MatchP(
            "q".into(),
            Box::new(cmp(BinOp::Eq, q(), offset(&final_old).clone())),
        ),
        cmp(BinOp::Eq, I::DerefBranch, offset(&final_old)),
        Bo::LetForm(
            LetForm::MutReference,
            Box::new(cmp(
                BinOp::Eq,
                I::Name("a".into(), true),
                offset(&final_old),
            )),
        ),
        Bo::LetForm(
            LetForm::RefMut,
            Box::new(cmp(
                BinOp::Eq,
                I::DerefAlias("*a".into()),
                offset(&final_old),
            )),
        ),
    ]
}

/// The body's result spelled through each construct: a `let`, `let mut`, a
/// quantifier's one point, a logic function, `if`, and patterns over the
/// parameters. `k` offsets one side: 0 is true.
fn result_templates(body: Body, k: i64) -> Vec<Bo> {
    let result = result_of(body);
    let w = || I::Name("w".into(), true);
    vec![
        eq_off(I::Result, result.clone(), k),
        Bo::Let(
            "t".into(),
            result.clone(),
            Box::new(eq_off(I::Result, I::Name("t".into(), false), k)),
        ),
        Bo::MutLet(
            "t".into(),
            result.clone(),
            Box::new(eq_off(I::Name("t".into(), false), I::Result, k)),
        ),
        Bo::Forall(
            "i".into(),
            result.clone(),
            Box::new(eq_off(I::Result, I::Name("i".into(), false), k)),
        ),
        Bo::Exists(
            "i".into(),
            I::Result,
            Box::new(eq_off(I::Name("i".into(), false), result.clone(), k)),
        ),
        cmp(
            BinOp::Eq,
            I::Add1(Box::new(I::Result)),
            add(result.clone(), 1 + k),
        ),
        Bo::Ite(
            Box::new(Bo::B),
            Box::new(eq_off(I::Result, result.clone(), k)),
            Box::new(eq_off(result.clone(), I::Result, k)),
        ),
        eq_off(
            I::Ite(
                Box::new(Bo::B),
                Box::new(I::Result),
                Box::new(result.clone()),
            ),
            result.clone(),
            k,
        ),
        Bo::MatchB(
            Box::new(eq_off(I::Result, result.clone(), k)),
            Box::new(eq_off(result.clone(), I::Result, k)),
        ),
        Bo::MatchTuple(
            "w".into(),
            Box::new(eq_off(w(), I::X, k)),
            Box::new(eq_off(I::Result, result.clone(), k)),
        ),
        Bo::MatchO(
            "w".into(),
            Box::new(eq_off(w(), w(), k)),
            Box::new(eq_off(I::Result, result.clone(), k)),
        ),
        Bo::IfLetSome(
            "w".into(),
            Box::new(eq_off(
                I::Add(Box::new(w()), Box::new(I::Result)),
                I::Add(Box::new(I::Result), Box::new(w())),
                k,
            )),
            Box::new(eq_off(I::Result, result, k)),
        ),
    ]
}

/// Constructs whose truth is the parameters' or constants' alone: pattern
/// forms, the arithmetic the parser lowers, bit operators, floats, method
/// calls. Each `(true instance, false twin)` comes three ways.
fn value_templates() -> Vec<Bo> {
    let mut out = Vec::new();
    for k in [0, 1] {
        out.push(Bo::MatchRest(
            Box::new(cmp(BinOp::Ne, I::Lit(0), I::Lit(1 - k))),
            Box::new(Bo::Lit(true)),
        ));
        out.push(Bo::MatchRest(
            Box::new(Bo::Lit(true)),
            Box::new(Bo::Lit(k == 0)),
        ));
        out.push(Bo::MatchRest(
            Box::new(Bo::Lit(k == 0)),
            Box::new(cmp(BinOp::Eq, I::Lit(k), I::Lit(0))),
        ));
        // Arms that tell `Some(..)` from `None`: `Some(..)` read as a
        // constructor with no fields matched no `Some` value.
        out.push(Bo::MatchRest(
            Box::new(Bo::ONone(k != 0)),
            Box::new(Bo::ONone(k == 0)),
        ));
        out.push(Bo::MatchRest(
            Box::new(Bo::ONone(k == 0)),
            Box::new(Bo::Lit(true)),
        ));
        out.push(Bo::MatchRest(
            Box::new(Bo::Lit(true)),
            Box::new(Bo::ONone(k == 0)),
        ));
        // The same, telling the arms apart by a nested `match` the driver
        // decides.
        let is_some = |some: bool| {
            Bo::MatchO(
                "w".into(),
                Box::new(Bo::Lit(some)),
                Box::new(Bo::Lit(!some)),
            )
        };
        out.push(Bo::MatchRest(
            Box::new(is_some(k == 0)),
            Box::new(is_some(k != 0)),
        ));
        out.push(Bo::MatchRest(
            Box::new(is_some(k == 0)),
            Box::new(Bo::Lit(true)),
        ));
        out.push(Bo::MatchRest(
            Box::new(Bo::Lit(true)),
            Box::new(is_some(k != 0)),
        ));
        for (u, w) in [
            ("u", None),
            ("u", Some("w")),
            ("aa", None),
            ("ab", Some("ac")),
            ("ad", None),
        ] {
            let body = match w {
                None => eq_off(I::Name(u.into(), true), I::SA, k),
                Some(w) => eq_off(
                    I::Add(
                        Box::new(I::Name(u.into(), true)),
                        Box::new(I::Name(w.into(), true)),
                    ),
                    I::Add(Box::new(I::SA), Box::new(I::Name(w.into(), true))),
                    k,
                ),
            };
            out.push(Bo::MatchStruct(
                u.into(),
                w.map(String::from),
                Box::new(body),
            ));
        }
        // An or-pattern is one arm per alternative sharing the body; the
        // first alternative that matches binds.
        for extra in [0, 2, -5] {
            out.push(Bo::MatchOrB(Box::new(eq_off(
                add(I::X, extra),
                add(I::X, extra),
                k,
            ))));
            out.push(Bo::MatchOrTuple(
                "w".into(),
                Box::new(eq_off(
                    add(I::Name("w".into(), true), extra),
                    add(I::X, extra),
                    k,
                )),
            ));
            out.push(Bo::MatchOrO(Box::new(eq_off(
                add(I::Y, extra),
                add(I::Y, extra),
                k,
            ))));
        }
        for extra in [0, 3, -2] {
            out.push(Bo::MatchAlias(Box::new(eq_off(
                add(I::Name("a".into(), true), extra),
                add(I::Name("c".into(), true), extra),
                k,
            ))));
        }
        for form in LetForm::ALL {
            if form.reads_p() {
                continue;
            }
            let value = match form {
                LetForm::Reference => I::R,
                _ => I::X,
            };
            for extra in [0, 1, 5, -3, 8] {
                let mut inner = eq_off(add(form.a(), extra), add(value.clone(), extra), k);
                if form == LetForm::NestedTuple {
                    inner = Bo::And(
                        Box::new(inner),
                        Box::new(cmp(BinOp::Eq, I::Name("c".into(), true), I::Y)),
                    );
                }
                if matches!(form, LetForm::Alias | LetForm::RefAlias) {
                    inner = Bo::And(
                        Box::new(inner),
                        Box::new(cmp(BinOp::Eq, I::Name("c".into(), true), I::X)),
                    );
                }
                out.push(Bo::LetForm(form, Box::new(inner)));
            }
        }
        for (a, b, c) in [(7, 2, 3), (-7, 2, -3), (9, 4, 2), (10, 3, 3), (-9, 4, -2)] {
            out.push(eq_off(I::DivK(Box::new(I::Lit(a)), b), I::Lit(c), k));
        }
        for (a, b, c) in [(7, 2, 1), (-7, 2, -1), (9, 4, 1), (10, 3, 1), (-9, 4, -1)] {
            out.push(eq_off(I::RemK(Box::new(I::Lit(a)), b), I::Lit(c), k));
        }
        for (a, c) in [(300, 44), (-1, 255), (256, 0), (511, 255), (7, 7)] {
            out.push(eq_off(I::CastU8(a), I::Lit(c), k));
        }
        // `-1i32 as u8` is `(-1i32) as u8`: a parser that bound the cast
        // tighter than the sign would read `-1` here.
        out.push(eq_off(I::CastU8(-1), I::Lit(-1), k));
        for a in [5, -6, 7, 0, -100] {
            out.push(eq_off(I::CastI64(a), I::Lit(a), k));
        }
        out.push(eq_off(
            I::Neg(Box::new(I::X)),
            I::Sub(Box::new(I::Lit(0)), Box::new(I::X)),
            k,
        ));
        out.push(eq_off(
            I::Neg(Box::new(I::Y)),
            I::Sub(Box::new(I::Lit(0)), Box::new(I::Y)),
            k,
        ));
        out.push(eq_off(I::Neg(Box::new(I::Neg(Box::new(I::R)))), I::R, k));
        out.push(eq_off(
            I::MulK(Box::new(I::Y), 2),
            I::Add(Box::new(I::Y), Box::new(I::Y)),
            k,
        ));
        out.push(eq_off(
            I::MulK(Box::new(I::X), 3),
            I::Add(
                Box::new(I::X),
                Box::new(I::Add(Box::new(I::X), Box::new(I::X))),
            ),
            k,
        ));
        out.push(eq_off(
            I::MulK(Box::new(I::R), -1),
            I::Neg(Box::new(I::R)),
            k,
        ));
        for extra in [0, 2, 4] {
            out.push(eq_off(add(I::Len, extra), add(I::Len, extra), k));
            out.push(eq_off(add(I::PushLen, extra), add(I::Len, extra), 1 + k));
        }
        for (op, triples) in [
            (
                BinOp::BitAnd,
                [(6, 3, 2), (12, 10, 8), (5, 4, 4), (7, 7, 7), (15, 1, 1)],
            ),
            (
                BinOp::BitOr,
                [(6, 3, 7), (8, 1, 9), (4, 4, 4), (0, 5, 5), (10, 5, 15)],
            ),
            (
                BinOp::BitXor,
                [(6, 3, 5), (5, 5, 0), (9, 3, 10), (0, 7, 7), (12, 10, 6)],
            ),
            (
                BinOp::Shl,
                [(1, 3, 8), (2, 2, 8), (3, 1, 6), (1, 0, 1), (5, 2, 20)],
            ),
            (
                BinOp::Shr,
                [(8, 3, 1), (16, 2, 4), (7, 1, 3), (1, 0, 1), (20, 2, 5)],
            ),
        ] {
            for (a, b, c) in triples {
                out.push(Bo::Bits(op, a, b, c + k));
            }
        }
        for value in [1.5, 2.25, 0.75, 3.0, 0.125] {
            out.push(Bo::FloatEq(value, value + k as f64));
        }
        out.push(Bo::IsNone(k == 0));
        out.push(Bo::IsSome);
        for extra in [0, 1, 2, 5, -4] {
            out.push(Bo::Exists(
                "i".into(),
                add(I::X, extra),
                Box::new(eq_off(I::Name("i".into(), false), add(I::X, extra), k)),
            ));
        }
        // Each ordered comparison and `!=`, true with `k == 0`.
        for term in [I::X, I::Y, I::R, I::SA, I::Old(Box::new(I::X))] {
            let next = add(term.clone(), 1 - 2 * k);
            out.push(cmp(BinOp::Lt, term.clone(), next.clone()));
            out.push(cmp(BinOp::Gt, next.clone(), term.clone()));
            out.push(cmp(BinOp::Le, term.clone(), add(term.clone(), -k)));
            out.push(cmp(BinOp::Ge, add(term.clone(), -k), term.clone()));
            out.push(cmp(BinOp::Ne, term.clone(), add(term.clone(), 1 - k)));
        }
    }
    // A generic argument names which instance is called: two calls differing
    // only in a type argument, or in a const argument whatever its block
    // holds, are two values.
    out.push(Bo::TagEq("u8", "u16"));
    out.push(Bo::TagEq("u8", "u8"));
    out.push(Bo::AddnEq("2 * 3", "1 * 3"));
    out.push(Bo::AddnEq("2 * 3", "3 * 2"));
    out
}

/// A connective around `inner`, read over a tautology: each of `&&`, `||`,
/// `==>` and `!` in turn.
fn in_context(inner: Bo, at: usize) -> Bo {
    let tautology = cmp(BinOp::Le, I::X, add(I::X, 1));
    match at % 5 {
        0 => Bo::And(Box::new(tautology), Box::new(inner)),
        1 => Bo::Or(Box::new(Bo::Not(Box::new(tautology))), Box::new(inner)),
        2 => Bo::Implies(Box::new(tautology), Box::new(inner)),
        3 => Bo::Not(Box::new(Bo::Not(Box::new(inner)))),
        _ => Bo::Or(Box::new(inner), Box::new(Bo::Lit(false))),
    }
}

/// Every case: each template against the bodies it reads, a few random
/// comparisons of plain terms, and a connective around every fifth.
fn clauses(rng: &mut Rng) -> Vec<(Body, Bo)> {
    let mut out = Vec::new();
    for k in [0, 1] {
        for body in [
            Body::IncP,
            Body::SetPToX,
            Body::DoubleP,
            Body::ShadowIncP,
            Body::ShadowParam,
        ] {
            out.extend(
                state_templates(body, k, false)
                    .into_iter()
                    .map(|clause| (body, clause)),
            );
        }
        out.extend(
            state_templates(Body::IncP, k - 1, true)
                .into_iter()
                .map(|clause| (Body::IncP, clause)),
        );
    }
    for at in 0..RAW_READS.len() {
        for d in [0, 1, 2] {
            out.push((Body::IncP, Bo::RawState(at, d)));
        }
    }
    for k in [0, 1] {
        for body in [
            Body::IncP,
            Body::SetPToX,
            Body::IncPIfB,
            Body::ShadowIncP,
            Body::ShadowParam,
        ] {
            out.extend(
                result_templates(body, k)
                    .into_iter()
                    .map(|clause| (body, clause)),
            );
        }
        // A body the driver leaves unknown whatever the clause: its false
        // clauses still must not verify.
        out.extend(
            result_templates(Body::AddSomeToP, k)
                .into_iter()
                .take(4)
                .map(|clause| (Body::AddSomeToP, clause)),
        );
    }
    let bodies = [Body::IncP, Body::SetPToX, Body::IncPIfB, Body::DoubleP];
    for (at, clause) in value_templates().into_iter().enumerate() {
        out.push((bodies[at % bodies.len()], clause));
    }
    for at in 0..8 {
        let a = plain(rng, 2);
        let op = rng.pick(&[
            BinOp::Eq,
            BinOp::Ne,
            BinOp::Lt,
            BinOp::Le,
            BinOp::Gt,
            BinOp::Ge,
        ]);
        let b = plain(rng, 1);
        out.push((bodies[at % bodies.len()], cmp(op, a, b)));
    }
    let wrapped: Vec<(Body, Bo)> = out
        .iter()
        .enumerate()
        .filter(|(at, _)| at % 5 == 0)
        .map(|(at, (body, clause))| (*body, in_context(clause.clone(), at / 5)))
        .collect();
    out.extend(wrapped);
    out
}

// ---- Cases ------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Truth {
    True,
    False,
}

/// How a callee states the post-state of the body it runs: the pre-Creusot
/// dialect through `*p`, `p@` or a `match` binder of `p` (each beside an
/// `old(*p)`), or Creusot's `^p`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Dialect {
    Old,
    OldView,
    OldAlias,
    Creusot,
}

impl Dialect {
    const ALL: [Self; 4] = [Self::Old, Self::OldView, Self::OldAlias, Self::Creusot];
}

/// Where a generated clause is written, and so which lane reads it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Host {
    /// A function's postcondition, read by its own lane.
    Fn,
    /// A caller's postcondition over a call of a callee running the body,
    /// whose true contract is spelled in the dialect: the call reads the
    /// callee's clause.
    Caller(Dialect),
    /// A closure's postcondition.
    Closure,
    /// A shape of parameters the fixed signature has none of (see
    /// [`ShapeKind`]).
    Shape(ShapeKind),
    /// A bundle claim with a pointer summary fact, verified natively.
    BundleFact,
}

#[derive(Debug, Clone)]
struct Case {
    name: String,
    host: Host,
    body: Body,
    /// The postcondition as written, or `|ret: i32| ..` when `closure`.
    ensures: String,
    truth: Truth,
    kinds: BTreeSet<NodeKind>,
    /// The functions written for this case, or the shape's.
    source: String,
}

fn truth(clause: &Bo, body: Body, points: &[Point]) -> Truth {
    let mut reading = Reading {
        old_dialect: false,
        explicit_final: false,
    };
    clause.scan(false, &mut reading);
    for point in points {
        let (p1, result) = body.run(point);
        let at = At {
            point,
            p1,
            result,
            reading,
            in_old: false,
        };
        if !clause.eval(&Env::default(), &at) {
            return Truth::False;
        }
    }
    Truth::True
}

/// `|ret: i32| ..` over `clause` with `result@` read through `ret`.
fn closure_form(clause: &str) -> String {
    format!("|ret: i32| {}", clause.replace("result@", "ret@"))
}

const SIGNATURE: &str = "p: &mut i32, x: i32, y: i32, b: bool, o: Option<i32>, s: S, r: &i32, \
                         v: &Vec<i32>";

/// `*p` at exit spelled over the entry state, every body: with `old((*p)@)`
/// for the entry value (the pre-Creusot dialect), and with `(*p)@`
/// (Creusot's).
fn callee_final(body: Body) -> (I, I) {
    let old_p = || I::Old(Box::new(I::DerefP));
    let step = |entry: I| match body {
        Body::IncP | Body::ShadowIncP => add(entry, 1),
        Body::ShadowParam => I::Add(
            Box::new(I::Y),
            Box::new(I::Sub(Box::new(entry.clone()), Box::new(entry))),
        ),
        // The entry value read and cancelled, so the pre-Creusot spelling
        // names `p` inside `old`.
        Body::SetPToX => I::Add(
            Box::new(I::X),
            Box::new(I::Sub(Box::new(entry.clone()), Box::new(entry))),
        ),
        Body::DoubleP => I::MulK(Box::new(entry), 2),
        Body::IncPIfB => I::Add(
            Box::new(entry),
            Box::new(I::Ite(
                Box::new(Bo::B),
                Box::new(I::Lit(1)),
                Box::new(I::Lit(0)),
            )),
        ),
        Body::AddSomeToP => I::Add(
            Box::new(entry),
            Box::new(I::MatchO(
                "w".into(),
                Box::new(I::Name("w".into(), true)),
                Box::new(I::Lit(0)),
            )),
        ),
    };
    (step(old_p()), step(I::DerefP))
}

/// The true contract of a callee running `body`, in `dialect`: the value
/// `p` is left with and the result.
fn callee_contract(body: Body, dialect: Dialect) -> Bo {
    let (final_old, final_entry) = callee_final(body);
    let state = match dialect {
        Dialect::Old => cmp(BinOp::Eq, I::DerefP, final_old),
        Dialect::OldView => cmp(BinOp::Eq, I::ViewP, final_old),
        Dialect::OldAlias => Bo::MatchP(
            "q".into(),
            Box::new(cmp(BinOp::Eq, I::DerefAlias("q".into()), final_old)),
        ),
        Dialect::Creusot => cmp(BinOp::Eq, I::FinalP, final_entry),
    };
    Bo::And(
        Box::new(state),
        Box::new(cmp(BinOp::Eq, I::Result, result_of(body))),
    )
}

fn fn_source(name: &str, ensures: &str, body: &str) -> String {
    format!(
        "\n#[requires({PRECONDITION})]\n#[ensures({ensures})]\nfn {name}({SIGNATURE}) -> i32 \
         {{\n    {body}\n}}\n"
    )
}

/// The case `clause` over `body`, written for `host`.
fn case_for(
    name: String,
    host: Host,
    body: Body,
    clause: &Bo,
    ensures: String,
    points: &[Point],
) -> Case {
    let clause_truth = truth(clause, body, points);
    let kinds = parse_contract_census(&ensures).unwrap_or_default();
    let source = match host {
        Host::Fn => fn_source(&name, &ensures, body.rust()),
        Host::Caller(dialect) => {
            let contract = callee_contract(body, dialect);
            assert_eq!(
                truth(&contract, body, points),
                Truth::True,
                "a callee contract must be true: {}",
                contract.render()
            );
            let callee = format!("{name}_callee");
            fn_source(&callee, &contract.render(), body.rust())
                + &fn_source(
                    &name,
                    &ensures,
                    &format!("{callee}(p, x, y, b, o, s, r, v)"),
                )
        }
        Host::Closure => format!(
            "\nfn {name}() {{\n    let _c = #[requires({PRECONDITION})]\n    \
             #[ensures({ensures})]\n    |{SIGNATURE}| -> i32 {{ {} }};\n}}\n",
            body.rust()
        ),
        Host::Shape(_) | Host::BundleFact => unreachable!("written by their own family"),
    };
    Case {
        name,
        host,
        body,
        ensures,
        truth: clause_truth,
        kinds,
        source,
    }
}

/// The clauses that read the state: `p`'s referent at each state the text can
/// reach it (`state_templates`, [`RAW_READS`]) and the result through each
/// construct (`result_templates`).
fn state_clauses() -> Vec<(Body, Bo)> {
    let mut out = Vec::new();
    for k in [0, 1] {
        for body in [Body::IncP, Body::SetPToX, Body::DoubleP] {
            out.extend(
                state_templates(body, k, false)
                    .into_iter()
                    .map(|clause| (body, clause)),
            );
        }
        out.extend(
            state_templates(Body::IncP, k - 1, true)
                .into_iter()
                .map(|clause| (Body::IncP, clause)),
        );
        out.extend(
            result_templates(Body::IncP, k)
                .into_iter()
                .map(|clause| (Body::IncP, clause)),
        );
    }
    for at in 0..RAW_READS.len() {
        for d in [0, 1, 2] {
            out.push((Body::IncP, Bo::RawState(at, d)));
        }
    }
    out
}

fn generate() -> Vec<Case> {
    let points = grid();
    let mut rng = Rng(0x7275_7374_2d77_7037);
    let mut cases = Vec::new();
    let mut results = 0usize;
    for (body, clause) in clauses(&mut rng) {
        let rendered = clause.render();
        // Every fourth clause reading the result names it through a closure
        // parameter instead: `|ret: i32| ..`.
        let as_closure = rendered.contains("result@") && {
            results += 1;
            results % 4 == 0
        };
        let ensures = if as_closure {
            closure_form(&rendered)
        } else {
            rendered
        };
        let name = format!("case_{}", cases.len());
        cases.push(case_for(name, Host::Fn, body, &clause, ensures, &points));
    }
    // The same state-reading clauses, over a call of a callee whose true
    // contract is spelled in each dialect in turn, and on a closure: the call
    // and the closure read a clause through the state elaboration the
    // function's own lane does.
    for (at, (body, clause)) in state_clauses().into_iter().enumerate() {
        let dialect = Dialect::ALL[at % Dialect::ALL.len()];
        let name = format!("case_{}", cases.len());
        cases.push(case_for(
            name,
            Host::Caller(dialect),
            body,
            &clause,
            clause.render(),
            &points,
        ));
        let name = format!("case_{}", cases.len());
        cases.push(case_for(
            name,
            Host::Closure,
            body,
            &clause,
            clause.render(),
            &points,
        ));
    }
    cases.extend(shape_cases());
    cases
}

// ---- Shapes the fixed signature has none of ---------------------------------------

/// A shape of parameters, each with its own body: a method on `&mut self`
/// and a caller of one, two `&mut` parameters (a swap) and a caller of one,
/// a destructuring parameter pattern binding `&mut`s, a tuple parameter
/// holding one, a `&mut` struct parameter's fields, a closure's `&mut`
/// parameter bound under `old(..)`, a function whose result may borrow its
/// `&mut` parameter and a caller of one, and a caller of a closure; a
/// caller that writes through, or reads, a `&mut` result lent its argument;
/// a `&mut` parameter whose referent holds a cell (inline, boxed, in a
/// field) written through a shared reborrow, and a caller writing a cell
/// through a `&Cell` or `&Box<Cell>` result; a function storing its `&mut`
/// parameter in another parameter's referent, and a caller writing through
/// the stored borrow; a final value read in the entry state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ShapeKind {
    MethodSelf,
    MethodSelfCaller,
    TwoMut,
    TwoMutCaller,
    Destructured,
    TupleParam,
    MutStructField,
    ClosureAlias,
    Lent,
    LentCaller,
    ClosureCaller,
    LentWriteCaller,
    InteriorWrite,
    CellLentCaller,
    LentIntoParam,
    LentIntoParamCaller,
    EntryFinal,
    ResultResolve,
    HeldFinal,
    HeldFinalRequires,
    HeldCurrent,
    WriteThenAssert,
    JoinedWriteThenAssert,
    RetargetedWriteThenAssert,
    LoopCarriedLocalThenAssert,
    LoopTestThenAssert,
    LoopAfterLoopThenAssert,
}

impl ShapeKind {
    const ALL: [Self; 27] = [
        Self::MethodSelf,
        Self::MethodSelfCaller,
        Self::TwoMut,
        Self::TwoMutCaller,
        Self::Destructured,
        Self::TupleParam,
        Self::MutStructField,
        Self::ClosureAlias,
        Self::Lent,
        Self::LentCaller,
        Self::ClosureCaller,
        Self::LentWriteCaller,
        Self::InteriorWrite,
        Self::CellLentCaller,
        Self::LentIntoParam,
        Self::LentIntoParamCaller,
        Self::EntryFinal,
        Self::ResultResolve,
        Self::HeldFinal,
        Self::HeldFinalRequires,
        Self::HeldCurrent,
        Self::WriteThenAssert,
        Self::JoinedWriteThenAssert,
        Self::RetargetedWriteThenAssert,
        Self::LoopCarriedLocalThenAssert,
        Self::LoopTestThenAssert,
        Self::LoopAfterLoopThenAssert,
    ];
}

/// A point of a shape's grid: the entry values its parameters hold.
#[derive(Debug, Clone, Copy)]
struct ShapePoint {
    /// `self.a` / `c.a` / `*a` / `*p` at entry.
    a0: i128,
    /// `self.b` / `c.b` / `*q` at entry.
    b0: i128,
    x: i128,
}

fn shape_grid() -> Vec<ShapePoint> {
    let mut points = Vec::new();
    for a0 in [-5, 0, 9] {
        for b0 in [-2, 4] {
            for x in [-3, 0, 7] {
                points.push(ShapePoint { a0, b0, x });
            }
        }
    }
    points
}

/// A clause over a shape, `{k}` its offset, and whether it holds at a point
/// for an offset, read as contract-syntax.md reads it.
type ShapeTemplate = (&'static str, fn(&ShapePoint, i128) -> bool);

/// `let r = self.b; self.a = x; r` (the field returned is read before the
/// store: a read after it is refused as stale), and the same through a caller
/// (with `self` read as `c`). A clause naming `self` inside `old` reads
/// `self.a` as the field `self` is left with.
const METHOD_TEMPLATES: [ShapeTemplate; 8] = [
    ("self.a == x + {k} && old(self.b) == old(self.b)", |_, k| {
        k == 0
    }),
    ("(^self).a == x + {k}", |_, k| k == 0),
    (
        "{ let t = self; t.a == x + {k} && old(t.b) == t.b }",
        |_, k| k == 0,
    ),
    ("match self { t => (^t).a == x + {k} }", |_, k| k == 0),
    ("result == self.b + {k}", |_, k| k == 0),
    ("result == old(self.b) + {k} && self.a == x", |_, k| k == 0),
    ("self.a == x + {k}", |pt, k| pt.a0 == pt.x + k),
    ("self.a == old(self.a) + {k}", |pt, k| pt.x == pt.a0 + k),
];

/// A method's true contracts, one per dialect, for the callers.
const METHOD_CALLEES: [&str; 3] = [
    "self.a == x && self.b == old(self.b) && result == old(self.b)",
    "(^self).a == x && (^self).b == self.b && result == self.b",
    "{ let t = self; t.a == x && t.b == old(t.b) && result == old(t.b) }",
];

const METHOD_BODY: &str = "let r = self.b;\n        self.a = x;\n        r";

/// `let t = *a; *a = *q; *q = t;`
const SWAP_TEMPLATES: [ShapeTemplate; 6] = [
    ("*a == old(*q) + {k} && *q == old(*a)", |_, k| k == 0),
    ("^a == *q + {k} && ^q == *a", |_, k| k == 0),
    ("match a { t => *t == old(*q) + {k} }", |_, k| k == 0),
    ("{ let t = q; ^a == *t + {k} }", |_, k| k == 0),
    ("*a == *q + {k}", |pt, k| pt.a0 == pt.b0 + k),
    ("^a == *a + {k}", |pt, k| pt.b0 == pt.a0 + k),
];

const SWAP_CALLEES: [&str; 3] = [
    "*a == old(*q) && *q == old(*a)",
    "^a == *q && ^q == *a",
    "(match a { t => *t == old(*q) }) && *q == old(*a)",
];

/// `*p += 1` on `(p, q): (&mut i32, &mut i32)`: every read of `p`'s referent
/// is refused; the rest are read. Each read's false twin (`{k}` 1) is the
/// one an entry reading of `p` makes true: `*p == old(*p)`.
const DESTRUCTURED_TEMPLATES: [ShapeTemplate; 5] = [
    ("*p == old(*p) + 1 - {k}", |_, k| k == 0),
    ("^p == *p + 1 - {k}", |_, k| k == 0),
    ("p@ == old(p@) + 1 - {k}", |_, k| k == 0),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

/// `*t.0 += 1` on `t: (&mut i32, i32)`: a `&mut` held in a field of a
/// parameter, every read of whose referent is refused.
const TUPLE_PARAM_TEMPLATES: [ShapeTemplate; 5] = [
    ("*t.0 == old(*t.0) + 1 - {k}", |_, k| k == 0),
    ("(*t.0)@ == old((*t.0)@) + 1 - {k}", |_, k| k == 0),
    ("t.1 == t.1 + {k}", |_, k| k == 0),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

/// `c.a = x` on `c: &mut S`: `c.a` is the field of `*c`, read at the state
/// `*c` is read at.
const FIELD_TEMPLATES: [ShapeTemplate; 6] = [
    ("c.a == x + {k} && old(c.a) == old(c.a)", |_, k| k == 0),
    ("c.a == x + {k}", |pt, k| pt.a0 == pt.x + k),
    ("(^c).a == x + {k}", |_, k| k == 0),
    ("(^c).b == c.b + {k}", |_, k| k == 0),
    ("c.b == old(c.b) + {k}", |_, k| k == 0),
    (
        "{ let t = c; t.a == x + {k} && old(t.b) == t.b }",
        |_, k| k == 0,
    ),
];

/// `*p += 1` on a closure's `p: &mut u32`: a binder of `p` is `p`, `old(..)`
/// included, so `q@` outside `old` is the value `p` is left with. Each false
/// twin (`{k}` 1) is the one an entry reading of `q` makes true.
const CLOSURE_ALIAS_TEMPLATES: [ShapeTemplate; 6] = [
    ("{ let q = p; old(q@) + 1 - {k} == q@ }", |_, k| k == 0),
    ("match p { q => old(q@) + 1 - {k} == q@ }", |_, k| k == 0),
    (
        "if let q = p { old(q@) + 1 - {k} == q@ } else { true }",
        |_, k| k == 0,
    ),
    ("p@ == old(p@) + 1 - {k}", |_, k| k == 0),
    ("(^p)@ == (*p)@ + 1 - {k}", |_, k| k == 0),
    ("{ let q = p; (^q)@ == q@ + 1 - {k} }", |_, k| k == 0),
];

/// `*p += 1` on a `p: &mut i32` the result may borrow (the body returns it
/// as a raw pointer, or a `Vec` built from `*p`): the value `p` is left with
/// is whoever holds the result's to decide, so a pre-Creusot bare `*p` has no
/// reading. Each false twin (`{k}` 1) is the one an entry reading of that
/// `*p` makes true: `*p == old(*p)`.
const LENT_TEMPLATES: [ShapeTemplate; 7] = [
    ("*p == old(*p) + 1 - {k}", |_, k| k == 0),
    ("p@ == old(p@) + 1 - {k}", |_, k| k == 0),
    ("match p { q => *q == old(*q) + 1 - {k} }", |_, k| k == 0),
    ("^p == *p + 1 - {k}", |_, k| k == 0),
    ("old(*p) + {k} == old(*p)", |_, k| k == 0),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

/// The bodies of [`LENT_TEMPLATES`]: each returns a value that may carry
/// `p`'s borrow.
const LENT_BODIES: [(&str, &str); 2] = [
    ("*mut i32", "*p += 1;\n    p as *mut i32"),
    ("Vec<i32>", "*p += 1;\n    vec![*p]"),
];

/// A callee's true contract of `*p += 1`, one per dialect: the pre-Creusot
/// ones have no reading at a call of a callee whose result may borrow `p`,
/// and Creusot's is read as written.
const INC_CALLEES: [&str; 4] = [
    "*p == old(*p) + 1",
    "p@ == old(p@) + 1",
    "match p { q => *q == old(*q) + 1 }",
    "^p == *p + 1",
];

/// A caller's clause over a call that runs `*p += 1` on its `p`, read as
/// contract-syntax.md reads it. Each false twin (`{k}` 1) is the claim that
/// `p` is left as it was.
const INC_CALLER_TEMPLATES: [ShapeTemplate; 5] = [
    ("^p == *p + 1 - {k}", |_, k| k == 0),
    ("*p == old(*p) + 1 - {k}", |_, k| k == 0),
    ("p@ == old(p@) + 1 - {k}", |_, k| k == 0),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

/// A callee `*p += 1; p` returning its `&mut i32` argument, one contract
/// per dialect: the pre-Creusot one has no reading (the result may borrow
/// `p`), Creusot's with `^result == ^p` is true, and the last claims a final
/// value only a caller that leaves the result alone makes true.
const LENT_WRITE_CALLEES: [&str; 3] = [
    "*p == old(*p) + 1",
    "*result == *p + 1 && ^result == ^p",
    "^p == *p + 1",
];

/// A caller `let r = NAME_callee(p); *r = 7; *r` of a
/// [`LENT_WRITE_CALLEES`] callee: it writes through the result and reads it
/// after, so `p` is left 7 and the result is 7; a claim that `p` is left as
/// the callee leaves it is false.
const LENT_WRITE_CALLER_TEMPLATES: [ShapeTemplate; 7] = [
    ("^p == 7 + {k}", |_, k| k == 0),
    ("result == 7 + {k}", |_, k| k == 0),
    ("^p == *p + 1 + {k}", |pt, k| pt.a0 + 1 + k == 7),
    ("*p == old(*p) + 1 + {k}", |pt, k| pt.a0 + 1 + k == 7),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
    ("{k} + 1 > {k}", |_, _| true),
];

/// A caller `let r = NAME_callee(p); *r` of a [`LENT_WRITE_CALLEES`]
/// callee that only reads the result after the call: `p` is left, and the
/// result is, 1 above `p`'s entry value.
const LENT_READ_CALLER_TEMPLATES: [ShapeTemplate; 5] = [
    ("result == *p + 1 + {k}", |_, k| k == 0),
    ("^p == *p + 1 + {k}", |_, k| k == 0),
    ("result == *p + {k}", |_, k| k == 1),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

/// A cell reachable from a `&mut` parameter, written through a shared
/// reborrow with `x` (the parameter's type, the body): inline, behind a
/// `Box`, in a field, a boxed one in a field; a `&Cell` copied out of the
/// referent (a struct field, a tuple, behind a `Box`) and set; a `RefCell`
/// in a field, and a copied `&RefCell`, written through `borrow_mut`. The
/// entry content is `a0`.
const INTERIOR_WRITES: [(&str, &str); 9] = [
    ("Cell<i32>", "p.set(x)"),
    ("Box<Cell<i32>>", "p.set(x)"),
    ("HC", "p.c.set(x)"),
    ("HB", "p.c.set(x)"),
    ("SC<'_>", "let c = p.c;\n    c.set(x)"),
    ("(u8, &Cell<i32>)", "let (_, c) = *p;\n    c.set(x)"),
    ("Box<SC<'_>>", "let c = p.c;\n    c.set(x)"),
    ("HR", "*p.c.borrow_mut() = x"),
    ("SR<'_>", "let c = p.c;\n    *c.borrow_mut() = x"),
];

/// Clauses over a `&mut` parameter whose cell is set to `x`: a claim that
/// `p` is left as it was holds only where `x` is its entry content, however
/// it is spelled (`^`, `resolve` by any spelling, a logic function reading
/// `^q` or `resolve(q)`, a quantified borrow equal to `p`, a binder). `{ty}`
/// is the parameter's referent type.
const INTERIOR_TEMPLATES: [ShapeTemplate; 13] = [
    ("^p == *p", |pt, _| pt.x == pt.a0),
    ("*p == old(*p)", |pt, _| pt.x == pt.a0),
    ("match p { q => ^q == *q }", |pt, _| pt.x == pt.a0),
    ("resolve(p)", |pt, _| pt.x == pt.a0),
    ("p.resolve()", |pt, _| pt.x == pt.a0),
    ("structural_resolve(p)", |pt, _| pt.x == pt.a0),
    ("unchanged(p)", |pt, _| pt.x == pt.a0),
    ("settled(p)", |pt, _| pt.x == pt.a0),
    ("exists<q: &mut {ty}> q == p && ^q == *q", |pt, _| {
        pt.x == pt.a0
    }),
    ("match (p, {k}) { (q, _) => resolve(q) }", |pt, _| {
        pt.x == pt.a0
    }),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
    ("{k} + 1 > {k}", |_, _| true),
];

/// A callee lending its `&mut` argument's cell through a shared result (the
/// parameter's type, the result's, the body) and the contracts it is given,
/// one per dialect and one silent about it: each of the first two claims the
/// argument is left as it was, which the result's holder decides.
const CELL_LENDERS: [(&str, &str, &str); 3] = [
    ("Cell<i32>", "&Cell<i32>", "&*p"),
    ("Box<Cell<i32>>", "&Box<Cell<i32>>", "&*p"),
    ("HB", "&Box<Cell<i32>>", "&p.c"),
];

const CELL_LENDER_CALLEES: [&str; 4] = ["*p == old(*p)", "^p == *p", "true", "resolve(p)"];

/// A callee storing its `&mut i32` argument in another parameter's referent
/// (the other parameter's type, the store), and the contracts it is given
/// (the last silent about `p`): the value `p` is left with is the holder's
/// of the other parameter to decide, so a claim of it is false of a holder
/// that writes through it.
const PARAM_LENDERS: [(&str, &str); 3] = [
    ("&mut Option<&'a mut i32>", "*slot = Some(p)"),
    ("&mut Vec<&'a mut i32>", "slot.push(p)"),
    ("&mut Option<&'a mut i32>", "let _ = slot.insert(p)"),
];

/// Clauses of a [`PARAM_LENDERS`] function: every claim of `p`'s final value
/// is false (a holder of the other parameter writes through it after the
/// call); the rest are read.
const LENT_INTO_PARAM_TEMPLATES: [ShapeTemplate; 7] = [
    ("^p == *p + {k}", |_, _| false),
    ("*p == old(*p) + {k}", |_, _| false),
    ("(^p)@ == (*p)@ + {k}", |_, _| false),
    ("resolve(p) || {k} > 1", |_, _| false),
    ("unchanged(p) || {k} > 1", |_, _| false),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

const PARAM_LENDER_CALLEES: [&str; 4] = ["*p == old(*p)", "^p == *p", "true", "resolve(p)"];

/// A caller of a [`PARAM_LENDERS`] callee that stores 7 through the stored
/// borrow: `p` is left 7, not as the callee claims.
const LENT_INTO_PARAM_CALLER_TEMPLATES: [ShapeTemplate; 6] = [
    ("^p == 7 + {k}", |_, k| k == 0),
    ("^p == *p + {k}", |pt, k| pt.a0 + k == 7),
    ("*p == old(*p) + {k}", |pt, k| pt.a0 + k == 7),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
    ("{k} + 1 > {k}", |_, _| true),
];

/// `*p = x` on a `p: &mut i32`, and a final value read inside `old(..)`:
/// the entry state has no final value, so each such clause is refused. The
/// evaluator reads a prophecy as state-independent (`old(^p)` is `^p`, and
/// `old(resolve(p))` is `old(*p) == ^p`), so `old(^p) == x` is true and
/// refused; the rest are read.
const ENTRY_FINAL_TEMPLATES: [ShapeTemplate; 7] = [
    ("old(resolve(p))", |pt, _| pt.x == pt.a0),
    ("old(resolve(p) && {k} == 0)", |pt, k| {
        pt.x == pt.a0 && k == 0
    }),
    ("old(structural_resolve(p) || {k} > 1)", |pt, _| {
        pt.x == pt.a0
    }),
    ("old(^p) == x + {k}", |_, k| k == 0),
    ("^p == x + {k}", |_, k| k == 0),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

/// A claim over the returned value, which holds `p`'s borrow: the caller
/// decides that borrow's final value after the call, so its `resolve` at the
/// return is no fact of the function (D-126). Spelled through the closure
/// postcondition's binder (`|r| ..`, whose `r` is `result` read unannotated),
/// through a `let`, and on `result` directly; and a claim that every borrow a
/// quantifier ranges over is resolved, whose binder's `^q` was its `*q`.
/// `{out}` is the return type.
const RESULT_RESOLVE_TEMPLATES: [ShapeTemplate; 8] = [
    ("|r: {out}| resolve(r) || {k} == 1", |_, k| k == 1),
    ("|r| resolve(r) || {k} == 1", |_, k| k == 1),
    (
        "|r: {out}| { let t = r; resolve(t) } || {k} == 1",
        |_, k| k == 1,
    ),
    ("resolve(result) || {k} == 1", |_, k| k == 1),
    ("!(exists<q: &mut i32> !resolve(q)) || {k} == 1", |_, k| {
        k == 1
    }),
    ("!(exists<q: &mut i32> ^q != *q) || {k} == 1", |_, k| k == 1),
    ("|r: {out}| {k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

/// The bodies of [`RESULT_RESOLVE_TEMPLATES`]: each returns `p`'s borrow in
/// a value of a sort the encoder reads (a borrow, an `Option` of one, a
/// value-model container of one).
const RESULT_RESOLVE_BODIES: [(&str, &str); 3] = [
    ("&mut i32", "p"),
    ("Option<&mut i32>", "Some(p)"),
    ("Vec<&mut i32>", "vec![p]"),
];

/// `*h.m = x; h.v = x` on `h: &mut HM<'_>`, whose field `m` is a borrow the
/// caller keeps: after the call the caller may write through it, so the
/// final value of the borrow `h.m` (however spelled: through the field, the
/// referent, the referent's final value, a branch choosing the holder, or
/// `resolve`) is the caller's to decide, and every claim of it is false. The
/// final value of the OUTER borrow's scalar field (`(^h).v`) is the body's.
const HELD_FINAL_TEMPLATES: [ShapeTemplate; 9] = [
    ("^h.m == x + {k}", |_, _| false),
    ("^(h.m) == x + {k}", |_, _| false),
    ("^(*h).m == x + {k}", |_, _| false),
    ("^(^h).m == x + {k}", |_, _| false),
    ("^(if x > 0 { *h } else { *h }).m == x + {k}", |_, _| false),
    ("resolve(h.m) || {k} > 1", |_, _| false),
    ("(^h).v == x + {k}", |_, k| k == 0),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

/// The same borrow's final value read by a PRECONDITION of `*h.m = 5` on
/// `h: &mut H1<'_>` ensuring `x == 5`: a caller that writes `x` through the
/// borrow after the call satisfies every such precondition with any `x`, so
/// each is false; a precondition over `x` alone decides it. `H1` has the one
/// field: the named-field getter is the path on which the encoder read
/// `^h.m` as the body's write (`(^h).m`) and proved `x == 5`.
const HELD_FINAL_REQUIRES_TEMPLATES: [ShapeTemplate; 8] = [
    ("^h.m == x + {k}", |_, _| false),
    ("^(h.m) == x + {k}", |_, _| false),
    ("^(*h).m == x + {k}", |_, _| false),
    ("^(^h).m == x + {k}", |_, _| false),
    ("resolve(h.m) && *h.m == x + {k}", |_, _| false),
    ("x == 5 + {k}", |_, k| k == 0),
    ("x + {k} == 5 && 0 < 1", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0) && x == 5", |_, _| true),
];

/// `*h.{f} = x` on a ONE-field holder `h` (each of [`HELD_CURRENT_HOLDERS`]),
/// read as the value `h` is left with: the borrow it holds has current `x`,
/// where it had `a0` at entry, so every claim that the held borrow's current
/// did not change is false. A one-field referent is a record like any other
/// and its field write reaches `^h` (D-184).
const HELD_CURRENT_TEMPLATES: [ShapeTemplate; 9] = [
    ("old(*h.{f}) == *h.{f} + {k}", |pt, k| pt.a0 == pt.x + k),
    ("*h.{f} == *old(h.{f}) + {k}", |pt, k| pt.x == pt.a0 + k),
    ("h.{f} == old(h.{f}) || {k} == 1", |_, k| k == 1),
    ("(^h).{f} == (*h).{f} || {k} == 1", |_, k| k == 1),
    ("*(^h).{f} == *(*h).{f} + {k}", |pt, k| pt.x == pt.a0 + k),
    ("*(^h).{f} == x + {k}", |_, k| k == 0),
    ("*h.{f} == x + {k} && old(*h.{f}) == old(*h.{f})", |_, k| {
        k == 0
    }),
    ("{k} == 0", |_, k| k == 0),
    ("(0 < 1 + {k}) == (1 + {k} > 0)", |_, _| true),
];

/// The one-field holders of [`HELD_CURRENT_TEMPLATES`]: a named field, a
/// tuple struct and a one-tuple, each with its field's name.
const HELD_CURRENT_HOLDERS: [(&str, &str); 3] =
    [("H1<'_>", "m"), ("N1<'_>", "0"), ("(&mut i32,)", "0")];

/// A `proof_assert!` after a write, read at its program point (D-185): `v`
/// is the pointee copied before the write (`a0` at entry), `{cur}` the
/// pointee after it (`x`), each in the spelling of one of
/// [`WRITE_ASSERT_BODIES`]. Every claim that the copy or the current pointee
/// is the other, or that the current pointee is still the entry one, is
/// false: the grid has points with `a0 != x`. The second precondition of
/// each case pins the entry pointee away from `x` (`{cur} != x` at entry),
/// under which `v != {cur}` holds.
const WRITE_ASSERT_TEMPLATES: [ShapeTemplate; 7] = [
    ("{cur} == x + {k}", |_, k| k == 0),
    ("v == {cur} + {k}", |pt, k| pt.a0 == pt.x + k),
    ("v == x + {k}", |pt, k| pt.a0 == pt.x + k),
    ("{cur} == v + {k}", |pt, k| pt.x == pt.a0 + k),
    ("v != {cur} || {k} == 1", |pt, k| pt.a0 != pt.x || k == 1),
    ("v + {k} == v", |_, k| k == 0),
    ("{k} == 0", |_, k| k == 0),
];

/// The bodies of [`WRITE_ASSERT_TEMPLATES`]: the parameters, the current
/// pointee's spelling, the write, and any callee the write calls. Each copies
/// the pointee into `v`, writes `x` over it, and asserts the claim: through a
/// plain `&mut i32`, through a borrow a one-field holder or a one-tuple holds,
/// and through a contracted callee.
const WRITE_ASSERT_BODIES: [(&str, &str, &str, &str); 5] = [
    ("p: &mut i32", "*p", "*p = x;", ""),
    ("h: &mut H1<'_>", "*h.m", "*h.m = x;", ""),
    ("h: &mut (&mut i32,)", "*h.0", "*h.0 = x;", ""),
    (
        "p: &mut i32",
        "*p",
        "NAME_set(p, x);",
        "\n#[ensures(^p == x)]\nfn NAME_set(p: &mut i32, x: i32) {\n    *p = x;\n}\n",
    ),
    (
        "h: &mut H1<'_>",
        "*h.m",
        "NAME_set(h, x);",
        "\n#[ensures(*(^h).m == x)]\nfn NAME_set(h: &mut H1<'_>, x: i32) {\n    *h.m = \
         x;\n}\n",
    ),
];

/// A `proof_assert!` reading a pointee where more than one write may be
/// the one it sees (D-186): `{cur}` is `*p` at the assertion, `v` the entry
/// pointee copied first (`a0`). Each holds at a point for the pointee value
/// `cur` the body may leave there.
type JoinedTemplate = (&'static str, fn(i128, i128, i128, i128) -> bool);

/// The claims of [`JOINED_WRITE_ASSERT_BODIES`], each read as
/// `holds(v, cur, x, k)`.
const JOINED_WRITE_ASSERT_TEMPLATES: [JoinedTemplate; 6] = [
    ("*p == x + {k}", |_, cur, x, k| cur == x + k),
    ("*p == x || *p == x + 1 + {k}", |_, cur, x, k| {
        cur == x || cur == x + 1 + k
    }),
    ("v == *p + {k}", |v, cur, _, k| v == cur + k),
    ("*p != x + 1 || {k} == 1", |_, cur, x, k| {
        cur != x + 1 || k == 1
    }),
    ("*p == x + 1 + {k}", |_, cur, x, k| cur == x + 1 + k),
    ("{k} == 0", |_, _, _, k| k == 0),
];

/// Bodies whose assertion (`ASSERT`, or the end of the body) may see more
/// than one write: two writes joining at an `if` (with and without an
/// `else`, over a `bool` and a float condition), at a `match` arm whose
/// value does not fit in `i64` (`1 << 100`, `i128::MIN`), a write a loop's
/// back edge carries into the next iteration (`while`, and `for` with
/// `*p += 1`), a copy taken through a shared reborrow before the write, and
/// a join overwritten by one store after it. Each copies the entry pointee
/// into `v` first, and gives the values `*p` may hold at the assertion for
/// `x`: `x` where the first write is seen, `x + 1` where the second is.
const JOINED_WRITE_ASSERT_BODIES: [(&str, fn(i128) -> Vec<i128>); 9] = [
    ("let v = *p;\n    *p = x;\n    if c { *p = x + 1; }\n    ASSERT", |x| {
        vec![x, x + 1]
    }),
    (
        "let v = *p;\n    *p = x;\n    if c { *p = x + 1; } else { *p = x; }\n    ASSERT",
        |x| vec![x, x + 1],
    ),
    ("let v = *p;\n    *p = x;\n    if f > 0.5 { *p = x + 1; }\n    ASSERT", |x| {
        vec![x, x + 1]
    }),
    (
        "let v = *p;\n    *p = x;\n    match w {\n        0x10000000000000000000000000u128 => { *p = \
         x + 1; }\n        _ => {}\n    }\n    ASSERT",
        |x| vec![x, x + 1],
    ),
    (
        "let v = *p;\n    *p = x;\n    match z {\n        \
         -170141183460469231731687303715884105728i128 => { *p = x + 1; }\n        _ => {}\n    \
         }\n    ASSERT",
        |x| vec![x, x + 1],
    ),
    (
        "let v = *p;\n    *p = x;\n    let mut i = 0u32;\n    while i < n {\n        ASSERT\n        \
         *p = x + 1;\n        i += 1;\n    }",
        |x| vec![x, x + 1],
    ),
    (
        "let v = *p;\n    *p = x;\n    for _i in 0..n {\n        ASSERT\n        *p += 1;\n    }",
        |x| vec![x, x + 1, x + 2],
    ),
    (
        "let r: &i32 = &*p;\n    let v = *r;\n    *p = x + 1;\n    ASSERT",
        |x| vec![x + 1],
    ),
    (
        "let v = *p;\n    *p = x;\n    if c { *p = x + 7; }\n    *p = x + 1;\n    ASSERT",
        |x| vec![x + 1],
    ),
];

/// A `proof_assert!` reading through a pointer `r` that may be RE-TARGETED
/// after a store through it (D-187): `{k}` the offset, `v` the entry value of
/// `*q` copied first (`b0`), `*r` the value read through `r` at the assertion.
/// Each holds as `holds(v, cur, x, k)` for the value `cur` the body may leave
/// behind `r` there. The claims of [`RETARGET_ASSERT_BODIES`].
const RETARGET_ASSERT_TEMPLATES: [JoinedTemplate; 5] = [
    ("*r == x + {k}", |_, cur, x, k| cur == x + k),
    ("*r == x || *r == v + {k}", |v, cur, x, k| {
        cur == x || cur == v + k
    }),
    ("*r == x + 1 + {k}", |_, cur, x, k| cur == x + 1 + k),
    ("*r != v + {k} || *r == x", |v, cur, x, k| {
        cur != v + k || cur == x
    }),
    ("{k} == 0", |_, _, _, k| k == 0),
];

/// Bodies whose assertion (`ASSERT`) reads through `r` after `*r = x`, with
/// `r` re-targeted to `q` after the store on some path (under an `if`,
/// unconditionally, in a wide `match` arm, in a loop body after the
/// assertion), before the store, or before a second store. Each gives the
/// values `*r` may hold at the assertion from the grid point: `x` (or `x + 1`)
/// where the stored value is seen, `b0` where `r` points at `*q`.
const RETARGET_ASSERT_BODIES: [(&str, fn(&ShapePoint) -> Vec<i128>); 6] = [
    (
        "let v = *q;\n    let mut r: &mut i32 = p;\n    *r = x;\n    if c { r = q; }\n    ASSERT",
        |pt| vec![pt.x, pt.b0],
    ),
    (
        "let v = *q;\n    let mut r: &mut i32 = p;\n    *r = x;\n    r = q;\n    ASSERT",
        |pt| vec![pt.b0],
    ),
    (
        "let v = *q;\n    let mut r: &mut i32 = p;\n    if c { r = q; }\n    *r = x;\n    ASSERT",
        |pt| vec![pt.x],
    ),
    (
        "let v = *q;\n    let mut r: &mut i32 = &mut *p;\n    *r = x;\n    match w {\n        \
         0x10000000000000000000000000u128 => { r = &mut *q; }\n        _ => {}\n    }\n    ASSERT",
        |pt| vec![pt.x, pt.b0],
    ),
    (
        "let v = *q;\n    let mut r: &mut i32 = &mut *p;\n    *r = x;\n    let mut i = 0u32;\n    \
         while i < n {\n        ASSERT\n        r = &mut *q;\n        i += 1;\n    }",
        |pt| vec![pt.x, pt.b0],
    ),
    (
        "let v = *q;\n    let mut r: &mut i32 = p;\n    *r = x;\n    if c { r = q; }\n    *r = x + \
         1;\n    ASSERT",
        |pt| vec![pt.x + 1],
    ),
];

/// A `proof_assert!` in a loop body reading a plain local `y` (D-187): each
/// holds as `holds(v, cur, x, k)` for the value `cur` the loop may have
/// left in `y` at the assertion on SOME iteration (`v` is unused). The claims
/// of [`LOOP_LOCAL_ASSERT_BODIES`].
const LOOP_LOCAL_ASSERT_TEMPLATES: [JoinedTemplate; 5] = [
    ("y == x + {k}", |_, cur, x, k| cur == x + k),
    ("y == x || y == x + 1 + {k}", |_, cur, x, k| {
        cur == x || cur == x + 1 + k
    }),
    ("y != x + 1 || {k} == 1", |_, cur, x, k| {
        cur != x + 1 || k == 1
    }),
    ("y == x + 1 + {k}", |_, cur, x, k| cur == x + 1 + k),
    ("{k} == 0", |_, _, _, k| k == 0),
];

/// Loop bodies whose assertion (`ASSERT`) reads `y`: written later in the
/// body (`while`, `for`, `loop` with `break` and a conditional write),
/// computed from the counter, set afresh before the read, and written before
/// the read and reset after it. Each gives the values `y` may hold at the
/// assertion on some iteration for `x`.
const LOOP_LOCAL_ASSERT_BODIES: [(&str, fn(i128) -> Vec<i128>); 6] = [
    (
        "let mut y = x;\n    let mut i = 0u32;\n    while i < n {\n        ASSERT\n        y = x + \
         1;\n        i += 1;\n    }",
        |x| vec![x, x + 1],
    ),
    (
        "let mut i = 0u32;\n    while i < n && i < 2 {\n        let y = x + i as i32;\n        \
         ASSERT\n        i += 1;\n    }",
        |x| vec![x, x + 1],
    ),
    (
        "let mut y = x;\n    for _k in 0..n {\n        ASSERT\n        y = x + 1;\n    }",
        |x| vec![x, x + 1],
    ),
    (
        "let mut y = x;\n    let mut i = 0u32;\n    loop {\n        if i >= n { break; }\n        \
         ASSERT\n        if c { y = x + 1; }\n        i += 1;\n    }",
        |x| vec![x, x + 1],
    ),
    (
        "let mut i = 0u32;\n    while i < n {\n        let y = x;\n        ASSERT\n        i += \
         1;\n    }",
        |x| vec![x],
    ),
    (
        "let mut y = x;\n    let mut i = 0u32;\n    while i < n {\n        y = x + 1;\n        \
         ASSERT\n        y = x;\n        i += 1;\n    }",
        |x| vec![x + 1],
    ),
];

/// A claim over a loop counter `i` and its bound `n` at an assertion placed
/// before, after, or beside the loop's test (D-188), read as
/// `holds(i, n, k)`. The claims of [`LOOP_TEST_ASSERT_BODIES`].
type LoopTestTemplate = (&'static str, fn(i128, i128, i128) -> bool);

const LOOP_TEST_ASSERT_TEMPLATES: [LoopTestTemplate; 5] = [
    ("i < n || {k} == 1", |i, n, k| i < n || k == 1),
    ("i <= n || {k} == 1", |i, n, k| i <= n || k == 1),
    ("i >= n || {k} == 1", |i, n, k| i >= n || k == 1),
    ("i != n || {k} == 1", |i, n, k| i != n || k == 1),
    ("{k} == 0", |_, _, k| k == 0),
];

/// Loops whose assertion (`ASSERT`) reads the counter `i`: before a `loop`'s
/// break test, in a `while` condition block before its test, in an inner
/// loop whose test breaks the outer one by label, under an `if` before the
/// test; after the test (`while`, `loop`); after a loop a `break` can leave,
/// after a loop with `i` written since its exit, and after a loop left only
/// through its test. Each gives the values `i` may hold at the assertion for
/// a bound `n`.
const LOOP_TEST_ASSERT_BODIES: [(&str, fn(i128) -> Vec<i128>); 9] = [
    (
        "let mut i = 0u32;\n    loop {\n        ASSERT\n        if i >= n { break; }\n        i += \
         1;\n    }",
        |n| (0..=n).collect(),
    ),
    (
        "let mut i = 0u32;\n    while {\n        ASSERT\n        i < n\n    } {\n        i += \
         1;\n    }",
        |n| (0..=n).collect(),
    ),
    (
        "'outer: loop {\n        let mut i = 0u32;\n        loop {\n            ASSERT\n            \
         if i >= n { break 'outer; }\n            i += 1;\n        }\n    }",
        |n| (0..=n).collect(),
    ),
    (
        "let mut i = 0u32;\n    loop {\n        if c { ASSERT }\n        if i >= n { break; }\n        \
         i += 1;\n    }",
        |n| (0..=n).collect(),
    ),
    (
        "let mut i = 0u32;\n    while i < n {\n        ASSERT\n        i += 1;\n    }",
        |n| (0..n).collect(),
    ),
    (
        "let mut i = 0u32;\n    loop {\n        if i >= n { break; }\n        ASSERT\n        i += \
         1;\n    }",
        |n| (0..n).collect(),
    ),
    (
        "let mut i = 0u32;\n    while i < n {\n        if c { break; }\n        i += 1;\n    }\n    \
         ASSERT",
        |n| vec![0, n],
    ),
    (
        "let mut i = 0u32;\n    while i < n {\n        i += 1;\n    }\n    i = 0u32;\n    ASSERT",
        |_| vec![0],
    ),
    (
        "let mut i = 0u32;\n    while i < n {\n        i += 1;\n    }\n    ASSERT",
        |n| vec![n],
    ),
];

/// Bodies whose assertion (`ASSERT`) reads the counter `i` of a loop that
/// carries `#[invariant(i <= n)]` and has finished (D-189): inside a LATER
/// loop that writes `i` after the assertion, under a branch or in the same
/// block, so its back edge carries the write round to the assertion again
/// (`while`, `loop`, a write of `n + 1`, the two loops inside an outer one);
/// inside a later loop that writes `i` before the assertion; inside a later
/// loop that writes only its own counter; at function level with `i` written
/// after the assertion and no loop round to it; and after a loop over a
/// block-local `i` that shadows the `i` the assertion reads. Each gives the
/// values `i` may hold at the assertion for a bound `n`.
const LOOP_AFTER_LOOP_ASSERT_BODIES: [(&str, fn(i128) -> Vec<i128>); 9] = [
    (
        "let mut i = 0u32;\n    #[invariant(i <= n)]\n    while i < n {\n        i += 1;\n    }\n    \
         let mut k = 0u32;\n    while k < 2 {\n        ASSERT\n        if c { i = 0u32; }\n        \
         k += 1;\n    }",
        |n| vec![n, 0],
    ),
    (
        "let mut i = 0u32;\n    #[invariant(i <= n)]\n    while i < n {\n        i += 1;\n    }\n    \
         let mut k = 0u32;\n    while k < 2 {\n        ASSERT\n        i = 0u32;\n        k += \
         1;\n    }",
        |n| vec![n, 0],
    ),
    (
        "let mut i = 0u32;\n    #[invariant(i <= n)]\n    while i < n {\n        i += 1;\n    }\n    \
         let mut k = 0u32;\n    loop {\n        ASSERT\n        k += 1;\n        if k >= 2 { break; \
         }\n        if c { i = 0u32; }\n    }",
        |n| vec![n, 0],
    ),
    (
        "let mut i = 0u32;\n    #[invariant(i <= n)]\n    while i < n {\n        i += 1;\n    }\n    \
         let mut k = 0u32;\n    while k < 2 {\n        ASSERT\n        if c { i = n + 1; }\n        \
         k += 1;\n    }",
        |n| vec![n, n + 1],
    ),
    (
        "let mut o = 0u32;\n    while o < 1 {\n        let mut i = 0u32;\n        #[invariant(i <= \
         n)]\n        while i < n {\n            i += 1;\n        }\n        let mut k = 0u32;\n        \
         while k < 2 {\n            ASSERT\n            if c { i = 0u32; }\n            k += 1;\n        \
         }\n        o += 1;\n    }",
        |n| vec![n, 0],
    ),
    (
        "let mut i = 0u32;\n    #[invariant(i <= n)]\n    while i < n {\n        i += 1;\n    }\n    \
         let mut k = 0u32;\n    while k < 2 {\n        if c { i = 0u32; }\n        ASSERT\n        \
         k += 1;\n    }",
        |n| vec![n, 0],
    ),
    (
        "let mut i = 0u32;\n    #[invariant(i <= n)]\n    while i < n {\n        i += 1;\n    }\n    \
         let mut k = 0u32;\n    while k < 2 {\n        ASSERT\n        k += 1;\n    }",
        |n| vec![n],
    ),
    (
        "let mut i = 0u32;\n    #[invariant(i <= n)]\n    while i < n {\n        i += 1;\n    }\n    \
         ASSERT\n    i = 0u32;",
        |n| vec![n],
    ),
    (
        "let i = 0u32;\n    {\n        let mut i = 0u32;\n        #[invariant(i <= n)]\n        \
         while i < n {\n            i += 1;\n        }\n    }\n    ASSERT",
        |_| vec![0],
    ),
];

const SHAPE_PRE: &str = "x < 100 && x > -100";

fn shape_truth(holds: fn(&ShapePoint, i128) -> bool, k: i128) -> Truth {
    if shape_grid().iter().all(|point| holds(point, k)) {
        Truth::True
    } else {
        Truth::False
    }
}

fn shape_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    let push = |cases: &mut Vec<Case>, kind: ShapeKind, ensures: String, truth, source: String| {
        let kinds = parse_contract_census(&ensures).unwrap_or_default();
        let name = format!("shape_{}", cases.len());
        let source = source.replace("NAME", &name);
        cases.push(Case {
            name,
            host: Host::Shape(kind),
            body: Body::IncP,
            ensures,
            truth,
            kinds,
            source,
        });
    };
    for k in [0i128, 1] {
        for (at, (template, holds)) in METHOD_TEMPLATES.iter().enumerate() {
            let ensures = template.replace("{k}", &k.to_string());
            let truth = shape_truth(*holds, k);
            push(
                &mut cases,
                ShapeKind::MethodSelf,
                ensures.clone(),
                truth,
                format!(
                    "\nimpl S {{\n    #[requires({SHAPE_PRE})]\n    #[ensures({ensures})]\n    fn \
                     NAME(&mut self, x: i32) -> i32 {{\n        {METHOD_BODY}\n    }}\n}}\n"
                ),
            );
            let callee = METHOD_CALLEES[at % METHOD_CALLEES.len()];
            let caller = ensures.replace("self", "c");
            push(
                &mut cases,
                ShapeKind::MethodSelfCaller,
                caller.clone(),
                truth,
                format!(
                    "\nimpl S {{\n    #[requires({SHAPE_PRE})]\n    #[ensures({callee})]\n    fn \
                     NAME_callee(&mut self, x: i32) -> i32 {{\n        {METHOD_BODY}\n    \
                     }}\n}}\n#[requires({SHAPE_PRE})]\n#[ensures({caller})]\nfn NAME(c: &mut S, \
                     x: i32) -> i32 {{\n    c.NAME_callee(x)\n}}\n"
                ),
            );
        }
        for (at, (template, holds)) in SWAP_TEMPLATES.iter().enumerate() {
            let ensures = template.replace("{k}", &k.to_string());
            let truth = shape_truth(*holds, k);
            push(
                &mut cases,
                ShapeKind::TwoMut,
                ensures.clone(),
                truth,
                format!(
                    "\n#[ensures({ensures})]\nfn NAME(a: &mut i32, q: &mut i32) {{\n    let t = \
                     *a;\n    *a = *q;\n    *q = t;\n}}\n"
                ),
            );
            let callee = SWAP_CALLEES[at % SWAP_CALLEES.len()];
            push(
                &mut cases,
                ShapeKind::TwoMutCaller,
                ensures.clone(),
                truth,
                format!(
                    "\n#[ensures({callee})]\nfn NAME_callee(a: &mut i32, q: &mut i32) {{\n    let \
                     t = *a;\n    *a = *q;\n    *q = t;\n}}\n#[ensures({ensures})]\nfn NAME(a: &mut \
                     i32, q: &mut i32) {{\n    NAME_callee(a, q)\n}}\n"
                ),
            );
        }
        for (template, holds) in DESTRUCTURED_TEMPLATES {
            let ensures = template.replace("{k}", &k.to_string());
            push(
                &mut cases,
                ShapeKind::Destructured,
                ensures.clone(),
                shape_truth(holds, k),
                format!(
                    "\n#[requires(*p < 100 && *p > -100)]\n#[ensures({ensures})]\nfn NAME((p, \
                     q): (&mut i32, &mut i32)) {{\n    *p += 1;\n}}\n"
                ),
            );
        }
        for (template, holds) in TUPLE_PARAM_TEMPLATES {
            let ensures = template.replace("{k}", &k.to_string());
            push(
                &mut cases,
                ShapeKind::TupleParam,
                ensures.clone(),
                shape_truth(holds, k),
                format!(
                    "\n#[requires(*t.0 < 100 && *t.0 > -100)]\n#[ensures({ensures})]\nfn \
                     NAME(t: (&mut i32, i32)) {{\n    *t.0 += 1;\n}}\n"
                ),
            );
        }
        for (template, holds) in CLOSURE_ALIAS_TEMPLATES {
            let ensures = template.replace("{k}", &k.to_string());
            push(
                &mut cases,
                ShapeKind::ClosureAlias,
                ensures.clone(),
                shape_truth(holds, k),
                format!(
                    "\nfn NAME() {{\n    let _c = #[requires((*p)@ < 100)]\n    \
                     #[ensures({ensures})]\n    |p: &mut u32| {{\n        *p += 1;\n    }};\n}}\n"
                ),
            );
        }
        for (at, (template, holds)) in LENT_TEMPLATES.iter().enumerate() {
            let ensures = template.replace("{k}", &k.to_string());
            let (output, body) = LENT_BODIES[at % LENT_BODIES.len()];
            push(
                &mut cases,
                ShapeKind::Lent,
                ensures.clone(),
                shape_truth(*holds, k),
                format!(
                    "\n#[requires(*p < 100 && *p > -100)]\n#[ensures({ensures})]\nfn NAME(p: &mut \
                     i32) -> {output} {{\n    {body}\n}}\n"
                ),
            );
        }
        for (at, (template, holds)) in INC_CALLER_TEMPLATES.iter().enumerate() {
            let ensures = template.replace("{k}", &k.to_string());
            for (dialect, callee) in INC_CALLEES.iter().enumerate() {
                let (output, body) = LENT_BODIES[(at + dialect) % LENT_BODIES.len()];
                push(
                    &mut cases,
                    ShapeKind::LentCaller,
                    ensures.clone(),
                    shape_truth(*holds, k),
                    format!(
                        "\n#[requires(*p < 100 && *p > -100)]\n#[ensures({callee})]\nfn \
                         NAME_callee(p: &mut i32) -> {output} {{\n    {body}\n}}\n#[requires(*p \
                         < 100 && *p > -100)]\n#[ensures({ensures})]\nfn NAME(p: &mut i32) {{\n    \
                         let _ = NAME_callee(p);\n}}\n"
                    ),
                );
                // The closure's parameter is named apart from the caller's,
                // so its clause reaches the caller through the call's
                // arguments alone.
                let closure_callee = callee.replace('p', "t");
                push(
                    &mut cases,
                    ShapeKind::ClosureCaller,
                    ensures.clone(),
                    shape_truth(*holds, k),
                    format!(
                        "\n#[requires(*p < 100 && *p > -100)]\n#[ensures({ensures})]\nfn NAME(p: \
                         &mut i32) {{\n    let c = #[requires(*t < 100 && *t > -100)]\n    \
                         #[ensures({closure_callee})]\n    |t: &mut i32| {{\n        *t += 1;\n    \
                         }};\n    c(p);\n}}\n"
                    ),
                );
            }
        }
        let lent_write_callers = LENT_WRITE_CALLER_TEMPLATES
            .iter()
            .map(|template| (template, "*r = 7;\n    *r"))
            .chain(
                LENT_READ_CALLER_TEMPLATES
                    .iter()
                    .map(|template| (template, "*r")),
            );
        for ((template, holds), use_of_result) in lent_write_callers {
            let ensures = template.replace("{k}", &k.to_string());
            for callee in LENT_WRITE_CALLEES {
                push(
                    &mut cases,
                    ShapeKind::LentWriteCaller,
                    ensures.clone(),
                    shape_truth(*holds, k),
                    format!(
                        "\n#[requires(*p < 100 && *p > -100)]\n#[ensures({callee})]\nfn \
                         NAME_callee(p: &mut i32) -> &mut i32 {{\n    *p += 1;\n    p\n}}\n\
                         #[requires(*p < 100 && *p > -100)]\n#[ensures({ensures})]\nfn NAME(p: \
                         &mut i32) -> i32 {{\n    let r = NAME_callee(p);\n    \
                         {use_of_result}\n}}\n"
                    ),
                );
            }
        }
        for (template, holds) in INTERIOR_TEMPLATES {
            let ensures = template.replace("{k}", &k.to_string());
            for (ty, body) in INTERIOR_WRITES {
                let ensures = ensures.replace("{ty}", ty);
                push(
                    &mut cases,
                    ShapeKind::InteriorWrite,
                    ensures.clone(),
                    shape_truth(holds, k),
                    format!(
                        "\n#[requires({SHAPE_PRE})]\n#[ensures({ensures})]\nfn NAME(p: &mut \
                         {ty}, x: i32) {{\n    {body};\n}}\n"
                    ),
                );
            }
            for (at, (ty, output, lend)) in CELL_LENDERS.iter().enumerate() {
                let callee = CELL_LENDER_CALLEES[(at + k as usize) % CELL_LENDER_CALLEES.len()];
                let ensures = ensures.replace("{ty}", ty);
                push(
                    &mut cases,
                    ShapeKind::CellLentCaller,
                    ensures.clone(),
                    shape_truth(holds, k),
                    format!(
                        "\n#[ensures({callee})]\nfn NAME_callee(p: &mut {ty}) -> {output} {{\n    \
                         {lend}\n}}\n#[requires({SHAPE_PRE})]\n#[ensures({ensures})]\nfn \
                         NAME(p: &mut {ty}, x: i32) {{\n    let c = NAME_callee(p);\n    \
                         c.set(x);\n}}\n"
                    ),
                );
            }
        }
        for (template, holds) in LENT_INTO_PARAM_TEMPLATES {
            let ensures = template.replace("{k}", &k.to_string());
            for (other, store) in PARAM_LENDERS {
                push(
                    &mut cases,
                    ShapeKind::LentIntoParam,
                    ensures.clone(),
                    shape_truth(holds, k),
                    format!(
                        "\n#[requires(*p < 100 && *p > -100)]\n#[ensures({ensures})]\nfn \
                         NAME<'a>(p: &'a mut i32, slot: {other}) {{\n    {store};\n}}\n"
                    ),
                );
            }
        }
        for (at, (template, holds)) in LENT_INTO_PARAM_CALLER_TEMPLATES.iter().enumerate() {
            let ensures = template.replace("{k}", &k.to_string());
            for (dialect, callee) in PARAM_LENDER_CALLEES.iter().enumerate() {
                let (other, store) = PARAM_LENDERS[(at + dialect) % PARAM_LENDERS.len()];
                let local = other.trim_start_matches("&mut ").replace("'a ", "");
                let (init, take) = if local.starts_with("Vec") {
                    (
                        "Vec::new()",
                        "if let Some(r) = slot.pop() {\n        *r = 7;\n    }",
                    )
                } else {
                    ("None", "if let Some(r) = slot {\n        *r = 7;\n    }")
                };
                push(
                    &mut cases,
                    ShapeKind::LentIntoParamCaller,
                    ensures.clone(),
                    shape_truth(*holds, k),
                    format!(
                        "\n#[requires(*p < 100 && *p > -100)]\n#[ensures({callee})]\nfn \
                         NAME_callee<'a>(p: &'a mut i32, slot: {other}) {{\n    {store};\n}}\n\
                         #[requires(*p < 100 && *p > -100)]\n#[ensures({ensures})]\n\
                         fn NAME(p: &mut i32) {{\n    let mut slot: {local} = {init};\n    \
                         NAME_callee(p, &mut slot);\n    {take}\n}}\n"
                    ),
                );
            }
        }
        for (template, holds) in FIELD_TEMPLATES {
            let ensures = template.replace("{k}", &k.to_string());
            push(
                &mut cases,
                ShapeKind::MutStructField,
                ensures.clone(),
                shape_truth(holds, k),
                format!(
                    "\n#[requires({SHAPE_PRE})]\n#[ensures({ensures})]\nfn NAME(c: &mut S, x: \
                     i32) {{\n    c.a = x;\n}}\n"
                ),
            );
        }
        for (template, holds) in HELD_FINAL_TEMPLATES {
            let ensures = template.replace("{k}", &k.to_string());
            push(
                &mut cases,
                ShapeKind::HeldFinal,
                ensures.clone(),
                shape_truth(holds, k),
                format!(
                    "\n#[requires({SHAPE_PRE})]\n#[ensures({ensures})]\nfn NAME(h: &mut HM<'_>, \
                     x: i32) {{\n    *h.m = x;\n    h.v = x;\n}}\n"
                ),
            );
        }
        for (template, holds) in HELD_FINAL_REQUIRES_TEMPLATES {
            let requires = template.replace("{k}", &k.to_string());
            push(
                &mut cases,
                ShapeKind::HeldFinalRequires,
                requires.clone(),
                shape_truth(holds, k),
                format!(
                    "\n#[requires({SHAPE_PRE} && ({requires}))]\n#[ensures(x == 5i32)]\nfn \
                     NAME(h: &mut H1<'_>, x: i32) {{\n    *h.m = 5;\n}}\n"
                ),
            );
        }
        for (template, holds) in HELD_CURRENT_TEMPLATES {
            for (holder, field) in HELD_CURRENT_HOLDERS {
                let ensures = template
                    .replace("{k}", &k.to_string())
                    .replace("{f}", field);
                // With and without a precondition that reads the held borrow
                // at entry (`*h.m != x`), as the v16 case's does. Every false
                // template has a falsifying point with `a0 != x`.
                for pre in [String::new(), format!(" && *h.{field} != x")] {
                    push(
                        &mut cases,
                        ShapeKind::HeldCurrent,
                        ensures.clone(),
                        shape_truth(holds, k),
                        format!(
                            "\n#[requires({SHAPE_PRE}{pre})]\n#[ensures({ensures})]\nfn NAME(h: \
                             &mut {holder}, x: i32) {{\n    *h.{field} = x;\n}}\n"
                        ),
                    );
                }
            }
        }
        for (template, holds) in WRITE_ASSERT_TEMPLATES {
            for (params, cur, write, callee) in WRITE_ASSERT_BODIES {
                let claim = template
                    .replace("{k}", &k.to_string())
                    .replace("{cur}", cur);
                // With and without a precondition pinning the entry pointee
                // away from `x`; the truth is read over the grid points the
                // precondition admits.
                for pinned in [false, true] {
                    let pre = if pinned {
                        format!(" && {cur} != x")
                    } else {
                        String::new()
                    };
                    let truth = if shape_grid()
                        .iter()
                        .filter(|pt| !pinned || pt.a0 != pt.x)
                        .all(|pt| holds(pt, k))
                    {
                        Truth::True
                    } else {
                        Truth::False
                    };
                    push(
                        &mut cases,
                        ShapeKind::WriteThenAssert,
                        claim.clone(),
                        truth,
                        format!(
                            "{callee}\n#[requires({SHAPE_PRE}{pre})]\nfn NAME({params}, x: i32) \
                             {{\n    let v = {cur};\n    {write}\n    proof_assert!({claim});\n}}\n"
                        ),
                    );
                }
            }
        }
        for (template, holds) in JOINED_WRITE_ASSERT_TEMPLATES {
            let claim = template.replace("{k}", &k.to_string());
            for (body, values) in JOINED_WRITE_ASSERT_BODIES {
                let truth = if shape_grid().iter().all(|pt| {
                    values(pt.x)
                        .into_iter()
                        .all(|cur| holds(pt.a0, cur, pt.x, k))
                }) {
                    Truth::True
                } else {
                    Truth::False
                };
                let body = body.replace("ASSERT", &format!("proof_assert!({claim});"));
                push(
                    &mut cases,
                    ShapeKind::JoinedWriteThenAssert,
                    claim.clone(),
                    truth,
                    format!(
                        "\n#[requires({SHAPE_PRE})]\n#[allow(unused_variables, unused_assignments)]\nfn \
                         NAME(p: &mut i32, x: i32, c: bool, f: f64, w: u128, z: i128, n: u32) \
                         {{\n    {body}\n}}\n"
                    ),
                );
            }
        }
        for (template, holds) in RETARGET_ASSERT_TEMPLATES {
            let claim = template.replace("{k}", &k.to_string());
            for (body, values) in RETARGET_ASSERT_BODIES {
                let truth = if shape_grid()
                    .iter()
                    .all(|pt| values(pt).into_iter().all(|cur| holds(pt.b0, cur, pt.x, k)))
                {
                    Truth::True
                } else {
                    Truth::False
                };
                let body = body.replace("ASSERT", &format!("proof_assert!({claim});"));
                push(
                    &mut cases,
                    ShapeKind::RetargetedWriteThenAssert,
                    claim.clone(),
                    truth,
                    format!(
                        "\n#[requires({SHAPE_PRE})]\n#[allow(unused_variables, unused_assignments)]\nfn \
                         NAME<'a>(p: &'a mut i32, q: &'a mut i32, x: i32, c: bool, w: u128, n: \
                         u32) {{\n    {body}\n}}\n"
                    ),
                );
            }
        }
        for (template, holds) in LOOP_LOCAL_ASSERT_TEMPLATES {
            let claim = template.replace("{k}", &k.to_string());
            for (body, values) in LOOP_LOCAL_ASSERT_BODIES {
                let truth = if shape_grid()
                    .iter()
                    .all(|pt| values(pt.x).into_iter().all(|cur| holds(0, cur, pt.x, k)))
                {
                    Truth::True
                } else {
                    Truth::False
                };
                let body = body.replace("ASSERT", &format!("proof_assert!({claim});"));
                push(
                    &mut cases,
                    ShapeKind::LoopCarriedLocalThenAssert,
                    claim.clone(),
                    truth,
                    format!(
                        "\n#[requires({SHAPE_PRE})]\n#[allow(unused_variables, unused_assignments)]\nfn \
                         NAME(x: i32, c: bool, n: u32) {{\n    {body}\n}}\n"
                    ),
                );
            }
        }
        for (template, holds) in LOOP_TEST_ASSERT_TEMPLATES {
            let claim = template.replace("{k}", &k.to_string());
            for (body, values) in LOOP_TEST_ASSERT_BODIES {
                let truth = if (0..=3).all(|n| values(n).into_iter().all(|i| holds(i, n, k))) {
                    Truth::True
                } else {
                    Truth::False
                };
                let body = body.replace("ASSERT", &format!("proof_assert!({claim});"));
                push(
                    &mut cases,
                    ShapeKind::LoopTestThenAssert,
                    claim.clone(),
                    truth,
                    format!(
                        "\n#[requires({SHAPE_PRE})]\n#[allow(unused_variables, unused_assignments, \
                         unreachable_code)]\nfn NAME(x: i32, c: bool, n: u32) {{\n    {body}\n}}\n"
                    ),
                );
            }
        }
        for (template, holds) in LOOP_TEST_ASSERT_TEMPLATES {
            let claim = template.replace("{k}", &k.to_string());
            for (body, values) in LOOP_AFTER_LOOP_ASSERT_BODIES {
                let truth = if (0..=3).all(|n| values(n).into_iter().all(|i| holds(i, n, k))) {
                    Truth::True
                } else {
                    Truth::False
                };
                let body = body.replace("ASSERT", &format!("proof_assert!({claim});"));
                push(
                    &mut cases,
                    ShapeKind::LoopAfterLoopThenAssert,
                    claim.clone(),
                    truth,
                    format!(
                        "\n#[requires({SHAPE_PRE} && n < 1000)]\n#[allow(unused_variables, \
                         unused_assignments, unreachable_code)]\nfn NAME(x: i32, c: bool, n: u32) \
                         {{\n    {body}\n}}\n"
                    ),
                );
            }
        }
        for (template, holds) in ENTRY_FINAL_TEMPLATES {
            let ensures = template.replace("{k}", &k.to_string());
            push(
                &mut cases,
                ShapeKind::EntryFinal,
                ensures.clone(),
                shape_truth(holds, k),
                format!(
                    "\n#[requires({SHAPE_PRE})]\n#[ensures({ensures})]\nfn NAME(p: &mut i32, x: \
                     i32) {{\n    *p = x;\n}}\n"
                ),
            );
        }
        for (template, holds) in RESULT_RESOLVE_TEMPLATES {
            for (out, body) in RESULT_RESOLVE_BODIES {
                let ensures = template
                    .replace("{k}", &k.to_string())
                    .replace("{out}", out);
                push(
                    &mut cases,
                    ShapeKind::ResultResolve,
                    ensures.clone(),
                    shape_truth(holds, k),
                    format!("\n#[ensures({ensures})]\nfn NAME(p: &mut i32) -> {out} {{\n    {body}\n}}\n"),
                );
            }
        }
    }
    cases
}

// ---- Running the driver ---------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Verdict {
    Verified,
    Failed,
    Unknown,
    Error,
    /// No verdict line: refused before verification.
    Refused,
}

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn write_crate(cases: &[Case], dir: &Path) {
    std::fs::create_dir_all(dir.join("src")).expect("oracle crate dir");
    let trust_wp = workspace().join("crates/trust-wp");
    std::fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"contract-oracle\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n\
             [workspace]\n\n[dependencies]\ntrust-wp = {{ path = {:?} }}\n\n[lib]\npath = \
             \"src/lib.rs\"\ndoctest = false\n",
            trust_wp
                .canonicalize()
                .expect("trust-wp crate")
                .display()
                .to_string()
        ),
    )
    .expect("oracle manifest");
    let lock = std::fs::read_to_string(
        workspace().join("tests/fixtures/reference_level_contracts/Cargo.lock"),
    )
    .expect("fixture lock")
    .replace(
        "name = \"reference-level-contracts-fixture\"",
        "name = \"contract-oracle\"",
    );
    std::fs::write(dir.join("Cargo.lock"), lock).expect("oracle lock");
    let mut source = String::from(PRELUDE);
    for case in cases {
        source.push_str(&case.source);
    }
    std::fs::write(dir.join("src/lib.rs"), source).expect("oracle source");
}

/// How many crates the corpus is split over, each verified by its own driver
/// process at once.
const CRATES: usize = 4;

/// The verdict line a case's function prints under.
fn verdict_name(case: &Case) -> String {
    match case.host {
        Host::Closure | Host::Shape(ShapeKind::ClosureAlias) => {
            format!("{}::{{closure#0}}", case.name)
        }
        Host::Shape(ShapeKind::MethodSelf) => format!("S::{}", case.name),
        _ => case.name.clone(),
    }
}

fn run_driver(cases: &[Case]) -> (BTreeMap<String, Verdict>, String) {
    let chunk = cases.len().div_ceil(CRATES);
    let wrapper = trust_wp_rustc_path();
    let children: Vec<_> = cases
        .chunks(chunk)
        .enumerate()
        .map(|(at, part)| {
            let dir = workspace().join(format!("target/contract_oracle/crate_{at}"));
            let _ = std::fs::remove_dir_all(&dir);
            write_crate(part, &dir);
            // Every function gets its share of the crate budget without the
            // floor oversubscribing it, so no verdict is cut short by a
            // failure elsewhere.
            let timeout = (part.len() * 6 + 60).to_string();
            // Each child writes its own file: a pipe read after another
            // child's exit could fill and stall the child writing it.
            let log = dir.with_extension("stderr");
            let sink = std::fs::File::create(&log).expect("oracle crate log");
            let child = nested_cargo("check")
                .current_dir(&dir)
                .env(
                    "CARGO_TARGET_DIR",
                    trust_wp_rustc_fixture_target_dir(&format!("contract_oracle_{at}")),
                )
                .env("RUSTC_WRAPPER", &wrapper)
                .env("TRUST_WP_ARGS", format!("--verify --timeout {timeout}"))
                .args(["--quiet", "--locked", "--lib"])
                .stdout(std::process::Stdio::null())
                .stderr(sink)
                .spawn()
                .expect("targo check of an oracle crate");
            (child, log)
        })
        .collect();
    let mut stderr = String::new();
    for (mut child, log) in children {
        child.wait().expect("oracle crate run");
        let crate_stderr = std::fs::read_to_string(&log).unwrap_or_default();
        // A crate rustc refuses gives none of its cases a verdict, and each
        // would count as refused: the corpus must type-check.
        assert!(
            !crate_stderr.contains("error["),
            "an oracle crate does not compile ({}):\n{crate_stderr}",
            log.display()
        );
        stderr.push_str(&crate_stderr);
    }
    let mut verdicts = BTreeMap::new();
    for case in cases {
        let prefix = format!("trust-wp: {} ", verdict_name(case));
        let verdict = stderr
            .lines()
            .find_map(|line| line.strip_prefix(&prefix))
            .map_or(Verdict::Refused, |rest| {
                if rest.starts_with("verified") {
                    Verdict::Verified
                } else if rest.starts_with("FAILED") {
                    Verdict::Failed
                } else if rest.starts_with("unknown") {
                    Verdict::Unknown
                } else {
                    Verdict::Error
                }
            });
        verdicts.insert(case.name.clone(), verdict);
    }
    (verdicts, stderr)
}

// ---- Bundle claims ------------------------------------------------------------------

/// Claims over a quantified integer for the forms rustc refuses in a clause
/// (`box p`), each with its truth: `t` is bound to `q + extra`, so
/// `t + 1 > q + extra + k` holds exactly when `k <= 0`.
fn bundle_claims() -> Vec<(String, Truth)> {
    let mut claims = Vec::new();
    // `0 < 1 ==> a + 1 > b + k` is the shape native replay's linear rules
    // decide: true for `k <= 0` when `a` is `b`.
    for k in [0, 1, -1] {
        let truth = if k <= 0 { Truth::True } else { Truth::False };
        for extra in [0, 2, 7] {
            claims.push((
                format!("forall<q: Int> {{ let box t = q + {extra}; 0 < 1 ==> t + 1 > q + {extra} + {k} }}"),
                truth,
            ));
        }
        claims.push((
            format!("forall<q: Int> {{ let box (t) = q; 0 < 1 ==> t + 1 > q + {k} }}"),
            truth,
        ));
        claims.push((
            format!("forall<q: Int> {{ let (box t, u) = (q, q); 0 < 1 ==> t + 1 > u + {k} }}"),
            truth,
        ));
    }
    claims
}

/// Claims a pointer summary fact on the obligation's `p`, `q` decides, each
/// with its truth as contract-syntax.md reads the fact: it is about a name
/// free in the claim or bound by the universal quantifiers the claim opens
/// with AS WRITTEN. A quantifier under a `let`, a `match`, an `if let`, an
/// `exists` or a connective binds another value, which the fact says nothing
/// of, and ranges over the value that is `q` too.
fn fact_claims() -> Vec<(String, Fact, Truth)> {
    let mut claims = Vec::new();
    for (fact, relation) in [(Fact::Disjoint, "!="), (Fact::Equal, "==")] {
        for payload in [
            format!("forall<p: &Int> forall<q: &Int> p {relation} q"),
            format!("forall<q: &Int> forall<p: &Int> p {relation} q"),
            format!("forall<p: &Int> forall<q: &Int> q {relation} p"),
        ] {
            claims.push((payload, fact, Truth::True));
        }
        for payload in [
            format!("{{ let r = q; forall<p: &Int> p {relation} r }}"),
            format!("match q {{ r => forall<p: &Int> p {relation} r }}"),
            format!("if let r = q {{ forall<p: &Int> p {relation} r }} else {{ false }}"),
            format!("match (q,) {{ (r,) => forall<p: &Int> p {relation} r }}"),
            format!("match (q, 0) {{ (r, _) => forall<p: &Int> p {relation} r }}"),
            format!("forall<q: &Int> {{ let r = q; forall<p: &Int> p {relation} r }}"),
            format!("forall<q: &Int> (0 < 1 && forall<p: &Int> p {relation} q)"),
            format!("forall<q: &Int> !(exists<p: &Int> !(p {relation} q))"),
        ] {
            claims.push((payload, fact, Truth::False));
        }
    }
    claims
}

#[derive(Debug, Clone, Copy)]
enum Fact {
    Disjoint,
    Equal,
}

fn verify_bundle_claim(payload: &str, fact: Option<Fact>) -> Verdict {
    let mut obligation = BundleObligation::new(
        "claim",
        BundleObligationKind::Postcondition,
        "contract_oracle::claim",
        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, payload),
    );
    if let Some(fact) = fact {
        let (left, right) = ("p".to_string(), "q".to_string());
        let kind = match fact {
            Fact::Disjoint => {
                BundleSummaryFactKind::PointerProvenanceDisjointBinding { left, right }
            }
            Fact::Equal => BundleSummaryFactKind::PointerProvenanceEqBinding { left, right },
        };
        obligation = obligation.with_summary_fact(BundleSummaryFact::new(
            "fact",
            "tMIR",
            "dep_crate",
            "dep_crate::summary_source",
            kind,
            BundleDigest::new("sha256", format!("{:0<64}", "f")),
        ));
    }
    let request = VerifyBundleRequest::new(
        "contract-oracle",
        BundleProducer::new("tRust"),
        BundleTarget::new("contract_oracle"),
    )
    .with_obligation(obligation);
    match NativeTrustWpBundleVerifier.verify_bundle(request).status {
        VerifyBundleStatus::Verified => Verdict::Verified,
        VerifyBundleStatus::Failed => Verdict::Failed,
        _ => Verdict::Refused,
    }
}

// ---- The test -----------------------------------------------------------------------

#[test]
#[timeout(3_600_000)]
fn the_driver_verifies_no_false_generated_contract_and_the_corpus_covers_every_kind() {
    let mut cases = generate();
    let (verdicts, stderr) = run_driver(&cases);
    assert!(
        verdicts
            .values()
            .any(|verdict| *verdict != Verdict::Refused),
        "the oracle crate produced no verdict at all: {stderr}"
    );
    let mut verdicts = verdicts;
    for (payload, truth) in bundle_claims() {
        let name = format!("bundle_{}", cases.len());
        verdicts.insert(name.clone(), verify_bundle_claim(&payload, None));
        cases.push(Case {
            name,
            host: Host::BundleFact,
            body: Body::IncP,
            kinds: parse_contract_census(&payload).expect("bundle claim parses"),
            ensures: payload,
            truth,
            source: String::new(),
        });
    }
    for (payload, fact, truth) in fact_claims() {
        let name = format!("bundle_{}", cases.len());
        verdicts.insert(name.clone(), verify_bundle_claim(&payload, Some(fact)));
        cases.push(Case {
            name,
            host: Host::BundleFact,
            body: Body::IncP,
            kinds: parse_contract_census(&payload).expect("fact claim parses"),
            ensures: format!("{payload} [{fact:?} p, q]"),
            truth,
            source: String::new(),
        });
    }

    let mut violations = Vec::new();
    let mut verified_true: BTreeMap<NodeKind, usize> = BTreeMap::new();
    let mut false_or_refused: BTreeMap<NodeKind, usize> = BTreeMap::new();
    let mut hosts: BTreeMap<Host, (usize, usize)> = BTreeMap::new();
    let count = |kinds: &BTreeSet<NodeKind>, map: &mut BTreeMap<NodeKind, usize>| {
        for kind in kinds {
            *map.entry(*kind).or_default() += 1;
        }
    };
    let mut tally: BTreeMap<(Truth, Verdict), usize> = BTreeMap::new();
    for case in &cases {
        let verdict = verdicts[&case.name];
        *tally.entry((case.truth, verdict)).or_default() += 1;
        let host = hosts.entry(case.host).or_default();
        match (case.truth, verdict) {
            (Truth::False, Verdict::Verified) => violations.push(format!(
                "{} ({:?}) VERIFIED although a grid point falsifies it: ensures `{}`\n{}",
                case.name, case.host, case.ensures, case.source
            )),
            (Truth::True, Verdict::Verified) => {
                count(&case.kinds, &mut verified_true);
                host.0 += 1;
            }
            (Truth::False, _) | (_, Verdict::Refused | Verdict::Error) => {
                count(&case.kinds, &mut false_or_refused);
                host.1 += 1;
            }
            (Truth::True, _) => {}
        }
    }

    let mut uncovered = Vec::new();
    for kind in NodeKind::all() {
        if !kind.written_by_the_parser() {
            continue;
        }
        let verified = verified_true.get(&kind).copied().unwrap_or(0);
        let refused = false_or_refused.get(&kind).copied().unwrap_or(0);
        if verified < COVERAGE || refused < COVERAGE {
            uncovered.push(format!(
                "{kind}: {verified} verified true, {refused} false or refused"
            ));
        }
    }
    // Every lane that reads a clause, and every shape of parameters, is
    // reached both ways: a host no true case verifies in, or no false one is
    // written in, tests nothing of its reading.
    let every_host = [Host::Fn, Host::Closure, Host::BundleFact]
        .into_iter()
        .chain(Dialect::ALL.into_iter().map(Host::Caller))
        .chain(ShapeKind::ALL.into_iter().map(Host::Shape));
    for host in every_host {
        let (verified, refused) = hosts.get(&host).copied().unwrap_or((0, 0));
        if verified < COVERAGE || refused < COVERAGE {
            uncovered.push(format!(
                "host {host:?}: {verified} verified true, {refused} false or refused"
            ));
        }
    }
    eprintln!(
        "contract oracle: {} cases, verdicts by (truth, verdict): {tally:?}, by host (verified \
         true, false or refused): {hosts:?}",
        cases.len()
    );
    let mut report = String::new();
    for case in &cases {
        let _ = writeln!(
            report,
            "{}\t{:?}\t{:?}\t{:?}\t{}\t{}",
            case.name,
            case.host,
            case.truth,
            verdicts[&case.name],
            case.body.rust(),
            case.ensures
        );
    }
    let _ = std::fs::write(
        workspace().join("target/contract_oracle/report.tsv"),
        report,
    );
    assert!(
        violations.is_empty(),
        "{} false contracts verified:\n{}",
        violations.len(),
        violations.join("\n")
    );
    assert!(
        uncovered.is_empty(),
        "kinds and hosts the corpus does not cover {COVERAGE} times each way:\n{}",
        uncovered.join("\n")
    );
    let _ = UnOp::ALL;
}
