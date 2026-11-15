<!-- Copyright 2026 Andrew Yates -->
<!-- Author: Andrew Yates <andrewyates.name@gmail.com> -->
<!-- Licensed under the Apache License, Version 2.0 -->

# trust-wp Contract Syntax

Author: Andrew Yates <andrewyates.name@gmail.com>

This document describes the user-facing contract syntax re-exported by the
`trust-wp` facade, typically via `use trust_wp::*;`.

It covers contract attributes, specification macros, and the contract expression
grammar. The facade also re-exports support items used in contracts:

- `resolve` / `Resolve` — see [`crates/trust-wp-std/src/resolve.rs`](crates/trust-wp-std/src/resolve.rs)
- `DeepModel` — see [`crates/trust-wp-std/src/logic/model.rs`](crates/trust-wp-std/src/logic/model.rs)
- `Default` — re-exported for compatibility

## Overview

trust-wp provides these contract attributes and specification macros from the
facade:

| Attribute/Macro | Purpose | Special Forms |
|-----------------|---------|---------------|
| `#[requires(...)]` | Precondition | None |
| `#[ensures(...)]` | Postcondition | `result`, `old(...)` |
| `#[invariant(...)]` | Loop invariant (on the function, or on the loop) | `result` |
| `#[variant(...)]` | Termination variant | None |
| `#[logic(...)]` | Specification-only function | `open`, `open(self)`, `open(crate)`, `open(super)`, `law`, `opaque`, `prophetic` |
| `#[predicate(...)]` | Bool-returning logic helper | Same modes as `#[logic(...)]` |
| `#[law]` | Open-mode logic alias | None |
| `#[opaque]` | Hide logic body or type structure | None |
| `#[check(...)]` | Enable extra verifier modes | `terminates`, `ghost` |
| `#[terminates]` | Standalone alias for `#[check(terminates)]` | None (takes no arguments) |
| `#[builtin("name")]` | Map the item to a prover primitive | Required name argument |
| `#[open_inv_result]` | Suppress result-type invariant injection | None (takes no arguments) |
| `#[erasure(target)]` | Records the runtime counterpart of a spec-enriched item | target path or `_` |
| `#[trusted]` | Skip verification of function body | None |
| `ghost! { ... }` | Verification-only code block | None |
| `ghost_let!(...)` | Ghost binding helper | `ghost_let!(var = expr)`, `ghost_let!(mut var = expr)` |
| `snapshot!(expr)` | Capture value snapshot | None |
| `proof_assert!(expr)` | Verification-only assertion | None |
| `pearlite!(expr)` | Pearlite DSL expression | `x@` (view syntax) |
| `extern_spec! { ... }` | Specs for external functions | None |
| `#[bitwise_proof]` | Bitvector-mode compatibility marker (BV mode is always on) | None |
| `#[maintains(...)]` | Desugars to `#[requires]` + `#[ensures]` | `#[maintains(clause)]` |
| `seq![...]` | Seq literal helper for ghost/spec contexts | `seq![a, b, c]` |

### Attribute Forms

**Recommended:** Import from the facade and use the Creusot-compatible proc
macro attributes from the `trust-wp` crate:

```rust
use trust_wp::*;

#[requires(x > 0)]
#[ensures(result > x)]
fn increment(x: i32) -> i32 {
    x + 1
}
```

The same facade also exports logic helpers such as `#[predicate]` and `#[law]`,
marker attributes such as `#[check(...)]` and `#[opaque]`, plus ghost helpers
such as `ghost!` and `ghost_let!`.

This syntax is compatible with Creusot where the underlying feature exists,
enabling code to be verified by either tool. The proc macros provide IDE
support, type checking, and syntax highlighting.

> Placement: `#[invariant(...)]` may sit with the other contract attributes on
> the function, or directly on the loop in the Creusot style:
>
> ```rust
> #[invariant(i >= 0)]
> while i < n { ... }
> ```
>
> The loop form is an attribute in expression position, which rustc gates
> behind `proc_macro_hygiene`. `trust-wp <FILE.rs>` enables that gate for you,
> so both spellings work with no `#![feature(...)]` in your source. In a Cargo
> crate, add the feature attribute yourself or put the invariant on the
> function.
>
> Note: `#[invariant]` attributes support inductive loop verification with three
> checks: initialization (precondition implies invariant), preservation (invariant
> maintained across iterations), and postcondition (invariant implies ensures at
> exit). Body effects are extracted from MIR via `extract_body_effects()` in
> `mir_analysis::loops::body_effects` (in the driver crate, not included in this snapshot).

## Expression Grammar

Contract expressions are a subset of Rust expressions with specific restrictions.

### Allowed Expressions

```
contract_expr ::= binary_expr
                | unary_expr
                | paren_expr
                | if_expr
                | match_expr
                | closure_expr
                | quantifier_expr
                | literal
                | path_expr
                | call_expr
                | method_call_expr
                | field_expr
                | index_expr
                | reference_expr
                | cast_expr

binary_expr   ::= contract_expr BIN_OP contract_expr
unary_expr    ::= UNARY_OP contract_expr
paren_expr    ::= '(' contract_expr ')'
if_expr       ::= 'if' contract_expr '{' contract_expr '}' ('else' '{' contract_expr '}')?
match_expr    ::= 'match' contract_expr '{' (pattern '=>' contract_expr ',')* '}'
closure_expr  ::= ('|' params '|' | '||') contract_expr
quantifier_expr ::= ('forall' | 'exists') '<' quantifier_binding (',' quantifier_binding)* '>' contract_expr
quantifier_binding ::= IDENT (':' type_expr)?
```

### Supported Operators

**Arithmetic:**
- `+` (addition)
- `-` (subtraction)
- `*` (multiplication)
- `/` (integer division, truncating toward zero as Rust's `/` does: `-7 / 2 == -3`)
- `%` (remainder, truncating as Rust's `%` does: the result has the sign of
  the dividend, `-7 % 3 == -1` and `7 % -3 == 1`)

**Comparison:**
- `==` (equality)
- `!=` (inequality)
- `<` (less than)
- `<=` (less than or equal)
- `>` (greater than)
- `>=` (greater than or equal)

**Logical:**
- `&&` (logical AND)
- `||` (logical OR)
- `!` (logical NOT)
- `==>` (implication)

**Unary:**
- `-` (negation)
- `!` (logical NOT)

**Casts and annotations:**
- `e as T` for `T` one of `u8`, `u16`, `u32`, `u64`, `i8`, `i16`, `i32`, `i64` is
  Rust's `as` between integer types: the value of `T`'s range congruent to `e`
  modulo `2^bits` (`256 as u8 == 0`, `-1 as u32 == 4294967295`,
  `200 as i8 == -56`). An integer literal is an `i64`, so a value above
  `i64::MAX` has no literal (`18446744073709551615` is a parse error). A cast
  to any other type (`usize`, `isize`, `u128`, `i128`, floats, `char`,
  pointers, aliases) is refused as a parse error that names it.
- `(e : T)` and `let v: T = e` keep `e`'s value. For an integer type or `bool`
  they state `e`'s sort, and one that contradicts it (`((x > 0) : Int)`) is a
  parse error. So is one that contradicts the sort its name already has:
  the type a quantifier or closure binder declares, or the sort of the value
  a `let` binds (`forall<v: bool> (v : Int) > 0`, `{ let t = x > 0; (t : Int) }`,
  `forall<p: &bool> { let t = *p; (t : Int) > 0 }`). An annotation on an
  operand that has no sort of its own in the AST (a dereference, a call:
  `(*p : Int)`, `let t: Int = *p`) is checked by nothing, so a bundle claim
  that writes one is refused naming it.
- A suffixed literal must fit its suffix's type: `256u8` and `-1u8` are parse
  errors.

### Special Forms

#### `result` (ensures and invariants)

The `result` identifier refers to the return value of the function. It is
available in `#[ensures]` postconditions and `#[invariant]` loop invariants.
`old(...)` remains `#[ensures]`-only.

```rust
#[ensures(result > 0)]
fn positive() -> i32 { 42 }

#[ensures(result == x + 1)]
fn increment(x: i32) -> i32 { x + 1 }
```

#### `old(expr)` (ensures only)

The `old(expr)` form captures the value of `expr` at function entry,
before any modifications occur.

A parameter that is no `&mut` is one value in every state, so inside
`old(..)` it is itself: `old(v@ + 1)` and `forall<i: Int> .. old(v@ + i)` read
`v` as `v`.

```rust
#[ensures(result == old(x) * 2)]
fn double(x: i32) -> i32 { x * 2 }

#[ensures(result == old(v.len()) - 1)]
fn pop_and_len(v: &mut Vec<i32>) -> usize {
    v.pop();
    v.len()
}
```

#### Mutable borrow forms (`*v`, `^v`)

For mutable references, trust-wp supports RustHorn-style forms on `&mut` bindings:

- `*v` refers to the value of `v` at function entry, and `v@` (`view(v)`) to
  the view of that value, `(*v)@`: `#[requires(*p == 5)] #[ensures(*p ==
  5)]` holds of `*p = 0`.
- A postcondition that names a `&mut` parameter inside `old(..)` is read in
  the pre-Creusot dialect: `old(*v)` is the entry value, and `*v` and `v@`
  outside `old` are the value `v` is left with and its view
  (`#[ensures(*v == old(*v) + 1 && v@ == old(v@) + 1)]` holds of `*v += 1`),
  unless the clause also writes `^v` outside `old`, which keeps `*v` the
  entry value. This holds however the text reaches `v`: through a binder (`match v { q =>
  *q }`, `let q = v`, `if let q = v`, `match (v, 0) { (q, _) => .. }`), a
  branch (`*(if c { v } else { w })`) or a field of a tuple literal
  (`*(v, 0).0`), each read is `v`'s own, and so is a field of `v` itself
  (`v.f@` is `(*v).f@`, Rust's auto-deref: `self.v == x && result ==
  old(self.v)` reads `self.v` as the field `self` is left with). A read that
  reaches `v` some other way (`*t.0` of `let t = (v, 0)`, `*q` of `match
  Some(v) { Some(q) => .. }`) has no placement and is refused, as is `*x` of
  a parameter that is no reference (`x: i32`) and `^r` of a shared one,
  however spelled. So is every read of a `&mut` a parameter holds without
  being it: a binding of a destructuring parameter (`(p, q): (&mut i32, &mut
  i32)`), a field of a tuple parameter (`*t.0` of `t: (&mut i32, i32)`, and
  `*t.0.r` of `t: (W, i32)` whose `W` holds one in a field) or an element of
  an array parameter (`*a[0]` of `a: [&mut i32; 1]`), in either dialect. In a
  postcondition any other read of such a `&mut` is refused as well: a field
  through it by auto-deref (`t.0.f`, `p.f`), and the reference, or a value
  holding it, compared or handed to a function. A value beside it (`t.1`) is
  read as a by-value parameter is. A closure's parameters are read as a
  function's are.
- A write THROUGH a borrow a `&mut` parameter's referent holds (`*x.m = 5`
  of `x: &mut M` with `M { m: &mut i32 }`, one field or several, a tuple
  struct or a tuple) leaves `x` holding that borrow with a new current value,
  which the verifier does not state: a clause over the value `x` is left
  with that reads the borrow (`*(^x).m`, `(^x).m == (*x).m`, or `*x.m`
  beside `old(*x.m)`) gets no premise from the body and is not proved
  (D-184).
- When the function's result may borrow its `&mut` parameters (the return
  type is or holds a `&mut` or a raw pointer, a type whose fields reach one
  such as `Rc<T>` or `Vec<T>`, or a type the driver cannot see into: a type
  parameter, an `impl Trait`, a recursive type), the value such a parameter
  is left with is whoever holds the result's to decide. A pre-Creusot bare
  `*v` or `v@` of one has no reading and the clause is refused, in the
  function's own lane and at every call of it alike (`#[ensures(*p ==
  old(*p))]` on `fn leak(p: &mut i32) -> *mut i32` is refused, not read as
  `old(*p) == old(*p)`); state the claim over `result`, or in Creusot's
  reading (`^v`), which says which value it means. A shared reference lends
  when its holder can write through it: its referent has interior
  mutability, inline (`&Cell<T>`) or reachable some other way
  (`&Box<Cell<T>>`, a struct, tuple or `Option` holding one). A shared
  reference to a referent that carries no borrow and holds no cell (`-> &i32`)
  lends nothing.
- A `&mut` parameter whose borrow another holder may write through after
  the call by a write no prophecy of the function records has a final value
  the function cannot state: a read of it, in either dialect, is refused in
  its own lane and at every call. That is a parameter stored where another
  parameter's holder reads it after the call (`stash<'a>(p: &'a mut i32,
  slot: &mut Option<&'a mut i32>) { *slot = Some(p) }`, `v.push(p)`), decided
  from the signature as the borrow checker decides it: memory another
  parameter's holder writes (behind a `&mut`, a raw pointer or a cell, or a
  closure's capture) holds a slot at a lifetime the parameter's outlives
  (what the parameter types, the return type and an enclosing impl header
  imply, as the borrow checker assumes them well-formed), a raw-pointer
  slot, a type parameter a bound may name its lifetime in, or a projection
  that names such a lifetime (`<() as Tr<'a>>::Slot`, which may be
  `Option<&'a mut i32>`); a `'static` borrow may also go to a global. And it
  is every `&mut` parameter of a function whose result may be written
  through by interior mutability (`fn give(p: &mut Cell<i32>) ->
  &Cell<i32>`). A `&mut` result is read through its own prophecy (`^v ==
  ^result`) and keeps its reading. At a call of a standard-library (or
  other foreign) function, what the result may carry is read from the type
  the call returns: `Iterator::next` declares `Option<Self::Item>`, which
  may be anything, and on a `Range<i32>` returns `Option<i32>`, which lends
  nothing, so its `^self` is read and a `for` loop over a range keeps it.
- A `&mut` parameter over interior-mutable memory (`x: &mut Cell<i32>`, a
  referent holding a `Box<Cell<T>>`, a `&Cell<T>`, a `RefCell<T>`, or an
  `Option` of one) is written by whoever holds a shared reference into its
  referent, by routes the verifier does not track (`x.set(5)` in a loop, a
  `&Cell` copied out of the referent, a callee): a read of its final value,
  in either dialect, is refused in its own lane and at every call.
- A final value is refused by what denotes it, not by how it is spelled:
  `^v`, `final_value(v)`, `resolve(v)` (which is `*v == ^v`) by any path or
  as a method, `structural_resolve(v)`, `v.fin()`, a call of a logic function
  whose body or clauses read a final value (to a fixed point over their
  bodies), a `resolve` of a term that holds `v` (`resolve(v.c)`,
  `resolve(*v)`, `resolve((v, 0))`), and a final read of a name the clause
  binds (`exists<q: &mut T> q == v && ^q == *q`, a `match` or `let` binding)
  in a clause that names such a parameter.
- A call reads its callee's postcondition as the callee's own lane proves
  it: `swap`'s `*a == old(*b)` gives its caller `^x == *y`, not `*x == *y`.
  The callee's entry state is the call's pre-state, so `old(e)` over the
  callee's parameters is `e` with the arguments' values at the call: after
  `*x = 5; get(x)`, `get`'s `result == old(*p)` is `result == 5`, not the
  caller's entry `*x` (a closure's capture keeps its `old`: its value before
  and after the call differ). A clause whose
  reading the call cannot fix is no fact at the call (the caller then fails
  closed): one that reads an argument the driver sees only at its entry value
  (read through a reference after a store through it), one the callee's own
  lane refuses (a pre-Creusot read of a parameter its result may borrow, a
  final value another holder decides, as above), and one whose reading
  depends on a parameter type the call cannot read. A `&mut` argument the
  callee's clause does not mention is left at a value the call does not
  know. A local whose borrow a tuple, struct, enum or array holds (built
  around the borrow, or given it by a store into one of its places: `t.0 =
  &mut c`, `m.m = x`) is read stale after a store through the holder, and
  after any call or drop handed a value of it: a postcondition, a returned
  value, a call's precondition or a `proof_assert!` reading it fails closed
  (D-127, D-129).
- A caller rests on the postconditions of the local functions it calls, and
  keeps its credit only where each callee's own verification proves them: a
  callee refuted, unknown, refused or never verified withdraws the credit of
  every function that names it, directly or through other calls (D-127).
- `^v` refers to the final value of `v` when the borrow ends (postconditions
  only). A final value read inside `old(..)`, however denoted (`old(^v)`,
  `old(resolve(v))`), has no reading and is refused, in the function's own
  lane and at every call. `resolve(v)` of a borrow is `*v == ^v` wherever it
  is read, over the final value the lane names; where the lane names none (a
  loop head, a by-value parameter holding a borrow, a snapshot of one, a
  `let` binding) it is refused. It is `true` only of the variable itself
  whose type is a scalar, `()` or a shared reference to one: a struct or
  enum (its declaration may read an `Option<&mut T>` field as a scalar), an
  unannotated value (the `|r| ..` binder of a closure postcondition), a
  value-model container (`Vec`, `Seq`, `HashMap`, `Rc`, `Snapshot`, ...,
  whose element type the model erases), a tuple and a type parameter are not
  known to hold none. Any other operand is resolved at its own type (`true`
  of the integer `*x` of `x: &mut i32`, the inner borrow's `**x == ^*x` of
  `*x` of `x: &mut &mut i32` or of a field `x.m` that is a borrow), which the
  verifier cannot tell apart (`b: Box<&mut i32>` has the sort of `x: &mut
  i32`), so it is refused: `resolve(*x)`, `resolve(x.f)`, `resolve(x@)`,
  `resolve(Some(*x))`, a literal. Only a dereference of a shared reference to
  a value (`resolve(*r)` of `r: &i32`) is `true`. The final value of a
  quantifier's binder is refused unless its written type is a scalar, `()` or
  a shared reference to one: `forall<q: &mut i32> ..`, and a binder written
  without a type or with one the parser does not keep (`exists<g>` over a
  closure state, `forall<q: (&mut i32, i32)>`), so `^q` and `resolve(q)` of
  it are refused (D-126, D-127). A final value of a value held through a
  `&mut` or shared reference parameter is the final value of a borrow the
  referent holds, which the caller decides after the call. Every clause that
  reads a parameter -- a precondition as well as a postcondition, a
  `proof_assert!`, a loop invariant, and a callee's precondition at every
  call -- refuses each final read whose operand reaches the parameter through
  a dereference, a final value, a field, an element or a view, on any branch
  of an `if` or `match` or through a `let` or `match` binding
  (`^x.m`, `^(x.0)`, `^*x`, `^^x`, `^(^x).m`, `^(x[0])`, `^(x@[0])`,
  `^(if c { *x } else { *x }).m`, `resolve(x.m)`, `^s.m` of `s: &M`); a
  call site, which does not read the callee's parameter types, refuses it of
  every parameter (D-183). A `proof_assert!` or a
  loop invariant refuses every final read whose operand is no borrow named as one (a
  variable, `*` or `^` of one, or an `if`, `match` or `let` choosing among
  such), whatever the type: `^x.m`, `^x.a`, `^x[0]`, `^x[0].m`, `^(^x).m`,
  `^(if c { x } else { x }).m`. `(^x).m` is the field `x` is left with, and
  `^x@[0]` is `(^x)@[0]`, the element `x` is left with, as `^x@` is
  `(^x)@` (D-127, D-128, D-129).
- A `&mut` parameter's borrow stored into a place of another value (`t.0 =
  x`, `m.m = &mut *x`, `arr[i] = x`, `*p = x`) leaves the verifier no record
  of which borrow that place holds, so the parameter has no final value the
  function states from then on: `^x` and `resolve(x)` in its postcondition
  fail closed, whether or not the place is written through (D-79, D-128).
- A reference level is read where the text writes it. `*` of a borrow,
  parenthesized or not, is the borrowed value (`*&e`, `*(&e)` and `**(& &e)`
  are `e`, at `e`'s sort), and so is `*r` of a name a `let` binds to a borrow
  (`let r = &e; *r` is `e`). `let &t = p` and `let &mut t = p` bind `t` to
  `*p`; `let ref t = e` and `let ref mut t = e` bind `t` to a borrow of `e`,
  like `let t = &e`. In `ref x @ p` only `x` binds by reference: `p` matches
  the value itself (`let ref a @ t = e` binds `a` to a borrow of `e` and `t`
  to `e`). `ref` binds a name, and nothing else (`ref (a, b)` is refused).
- `^` of a borrow, or of a name bound to one (`^&p`, `^(&mut p)`,
  `final_value(&p)`, `let r = &p; ^r`, `let ref t = p; ^t`), is refused: `^`
  of a shared reference has no reading, and the final value of a reborrow is
  a reference. So is `^` of an operand that holds a borrow no `*` reads
  through (`^id(&p)`): the logic cannot say whether the borrow reaches the
  value `^` reads.
- An `if` or `match` whose branches are borrows at one level is read at that
  level (`*(if c { &a } else { &b })` is `if c { a } else { b }`); `*` or `^`
  of one whose branches are at different levels (`^(if c { &p } else { q
  })`) has no reading and is refused.
- The logic forms no reference: a borrow no `*` reads through is read as `e`
  where the text has `&e` (`result == &mut r.0`). A reference pattern binds
  as a `let` of it does wherever the pattern cannot fail: the first arm of a
  `match` that cannot fail, an `if let` of such a pattern, a closure
  parameter (`match p { &t => .. }` binds `t` to `*p`). In an arm that can
  fail it is read as its inner pattern (`match o { Some(&t) => .. }`). The
  driver reads these as Creusot does (a shared reference is its referent). A
  bundle claim refuses both, since it would read `e` a reference level below
  the one written.
- A name bound to another name is that name: `let q = p`, `match p { q =>
  .. }`, `if let q = p`, a tuple pattern over a tuple literal, each read as
  `p` wherever the binding reaches, and `*`, `^` and `@` of an `if`, a
  `match` or a `let` are read in each branch. Under `old(..)` a name is
  read in the entry state, so the binding stands in for a value there only
  as the operand of `*` or `^` (a reference is one value in every state) or,
  in the driver, when it names a parameter (`&mut` ones are references, the
  rest cannot change): `{ let t = x; old(t) }` is the `x` the clause is
  evaluated at, not `old(x)`.
- `(p)` in a pattern is `p` parenthesized, and `(p,)` matches what `p`
  matches, as the value `(e,)` is `e`. A closure's destructuring parameter is
  one parameter the body
  matches as `let` does: `#[ensures(|(x @ y, _z)| y == 1)]` reads `y` as the
  first field of the result, and `|((a, b), c)| b` the second field of the
  first.
- A bundle claim reads `*e` at the sort `e` references and `^e` at the sort
  a `&mut` references: `*p` of a `p: &Int` is an integer, of a `p: &bool` a
  boolean, `**p` of a `p: &&Int` an integer. A dereference of a name nothing
  makes a reference (`forall<v: bool> *v`, a free `*b`), of a reference to a
  sort native replay does not model (`&T`, `&[Int]`), or `^` of a shared
  reference, is refused naming it.
- A bundle claim reads the view `b@` (`view(b)`) of a free name as that
  integer, one view per operand however often it is written: a claim that
  reads it as anything else (`b@ == true`) is refused, and so is a view of a
  name the claim reads at a sort (`forall<v: Int> v@`).
- A pattern binds each name once (`(t, t)` is refused, as rustc refuses it)
  and reads the value it matches once, before any name it binds: `let x @ y
  = x + 1` binds both to the old `x` plus one, and `let (a, b) = (b, a)`
  swaps.
- A binder (`forall`, `exists`, `let`, a `match` arm, a closure parameter) of
  a name the contract already has, a parameter's or `result`, is another
  value: `#[ensures(forall<x: i32> x == result)]` does not hold of `fn(x:
  i32) -> i32 { x }`. The driver renames such a binder apart before it reads
  any name as a program variable, and no substitution (`result` for the
  returned value, a logic function's parameters for its arguments) captures
  a binder's name. A bundle pointer fact is about the obligation's own
  values: a name free in the claim, or bound by the universal quantifiers
  the claim opens with as written, at their first binding. Any other binder
  of the name (under an `exists`, a connective, a `let`, a `match` or an `if
  let`, or one shadowing the prefix's) binds another value the fact says
  nothing of, even where the `let` or the arm only renames a name:
  `forall<q: &Int> !(exists<p: &Int> p == q)` and `{ let r = q;
  forall<p: &Int> p != r }` are not proved by a disjointness fact on `p`,
  `q`.
- A const generic argument (a block `{ .. }` or a literal) is an expression,
  whatever it holds: `addn::<{ 2 * 3 }>(x)` and `addn::<{ 1 * 3 }>(x)` are
  different values. Any other generic argument is a type, and names which
  instance is called: `tag::<u8>()` and `tag::<u16>()` are two functions,
  neither of which the driver unfolds.
- Equality of two `&mut` depends on the lane. The driver follows Creusot: a
  `&mut` is its current and final value, and `result == &mut r.0` says both
  agree. In a bundle claim, `==` of two references is the same address:
  native replay decides it only by reflexivity or a pointer summary of the
  kind the compared values have (thin, or fat for a slice), and substitutes
  nothing through it. Two `&mut` at one address need not end at one value,
  so native replay derives no `^p == ^q` from `p == q` (nor `*p == *q`,
  which the address does give, and which is left unproved).

```rust
use trust_wp::{ensures, requires};

#[requires(*v > i32::MIN)]
#[ensures(^v == old(*v) + 1)]
fn increment_ref(v: &mut i32) {
    *v += 1;
}
```

#### Logic Function Calls

Logic function calls allow invoking `#[logic]` functions in contracts. These are
pure specification functions that have no runtime effect.

```rust
#[ensures(result == max(x, y))]
fn pick_larger(x: i32, y: i32) -> i32 { /* ... */ }

#[ensures(result == abs(x))]
fn positive(x: i32) -> i32 { /* ... */ }
```

**Syntax:**
- Simple calls: `max(x, y)`, `abs(x)`, `zero()`
- Qualified paths: `crate::specs::max(a, b)`
- Nested calls: `max(x, abs(y))`
- With expressions: `max(x + 1, y * 2)`

**Status:**
- `#[logic]` attribute: ✓ Complete (self-recursive functions supported)
- SMT encoding: ✓ Uninterpreted functions with on-demand declaration
- Self-recursive functions: ✓ Supported without `#[variant]` (mutual recursion pending)

**Limitations:**
- Mutual recursion between logic functions not yet supported
- Type parameters default to Int (type-specific sorts deferred)

#### Defining Logic Functions

Use the `#[logic]` attribute to mark pure specification helpers. Logic
functions are erased at runtime and are only available to contracts.

```rust
use trust_wp::logic;

#[logic]
fn max(x: i32, y: i32) -> i32 {
    if x >= y { x } else { y }
}
```

**Requirements:**
- No `mut` binding patterns (e.g., `mut x: T`); `&mut` references are allowed
- No `async` or `unsafe`
- Self-recursive calls are supported; mutual recursion is not yet supported

#### `#[predicate(...)]`

Use `#[predicate]` for bool-returning logic helpers. It accepts the same mode
arguments as `#[logic(...)]`, but the function must return `bool`.

```rust
use trust_wp::predicate;

#[predicate]
fn is_non_negative(x: i32) -> bool {
    x >= 0
}
```

#### `#[law]`

`#[law]` is a Creusot-compatible alias for `#[logic(open)]`. Use it when the
defining body should stay visible to callers as an axiom source.

```rust
use trust_wp::{ensures, law};

#[law]
fn triple(x: i32) -> i32 {
    x + x + x
}

#[ensures(result == triple(x))]
fn triple_runtime(x: i32) -> i32 {
    x + x + x
}
```

#### Logic Modes

`#[logic(...)]` and `#[predicate(...)]` accept the same mode arguments:

| Form | Current behavior |
|------|------------------|
| `#[logic]` / `#[predicate]` | Default mode. Same-module callers can currently use the body; outside that scope the function is treated as opaque. |
| `#[logic(open)]` | Body is visible to all callers. |
| `#[logic(open(self))]` | Same-module callers can use the body; outside that module the function is treated as opaque. |
| `#[logic(open(crate))]`, `#[logic(open(super))]` | Accepted syntax, currently normalized to open behavior. |
| `#[logic(law)]` | Alias for open-mode visibility. `#[law]` emits the same mode. |
| `#[logic(opaque)]` | Explicit alias for the default opaque behavior. |
| `#[logic(prophetic)]` | Accepted syntax. A logic function reads each `&mut` parameter as one value, so a final read inside it (`^q`, `resolve(q)`, a call of another such function) has no reading: the function gets no body, clauses or axiom, and every proof that may name it is refused. A prophetic function the verifier cannot read the body of is treated so too. |

#### `#[opaque]`

`#[opaque]` hides a logic function body or type structure from callers. On
logic functions this suppresses the defining axiom even if the logic mode would
otherwise be open.

#### `#[check(...)]`

`#[check(...)]` enables additional verifier modes. The currently recognized
forms are:

- `#[check(terminates)]` - enables recursive termination checking. Recursive
  functions must provide `#[variant(...)]`, and mutual recursion is still
  rejected.
- `#[check(ghost)]` - marks a function as a ghost helper in the current driver
  and encoding pipeline.

Unknown `#[check(...)]` modes are compile-time errors.

#### `#[erasure(target)]`

`#[erasure(target)]` records which runtime item a spec-enriched definition
corresponds to. The proc macro emits it as a `trust-wp:erasure:<target>` doc
marker, and the driver consumes it: `has_erasure_marker` / `get_erasure_targets`
(`crates/trust-wp-driver/src/attr_utils.rs`) feed erasure-pair discovery
(`crates/trust-wp-driver/src/callbacks/discovery/erasure.rs`), which resolves
each `(lhs, rhs)` `DefId` pair. Wildcard targets (`_`) are accepted and skipped,
matching Creusot's opt-out. A pair that fails the driver-side validity check is
counted as an `erasure_errors` fatal-result counter and maps to exit code 2.

#### `#[variant(...)]` (loops)

Specifies a termination variant (decreasing expression) for loops. The variant
must be non-negative while the loop continues and strictly decrease each iteration.

```rust
use trust_wp::{invariant, variant};

fn sum_to_n(n: u32) -> u32 {
    let mut i = 0;
    let mut sum = 0;
    #[invariant(sum <= i * n)]
    #[variant(n - i)]
    while i < n {
        i += 1;
        sum += i;
    }
    sum
}
```

#### `#[trusted]`

Marks a function as axiomatically correct. Preconditions are checked at call
sites, but postconditions are assumed without verifying the body. Useful for
FFI wrappers or incremental verification.

```rust
use trust_wp::{ensures, requires, trusted};

#[trusted]
#[requires(s.len() > 0)]
#[ensures(result > 0)]
fn external_hash(s: &str) -> u64 {
    // Body not verified by trust-wp
    std::collections::hash_map::DefaultHasher::new().finish()
}
```

#### `ghost! { ... }`

Marks a block as ghost (verification-only) code. Ghost blocks are erased at
compile time but verified by trust-wp. They can manipulate `Ghost<T>` values.

```rust
use trust_wp::ghost;
use trust_wp_std::ghost::Ghost;

fn example(x: i32) {
    ghost! {{
        let g: Ghost<i32> = Ghost::new(x);
        // Ghost computations for proof purposes
    }};
}
```

**Note:** Ghost/Snapshot handling is still partial, but the current pipeline
already wires constructors/accessors/deref through the std-spec table,
normalizes Ghost/Snapshot sorts into the Int-model lane, and lowers logical
`_ghost` method aliases. Runtime erasure and end-to-end ghost verification
remain incomplete (`#2209`).

#### `ghost_let!(...)`

`ghost_let!` declares a ghost binding without writing the surrounding
`Ghost::new(...)` boilerplate. It currently accepts:

- `ghost_let!(var = expr)`
- `ghost_let!(mut var = expr)`

The binding is a `Ghost<T>` under verification and is erased in normal builds.

```rust
use trust_wp::ghost_let;

fn example() {
    ghost_let!(g = 41 + 1);
    ghost_let!(mut counter = 0usize);
}
```

#### `snapshot!(expr)`

Captures a value snapshot as a `Snapshot<T>` for proof purposes. The snapshot
is zero-sized at runtime and always `Copy`.

```rust
use trust_wp::snapshot;
use trust_wp_std::ghost::Snapshot;

fn example(v: &mut Vec<i32>) {
    let original_len: Snapshot<usize> = snapshot!(v.len());
    v.push(42);
    // In verification: *original_len == v.len() - 1
}
```

#### `proof_assert!(expr)`

Inserts a verification-only assertion. Unlike `assert!`, it creates an SMT
verification condition and is completely erased at runtime.

```rust
use trust_wp::proof_assert;

fn example(x: i32, y: i32) {
    let sum = x + y;
    proof_assert!(sum == x + y);
}
```

The assertion reads the program state at its own program point. Memory
reached through a reference (a `&mut` parameter's pointee, a borrow a holder
holds, a closure's capture) is read as the last write left it, and a value
copied out of such memory keeps the value it had where it was copied:

```rust
#[requires(*x == 0)]
fn f(x: &mut i32) {
    let v = *x;
    *x = 5;
    proof_assert!(v == 0 && *x == 5); // proved
}
```

The verifier knows that value only when ONE write defines the memory at the
assertion: a whole-pointee store through the reference itself (`*x = e`), or a
store to the very place a closure's capture names, that every path to the
assertion runs last, with no back edge carrying it from one loop iteration into
the next (D-186). When two writes may reach it (`*x = 0; if c { *x = 5; }`,
whatever the condition's type, or a `match` arm), or a write and the entry
value, or a store later in a loop body that the back edge carries to an
assertion earlier in it, or a write it does not record may precede it (a store
through a borrow a holder holds, `*x.m = 5`; a field store, `x.f = 5`; a store
through an alias, `let r = &mut *x; *r = 5`; or a call or drop handed the
reference, `set(x)`), an assertion reading that memory is refused as a stale
read, and a value copied from it after the write is unknown (D-185, D-186). A
value copied through a shared borrow (`let r = &*x; let v = *r;`) is the
memory's value where it was copied, like a copy through `x`. A store's value is
read only through the pointer it went through: re-binding that pointer after
the store on some path to the assertion (`let mut p = a; *p = 0; if c { p = b;
}`, `p = &mut z`, a by-`mut` reference parameter `x = y`) makes `*p` memory the
store may not have written, and the assertion is refused as a stale read
(D-187).

An assertion in a loop body is checked at an ARBITRARY iteration, not the
first: every local the loop may change (its counter, a local written later in
the body, a by-`mut` parameter, a field of a local) holds there the value the
previous iteration left, which only the loop's condition and its
`#[invariant]`s constrain, and both are read as facts about that loop-head
value (D-187):

```rust
fn g(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    #[invariant(y == 0i32)]
    while i < n {
        proof_assert!(y == 0i32 && i < n); // proved: the invariant and the condition
        y = 5i32;
        proof_assert!(y == 5i32);          // proved
        y = 0i32;
        i += 1;
    }
}
```

Without the invariant the first assertion's `y == 0` is not proved: on the
second iteration of a loop whose body ends with `y = 5` it is false.

The loop condition is a fact only where every path has passed its test into
the body: an assertion placed before the test (`loop { proof_assert!(i < n); if
i >= n { break; } i += 1; }`, a `while { proof_assert!(i < n); i < n } { .. }`
condition block) runs on the iteration whose test fails too, and is not proved
from it. After a loop, its invariants and its negated condition are facts only
where every path left the loop through that test (not through a `break` or from
before the test), and only about locals nothing writes on any path from the
loop's head to the assertion, a path round a later loop's back edge included:
in `while k < 2 { proof_assert!(i >= n); if c { i = 0; } k += 1; }` after the
loop over `i`, the write after the assertion reaches it again on the next
iteration, so the first loop's facts about `i` are not facts there (D-188,
D-189). A fact naming a name the function binds to two locals (a shadowing
`let`, a block-local named like a parameter) is never assumed: it cannot say
which of them it is about (D-189).

#### `pearlite!(expr)`

Embeds a specification expression using Pearlite DSL syntax. Supports `x@`
(view) syntax. Erased at compile time.

```rust
use trust_wp::pearlite;

fn example(v: &Vec<i32>) {
    pearlite! { v@.len() > 0 };
}
```

**Status:** Quantifiers (`forall`, `exists`) and implication (`==>`) are
supported in `pearlite!`. Because `pearlite!` validates with `Requires`-kind
rules, `result` and `old(...)` remain unavailable there.

#### `extern_spec! { ... }`

Attaches specifications to external functions you don't own. External specs are
trusted (not verified against the implementation).

```rust
use trust_wp::extern_spec;

extern_spec! {
    impl<T> core::option::Option::<T> {
        #[requires(self.is_some())]
        #[ensures(Some(result) == old(self))]
        fn unwrap(self) -> T;
    }
}
```

**Note:** Generic types require turbofish syntax (`Option::<T>` not `Option<T>`).

#### `#[bitwise_proof]`

Compatibility marker for bitvector-mode verification. The attribute is no
longer needed to opt in: BV mode is unconditionally on, so bitwise operations
use ay's native BV theory rather than UF approximations. The driver sets
`bitwise_proof: true` for every contract
(`crates/trust-wp-driver/src/callbacks/verification/per_contract.rs`), the flag
rides the verification request (`crates/trust-wp-ay/src/verify/types/request.rs`)
and is applied by the encoder (`crates/trust-wp-ay/src/verify/pipeline.rs`). The
annotation is kept, accepted, and exported from the facade for Creusot
compile-surface parity.

#### `#[maintains(...)]`

Desugars a Creusot `maintains` clause into a matching pre/postcondition pair:
`#[maintains(P)]` emits both a `trust-wp:requires:P` and a `trust-wp:ensures:P`
doc marker, which the driver's ordinary contract discovery picks up with no
special casing. A required clause argument is expected
(`#[maintains(invariant_expr)]`); an empty attribute is a compile error.

`mut` in the clause is rewritten per side: `(mut x)` / `mut x` becomes `* x` in
the precondition (current value) and `^ x` in the postcondition (final value),
so `#[maintains(inv(mut self))]` means "`inv(*self)` on entry and `inv(^self)`
on exit". The rewrite only fires for `mut` immediately after `(` or `,` (or at
the start of the clause), so `mut` inside string literals or nested expressions
is left alone. See `crates/trust-wp-macros/src/marker_attrs.rs`.

#### `seq![...]`

Macro for constructing `Seq` literals in ghost, snapshot, and specification
contexts. `seq![a, b, c]` produces a `Seq` value usable in contracts and
logic functions.

```rust
use trust_wp::{ensures, seq};
use trust_wp_std::logic::seq::Seq;

#[ensures(result@ == seq![1, 2, 3])]
fn make_seq() -> Vec<i32> {
    vec![1, 2, 3]
}
```

### Disallowed Expressions

The following are **not** allowed in contract expressions:

| Expression | Reason |
|------------|--------|
| Assignments (`x = ...`) | Side effects |
| Loops (`loop`, `while`, `for`) | Non-termination |
| Async/await/yield | Non-determinism |
| Return/break/continue | Control flow |

> Note: `if`, `match`, blocks, and closures **are** allowed. `if` and `match`
> are encoded as ITE (if-then-else) in SMT. Blocks are allowed as containers
> for branch bodies. Closures pass through validation unchanged.

## Examples

### Preconditions

```rust
// Simple bounds check
#[requires(x > 0)]
fn positive_only(x: i32) -> i32 { x }

// Multiple conditions
#[requires(x >= 0 && x < 100)]
fn bounded(x: i32) -> i32 { x }

// Disjunction
#[requires(x == 0 || x == 1)]
fn binary_flag(x: i32) -> bool { x != 0 }

// Method calls
#[requires(v.len() > 0)]
fn first(v: &[i32]) -> i32 { v[0] }

// Field access
#[requires(p.x >= 0 && p.y >= 0)]
fn quadrant_one(p: &Point) -> bool { true }
```

### Postconditions

```rust
// Basic result constraint
#[ensures(result > 0)]
fn always_positive() -> i32 { 42 }

// Result relates to input
#[ensures(result == x + 1)]
fn increment(x: i32) -> i32 { x + 1 }

// Using old() for pre-state
#[ensures(result == old(x) * 2)]
fn double(x: i32) -> i32 { x * 2 }
```

### Combined Contracts

```rust
#[requires(x > 0)]
#[ensures(result > x)]
fn double_positive(x: i32) -> i32 { x * 2 }
```

### Conditional Expressions

`if` and `match` are allowed in contracts and encoded as ITE in SMT:

```rust
#[ensures(if x > 0 { result > 0 } else { result == 0 })]
fn abs_or_zero(x: i32) -> i32 {
    if x > 0 { x } else { 0 }
}

#[ensures(match result { Some(v) => v > 0, None => true })]
fn maybe_positive(x: i32) -> Option<i32> {
    if x > 0 { Some(x) } else { None }
}
```

### Quantified Expressions

Quantifiers are accepted directly in contract expressions:

```rust
#[requires(forall<i: i32> i >= 0 ==> i + 1 > i)]
fn quantified_precondition(x: i32) -> i32 { x }

#[ensures(exists<w: i32> w == result - x)]
fn witness(x: i32) -> i32 { x }
```

### Implication

To express "if P then Q" (logical implication), use `==>`. The `if` and
`!P || Q` forms remain equivalent alternatives when they read better in
context:

```rust
// Direct implication syntax
#[requires(x > 0 ==> y > 0)]
fn conditional(x: i32, y: i32) -> i32 { /* ... */ }

// Equivalent if-then-else form
#[requires(if x > 0 { y > 0 } else { true })]
fn conditional_if(x: i32, y: i32) -> i32 { /* ... */ }

// Equivalent boolean encoding
#[requires(!(x > 0) || y > 0)]
fn conditional_bool(x: i32, y: i32) -> i32 { /* ... */ }
```

## Error Messages

Invalid contract expressions produce compile-time errors:

```rust
// ERROR: requires: contract expressions cannot contain assignments
#[requires(x = 5)]
fn bad() {}

// ERROR: ensures: old() expects exactly 1 argument, found 2
#[ensures(result == old(x, y))]
fn also_bad(x: i32, y: i32) -> i32 { x }

// ERROR: requires: failed to parse contract: expected expression
#[requires()]
fn empty_bad() {}
```
