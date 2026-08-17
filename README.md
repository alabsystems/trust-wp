# trust-wp — Deductive Verification for Rust (Weakest Precondition)

**Author:** Andrew Yates <andrewyates.name@gmail.com>
**Version:** 0.1.1
**License:** Apache-2.0
**Copyright:** 2026 Andrew Yates

## What is trust-wp?

**trust-wp** is a deductive verification tool for Rust. The **wp** suffix stands for **Weakest Precondition**, referring to the Dijkstra-style WP calculus used to prove program correctness. 

By writing contracts — preconditions, postconditions, and loop invariants — directly in your Rust code, trust-wp proves they hold for all possible inputs by encoding verification conditions into first-order logic for the `ay` SMT solver.

## Key Features

- **One surface:** the `verus!{}` block front-end is retired in favor of Trust's native
  first-class contract clauses as the sole documented spec surface; the Creusot-compatible
  attributes below remain as a transitional compat lane.
- **The honesty meter:** every clause is graded on three axes — *logic*
  (`Certified` ⟺ a real CIC kernel proof with an empty axiom closure · `Trusted[axioms]` ·
  `Solver-Validated` · `Pending` · `Rejected`), *program* (is the spec-to-program link itself
  certified?), and *bound* (unbounded proof vs bounded check). Only
  `Certified × CertifiedReflection × Unbounded` licenses anything. `assume!` is available —
  and hard-caps your grade at `Trusted` with the debt named.
- **A kernel lane, not just a solver:** ground and quantified clauses in the covered fragment
  are proved by the Clean CIC kernel (checkable proof *terms*, not solver verdicts), racing
  alongside the SMT lanes. Everything outside the fragment declines honestly.
- **WP Calculus:** Uses the Weakest Precondition transformation to generate mathematical obligations from code.
- **Creusot Compatibility:** Uses [Creusot](https://github.com/creusot-rs/creusot)-compatible contract syntax.
- **RustHorn Encoding:** Employs a [RustHorn](https://doi.org/10.1145/3462205)-style encoding for mutable references, where `&mut` borrows are modeled as (current_value, final_value) pairs — plus a kernel-certified Aeneas give-back lens on the certified fragment: on that fragment the give-back lens is the normative `&mut` model and the prophecy encoding is retained as the untrusted SMT-lane encoding.
## Snapshot scope

This is a source snapshot of the trust-wp **specification surface and Weakest-Precondition
core** — the contract macros (`crates/trust-wp-macros`), verified std specs
(`crates/trust-wp-std`), the WP/formula core (`crates/trust-wp-core`), the Creusot-compat
contract crates, and the `targo-trust-wp` front-end (`targo trust-wp`, back-compat
alias `cargo trust-wp`) — together with the test harness,
examples, and reference docs.

The executable verifier lanes — the SMT encoder, the rustc-driver, and the CIC kernel
suite — take a hard dependency on the first-party `ay` solver, which is not yet public.
Those crates are omitted from this snapshot and will be restored once `ay` is published.
The WP-core crates build standalone; end-to-end verification of a `.rs` file is not
exercised here.

## Documentation

Public reference docs live at the repo root:

- `contract-syntax.md` — the contract syntax reference (the full grammar).
- `creusot-compatibility.md` — the Creusot-compatible attribute lane and its status.
- `INTERFACE-v1.md` — the frozen specification-language interface (carrier, grade,
  lane contract, invariants).
- `benchmarking.md` — running and extending the benchmark suite.

The project's goal statement, soundness-assumption inventory, developer-workflow
guide, and the `&mut` give-back (normativity-flip) decision record are internal
documents of the private tree and are not part of this snapshot; the soundness
and workflow notes concern the executable verifier lanes omitted above.

## Examples

See `examples/` for annotated contract examples (`simple.rs`, `loop_invariant.rs`,
`mut_borrow.rs`) and `examples/verified_math/` for a small verified crate.
