<!-- Copyright 2026 Andrew Yates -->
<!-- Licensed under the Apache License, Version 2.0 -->

# INTERFACE-v1 — the frozen specification-language interface

**Status: FROZEN (v1), 2026-07-06.** Additive evolution only; a breaking change requires
v2 and a migration note. Reference implementation: `iface/trust-spec-iface` (not included in this snapshot)
(compiling types + invariant tests). Normative sources: the internal design spec
(`design-trust-spec-language`, §3/§4/§6/§8/§10/§12), as corrected by the 2026-07-06
design review — both internal notes of the private tree.

This is the contract that lets every producer and consumer — **trust-wp, trust-vc, ay,
clean-auto, ty, trust-mc (Kani), authored/AI terms** — meet at one carrier with one meter,
so spec-writing can proceed against a stable target.

---

## 1. The carrier (unchanged, restated)

The one obligation carrier is `clean_kernel::Expr` (CIC). The one checker is
`TypeChecker::check_type` plus the axiom-closure meter. Nothing in v1 adds a second
carrier or a second checker.

```
UOb {
  goal        : Expr          // the proposition to PROVE
  hypotheses  : Vec<Expr>     // ASSUMED clauses (§4) — folded as Pi premises, never proven
  kind        : ObKind        // #[non_exhaustive] — extensible without breaking v1
  routing     : RoutingHint   // solver/arith mode — a HINT; never affects semantics
  taint       : CertTaint     // elaborator-TV status carried per §8-2
}
```

`ObKind` v1 values: `Postcondition, Refinement, UbCheck, Invariant, GiveBackRefinement,
TranslationValidation, Temporal(reserved)`. `Temporal` freezes the **slot** for ty's
temporal lane; its semantics stay deferred per §10 — adding them later is non-breaking.

## 2. The grade — one record, three axes (§12)

```
ClauseStatus {
  logic   : Certified{auto} | Trusted{closure} | SolverValidated | Pending | Rejected{why}
  program : CertifiedReflection | TrustedReflection     // the spec-to-program link (§8-3)
  bound   : Unbounded | BoundedChecked(N) | FiniteModelChecked(M)   // §10
}
```

- **logic** is computed by the ONE meter (`cert-meter`): `Certified` means the root
  judgment and complete reachable declaration/provenance graph pass Clean's strict
  audit; only the exact canonical `{propext, Quot.sound, Classical.choice}` foundations
  are admitted and trust markers are forbidden. `auto` records only *how* the term was
  produced (hands-free vs authored) — same gate.
- **program** is the reflection tier: `CertifiedReflection` only where the step relation
  covers the construct; loops/CFG/borrow/heap outside the covered fragment fail closed to
  `TrustedReflection`.
- **bound** is the coverage of the best evidence: an unbounded kernel proof is
  `Unbounded`; a model-checking pass to depth N is `BoundedChecked(N)` — **the trust-mc
  landing slot**. A bounded verdict never occupies the logic axis.

**UB-elision law (I2):** the three axes are necessary but not sufficient. During
the direct Rust/Clean-to-Trust-IR transition this record has no canonical typed
obligation identity or semantic digest, so its legacy elision query is hard-blocked.
Elision additionally requires validator-produced evidence binding this exact checked
goal and term to the exact Trust-IR obligation and machine check; that authority API is
not yet wired.

## 3. The lane contract (§3 L4 made a trait)

Every prover is a **peer racing to inhabit the same goal**:

```
trait Lane { fn name() -> str; fn attempt(env, &UOb) -> LaneVerdict }

LaneVerdict =
  Term(Expr)                          // kernel-checkable candidate — the meter grades it
| AxiomCapped { term, axioms }        // accept-on-trust wrapper (P2) — hard-capped ≤ Trusted
| SolverValidated { evidence }        // legacy solver verdict, no term (P0 grade)
| Bounded { n, evidence }             // model checker: checked to bound N, no term
| Counterexample { witness }          // the obligation is FALSE — surface as an error
| Decline { reason }                  // outside this lane's fragment (fail closed)
```

**No lane self-grades (I1).** Only `Term` can reach `Certified`, and only through the
meter. `AxiomCapped` caps at `Trusted` even if the term's closure is clean. `Bounded`
lands on the bound axis with logic left `Pending`. `Decline` is always legal and always
safe.

## 4. The invariants (frozen; each has a test in the reference crate)

| # | Invariant | Source |
|---|---|---|
| I1 | One meter; no lane self-grades; Certified ⟺ the strict root/declaration/provenance audit passes with only exact canonical foundations | §8 |
| I2 | No unbound grade elides; a future elision capability must bind Certified logic/reflection/unbounded coverage to the exact typed Trust-IR obligation digest | §6, §10 |
| I3 | Assumed vs proved: `hypotheses` are premises (Pi-folded), never proof obligations; preconditions/invariants assume, postconditions/refinements prove; inversion is banned at elaboration | §4 |
| I4 | Total elaboration: every well-formed surface spec lands at `Pending` before any proof exists | §6 |
| I5 | Fail closed everywhere: out-of-fragment → `Decline`/`TrustedReflection`/translator error — never a wrong verdict | §6, §8 |
| I6 | Monotone migration: grades never silently regress (SolverValidated exists so legacy passes don't fall to Pending) | P0 |
| I7 | Bounded evidence never launders: no path from `Bounded`/`FiniteModel` to `Certified` or to elision without a kernel term | §10 |

## 5. Adapters: what ty and trust-mc need (answer: no language changes)

**ty** — nothing. ty's cleancic gate *is* the I1 criterion (the design adopted it). ty
plugs in as a `Lane` producing `Term`; its temporal properties get `ObKind::Temporal`
when §10's semantics land (slot frozen now, semantics later — non-breaking).

**trust-mc (Kani)** — surface already covered: Kani contracts are a thin desugar shim
(§3 L1) into the same `UOb`; `kani::assume` → `hypotheses` (I3). Its verdicts land as
`LaneVerdict::Bounded{n}` → `BoundTier::BoundedChecked(N)` (I7 keeps them honest);
concrete-playback counterexamples land as `Counterexample{witness}`. **The bound axis is
part of v1 precisely so trust-mc has a first-class landing slot from day one.**

## 5a. The auto-fragment checker (P3, added additively 2026-07-06)

`classify_auto_fragment(goal) -> Ok(()) | Err(DeepReason)` — the design §6 predictability
rule as a decidable author-time check: quantifier-free goals over the interpreted
whitelist (`AUTO_FRAGMENT_CONSTS`) are Auto; binders, unknown constants, or structural
forms route Deep with a named reason. Extending the whitelist is a deliberate interface
change, never an emergent solver behavior — "never 'auto for whatever the solver happens
to close'". Session-validated against actual lane behavior.

## 5b. `proof!` — the authored-term surface (P3, added additively 2026-07-06)

`proof!(by <Expr>)` → `LaneVerdict::Term{auto:false}`; `proof!(assume [axioms], by <Expr>)`
→ `AxiomCapped` (hard-capped ≤ Trusted, P2). Authored terms enter the portfolio as
first-class lane verdicts — never self-graded (I1). (The Verus-shaped in-source
macro was deleted at R1 of the two-language design, 2026-07-11; the native trustc
clause surface desugars to this stable target.)

## 5c. The proof_by evaluator (P3 chain closure, added additively 2026-07-07)

`evaluate_proof_payload(ob, payload) -> LaneVerdict` — evaluates a consumer-supplied
`trust-wp:proof_by:` payload into the authored lane. v1 vocabulary: `by refl` (ground
equalities close by kernel computation); `assume [axioms], by refl` (hard-capped ≤
Trusted). Unknown tactics fail closed to `Decline` (I5). Vocabulary growth is additive.
The production driver does not currently consume the marker; driver routing remains
follow-on work rather than suppressed, uncalled scaffolding.

## 6. What is NOT frozen

Tactic internals; solver routing heuristics; the surface macro syntax beyond the
Verus-shaped contract form (`requires/ensures/invariant/proof!`); temporal semantics
(slot only); the reflection fragment's extent (it grows; the *tier telling the truth
about it* is what's frozen).

## 7. Build topology note (the one known sharp edge)

The reference crate builds on **stable** with a path dep on the first-party `clean`
CIC kernel crate. Inside the trust fork's workspace the same package resolves through
the fork's own copy — consumers there must `[patch]` the clean-kernel path or depend
through the fork's copy. This crate-graph conflict is a known sharp edge.
