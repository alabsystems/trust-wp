# Changelog

All notable changes to trust-wp will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html)
after reaching V1.

## [Unreleased]

Initial public release of trust-wp — deductive verification for Rust using the
Weakest Precondition calculus and the `ay` SMT solver.

History below is reconstructed from git at merge-level granularity, from when
this file was first staged (2026-07-18) through 2026-08-11. Each bullet names a
merged lane or landing; the referenced commits carry the detail.

### 2026-08-11 — semantic-authority convergence (`a893d85`, `08593c1`)

- soundness(authority): proof replay is mandatory — certificate-backed
  outcomes, replayed variant proofs for recursion, retained fresh replay
  artifacts, isolated verifier certificates, per-call proof-certificate
  aggregation for loops, and slice certificates preserved and enforced.
  Fresh SAT is rejected as UNSAT authority.
- soundness(proof_assert): exact checked slice replay bound to independently
  checked derivations; every strict obligation slice retained.
- soundness(seq/proof): certify asserted zero-length push-back; retain strict
  slice authority.
- fix(wrapper/cli): bind private sysroot to exact driver, recognize the
  canonical trustc compiler path, identify the primary targo binary; test
  discovery works across worktrees.

### 2026-08-11 — two-machine ADT-declaration-order convergence (`1c938bf`)

- fix(verify): do not demote on the ANALYTICAL result-sort scan (bug/1208
  false demotion).
- fix(encoder): scope the address-keyed sort-inference memo to one call
  (fmap_indexing payload-mangling flap).
- deps(ay): relock onto ay 0.7.0; migrate off the removed `ProofTrusted`
  variant, under a control.

### 2026-08-09..10 — false-accept root-causing

- fix(encoder): sort-aware fail-closed guard on the Final-collapse routes
  (Fix A — the adjudicated take_first_mut false accept demoted), generic-ADT
  refinement of that guard (guardref), and sort-faithful tuple getters in the
  FRESH-REBUILD scope (getters2).
- fix(driver+encoder): peel Rc/Arc in ADT collection and re-land the
  proof_assert adt_decls plumb (adtpa); do not panic when `-t` is below the
  adaptive per-function floor.
- test(adversarial): trust-wp-owned negative corpus for the root-caused
  false-accept mechanisms; all three SpecAxiomDropped sites counted in the
  lock.

### 2026-08-04..06 — solver stack and encoder sort planning

- feat(driver): default-enable the certified composed solver stack
  (set-if-absent).
- feat(std): FMap ghost premise trio — get_mut_ghost post-state,
  split_mut_ghost seed+havoc, split-handle insert/remove result laws.
- fix(encoder): evidence-complete, order-independent DT-view sort planning
  with fail-closed counterexample hygiene (arc_and_rc false reject);
  sort-typed tuple-getter placeholders (rusthorn inc_some_2_* flip).
- fix(verify): bounded in-worker base recheck on a disposable fresh-recheck
  encoder; fresh base-recheck verdicts surfaced on the pathology-rescue path.
- build(deps): re-lock ay 0.4.0 -> 0.5.0 from the first real driver build;
  re-lock clean-auto/clean-kernel after an environment version move.

### 2026-08-01..03 — Trust-native subcommands and encoder collision fixes

- Make trust-wp cargo-subcommands Trust-native: `targo trust-wp` is the
  primary bin (with `cargo trust-wp` back-compat alias), `trust-wp-driver`
  the primary rustc-driver bin (with `trust-wp-rustc` alias).
- fix(encoder): declare driver-extracted ADTs dependency-first, degrade
  declare-collision panics, and close two residual declare-collision routes
  (#2706).
- fix(driver): opaque uninterpreted-sort encoding for ghost-identity tokens.
- chore: prune Cargo.lock to the ay 153665fb9 dependency graph.

### 2026-07-30..31 — CLI front door and Trust-native runners

- feat(cli): trust-wp is a real front door, not a placeholder guide.
- fix(link): the driver is relocatable — loader-relative rpaths come first.
- spikes: run on Trust's targo, not stock Homebrew cargo; one sourced helper,
  zero RUST hacks.
- feat(atpkg): record why trust-wp cannot ship on PATH yet.

### 2026-07-24..26 — recovery, publish guards, AY 0.4 compatibility

- merge: phase0-false-accepts and the live-recovery reconciliation — fail
  closed on private toolchain ambiguity, preserve selected Trust compiler
  identity, eliminate ignored examples and static lint bypasses.
- fix(publish): fix the four stage guard failures at their cause; flat
  KEY_DEFAULT lines so the engine can read the staging remote; declare
  source-only release mode; constellation versioning + release-tier policy
  published.
- fix: close AY 0.4 proof and Seq compatibility gaps; advance TrustIR to
  proof-backed main.

### 2026-07-22..23 — Trust 1.99 port and lineage reconciliation

- port(driver): rebuild against Trust toolchain 7ee6f61a3 (rustc 1.99.0-dev);
  deterministic clean Trust 1.99 builds.
- merge(wp): integrate the nested-reborrow prophecy lineage; thread match-arm
  enum-discriminant path conditions into in-arm obligation VCs; fail closed
  when nested-transfer tracking is incomplete; strip collapsed
  nested-transfer body facts.
- fix(review): bind private dependency gates to locked inputs, reject unbound
  proof evidence, bind compatibility gates to exact inputs, validate locked
  dependencies in worktrees.
- refactor(env): migrate env mutation sites to lock-scoped helpers under the
  Trust toolchain env-wall lint.
- creusot-compat: proof_assert! tier (+11 corpus files) and pearlite!{}
  wrapper unwrap; replay hardening (reject ambiguous formula JSON, isolate
  old-state proof reasoning); spikes require committed dependency locks.

### 2026-07-18..20 — publication engine and closures fixes

- chore(publish): install the publish tool + scrub for staging; replace the
  driver copy with a central-engine shim; apply the constellation docs/
  export ban and fix relocated links.
- fix(closures): Box-env receiver transparency, consistent premise layering +
  exists-goal witnessing for call_fnmut, proof_assert goals retargeted to
  postcondition_mut chain depth (07).
- fix(encoder/mir): distribute Deref into Match arms (mirrors Ite); empty
  closure environment lowers to unit aggregate.
- build: require the explicit unverified Targo lane; bump ay to 893aea88
  (capture-projection gate fix + DT-cert infra).
