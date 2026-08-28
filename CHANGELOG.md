# Changelog

All notable changes to trust-wp will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html)
after reaching V1.

## [Unreleased]

### 2026-08-21 — the `trust-wp` command moves to its own crate (`crates/trust-wp-cli`)

- feat(cli): the front door is now the core-only package `trust-wp-cli`
  (binary still `trust-wp`), depending on `trust-wp-core` alone — no
  rustc_private, no solver — so it builds wherever the WP core builds and its
  in-process verbs run in the public snapshot. `trust-wp-driver` keeps the
  engine; its `[[bin]] trust-wp` is gone.
- feat(cli): in-process verbs that need no engine, sysroot or solver —
  `contract parse` / `contract vc` (the contract grammar and the WP SMT
  generator), `bundle verify|validate|replay|example` (trust-wp-core's native
  pure-replay prover, with independent evidence replay), and `result` (decode a
  saved result-protocol transcript). `help [COMMAND]` gains per-verb pages.
- feat(cli): `--json` prints one `trust-wp.cli-report.v1` document on stdout on
  every exit the CLI itself returns, a rejected command line included. It
  carries the engine's aggregate counters, the per-obligation `diagnostics`
  records (with `diagnostics_scope` and a derived `classification`, because the
  engine emits a record only for a NON-clean obligation), and a `status` derived
  from the exit code *and* the counters. `--format` replaces `--json` in the
  refused-flag list.
- The engine path is unchanged: everything the 2026-08-20 front-door work
  landed — EPIPE-safe printing, the fail-closed rule for a run that examined no
  obligation, `proof_assert_verified` on the wire, the `--emit-smt` fixes,
  crate-mode wire suppression, the `creusot_contracts` shim link, edition and
  `--timeout` validation, `--wide-pointers` refusal — is preserved verbatim and
  still covered by `demo/` (16/16) and the 14 front-door tests, which moved to
  the new crate with the binary.


Initial public release of trust-wp — deductive verification for Rust using the
Weakest Precondition calculus and the `ay` SMT solver.

### 2026-08-20 — the `trust-wp` command line, and a demo

The front-door binary landed earlier as a working shell; this pass made it hold
up as the way people actually meet the tool, and added `demo/` — a guided,
self-checking tour that doubles as a regression test for the CLI's
user-visible contract (`./demo/run.sh`, `demo/README.md`).

- **soundness(cli): a run that proves nothing no longer exits 0.** The engine
  emits a well-formed summary with every counter zero when it examined no
  obligation — a contract-free file, or a `--filter` that matched nothing — so
  the existing fail-closed guard (which only fired when the summary was
  *missing*) never ran. `StructuredVerificationResult::examined_nothing`
  states the condition; both modes now report it and exit 2.
- fix(cli): crate mode no longer prints the machine-readable `TRUST_WP_RESULT:`
  and `TRUST_WP_DIAGNOSTIC:` wire lines on the terminal. Single-file mode
  already hid them and the help promises they are opt-in; crate mode now
  relays `cargo-trust-wp`'s stderr through the same filter.
- fix(cli): a nonzero engine status with no verdict is reported as an engine
  error (2), not as "a contract was not proved" (1). A file that fails to
  compile was being labelled a counterexample, with two contradictory hints.
- fix(emit-smt): the emitted SMT-LIB2 was not parseable. The generator declared
  *untransformed* variable names while the printer emits the RustHorn
  spellings, so every query mentioning `x_view`, `v_current`, `v_final` or
  `old_n` referenced undeclared symbols; the `Seq` preamble could never
  trigger; and applied logic-function / type-invariant symbols were never
  declared at all. Queries are now self-contained — `ay` accepts them and
  returns `unsat` with a trust-free certificate.
- fix(emit-smt): well-definedness side conditions are lifted out of term
  position. The driver wraps a divided term in `LetAssume` so the divisor guard
  travels with the value, and the printer rendered that as `(=> guard term)` —
  `(=> Bool Int)`, which no solver accepts — so **every** contract containing a
  division emitted an unusable query. The guard is now its own assertion, under
  a comment that says the full encoder discharges it separately. Measured over
  the examples, the demo and six fixture crates (closures, traits, logic
  functions, `proof_assert`, views and prophecies), **96/96** emitted queries
  are accepted by `ay` after this pass. On the nine-source subset measured
  before it, 21 of 23 were rejected outright — the two that parsed were the
  contracts with no view, no `&mut` and no division.
- fix(encoder): the logical view of a *scalar* is declared at the scalar's sort.
  `x@` for an `i32` is an integer, not a sequence, which is what the injected
  integer-range preconditions assume.
- fix(encoder): a method *receiver* is declared at a value sort, not at the
  sort of the call it appears in. `(*f).precondition(x)` sits in a formula, so
  the receiver was declared `Bool` at that use and `Int` at another, and the
  query then applied one uninterpreted function to both.
- fix(encoder): the declaration block spells chained RustHorn wrappers the way
  the printer does — `Deref(Final(f))` is `f_final_current`, `View(Deref(v))`
  is `v_current_view`. Only the single-wrapper shapes were matched, so chained
  names went undeclared. Naming now goes through one mirror of the printer
  rather than a re-enumeration of shapes.
- fix(encoder): a nullary logic function prints as the bare identifier.
  SMT-LIB's term grammar is `( qual_identifier term+ )`, so the `(logic_zero)`
  this emitted was a parse error rather than a zero-argument application.
- fix(encoder): `__trust_wp_bit_not` and match-arm constructor testers
  (`is_some`, `is_<ctor>`) are declared; the bitwise preamble declares only the
  five *binary* operators, and pattern testers reached the query with nothing
  declaring them. A symbol applied at two different signatures is now named in
  a comment instead of being silently declared at the first one seen.
- fix(cli): counterexamples show the user's variables. Encoder temporaries
  (`__trust_wp_*`) and a `_view` binding that merely repeats its base are
  filtered out, and integers print `-1` rather than SMT-LIB `(- 1)`.
- fix(cli): single-file mode suppresses the `dead_code` warnings that come from
  compiling a lone file as a library, and the driver stops warning about the
  `feature(...)` gates it injects itself.
- fix(cli): the `ay` solver's routine `error!` chatter ("strict proof checker
  rejected UNSAT proof") no longer reaches a quiet run. trust-wp already
  reports that outcome as `unknown (proof-trusted)`; `-v` brings the solver's
  own logs back.
- fix(cli): `creusot_contracts` files verify in single-file mode — the front
  door links the compat shim exactly as it links `trust_wp`.
- fix(cli): the contract crate is resolved by recency across the uplifted
  `libtrust_wp.rlib` and `deps/libtrust_wp-<hash>.rlib`, so single-file mode
  works after an ordinary workspace build instead of failing with a bare
  `can't find crate`. A stale or compiler-mismatched crate now says so.
- fix(cli): engine lookup searches every shipped name per location, so a local
  `cargo-trust-wp` beats a stale bundle-installed `targo-trust-wp` on `$PATH`.
  `TRUST_WP_RUSTC` is honoured in crate mode too.
- fix(cargo-trust-wp): the cache-invalidating touch sets the file's mtime
  instead of reading the user's source and writing it back.
- fix(cli): `--dry-run` prints a shell-faithful command (the engine-argument
  block is newline-delimited on purpose); crate mode's dry run includes the
  `PATH` prepend the real run performs.
- fix(cli): `--wide-pointers` is refused rather than accepted and then fatal in
  the engine; `--timeout` and `--edition` values are validated; empty flag
  values and a flag value that is plainly the source file are rejected;
  `example` and `doctor` refuse a `--` tail they cannot honour; a closed stdout
  (`trust-wp --help | head`) ends output instead of panicking with 101.
- fix(docs): `--stop-after-analysis` stops the compiler after MIR analysis —
  contracts are still verified. Three help texts said the opposite, and the
  front door's fail-closed check was disabled by it.
- fix(docs): every Rust import in `contract-syntax.md` said `use trust-wp::`,
  which is not a legal path; the example READMEs pointed at
  `scripts/run-trust-wp-rustc.sh` rather than the front door.
- fix(examples): `examples/loop_invariant.rs` shipped an invariant that does not
  verify. Replaced the factorial case with repeated doubling, which is linear
  and provable, and said why the multiplicative one is not.
- fix(gitignore): `!tests/fixtures/*/*/` re-included fixture `target/`
  directories, so a crate-mode run inside a fixture left build output untracked.
- **soundness(protocol): the wire record carries `proof_assert_verified`.** It
  had a failure counter for `proof_assert` and no success counter, so a run
  that proved every assertion emitted an all-zero summary — indistinguishable
  from a run that examined nothing, which the new fail-closed rule then
  reported as an error. Optional field: a producer that predates it omits the
  key and a reader defaults it to 0.
- fix(cli): a fatal compiler diagnostic is reported as an engine error (2), not
  as an internal panic (101). `rustc_driver` aborts with 101 on a fatal
  diagnostic, which sent a user with a type error to the issue tracker.
- fix(cli): a closed stdout (`trust-wp doctor | head`) stops output without
  deciding the exit code. Exiting 0 there answered "ready" on behalf of a
  report the reader had truncated.
- **chore(deps): both sibling checkouts realigned with their remote mains.**
  `../ay` was 1308 commits behind at 0.5.0 against a manifest expecting the 0.10
  line, and `../clean` 2426 behind; the committed `Cargo.lock` pinned versions
  present in neither, so `cargo build --locked` could not resolve. Aligning ay
  (0.13.0) brings in `f6d4cdea1f` — the fix
  `docs/e2e-trait-refinement-ay010-drift-2026-08-16.md` names as root cause 2 —
  and the `targo-trust-wp` e2e suite goes **112 passed / 9 failed → 120 / 1**.
  The eight that recover are the `&mut`, closure-resolve and prophecy cases;
  contracts that had reported `unknown (proof-trusted)` (an unbounded `max`, an
  `abs` with no precondition, all of `tests/fixtures/simple_project`) verify.
  A stale sibling degrades whole lanes silently, which is why both READMEs now
  say to check it first.
- KNOWN: `extern_spec::test_extern_spec_user_defined_option_unwrap` still fails
  at ay 0.13.0 — `get_value` is `ay_result=unsat, FullyVerified` with an
  `unsat_proof` carrying 29 unverified trust steps, so the proof-authority gate
  declines it. ay-side; nothing in the WP core or the driver's authority path
  changed here.

  It resembles the drift note's root cause 2 and is NOT it. `f6d4cdea1f` is
  intact and un-narrowed at this revision (the diff over the files it touched is
  rustfmt-only, and every later change widens rather than narrows), and the
  published proof contains zero resolution steps and only two theory lemmas, so
  none of its derived-unit lemmas are what the gate trips over. The 29 steps are
  premiseless Alethe `trust` steps from export-time demotion of solver-injected
  facts (`ay-dpll/src/executor/proof_rewrite_division.rs`
  `demote_non_problem_assumptions`): the preprocessed assertion window narrows
  the demotion whitelist to the caller's ORIGINAL assertions, so anything the
  solver injects itself is demoted rather than justified.

  The trigger is `old(...)`, not `extern_spec!` and not `Option`. Deleting the
  whole `extern_spec!` block gives a byte-identical obligation and the same
  `trust=29 total=105` (trust-wp already carries a built-in `Option::unwrap`
  spec). `#[ensures(result == opt.unwrap())]` verifies with a 3-step
  certificate; `#[ensures(result == old(opt).unwrap())]` does not — the slice
  asks ay to prove `call_0 == spec_unwrap(old_opt)` from
  `call_0 == spec_unwrap(opt)`, where the only link between the two constants
  runs through a ground injectivity clause over the struct bridge.
- **fix(encoder): a truncated quotient by a SYMBOLIC divisor is now pinned.**
  `__trust_wp_int_div_trunc` carried no axiom at all unless the divisor was an
  integer literal — the symbolic branch was annotated "underconstrained UF
  (sound; rare)" — so `a / b` for non-literal `b` was a completely free integer
  and nothing about it could be proved. Not a sign corner: the whole function.
  `#[requires(a >= 0 && b > 0)] #[ensures(result * b <= a)]` was `unknown
  (incomplete)`; it verifies now.

  The fix mirrors `assert_int_div_euclidean_identity` line for line:
  `divisor != 0 ==> dividend == nlmul(divisor, quotient) + rem_trunc(dividend,
  divisor)`, linear over the opaque UF applications and path-guarded. Sharing
  the truncated remainder UF also ties `/` and `%` on the same operands, which
  makes `a == (a / b) * b + a % b` provable.

  The identity alone pins the quotient only *through* the opaque product, so it
  needed a second half: linear sign/magnitude bounds
  (`a >= 0 && b > 0 ==> 0 <= q <= a`, and the three other sign cases, each tight
  at `|b| == 1`). Without them `0 / 1 == 3` stayed a model and
  `#[requires(a == 0 && b > 0)] #[ensures(result == 0)]` reported **FAILED with
  a counterexample** — a verifier calling correct code wrong. That was
  pre-existing, not introduced here, and it is fixed: `result >= 0` for
  `a >= 0, b > 0` verifies, and `result * b == a` is now correctly *disproved*
  rather than declined.

  Gated on false accepts, because this constrains a previously-free UF:
  `tests/adversarial/run_adversarial.py` is byte-identical to its pre-change
  baseline (10/10 rejected, 0 false accepts, 0 over-refusals), and the new
  keystone test asserts both directions — the quotient bound proves, while
  `(n /trunc m) * m == n` and `n /trunc m >= n` must NOT, so an
  over-strengthened identity fails the test rather than shipping.
- **fix(contracts): `old(p)` on a by-value parameter is `p`.** Left as
  `Old(Var(p))` the encoder minted a separate, entirely unconstrained symbol
  `old_p`, so any contract relating the two was not merely declined but
  *disproved*: `#[ensures(result == old(x) + 1)]` over
  `fn f(mut x: i32) -> i32 { x += 1; x }` reported FAILED with the
  "counterexample" `old_x = 1, x = 0` — two values with no relationship at all.
  A by-value parameter cannot change under the caller's feet, so the entry value
  and the specification's `p` are the same thing; this is the non-mut-ref
  counterpart of `collapse_old_over_mut_ref_currents`, whose
  `old_body_is_mut_ref_entry_expr` already classifies a non-mut-ref `Var` as an
  entry-state expression. `old(*v)` on a `&mut` is untouched — that cell does
  change. This also resolves the `extern_spec` e2e failure noted above, whose
  trigger was `old(...)` rather than `extern_spec!`. False-accept corpus
  byte-identical to baseline.
- fix(cli): counterexample filtering matches the memory model's names precisely
  instead of by bare prefix, so a user variable called `heapsort_pivot` or
  `domainname` is no longer deleted from the report.
- test(cli): `crates/trust-wp-driver/tests/cli_front_door.rs` runs the binary as
  a process — exit codes, stream discipline, the advertised first run, the
  counterexample, the fail-closed path, and a check that the emitted SMT
  declares every symbol it uses.

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
