# trust-wp — the command line

`trust-wp` is the front door to the trust-wp weakest-precondition verifier: you
write contracts on ordinary Rust functions — `#[requires]`, `#[ensures]`,
`#[invariant]`, `#[variant]`, `proof_assert!` — and it proves them.

```sh
trust-wp example > demo.rs && trust-wp demo.rs
```

This crate (`trust-wp-cli`) is the binary only. It contains **no proof engine**:
it depends on `trust-wp-core` alone — no `rustc_private`, no solver — so it
builds and runs wherever the WP core builds. Its verbs come in two kinds.

**Engine verbs** hand the work to binaries that do carry the engine, and turn
their structured result protocol into an exit code or a JSON report:

| verb | engine | what it does |
| --- | --- | --- |
| `trust-wp FILE.rs` | `trust-wp-rustc` | verifies one file; no Cargo project needed |
| `trust-wp` | `cargo-trust-wp` | verifies the crate in the current directory |

**In-process verbs** run `trust-wp-core` in this process and need nothing
installed — no rustc, no sysroot, no solver, no network:

| verb | what it does |
| --- | --- |
| `trust-wp contract parse` | parse a contract expression with trust-wp's grammar |
| `trust-wp contract vc` | emit a weakest-precondition VC as SMT-LIB2 |
| `trust-wp bundle verify` | prove a verify-bundle request with the native pure-replay prover |
| `trust-wp bundle validate` | check a request's structure |
| `trust-wp bundle replay` | re-check a result's proof evidence, independently |
| `trust-wp result` | decode a saved result-protocol transcript |
| `trust-wp doctor` | report what is installed, and how to fix what is not |
| `trust-wp example` | write a tiny contracted sample |
| `trust-wp completions` | print a completion script for bash, zsh or fish |
| `trust-wp man` | print the roff manual page |

## Building

```sh
targo --unverified build --release -p trust-wp-cli      # target/release/trust-wp
```

`targo` is the Trust toolchain's cargo (`rust-toolchain.toml` pins it);
`--unverified` names the lane that builds with the Trust verification pass off.
That is enough for every in-process verb. `verify` additionally needs the
engine, which links the Trust compiler itself:

```sh
targo --unverified build --release -p trust-wp-driver --bin trust-wp-rustc   # single-file mode
targo --unverified build --release -p targo-trust-wp                         # crate mode
targo --unverified build --release -p trust-wp                               # contract crate, for single-file mode
```

`trust-wp doctor` reports which of these are in place. It finds each binary by
looking, in order, at the override environment variable, the directory holding
`trust-wp` itself, `<checkout>/target/release`, `<checkout>/target/debug`, and
`$PATH`.

## Verifying

```sh
trust-wp demo.rs                       # one file
trust-wp                               # the crate here
trust-wp --filter increment demo.rs    # one function
trust-wp --emit-smt demo.rs            # show the proof queries
trust-wp --json demo.rs                # machine-readable report
trust-wp --dry-run demo.rs             # print the engine command; run nothing
```

### Options

| option | meaning |
| --- | --- |
| `--filter <NAME>` | only verify functions whose path matches `NAME` |
| `--timeout <SECS>` | per-function solver timeout (engine default: 60) |
| `--emit-smt` | print the SMT-LIB2 queries to stdout (see the note below) |
| `--emit-smt-dir <DIR>` | write one annotated `.smt2` file per function |
| `--strict-trust` | require independently replayed proof authority (always on) |
| `--no-strict-trust` | deprecated compatibility spelling; ignored |
| `--strict-axioms` | treat unverified axioms as errors |
| `--strict-obligations` | treat dropped-obligation warnings as errors (exit 2) |
| `--stop-after-analysis` | stop after MIR analysis; prove nothing |
| `--no-verify` | skip verification entirely |
| `--track <LEVEL>` | memory tracking: `auto`, `reg`, `ptr`, `mem` |
| `--edition <YEAR>` | edition for single-file mode (default: 2021) |
| `--dry-run` | print the exact engine command instead of running it |
| `--json` | print one JSON report on stdout |
| `-q`, `--quiet` | print only failures, and the summary |
| `-v`, `--verbose` | show verification progress |
| `--color <WHEN>` | `auto` (default), `always`, `never` |

**What `--emit-smt` is, and is not.** The emitted queries are a
weakest-precondition *rendering* of each obligation, produced by the simple
generator in `trust-wp-core` — not the query the verdict came from, which the
engine's separation-logic encoder builds with loop, ADT, ghost and borrow
context on top. For a `&mut` parameter the rendering cannot decide the
obligation at all: the postcondition rests on `<param>_final`, nothing else in
the query constrains it, and the file is satisfiable whatever was proved. Every
one of the three functions in `examples/mut_borrow.rs` emits `sat` this way
while two of them verify. A query that is too weak to decide now says so in a
comment naming the free symbols, so it can be read as the shape of the
obligation without being mistaken for the verdict.

Options and the file may appear in either order. A value that itself starts
with `-` must be attached: `--filter=-foo`. `--wide-pointers` is refused rather
than accepted and then fatal, because the engine does not implement it.

Unknown options are refused, never ignored, and options from other verifiers
name the trust-wp equivalent (`--unwind` points at `#[invariant]`, `--solver`
at `--emit-smt`). To hand an option to the underlying tool unchanged, put it
after `--`:

```sh
trust-wp -- -p mycrate --all-features     # crate mode: goes to cargo
trust-wp demo.rs -- --cfg foo             # single file: goes to rustc
```

## Exit codes

| code | meaning |
| --- | --- |
| 0 | everything verified |
| 1 | at least one contract failed (a counterexample exists) |
| 2 | encoding/solver error, soundness gap, or the engine could not run |
| 3 | contract parse error, invalid input, or bad command line |
| 101 | internal error (panic) |

A clean compile that produces no verification summary exits 2: nothing was
proved, so nothing is reported as proved.

## The `--json` report

`--json` prints **exactly one** `trust-wp.cli-report.v1` document on stdout, on
every exit the CLI itself returns — success, a rejected command line, a missing
engine — while human output stays on stderr and exit codes are unchanged. The
schema is additive: ignore keys you do not know.

`--json` is refused where it would collide with the verb's own output: `help`,
`example` and `bundle example` write source rather than a report, and
`--emit-smt` already owns stdout (`--emit-smt-dir`, which writes files, is
fine).

Every document carries the envelope:

```json
{
  "schema": "trust-wp.cli-report.v1",
  "tool": { "name": "trust-wp", "version": "0.2.0" },
  "command": "verify",
  "exit_code": 1
}
```

### `verify` and `result`

```json
{
  "schema": "trust-wp.cli-report.v1",
  "tool": { "name": "trust-wp", "version": "0.2.0" },
  "command": "verify",
  "exit_code": 1,
  "mode": "file",
  "target": "/work/demo.rs",
  "status": "failed",
  "summary": { "verified": 1, "failed": 1, "errors": 0, "warnings": 0, "...": 0 },
  "diagnostics": [ { "def_path": "demo::increment", "...": null } ],
  "diagnostics_scope": "non_clean_obligations",
  "engine": {
    "driver": "/work/target/release/trust-wp-rustc",
    "driver_origin": "$TRUST_WP_RUSTC",
    "front": null,
    "front_origin": null,
    "child_exit_code": 1
  },
  "notes": [ "a contract was not proved. ..." ],
  "error": null
}
```

`mode` is `file`, `crate` or (for `result`) `transcript`.

**`status`** is derived from the exit code *and* the counters, because the exit
code alone conflates cases a consumer must tell apart:

| status | meaning |
| --- | --- |
| `verified` | contracts were proved |
| `no_obligations` | the engine examined no obligation — a `--filter` that matched nothing, or a target with no contracts. This **fails closed** (exit 2): a run that proved nothing is not a success. |
| `not_requested` | the run never asked for a verdict (`--no-verify`, or emit-only without `--verify`) |
| `failed` | a contract was disproved |
| `soundness_gap` | exit 2 whose only cause is unproved-but-accepted work (trusted, skipped, assumed, axiom-dependent, vacuous) |
| `error` | an encoding/solver error, panic, or structural failure |
| `compile_failed` | the target did not compile, so nothing was proved |
| `no_verdict` | the engine ran and reported no summary (fail-closed) |
| `parse_error` | a contract failed to parse |
| `dry_run` | nothing ran; the `dry_run` key holds the command |

**`summary`** is the engine's aggregate `TRUST_WP_RESULT:v1` counters, every
field always present, or `null` when the engine emitted no result line:
`base_exit_code`, `verified`, `failed`, `errors`, `warnings`, `assumed`,
`trusted`, `skipped`, `verified_with_axiom_deps`, `unverified_axioms`,
`vacuous`, `evidence_gaps`, `proof_assert_failed`, `proof_assert_errors`,
`panics`, `demoted`, `parse_errors`, `termination_errors`,
`logic_recursion_errors`, `erasure_errors`.

**`diagnostics`** holds the engine's per-obligation `TRUST_WP_DIAGNOSTIC:v1`
records. Read `diagnostics_scope` before iterating: the engine emits a record
only for an obligation that is **not** cleanly verified, so a function that
verified cleanly has no entry, and an entry whose `status` is `verified` is an
*uncredited evidence gap* rather than a success. Branch on `classification`
(`failed`, `unknown`, `assumed`, `evidence_gap`, `other`), not on `status`.

Each record carries `def_path`, `kind`, `status`, `classification`, `reason`,
`solve_time_ms`, `assertions`, `timeout_ms`, `ay_result`,
`accepted_for_consumer`, `model_validated`, `unsat_proof_available`,
`verification_level`, nested `replay` and `native_replay` objects, and an
`extra` map holding any key a newer engine adds. Sentinels are mapped, not
passed through: a numeric field is an integer or `null` (the engine said `none`,
or sent nothing parsable), a tri-state boolean is `true`/`false`/`null` (`null`
= the engine said `unknown`), a string field is `null` when the engine said
`none`.

`location`, `clause` and `counterexample` are **reserved and always `null`**:
the engine's diagnostic line carries none of them today — a failed contract's
source span, violated clause and counterexample exist only in its human output.
They are named so consumers can code against them now; when the engine starts
sending them they will arrive under `extra` first and then be promoted to these
keys.

### The other verbs

| command | keys beyond the envelope |
| --- | --- |
| `contract parse` | `ok`, `source`, `input`, `normalized`, `error` (with `position`) |
| `contract vc` | `ok`, `function`, `requires[]`, `ensures[]`, `result`, `smt`, `error` |
| `bundle verify` | `bundle_id`, `status`, `obligations{verified,failed,unknown,unsupported}`, and `result` (the whole result document) or `result_path` when `-o` wrote it |
| `bundle validate` | `bundle_id`, `status`, `obligations`, `diagnostics[]`, `error` |
| `bundle replay` | `bundle_id`, `status` (`replayed`/`not_replayed`), `obligations`, `error` (with `code`) |
| `doctor` | `ready`, `status`, `checks[{name,ok,detail,fixes[]}]` |
| `version` | `repository` |
| a rejected command line | `command` is `usage`, `status` is `error`, `error` is `{kind,message,help[]}` |

`error` is the uniform non-verdict object: `kind` is one of `usage`, `io`,
`contract_parse`, `invalid_bundle`, `engine_missing`, `engine_spawn`,
`no_verdict`, and `message` explains it.

## Contracts and bundles without an engine

```sh
trust-wp contract parse 'x > 0 && result == x + 1'
trust-wp contract vc --name increment \
    --requires 'x > 0' --ensures 'result > x' --result 'x + 1'
```

`contract vc` emits the verification condition the WP calculus produces:
preconditions asserted, `result` bound to `--result`, the postcondition
negated, `(check-sat)` — unsat means the contract holds. It is the same simple
generator `verify --emit-smt` uses; the engine's encoder adds loop, ADT, ghost
and borrow context on top, so treat this as the calculus rather than as what
the verdict solves.

The `bundle` verbs speak `trust-wp.verify-bundle.v1`, the request/result format
external producers use:

```sh
trust-wp bundle example -o request.json
trust-wp bundle validate request.json
trust-wp bundle verify request.json -o result.json
trust-wp bundle replay request.json result.json
```

`bundle verify` runs trust-wp-core's **native pure-replay prover**, not the SMT
solver: it decodes each claim (`trust_wp_pure_expr_v1` or `trust_formula_v1`),
proves it by replaying trust-wp's own rewrite rules, and attaches hash-addressed
proof evidence that `bundle replay` re-checks independently of the run that
produced it. It settles what it can and refuses to guess at the rest — `x + 1 > x`
is proved, `false` fails, and an open predicate such as `x > 0` comes back
`unsupported` rather than verified. Exit 0 verified / 1 failed / 2 unknown or
unsupported / 3 invalid request.

## Reading a saved run

```sh
TRUST_WP_RESULT_PROTOCOL=1 cargo-trust-wp 2> run.log
trust-wp --json result run.log
```

`result` merges the machine lines in a transcript exactly as `verify` does and
exits with the decoded verdict's code — a transcript with no result line exits
2, because nothing was proved. With no file (or `-`) it reads stdin.

## Environment

| variable | meaning |
| --- | --- |
| `TRUST_WP_RUSTC` | path to the `trust-wp-rustc` driver binary |
| `TRUST_WP_RUSTC_BIN` | the same, as spelled by the repo's driver launcher script |
| `TRUST_WP_CARGO` | path to the `cargo-trust-wp` binary |
| `TRUST_WP_HOME` | trust-wp checkout to resolve helpers and libraries from |
| `TRUST_WP_RESULT_PROTOCOL=1` | also print the engine's machine lines on stderr |
| `TRUST_WP_LOG` | log filter, e.g. `TRUST_WP_LOG=verify=debug` |
| `NO_COLOR` | set to any value and `--color auto` stays plain |

`trust-wp` never modifies its own environment; every variable above is read, and
child processes receive what they need explicitly.

## Manual page

```console
$ trust-wp man | man -l -                                  # read it now
$ trust-wp man > ~/.local/share/man/man1/trust-wp.1        # install it
```

Generated from the same option table as the completions and `--help`, and
dated by commit rather than by build, so rebuilding the same source does not
churn an installed page. `mandoc -T lint` is clean.

## Shell completions

```console
$ trust-wp completions bash > ~/.local/share/bash-completion/completions/trust-wp
$ trust-wp completions zsh  > "${fpath[1]}/_trust-wp"
$ trust-wp completions fish > ~/.config/fish/completions/trust-wp.fish
```

The scripts are generated from the same option table the parser and `--help`
are tested against, so a flag cannot be added to one without the others
failing. They complete the verbs, `.rs` files in first position, every option,
and the fixed value sets of `--color`, `--track` and `--edition`.

## See also

- `contract-syntax.md` (repository root) — the full contract grammar.
- `creusot-compatibility.md` — the Creusot-compatible attribute lane.
- `INTERFACE-v1.md` — the frozen specification-language interface.

The verbs, flag spellings and exit codes are meant to feel familiar to users of
Creusot. trust-wp is an independent ALab tool: not affiliated with, derived
from, or endorsed by that project.
