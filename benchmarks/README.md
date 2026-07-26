# Benchmarks

Docker-based evaluation harness templates for reproducible benchmarks.

## Usage

```bash
# Copy templates to set up benchmarking
cp -r templates/* .

# Run evaluation
./run_eval.sh --suite default

# Or use Docker
docker compose up --build
```

## Files

- `templates/` - Copy these files to start
  - `Dockerfile` - Container definition
  - `docker-compose.yaml` - Compose configuration
  - `run_eval.sh` - Evaluation runner script

## SWE-bench Baseline

Tracked in #2147. SWE-bench measures AI agent performance on real software engineering tasks.

| Date | Run ID | Model | Instances | Resolved | Accuracy | Notes |
|------|--------|-------|-----------|----------|----------|-------|
| early baseline | baseline-10-final | opus | small sample | none | none | all instances exceeded the configured per-instance timeout |

### Findings

**Current state:** 0% baseline - all instances timeout before producing patches.

**Root causes identified:**
1. **Timeout too short:** the initial per-instance timeout was insufficient for opus on complex tasks
2. **No Docker isolation:** Dependencies may be missing (Gap #2 per methodology report)
3. **Agent prompt not optimized:** Current prompt may encourage exploration over solution

**Recommended next steps:**
1. Raise `instance_timeout` in the eval config (see `evals/registry/swe-bench.yaml`)
2. Test with sonnet model (faster response)
3. Implement Docker-based evaluation (#2157)

See `reports/research/2026-02-03-swe-bench-evaluation-methodology.md` for full gap analysis.

Results stored in `evals/results/swe-bench/baseline-*/`.

### Running Evaluations

```bash
# Run 10 instances (default)
python -m evals.templates.swe_bench --spec evals/registry/swe-bench.yaml

# Custom instance count
python -m evals.templates.swe_bench --max-instances 5 --run-id my-test

# Dry run (validate without execution)
python -m evals.templates.swe_bench --dry-run
```

See `evals/registry/swe-bench.yaml` for configuration.

## Documentation

See `benchmarking.md` at the repo root for full documentation.
