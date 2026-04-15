# Trustworthy Vibe Coding Benchmark

A benchmark for evaluating LLM agents on producing verified, efficient
implementations of Elias-Fano encoding — from literature research through
formal proofs to extracted runnable code.

## Project context

This project explores the "Proofs as Reviews" thesis: LLMs vibe-code at
high speed, proof checkers (Rocq, Lean, …) verify correctness mechanically.
The human reviews only the specification (~20 lines) and a few lines of
unverified C stubs. Everything else is machine-checked.

The benchmark compares LLM agents (and potentially automated provers) on
how well they can autonomously produce a verified Elias-Fano implementation.

## Benchmarks

The benchmark suite lives in `benchmarks/` with Docker-based evaluation.
See `benchmarks/README.md` for full details and quick start.

### Benchmark A — The Logical Core (Auto-Formalization)

Can the agent go from 8 `Conjecture` statements to Qed on abstract
(Z-level) correctness proofs?

- **Input:** `EliasFanoSpec.v` with 8 conjectures
- **Output:** `EliasFano.v` with concrete definitions and proofs
- **Metric:** Auto-formalization rate (0–8)
- **Evaluation:** `benchmarks/harness/evaluate_a.sh`

**Known issue:** The `space_bound` conjecture is vacuous — `bit_size`
is a `Parameter` that the implementation defines freely, so an identity
encoding with `bit_size := 0` satisfies it. See FIXME in
`theories/EliasFanoSpec.v`.

### Benchmark B — The Implementation Gap (Refinement Proofs)

Given verified Z-level proofs and concrete Int63 implementations,
can the agent bridge the refinement gap?

- **Input:** Skeleton `EliasFanoInt63.v` (implementations given, proofs stripped)
- **Output:** Filled-in proofs for 5 agreement theorems
- **Metric:** Agreement theorems proved (0–5), expansion factor
- **Evaluation:** `benchmarks/harness/evaluate_b.sh`

### Benchmark C — Deferred

Optimization benchmark (naive-but-proved → fast). Deferred until A and B
are validated.

## Build

Use `./build.sh` (wrapper around `opam exec -- dune build`).

```
./build.sh
```

## Environment

- Local opam switch at project root
- Rocq 9.1.1, coq-coqutil 0.0.7 (for bitblast tactic)
- OCaml 5.3.0, dune 3.21
- sux and sdsl C++ reference implementations in `bench/`

## Key files

| File | Role |
|------|------|
| `theories/EliasFanoSpec.v` | Specification (conjectures to prove) |
| `theories/EliasFano.v` | Z-level implementation + proofs |
| `theories/EliasFanoInt63.v` | Int63/PArray refinement + proofs |
| `extract/elias_fano.mli` | OCaml interface contract |
| `extract/elias_fano.ml` | Hand-written OCaml implementation |
| `bench/run.sh` | Oracle + benchmark runner |
| `bench/bench_ocaml.ml` | OCaml benchmark with oracle checks |
| `benchmarks/` | Docker-based benchmark suite (A and B) |
| `benchmarks/harness/run.sh` | Agent-agnostic benchmark orchestrator |
| `slides/proofs_as_reviews.md` | "Proofs as Reviews" presentation |

## Permissions

- Writing files in `/tmp/` is always allowed — do not prompt for confirmation.
- Using shell redirection (`<<`, `>`, `|`) in Bash commands is always allowed.
