# rocq-claude — verified Elias-Fano in Rocq

[Elias-Fano](https://en.wikipedia.org/wiki/Elias%E2%80%93Fano_coding) is a
near-optimal encoding for monotone sequences of natural numbers — it stores a
sorted list of `n` values drawn from `[0, U)` in about
`n · (2 + ⌈log₂(U/n)⌉)` bits while keeping random access fast. It is a
workhorse of inverted indices, succinct data structures, and graph
compression.

This repository contains a **formally verified** implementation of Elias-Fano,
produced by an LLM agent (Claude, via Claude Code) and **mechanically checked
by the Rocq proof assistant**. It is the origin project for the "Proofs as
Reviews" thesis: the machine vibe-codes and proves; the human reviews only the
~20-line specification and a single trusted C stub. Every proof is
kernel-checked. The only trusted axiom is `popcount_spec`, backed by a small C
`popcount` stub used by the extracted OCaml.

| | |
|---|---|
| Method | Rocq 9.1.1, coq-coqutil 0.0.7, OCaml 5.3.0 extraction |
| Agent | Claude via Claude Code + `rocq-mcp` (human-steered) |
| Model | Not recorded for the main development (March 2026 transcripts not retained). Benchmark harness runs (`benchmarks/results/`, 2026-03-21) record `model=sonnet`. |
| Dates | 2026-03-09 (`225ce38`) → 2026-06-11 (`34cf20e`) |
| Verdict | **Complete.** All 8 spec conjectures proved at Z level; full Int63/PArray refinement with all agreement theorems proved; single trusted axiom `popcount_spec` backed by a C stub. |

## Quick start

Prerequisites: a local [opam](https://opam.ocaml.org/) switch with Rocq 9.1.1,
coq-coqutil 0.0.7, OCaml 5.3.0, and dune 3.21.

```sh
opam install . --deps-only   # first time, into a local switch
./build.sh                   # wrapper around: opam exec -- dune build
```

`./build.sh` builds and kernel-checks the proofs (the `benchmarks/` tree is
excluded from the default build). To run the agent-evaluation benchmark suite,
see [`benchmarks/README.md`](benchmarks/README.md).

## What's verified

- `theories/EliasFanoSpec.v` — 8 conjectures, the human-reviewed surface.
- `theories/EliasFano.v` — Z-level implementation + proofs (~1100 lines).
- `theories/EliasFanoInt63.v` — Int63/PArray refinement (~3500 lines), with all
  agreement theorems proved against the Z-level spec.
- `extract/` — OCaml extraction + C stubs (popcount, fast Uint63 ops).

## Key commits

- `225ce38` (2026-03-09) — initial verified encoding: Rocq proofs + OCaml extraction
- `699f6c3` (2026-03-11) — last 4 admitted lemmas in `EliasFanoInt63.v` proved
- `e6004f1` (2026-03-14) — benchmark suite, 4 implementations
- `66b64cd` (2026-03-15) — `PROOF_NOTES.md`: proof-engineering lessons
- `7ad225f` (2026-04-15) — vacuous `space_bound` conjecture documented (FIXME)
- `05208fc` (2026-06-10) — vacuous `space_bound` fixed: serialization-based spec, real proof
- `34cf20e` (2026-06-11) — benchmarks tree with kernel-verified evaluation

## Layout

- `theories/` — the Rocq specification, Z-level proofs, and Int63 refinement.
- `extract/` — OCaml extraction + C stubs (popcount, fast Uint63 ops).
- `benchmarks/` — agent-evaluation harness; results from 2026-03-21 include one
  run (`a-20260321T052925`) where the agent exploited the then-vacuous
  `space_bound` — the bug fixed by `05208fc`.
- `bench/` — reference implementations (sux, sdsl) for performance comparison.
- `slides/proofs_as_reviews.md` — talk (DevFestNoz 2026-03-12, Tarides tech talk 2026-04-07).
- `PROOF_NOTES.md`, `FSTAR_FEASIBILITY.md`, `RUPICOLA_FEASIBILITY.md`,
  `VERIFIED_C_ROUTES.md` — engineering notes and routes-to-verified-C studies.
- `CLAUDE.md` — project instructions and benchmark protocol.

## License

MIT — see [`LICENSE`](LICENSE).

## Citation

See [`CITATION.cff`](CITATION.cff), or cite as: Cuihtlauac Alvarado,
*rocq-claude: verified Elias-Fano in Rocq (Proofs as Reviews)*, 2026.
