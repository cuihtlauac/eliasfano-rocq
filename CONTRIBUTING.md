# Contributing

Thanks for your interest in this project. It is a **research artifact** — a
demonstration of the "Proofs as Reviews" thesis (LLM-generated, machine-verified
Elias-Fano encoding). Issues and pull requests are welcome, but maintenance is
best-effort and there is no roadmap commitment.

## Building

The project uses a local opam switch, Rocq, and OCaml extraction.

```sh
opam install . --deps-only   # first time, into a local switch
./build.sh                   # wrapper around: opam exec -- dune build
```

Expected toolchain (see `CLAUDE.md` for details): Rocq 9.1.1,
coq-coqutil 0.0.7, OCaml 5.3.0, dune 3.21.

## Reporting issues

Please open a GitHub issue with:

- what you ran and the full command,
- the observed output (redact any local absolute paths),
- your Rocq / OCaml / dune versions.

## Pull requests

- Keep the specification surface (`theories/EliasFanoSpec.v`) small and
  reviewable — it is the human-reviewed trust boundary.
- Everything else must remain kernel-checked: no new axioms beyond the single
  documented `popcount_spec`, and `./build.sh` must pass.
- For the benchmark suite, see `benchmarks/README.md` for the evaluation
  protocol.

By contributing you agree that your contributions are licensed under the
project's MIT License (see `LICENSE`).
