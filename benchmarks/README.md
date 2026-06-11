# Elias-Fano Verified Implementation Benchmarks

Two benchmarks for evaluating LLM agents on producing formally verified
code, from auto-formalization through machine-integer refinement.

## Benchmarks

### Benchmark A — The Logical Core (Auto-Formalization)

**What it tests:** Can the agent go from high-level conjectures to Qed
on abstract (Z-level) correctness proofs?

- **Input:** `EliasFanoSpec.v` with 8 `Conjecture` statements
- **Output:** `EliasFano.v` with concrete definitions and proofs
- **Metric:** Auto-formalization rate (0–8 conjectures proved)
- **Time limit:** 30 minutes for compilation

### Benchmark B — The Implementation Gap (Refinement Proofs)

**What it tests:** Given verified Z-level proofs and concrete Int63
implementations, can the agent bridge the refinement gap?

- **Input:** `EliasFanoSpec.v`, `EliasFano.v` (read-only), skeleton
  `EliasFanoInt63.v` with implementations given and proofs as `Admitted`
- **Output:** Filled-in `EliasFanoInt63.v` with all proofs
- **Metric:** Agreement theorems proved (0–5), expansion factor (ΔP)
- **Time limit:** 60 minutes for compilation

### Evaluation integrity

A theorem only scores if the kernel certifies it proves the *verbatim*
target statement: the evaluator extracts each conjecture from the
canonical (agent-unwritable) spec/skeleton and compiles
`Lemma _ : <verbatim statement>. Proof. exact <agent theorem>. Qed.`
Name-grepping alone would let a renamed or weakened statement pass.
The evaluators also diff the read-only inputs against canonical copies,
check that restated spec definitions are definitionally identical
(benchmark A) and that the given implementations appear verbatim
(benchmark B), and inspect `Print Assumptions` for unexpected axioms.

## Quick start

### Prerequisites

- Docker (tested with Docker 24+)
- ~8 GB disk space for images

### Build images

```bash
cd benchmarks

# Build base image (OCaml 5.4 + Rocq 9.1.1 + coqutil + dune)
docker build -t eliasfano-bench-base -f docker/Dockerfile.base .

# Build benchmark-specific image
docker build -t eliasfano-bench-a -f docker/Dockerfile.a .
```

### Run with Claude Code

The harness includes a retry loop that feeds build errors back to Claude
via `--resume`, so the agent can iterate on compilation failures.

```bash
cd benchmarks/harness
./run.sh a --claude                          # default: sonnet, 5 retries
./run.sh a --claude --model opus --max-retries 10
./run.sh b --claude --max-retries 3
```

**Prerequisites:** Claude Code credentials at `~/.claude/.credentials.json`
and `~/.claude.json`, and `claude` on `PATH`.

**How it works:**
1. Sends the task prompt via `claude -p --output-format json`
2. Captures the `session_id` from the JSON response
3. Runs `dune build theories/`
4. If the build fails, feeds the first 200 lines of the error back via
   `claude -p --resume <session_id>`
5. Repeats up to `--max-retries` times (default 5)

Artifacts are saved to `benchmarks/results/<benchmark>-<timestamp>/`.
Monitor progress from another terminal:

```bash
tail -f benchmarks/results/a-*/run.log       # live harness log
ls benchmarks/results/a-*/attempts/           # .v snapshots per attempt
cat benchmarks/results/a-*/build_error_0.log  # full build error from attempt 0
```

The output directory contains:
- `run.log` — live log (attempt status, build pass/fail, timestamps)
- `attempts/<n>/*.v` — snapshot of `.v` files after each Claude attempt
- `build_error_<n>.log` — full build error for each failed attempt
- `response_<n>.json` — raw Claude JSON response per attempt
- `eval.log` — final evaluation output

Key points:
- `--user $(id -u):$(id -g)` — must match the UID owning `~/.claude/.credentials.json`
- `--network host` — needed for API access (and web search in Benchmark A)
- `CLAUDE_CODE_MAX_OUTPUT_TOKENS=128000` — set automatically by the harness
- `--dangerously-skip-permissions` — safe here since the container is a sandbox
- `--resume` (not `--continue`) is used to avoid conflicts between concurrent runs

**Manual mode** (no `--claude` flag) still works — it starts an interactive
shell where you can run any agent:

```bash
./run.sh a                                   # interactive shell
docker exec -it eliasfano-bench-a-run bash   # attach in another terminal
```

### Validate with ground truth

```bash
cd benchmarks

docker run --rm \
  -v "$(pwd)/ground-truth/a/theories/EliasFano.v:/workspace/theories/EliasFano.v" \
  -v "$(pwd)/harness/evaluate_a.sh:/evaluate.sh:ro" \
  eliasfano-bench-a bash -c 'eval $(opam env) && bash /evaluate.sh /workspace'
```

### Evaluate a local workspace (no Docker)

```bash
cd benchmarks/harness
./run.sh a --eval-only /path/to/workspace
```

## Directory structure

```
benchmarks/
  README.md                        # This file
  docker/
    Dockerfile.base                # OCaml 5.3 + Rocq 9.1.1 + coqutil + dune
    Dockerfile.a                   # Base + pre-built EliasFanoSpec.vo
    Dockerfile.b                   # Base + pre-built EliasFano.vo
  harness/
    run.sh                         # Build image, start container, evaluate
    run_claude.sh                  # Claude Code retry loop (--resume)
    evaluate_a.sh                  # Benchmark A evaluation
    evaluate_b.sh                  # Benchmark B evaluation
  tasks/
    a/                             # Files for Benchmark A
      PROMPT.md                    # Agent prompt
      theories/
        EliasFanoSpec.v            # 8 conjectures to prove
        dune
      dune-project
    b/                             # Files for Benchmark B
      PROMPT.md                    # Agent prompt
      theories/
        EliasFanoSpec.v            # Spec (read-only)
        EliasFano.v                # Z-level proofs (read-only)
        EliasFanoInt63_skeleton.v  # Implementations given, proofs stripped
        dune
      dune-project
  results/                          # Output artifacts from --claude runs
  ground-truth/                    # Reference solutions (not visible to agent)
    a/theories/EliasFano.v
    b/theories/EliasFanoInt63.v
```

## Prior art alignment

| Pattern | SWE-bench | VeriBench | Ours |
|---------|-----------|-----------|------|
| Environment | Docker per-instance | Lean pre-installed | Docker + Rocq + OCaml |
| Agent input | Issue text + repo | Problem + spec | Prompt + starter files |
| Evaluation | Test suite (opaque) | Lean kernel (opaque) | Rocq kernel + oracle (opaque) |
| Metric | Pass@1 | Proof rate | Per-benchmark (see above) |

## Evaluation criteria

### Benchmark A

1. `dune build theories/` succeeds (timeout 30 min)
2. No `Admitted` in `EliasFano.v`
3. Each of 8 conjecture names has a corresponding `Theorem`/`Lemma`
4. `Print Assumptions` shows no unexpected axioms

### Benchmark B

1. `dune build theories/` succeeds (timeout 60 min)
2. No `Admitted` outside `EliasFanoSpec.v`
3. Each of 5 agreement theorem names has a corresponding proof
4. `Print Assumptions` shows only `popcount_spec` (expected axiom)

## Benchmark C (Deferred)

A third benchmark testing optimization of a naive-but-proved implementation
is planned but deferred until Benchmarks A and B are validated.

## Environment details

- Base image: [ghcr.io/tarides/ocaml-devcontainer](https://github.com/tarides/ocaml-devcontainer)
- OCaml 5.4.0, dune 3.21.1, opam 2.5.0
- Rocq (Coq) 9.1.1, coq-coqutil 0.0.7 (bitblast tactic)
- Added opam repos: `coq-released`, `rocq-released`
