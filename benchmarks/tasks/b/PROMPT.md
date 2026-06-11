# Benchmark B — The Implementation Gap

## Task

Prove the 5 agreement conjectures in `theories/EliasFanoInt63.v`.
The implementations are given. You must prove they agree with the
Z-level spec in `theories/EliasFano.v`.

## What to produce

Fill in the proof bodies in `theories/EliasFanoInt63.v` (which starts
as a skeleton with implementations given and proofs as `Admitted` or
`Conjecture`). You may add helper lemmas and additional `.v` files.

The 5 top-level agreement theorems to prove:

1. **`access63_agrees`** — `access63` on Int63 agrees with `access_ef` on Z
2. **`decode63_agrees`** — `decode63` round-trips: `map to_Z (decode63 ...) = to_Z_list vals`
3. **`nextGEQ63_found`** — if `nextGEQ63` returns `Some r`, then `r` is in the list and `r >= v`
4. **`nextGEQ63_smallest`** — the result is the smallest element `>= v`
5. **`nextGEQ63_none`** — if `nextGEQ63` returns `None`, all elements are `< v`

## Given (read-only)

- `theories/EliasFanoSpec.v` — specification (conjectures as type signatures)
- `theories/EliasFano.v` — complete Z-level implementation and proofs

These files must not be modified.

## Given (in skeleton)

The skeleton `EliasFanoInt63.v` provides:
- All type definitions (`ef63`, `bv_agreement`, `valid_encoding`, etc.)
- All concrete implementations (`encode63`, `access63`, `decode63`, `nextGEQ63`)
- All utility functions (`bv_get`, `bv_set`, `bv_select`, `fill_lower`, `fill_upper`, etc.)
- Fast Acc-based variants (`bv_select_fast`, `access63_fast`, `decode63_fast`, `nextGEQ63_fast`)
- Supporting lemma *statements* (as `Admitted`) where useful

You must supply the proof bodies.

## Key challenges

- **Bitvector refinement**: proving `bv_get`/`bv_set` on packed Int63 arrays
  agrees with list-level `nth` on `list bool`
- **Popcount-based select**: proving `bv_select` (using `popcount` and `tail0`)
  agrees with `position_of_ith_one` on lists
- **Overflow safety**: every Int63 arithmetic operation must be shown to
  stay within `[0, 2^63)`
- **Encoding agreement**: proving `encode63` produces a `valid_encoding`
  w.r.t. the Z-level `encode`

## Environment

- Rocq 9.1.1 with Stdlib + coq-coqutil 0.0.7 (for `bitblast` tactic)
- dune build system: run `eval $(opam env) && dune build theories/`
- `EliasFanoSpec.v` and `EliasFano.v` are pre-built (`.vo` available)

## Constraints

- No `Admitted` allowed (outside `EliasFanoSpec.v`)
- The only acceptable axiom is `popcount_spec` (backed by C stub)
- `Print Assumptions` on each top-level theorem should show only
  `popcount_spec` plus standard Uint63/PArray primitives
- Do not modify `EliasFanoSpec.v` or `EliasFano.v` — the evaluator
  diffs them against canonical copies
- Do not modify the given definitions in the skeleton — the evaluator
  checks each `Definition`/`Fixpoint`/`Record` appears verbatim, and
  verifies each agreement theorem proves the skeleton's *exact*
  statement (kernel-checked via `exact`), not just a theorem with the
  right name

## Useful tactics and libraries

- `lia` — linear integer arithmetic
- `bitblast` (from coqutil) — bitwise reasoning on Z
- `Z.testbit`, `Z.land_ones`, `Z.bits_inj'` — Z-level bit manipulation
- PArray lemmas need monomorphic wrappers due to Rocq 9.1 universe bug
  (see skeleton comments)
