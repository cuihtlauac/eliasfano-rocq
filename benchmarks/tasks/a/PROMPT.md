# Benchmark A — The Logical Core

## Task

Implement Elias-Fano encoding on Z/lists in Rocq and prove all 8
conjectures in `theories/EliasFanoSpec.v`.

## What to produce

Write `theories/EliasFano.v` containing:

1. **Concrete definitions** for the abstract types and functions declared
   in `EliasFanoSpec.v`:
   - `encoded` (the encoding data structure)
   - `encode : Z -> list Z -> encoded`
   - `decode : encoded -> list Z`
   - `access : encoded -> nat -> Z`
   - `to_bits : encoded -> list bool` (serialization)
   - `of_bits : Z -> nat -> list bool -> encoded` (deserialization,
     given the universe and the element count)
   - `nextGEQ : encoded -> Z -> option Z`
   - `popcount : int -> int`

2. **Proofs** (no `Admitted`) of all 8 conjectures:
   - `round_trip` — decode after encode recovers the original list
   - `access_correct` — random access returns the correct element
   - `nextGEQ_found` — successor query returns a valid, large-enough element
   - `nextGEQ_smallest` — the result is the smallest such element
   - `nextGEQ_none` — None means no element is large enough
   - `space_bound` — the serialized encoding decodes back to the input
     and fits in n*(2 + ⌈log₂(U/n)⌉) bits (exact rational U/n)
   - `rank_select` — rank(select(i)) = i
   - `select_rank` — select(rank(pos)) = pos when pos holds a 1

## Algorithm hint

Elias-Fano encoding splits each value into lower bits (stored verbatim)
and upper bits (stored in a unary-coded bitvector). The key parameter is
`l = floor(log2(U/n))` where U is the universe size and n is the number
of elements. Each upper value `x >> l` is encoded as a gap in unary:
`(gap zeros) ++ [true]`.

## Environment

- Rocq 9.1.1 with Stdlib (ZArith, List, Bool, Sorting, Lia, Uint63)
- dune build system: run `eval $(opam env) && dune build theories/`
- `EliasFanoSpec.v` is already provided and must not be modified

## Constraints

- `theories/EliasFano.v` must compile with `dune build theories/`
- No `Admitted` allowed
- `popcount` may be declared as `Parameter` with `Axiom popcount_spec`
  (it is backed by a C stub in production)
- `Print Assumptions` on each theorem should show only `popcount_spec`
  (plus standard Uint63/PArray primitives from Stdlib)
- Do not modify `EliasFanoSpec.v` — the evaluator diffs it against a
  canonical copy
- Each theorem must prove the spec's *exact* conjecture statement: the
  evaluator kernel-checks this (`Lemma _ : <verbatim conjecture>.
  Proof. exact <your theorem>. Qed.`), so a renamed or weakened
  statement scores zero. Definitions restated from the spec (`sorted`,
  `ceil_log2`, …) must be definitionally identical to the spec's.
