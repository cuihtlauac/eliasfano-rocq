# Verified C via Rupicola/Bedrock2: Feasibility Study

Can the Z-level proofs in `theories/EliasFano.v` serve as the basis for a
verified C implementation of Elias-Fano encoding, using Rupicola and
Bedrock2?

## Background

### Current pipeline

```
EliasFanoSpec.v          Specification (8 conjectures)
       |
EliasFano.v              Z-level proofs (773 lines)
       |
EliasFanoInt63.v         Int63/PArray refinement (3451 lines)
       |
ExtractInt63.v           Extraction directives + overrides
       |                 (Obj.magic, C stubs, mutable arrays)
       v
EliasFanoInt63.ml        Generated OCaml
  + ef_popcount.ml       Popcount wrapper
  + ef_parray.ml         Mutable array shim
  + ef_uint63_fast.ml    C-stub wrappers
  + uint63_stubs.c       6 C stubs (lsl, lsr, div, rem, head0, tail0)
  + elias_fano_stubs.c   2 C stubs (popcount, ctz)
```

Trusted components: Rocq extraction, OCaml compiler, 8 C stubs (~70 lines),
`Obj.magic` casts, mutable-array linearity assumption.

### What are Bedrock2 and Rupicola?

**Bedrock2** [1] is an imperative C-like language embedded in Coq/Rocq,
with a verified compiler to RISC-V. Programs operate on machine words
(32 or 64-bit) and byte-addressed memory governed by separation logic.

**Rupicola** [2] is a relational compilation framework on top of Bedrock2.
You write functional Gallina annotated with `let/n` bindings, then `Derive`
a Bedrock2 function body via the `compile` tactic. The result can be
pretty-printed to C via `ToCString` or compiled to verified RISC-V.

**Fiat-crypto** [3] uses this pipeline in production to generate verified
cryptographic C primitives.

## What maps well

| Aspect | Current (Int63/Extraction) | Bedrock2/Rupicola |
|--------|---------------------------|-------------------|
| Word size | 63-bit (Uint63) | 64-bit native |
| Bitwise ops | `land/lor/lxor/lsl/lsr` | `and/or/xor/slu/sru` -- first-class |
| Z-level specs | `EliasFano.v` | Reusable as-is |
| Arrays | PArray (universe bugs, monomorphic wrappers) | Memory loads/stores via sep-logic |
| Shifts | Need bounds guards + C stubs | Native, specified via `Z.shiftl`/`Z.shiftr` |
| Word arithmetic | 63-bit modular, `uint63_stubs.c` for div/rem | 64-bit modular, native |

The 63-to-64-bit upgrade alone eliminates: the `uint63_stubs.c` file,
`ef_uint63_fast.ml`, every `Obj.magic` cast in `ExtractInt63.v`, and the
off-by-one `word_bits = 62` workaround in the hand-written OCaml.

## What is fundamentally different

### 1. Separation logic replaces PArray

The entire refinement layer changes proof methodology. Currently
`EliasFanoInt63.v` reasons about `PArray.get`/`PArray.set` with equational
lemmas (and monomorphic wrappers to dodge universe bugs). In Bedrock2,
arrays are contiguous memory regions governed by separation-logic
predicates:

```coq
(* current *)
Record ef63 := { ef63_lower : array int; ef63_upper : array int; ... }.

(* bedrock2 -- hypothetical *)
sizedlistarray_value access_size.word lower_ptr n *
sizedlistarray_value access_size.word upper_ptr m * ...
```

This is not a port of `EliasFanoInt63.v`. It is a **rewrite** of the
refinement layer (3451 lines) with a different proof style.

### 2. No popcount/ctz intrinsics

Bedrock2 has no `__builtin_popcountl` or `__builtin_ctzl`. Options:

- **Software popcount.** Rupicola ships a bit-by-bit loop in `DownTo.v`.
  Fully verified, but ~10x slower than hardware -- unacceptable for
  Elias-Fano where select performance dominates.
- **`interact` escape hatch.** Bedrock2's `interact` mechanism calls
  external functions with an axiomatic spec. Same trust story as the
  current `popcount_spec` axiom backed by 6 lines of C.

### 3. No recursion, no heap allocation

Bedrock2 forbids recursive functions (guaranteeing no stack overflow) and
has no `malloc`. The caller pre-allocates all output buffers. Both
constraints are natural for Elias-Fano: all loops are bounded, and the
caller knowing the output size is standard for C APIs in this domain.

### 4. Explicit loop invariants

Rupicola automates `let/n` sequences but requires explicit invariants for
loops. The encoding function alone has 4 nested loops (fill lower bits,
build upper bitvector, cumulative popcount, select indices) each needing
an invariant that relates partial state to the Z-level spec. This is where
most proof effort would concentrate.

## Trust comparison

```
CURRENT PIPELINE                    TRUST
-----------------------------------------------
EliasFano.v        Z proofs         verified
EliasFanoInt63.v   Int63 refinement verified
Rocq Extraction    OCaml codegen    trusted (unverified)
ExtractInt63.v     Obj.magic casts  trusted (linearity assumption)
OCaml 5.3 compiler                  trusted
uint63_stubs.c     6 C stubs        trusted (~50 lines)
elias_fano_stubs.c popcount/ctz     trusted (~6 lines)
```

### Option A -- Bedrock2 to C

```
PROPOSED PIPELINE                   TRUST
-----------------------------------------------
EliasFano.v        Z proofs         verified
Rupicola layer     refinement       verified (new)
ToCString          C pretty-print   trusted (simple, <500 LOC)
gcc/clang                           trusted
interact stubs     popcount/ctz     trusted (~6 lines)
```

Removes: Rocq Extraction, OCaml compiler, `Obj.magic`, linearity
assumption, `uint63_stubs.c`. Adds: `ToCString` (simpler than Extraction).

### Option B -- Bedrock2 to RISC-V

```
PROPOSED PIPELINE                   TRUST
-----------------------------------------------
EliasFano.v        Z proofs         verified
Rupicola layer     refinement       verified (new)
Bedrock2 compiler  to RISC-V        verified (Coq proof)
interact stubs     popcount/ctz     trusted (~6 lines)
```

End-to-end verified from spec to machine code. Only the popcount/ctz
stubs remain unverified (same 6 lines as today).

## Options

### Option 1: Spike -- single operation through Rupicola

Port `bv_get` (read one bit from a packed bitvector) through Rupicola
with 64-bit semantics. This exercises:

- Rocq 9.1.1 compatibility with bedrock2/rupicola
- Bitwise compilation (`land`, `lsr`)
- Word-array memory access
- Connection back to the Z-level `nth_bit` spec

**Effort:** 1--2 days.
**Output:** Working `bv_get.c` + Rocq proof of correctness, or a clear
"blocked by X" report.

### Option 2: Core read path -- access + select

Port `bv_get`, `bv_select` (popcount-based), and `access63` to produce a
C library that can look up the i-th element of a pre-built Elias-Fano
structure. The structure itself is built by the existing OCaml code and
passed via a C-compatible memory layout.

**Effort:** 2--4 weeks (separation-logic learning curve dominates).
**Output:** Verified C `ef_access(enc, i)` with correctness theorem
connecting to `access_ef_correct` in `EliasFano.v`.

### Option 3: Full C library

Port encode, decode, access, and nextGEQ to produce a standalone verified
C library. Replaces the OCaml extraction pipeline entirely.

**Effort:** 2--4 months (rewrite of the 3451-line refinement layer).
**Output:** Self-contained `elias_fano.c` + `elias_fano.h` with
end-to-end correctness theorems.

### Option 4: Benchmark C -- new benchmark tier

Define a new benchmark tier (Benchmark C, currently deferred) around
Rupicola: given Z-level proofs and a Bedrock2 skeleton, can an LLM agent
produce the refinement proofs and generate verified C? This reframes the
Rupicola work as a benchmark artifact rather than a production target.

**Effort:** Depends on Option 1--3 as prerequisite.
**Output:** Benchmark C evaluation harness + reference solution.

## Preflight checklist

Ordered by priority. Each item is a go/no-go gate for the options that
depend on it.

### P0 -- Blocks everything

- [ ] **Rocq 9.1.1 compatibility.** Install `coq-bedrock2` and
  `coq-rupicola` in the project's opam switch. Released packages
  (`coq-bedrock2.0.0.9`, `coq-rupicola.0.0.11`) target Rocq 9.0.x.
  Try dev pins from `mit-plv/bedrock2` and `mit-plv/rupicola` master.
  If the Rocq API has changed enough to break compilation, stop here.

  ```
  opam pin add coq-bedrock2 --dev-repo
  opam pin add coq-rupicola --dev-repo
  ```

- [ ] **`BasicC64Semantics` works.** Verify that the 64-bit semantics
  module (`BasicC64Semantics.v`) compiles and that `ToCString` produces
  valid C for a trivial function (e.g., `word.and` of two arguments).

### P1 -- Blocks Options 1--4

- [ ] **`bv_get` spike compiles.** Write a Rupicola `bv_get` that reads
  bit `pos` from a word array. This tests: array memory access, bitwise
  ops (`lsr`, `land`), division by word size, the `compile` tactic on a
  non-trivial body. If the `compile` tactic cannot handle the index
  arithmetic, assess whether a custom compilation lemma is feasible.

- [ ] **Z-level connection.** Prove that the Bedrock2 `bv_get` satisfies
  the same spec as `nth_bit` in `EliasFano.v`. This tests whether the
  existing Z proofs can be reused through the Bedrock2 `word.unsigned`
  bridge or whether significant glue is needed.

### P2 -- Blocks Options 2--4

- [ ] **`interact` for popcount.** Define a Bedrock2 `interact` action
  for popcount with the `popcount_spec` axiom. Verify that it integrates
  with Rupicola's `compile` tactic (i.e., the tactic can handle a `let/n`
  binding that calls an external function).

- [ ] **Separation-logic array invariants.** Write the `bv_agreement`
  equivalent as a separation-logic predicate relating a word-array region
  to a `list bool` (the Z-level bitvector). This is the foundational
  abstraction that all higher-level proofs build on.

### P3 -- Blocks Options 3--4

- [ ] **Loop compilation for `encode`.** Prototype the encoding loop
  (filling the lower-bits array) in Rupicola. Assess whether
  `ranged_for_u` handles the pattern or whether a custom compilation
  lemma is needed. The encoding loop modifies two arrays and an index
  simultaneously -- the hardest compilation pattern in the codebase.

- [ ] **Memory layout for `ef_encoded`.** Design the C struct layout for
  the Elias-Fano record (lower array, upper bitvector, cumulative
  popcount, select indices, metadata). Define the separation-logic
  predicate that bundles all components. This predicate must be
  ergonomic enough that proofs about individual operations can frame
  away the components they don't touch.

### P4 -- Exploration only

- [ ] **LiveVerif alternative.** LiveVerif [4] (PLDI 2024) is a newer
  layer on top of Bedrock2 for more natural verified C programming. It
  may reduce the separation-logic proof burden. Assess maturity and
  Rocq 9.1.1 compatibility. LiveVerif is more experimental than Rupicola
  but its proof style is closer to the equational reasoning already used
  in `EliasFanoInt63.v`.

- [ ] **Verified RISC-V backend.** If Option B (end-to-end verified
  compilation) is a goal, check that the Bedrock2 RISC-V compiler
  handles all instructions emitted by the Elias-Fano code. The compiler
  targets RV32IM/RV64IM; verify that 64-bit multiply-high (`mulhuu`,
  needed for fast division) is supported.

## Verdict

**Feasible but expensive.** The Z-level proofs in `EliasFano.v` are
directly reusable. The refinement layer (`EliasFanoInt63.v`) must be
rewritten, not ported -- different proof methodology, different memory
model, different word size. The trust story strictly improves (especially
Option B), and the 63-to-64-bit upgrade eliminates several workarounds.

**Recommendation:** Execute the preflight checklist through P1 (1--2 days).
If P0 and P1 pass, the path to Option 2 (verified C read path) is clear.
If P0 fails on version compatibility, reassess when Rocq Platform 9.1
ships bedrock2/rupicola packages.

## References

1. Erbsen, Gruetter, Choi, Wood, Chlipala. **Integration Verification
   across Software and Hardware for a Simple Embedded System.** PLDI 2021.
   [mit-plv/bedrock2](https://github.com/mit-plv/bedrock2)

2. Pit-Claudel, Philipoom, Jamner, Erbsen, Chlipala. **Relational
   Compilation for Performance-Critical Applications.** PLDI 2022.
   [mit-plv/rupicola](https://github.com/mit-plv/rupicola)

3. Erbsen, Philipoom, Gross, Sloan, Chlipala. **Simple High-Level Code
   for Cryptographic Arithmetic -- With Proofs, Without Compromises.**
   IEEE S&P 2019.
   [mit-plv/fiat-crypto](https://github.com/mit-plv/fiat-crypto)

4. Gruetter, Chlipala. **LiveVerif: a Verification Framework for Verified
   Systems Software in Rocq.** PLDI 2024.
   [mit-plv/bedrock2 LiveVerif/](https://github.com/mit-plv/bedrock2/tree/master/LiveVerif)

5. Vigna. **Broadword Implementation of Rank/Select Queries.** WEA 2008.
   (Elias-Fano select algorithm reference.)

6. Leroy. **Well-founded recursion done right.** CoqPL 2024.
   (Acc-based extraction pattern used in current `EliasFanoInt63.v`.)

7. Sakaguchi. **Program Extraction for Mutable Arrays.** FLOPS 2018.
   (Linearity argument for current PArray-to-OCaml-array extraction.)

8. Vigna. **Quasi-Succinct Indices.** WSDM 2013.
   (Elias-Fano encoding for inverted indices; benchmark methodology reference.)

---

## Appendix: Benchmarking verified C against Sux

### Existing framework

The project already has a multi-implementation benchmark suite in `bench/`
that compares four implementations on identical workloads:

| Label | Language | Library |
|-------|----------|---------|
| sux | C++20 | `sux::bits::EliasFano<>` (Vigna) [5] |
| sdsl | C++20 | `sdsl::sd_vector<>` (xxsds/sdsl-lite v3) |
| ocaml | OCaml 5.3 | Hand-written `elias_fano` |
| extracted | OCaml 5.3 | Rocq-extracted `EliasFanoInt63` |

Adding a fifth implementation (`bedrock2` -- Rupicola-generated C) requires
no changes to the framework's core design. The suite already accommodates
C/C++ implementations alongside OCaml ones.

### Data protocol

All implementations read the same stdin format produced by `gen_data.ml`:

```
<value_1>           ─┐
...                   │ n sorted unique integers in [0, universe)
<value_n>           ─┘
---
<access_index_1>    ─┐
...                   │ 100,000 random indices in [0, n)
<access_index_nq>   ─┘
---
<nextgeq_value_1>   ─┐
...                   │ 100,000 random values in [0, universe)
<nextgeq_value_nq>  ─┘
```

Universe = 10n (10% density). Deterministic seed = 42. Sizes: 1K, 10K,
100K, 1M, 10M, 100M.

### Measurement protocol

Every implementation follows the same protocol (see `bench/BENCH_REPORT.md`
for the full methodology):

1. **Timer:** `clock_gettime(CLOCK_MONOTONIC)`, nanosecond resolution
2. **Warm-up:** 3 untimed iterations
3. **Repetitions:** 15 measured iterations; report median, min, p25, p75
4. **Batching:** 100,000 queries per batch for access/nextGEQ; XOR-accumulate
   into a volatile sink to prevent dead-code elimination
5. **Oracle:** decode-all, 100 spot-check access, 100 spot-check nextGEQ
6. **Output:** one TSV row per (implementation, size, operation) triple

The Sux and SDSL harnesses (`bench/sux/bench_sux.cpp`,
`bench/sdsl/bench_sdsl.cpp`) already implement this protocol in C++.
A Bedrock2 harness follows the same pattern.

### Harness design for Bedrock2-generated C

The Bedrock2 pipeline produces C functions with `uintptr_t` arguments and
flat memory pointers. The benchmark harness wraps these in a C program
that handles I/O, timing, and oracle checks.

#### Generated code (from Rupicola + ToCString)

ToCString output uses a fixed style:

```c
/* Generated by Bedrock2 ToCString -- do not edit */
#include "bedrock2.h"   /* uintptr_t, br2_load/store helpers */

uintptr_t ef_access(uintptr_t lower, uintptr_t upper,
                    uintptr_t cum_popcnt, uintptr_t sel1,
                    uintptr_t l, uintptr_t n, uintptr_t i) {
  /* ... generated body ... */
}
```

All values are `uintptr_t` (64-bit on x86-64). Arrays are passed as raw
pointers. There are no structs in the generated output -- Bedrock2 has
no struct type. The harness must manage memory layout explicitly.

#### Harness structure (`bench/bedrock2/bench_bedrock2.c`)

```
bench/bedrock2/
  bench_bedrock2.c       Benchmark harness (I/O, timing, oracle)
  ef_generated.c         Rupicola ToCString output (checked in)
  ef_generated.h         Function signatures
  ef_stubs.c             interact stubs: popcount, ctz
  Makefile               gcc -O3 -march=native
```

The harness follows the same structure as `bench_sux.cpp`:

```c
// Sketch -- actual code depends on what functions Rupicola generates
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include "ef_generated.h"

typedef struct {
    uint64_t *lower;
    uint64_t *upper;
    uint64_t *cum_popcnt;
    uint64_t *sel1;
    uint64_t *sel0;
    uint64_t l, n, upper_bits;
} ef_t;

// Timer: same clock as all other implementations
static inline int64_t monotonic_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000000LL + ts.tv_nsec;
}
```

The harness calls the generated functions, passing struct fields as
individual `uintptr_t` arguments. This is the natural interface for
Bedrock2-generated code.

#### Memory layout

The central design question. Bedrock2 arrays are contiguous word-sized
regions. The harness allocates them with `malloc` and passes base pointers
to generated functions.

```
ef_t layout (all uint64_t arrays, 64 bits per word):

lower:      [ w_0 | w_1 | ... | w_{n-1} ]     n words, each storing l bits
upper:      [ w_0 | w_1 | ... | w_{m-1} ]     m words, packed bitvector
cum_popcnt: [ c_0 | c_1 | ... | c_{m-1} ]     cumulative popcount per word
sel1:       [ s_0 | s_1 | ... ]                select-one samples (period 512)
sel0:       [ s_0 | s_1 | ... ]                select-zero samples (period 512)
```

Key difference from current implementations: **64 bits per word** (not 63
for Int63, not 62 for hand-written OCaml). This means the bitvector
packing, index arithmetic, and popcount boundaries all shift. The Z-level
proofs in `EliasFano.v` are parameterized by `num_lower_bits` and work
for any word size, so the correctness argument carries over.

### Integration with `bench/run.sh`

The changes to the benchmark runner are minimal.

#### Build step

Add after the SDSL build block:

```bash
# --- Build Bedrock2 ---
B2="$SCRIPT_DIR/bedrock2"
if [ ! -f "$B2/bench_bedrock2" ] || \
   [ "$B2/bench_bedrock2.c" -nt "$B2/bench_bedrock2" ] || \
   [ "$B2/ef_generated.c" -nt "$B2/bench_bedrock2" ]; then
  echo "Compiling Bedrock2 benchmark..." >&2
  gcc -std=c17 -O3 -DNDEBUG -march=native \
    "$B2/bench_bedrock2.c" "$B2/ef_generated.c" "$B2/ef_stubs.c" \
    -o "$B2/bench_bedrock2" -lm
fi
```

#### Benchmark loop

Add one runner line per size, between the SDSL and OCaml runs:

```bash
echo "  bedrock2..." >&2
$TASKSET "$B2/bench_bedrock2" < "$DATA" || echo "  bedrock2 FAILED at n=$N" >&2
```

#### Oracle cross-check

The bedrock2 implementation joins the cross-implementation oracle at
n=10,000. No changes to the oracle protocol -- TSV output + stderr
oracle lines are already implementation-agnostic.

### Integration with `bench/plot.gp`

Add a fifth line style and data series to each subplot:

```gnuplot
set style line 5 lc rgb "#ff7f00" lw 2 pt 11 ps 0.8   # bedrock2 - orange
```

Then append to each `plot` command:

```gnuplot
  "< awk -F'\\t' '$1==\"bedrock2\" && $3==\"access\"' ".tsv \
    using 2:4 with linespoints ls 5 title "bedrock2", \
```

### What the comparison reveals

The interesting comparison is not "verified C vs. OCaml" (that's
expected to favor C) but **"verified C vs. Vigna's hand-optimized
C++"**. Both are native code with the same compiler backend; the
difference is in algorithmic choices and the overhead of
verification-friendly code structure.

#### Expected performance characteristics

| Factor | Sux (C++) | Bedrock2 (C) | Impact |
|--------|-----------|--------------|--------|
| Word size | 64-bit | 64-bit | Parity |
| Select algorithm | Broadword [5] | Popcount + linear scan | Sux 2-4x faster |
| Popcount | `__builtin_popcountl` | Same (via `interact` stub) | Parity |
| Compiler | g++ -O3 | gcc -O3 | Parity |
| Memory layout | Class with pointers | Flat arrays | Slight Bedrock2 advantage |
| Branch prediction | Hand-tuned branchless | Rupicola-generated | Unknown |

The main performance gap will be the select algorithm. Sux uses Vigna's
broadword select [5] -- a single branch-free instruction sequence that
finds the k-th set bit in a 64-bit word without loops. The Bedrock2
implementation would use popcount-based scanning (clear lowest set bit
in a loop), same as the current OCaml implementations.

Closing this gap would require implementing broadword select in Rupicola
and proving it correct -- a significant verification effort but one that
would bring the verified C to near-parity with Sux on access queries.

#### Expected results (n=100M, estimates)

| Operation | sux | bedrock2 (est.) | Ratio |
|-----------|----:|----------------:|------:|
| access | 34 ns | 80--120 ns | 2--4x |
| nextGEQ | 144 ns | 200--300 ns | 1.5--2x |
| decode | 372 ms | 350--450 ms | ~1x |
| encode | 3421 ms | 400--600 ms | 0.1--0.2x (faster) |
| space | 5.95 b/e | ~5.0 b/e | 0.84x (smaller) |

The access estimate reflects the popcount-vs-broadword gap. The encode
estimate reflects that Sux builds heavy precomputed structures while a
direct packing loop (which Bedrock2 would generate) is much simpler.
Decode should be near parity since both implementations scan the
bitvector linearly.

### Phased approach

Building the benchmark harness can proceed incrementally, aligned with
the Options in the main document.

**Phase 1 (with Option 1 -- bv_get spike):**
No benchmark yet. Validate that ToCString produces compilable C and
that the generated code can be called from a trivial `main()`.

**Phase 2 (with Option 2 -- access + select):**
Build a read-only benchmark harness. The OCaml `encode` builds the
structure, exports it to a binary file, and the C harness loads it.
Benchmark access and nextGEQ only. This avoids the complexity of
encoding in Bedrock2 while still producing the most interesting
comparison (point-query latency vs. Sux).

Export format (binary, little-endian):
```
[header]  n: uint64, l: uint64, upper_bits: uint64
[lower]   n × uint64
[upper]   ceil(upper_bits / 64) × uint64
[cum_pop] ceil(upper_bits / 64) × uint64
[sel1]    ceil(n / 512) × uint64
[sel0]    ceil((upper_bits - n) / 512) × uint64
```

The OCaml exporter repacks 62-bit words into 64-bit words during export.
This is a one-time cost, not part of the timed benchmark.

**Phase 3 (with Option 3 -- full C library):**
Full benchmark harness with encode. The C harness reads values from
stdin, calls the generated `ef_encode`, and benchmarks all four
operations. No binary export needed -- the Bedrock2 C is self-contained.

### Summary

The existing benchmark framework is designed for exactly this kind of
comparison. Adding a Bedrock2 implementation requires:

- [ ] A C benchmark harness following the stdin/TSV/oracle protocol
- [ ] An `ef_stubs.c` for popcount/ctz (`interact` stubs, ~10 lines)
- [ ] A build rule in `run.sh` (5 lines)
- [ ] A plot line in `plot.gp` (5 lines per subplot)
- [ ] Phase 2: a binary export format for OCaml-to-C data transfer

The framework changes are trivial. The real work is producing the
Rupicola-generated C functions that the harness wraps -- that is the
subject of the main feasibility study above.
