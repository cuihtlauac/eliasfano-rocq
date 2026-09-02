# Verified C via F*/Low*/KaRaMeL: Feasibility Study

Can the Elias-Fano encoding be re-implemented in F* and compiled to
verified C via the Low*/KaRaMeL pipeline?

This document is a companion to `RUPICOLA_FEASIBILITY.md`, which explores
the same goal (verified C) through a different route (Rupicola/Bedrock2,
staying in the Rocq ecosystem).

## Background

### What are F* and Low*?

**F*** [1] is a proof-oriented programming language combining dependent
types with SMT-based proof automation (Z3). Specifications are encoded as
refinement types and pre/postconditions on function signatures.

**Low*** [2] is a shallow embedding of a C-like subset within F*. You
write low-level code using F*'s full type system for proofs, then erase
the proofs to obtain a first-order C-like program.

**KaRaMeL** [3] (formerly KreMLin) translates the erased Low* AST to
readable C source code. This is the pipeline used by **HACL*** [4]
(245K lines of verified cryptographic C, deployed in Firefox, the Linux
kernel, Python, WireGuard, and mbedTLS).

### How the pipeline works

```
Pure F* spec              Mathematical functions over int/nat/Seq.seq
     |
Low* implementation       Machine integers (UInt64.t), buffers, structs
     |                    Proofs embedded in refinement types
     |                    Z3 discharges most proof obligations
     v
F* type-checker           Verifies memory safety + functional correctness
     |
Proof erasure             Strips ghost code, specifications, proof terms
     |
KaRaMeL                   Translates Low* AST to C11 source
     |
     v
elias_fano.c              Readable C with uint64_t, standard control flow
```

### Starting point

Unlike the Rupicola route (which reuses `EliasFano.v` as-is), the F*
route **cannot reuse any existing Rocq proofs**. F* and Rocq are
separate type theories with no proof interoperability mechanism. The
entire formalization -- specification, implementation, and proofs --
must be re-done in F* from scratch.

What can be reused: the *mathematical ideas* (algorithms, lemma
statements, proof strategies), the specification *design*
(`EliasFanoSpec.v` as a reference), and the architectural decisions
documented in `CLAUDE.md` and memory files. But no Rocq term, tactic
script, or proof object transfers.

```
REUSABLE                          NOT REUSABLE
-----------------------------------------------
Algorithm design                  EliasFano.v proofs (773 lines)
Spec structure (8 conjectures)    EliasFanoInt63.v proofs (3451 lines)
Lemma statements (as comments)    Rocq bitblast/lia automation
Bitvector packing strategy        PArray universe-bug workarounds
Benchmark infrastructure          ExtractInt63.v extraction overrides
```

## What maps well

| Aspect | Current (Rocq/Int63) | F*/Low* |
|--------|----------------------|---------|
| Word size | 63-bit (Uint63) | **64-bit native** (`UInt64.t` = `uint64_t`) |
| Bitwise ops | `land/lor/lxor/lsl/lsr` | `logand/logor/logxor/shift_left/shift_right` -- first-class |
| Proof automation | Manual tactics (lia, bitblast) | **Z3 automatic** for many obligations |
| Refinement bridge | `to_Z`/`of_Z` between Int63 and Z | `v : UInt64.t -> int` (same idea, built-in) |
| Arrays | PArray (universe bugs) | `LowStar.Buffer` -- C-native, no universe issues |
| Structs | No native support (records + extraction hacks) | **C structs** from F* records (first-class in KaRaMeL) |
| Generated C | OCaml (via Extraction) + C stubs | **Direct C** -- readable, production-quality |
| Division | C stub (`uint63_stubs.c`) | Native (`/^`), divisor-nonzero proved at type level |

The struct support is a notable advantage: the `ef_encoded` record would
compile directly to a C struct, unlike Bedrock2 (no structs) or the
current Rocq extraction (records become OCaml tuples with `Obj.magic`).

## What is fundamentally different

### 1. Complete rewrite, not a refinement layer swap

The Rupicola path reuses `EliasFano.v` (773 lines of Z-level proofs) and
rewrites only the refinement layer. The F* path rewrites everything:

| Component | Rupicola path | F* path |
|-----------|---------------|---------|
| Z-level spec + proofs (773 lines) | **Reused** | Rewritten in F* |
| Refinement layer (3451 lines) | Rewritten (sep-logic) | Rewritten (Low*) |
| Extraction overrides (69 lines) | Eliminated | Not applicable |
| C stubs (70 lines) | Reduced to ~6 lines | Reduced to ~6 lines |
| **Total rewrite** | **~3500 lines** | **~4200 lines** |

### 2. Z3 automation vs. interactive tactics

F* delegates most proof obligations to Z3 automatically. For the kinds
of lemmas in `EliasFano.v` (bitwise arithmetic, list induction,
modular arithmetic), the practical experience is:

| Lemma category | Z3 outlook | Rocq comparison |
|----------------|-----------|-----------------|
| Linear arithmetic | Excellent -- automatic | `lia` automatic |
| Bitwise identities (e.g. `land_ones`) | Good -- Z3 bitvector theory | `bitblast` automatic |
| Non-linear arithmetic (e.g. `log2` bounds) | Weak -- needs hints/lemma calls | `lia` + manual |
| Induction over lists | Needs fuel tuning or Meta-F* tactics | Explicit `induction` tactic |
| Modular arithmetic wrap-around | Good -- bitvector encoding | Manual in Rocq |

Net effect: the Z-level proofs would likely be *shorter* in F* (Z3
handles the easy cases silently), but the hard lemmas (induction,
non-linear bounds) would require comparable effort via Meta-F* tactics.

### 3. Z3 brittleness

Z3 proofs are sensitive to syntactic changes and version bumps. The
Everest project reports ~5% unstable query rate across large codebases.
This contrasts with Rocq's deterministic tactic execution. Practical
consequences:

- Proofs that pass today may fail after an F* or Z3 update
- The `--quake` option retries with different seeds to detect flaky proofs
- Debugging Z3 failures requires understanding SMT encoding, triggers,
  and fuel -- a different skill set from Rocq tactic debugging

### 4. Memory model: HyperStack vs. separation logic

Low* uses **HyperStack** -- a hierarchical region-based memory model with
stack frames and eternal (heap) regions. Arrays are `LowStar.Buffer`
values with ghost length. Aliasing is tracked via `LowStar.Modifies`
(a coarser alternative to full separation logic).

This is higher-level than Bedrock2's flat memory but lower-level than
PArray:

```
PArray (Rocq)        Functional arrays, equational reasoning
                     Universe bugs, extraction to mutable arrays
                     ↕
LowStar.Buffer (F*)  C-like buffers, Modifies-based reasoning
                     Direct compilation to C arrays
                     ↕
Bedrock2 memory      Byte-addressed, full separation logic
                     Closest to actual hardware
```

For Elias-Fano, Low*'s buffer model is a natural fit: arrays of
`UInt64.t` with pointer arithmetic map directly to C `uint64_t*`.

## Trust comparison

### Current pipeline (Rocq extraction)

```
COMPONENT                           TRUST
-----------------------------------------------
EliasFano.v        Z proofs         verified
EliasFanoInt63.v   Int63 refinement verified
Rocq Extraction    OCaml codegen    trusted (unverified)
ExtractInt63.v     Obj.magic casts  trusted (linearity assumption)
OCaml 5.3 compiler                  trusted
uint63_stubs.c     6 C stubs        trusted (~50 lines)
elias_fano_stubs.c popcount/ctz     trusted (~6 lines)
```

### F*/Low*/KaRaMeL pipeline

```
COMPONENT                           TRUST
-----------------------------------------------
EliasFano.fst      F* spec+proofs   verified (Z3 + F* kernel)
EliasFanoLow.fst   Low* impl        verified (memory safety + correctness)
Z3 4.13.3          SMT solver       trusted (witnesses checked by F* kernel)
F* type-checker    kernel           trusted
KaRaMeL            F* AST -> C      trusted (unverified)
gcc/clang          C compiler       trusted
assume val stubs   popcount/ctz     trusted (~6 lines)
```

### Rupicola/Bedrock2 pipeline (from companion document)

```
COMPONENT                           TRUST
-----------------------------------------------
EliasFano.v        Z proofs         verified (reused)
Rupicola layer     refinement       verified
ToCString / B2     C / RISC-V       trusted (ToCString) or verified (RISC-V)
gcc/clang          (C path only)    trusted
interact stubs     popcount/ctz     trusted (~6 lines)
```

### Comparison

| Trust aspect | Rocq extraction | F*/KaRaMeL | Rupicola (C) | Rupicola (RISC-V) |
|-------------|:-:|:-:|:-:|:-:|
| Proof checker | Rocq kernel | F* kernel + Z3 | Rocq kernel | Rocq kernel |
| Code generator | Extraction (unverified) | KaRaMeL (unverified) | ToCString (unverified) | Verified compiler |
| C compiler | OCaml compiler | gcc/clang | gcc/clang | N/A |
| Runtime | OCaml runtime | None (bare C) | None (bare C) | None (bare metal) |
| Linearity assumption | Yes (PArray) | No | No | No |
| `Obj.magic` casts | Yes | No | No | No |
| C stubs | ~70 lines | ~6 lines | ~6 lines | ~6 lines |
| **TCB size** | Large | Medium | Medium | **Smallest** |

F* and Rupicola-to-C have comparable trust stories: both trust an
unverified translation to C plus a C compiler. F* adds Z3 to the TCB
(witnesses are checked, but the solver itself could have bugs).
Rupicola-to-RISC-V has the smallest TCB of all options.

## Path to verified C

Two strategies are available: top-down (spec first, then implement) or
bottom-up (transliterate existing code, then verify). They can be
combined.

### Bottom-up alternative: start from `elias_fano.ml`

`extract/elias_fano.ml` (212 lines) is vibed OCaml implementing the
same algorithm as the verified `EliasFanoInt63.v`. Since F* is ML-like,
this code transliterates almost mechanically to Low*:

| OCaml | F*/Low* |
|-------|---------|
| `int` | `UInt64.t` |
| `int array` | `B.buffer UInt64.t` |
| `a.(i)` / `a.(i) <- x` | `B.index a i` / `B.upd a i x` |
| `land`/`lor`/`lsr`/`lsl` | `logand`/`logor`/`shift_right`/`shift_left` |
| `ref x` / `!r` / `r := v` | `B.alloca x 1ul` / `B.index r 0ul` / `B.upd r 0ul v` |
| `while`/`for` | `C.Loops.while` / `C.Loops.for` |
| `type t = { ... }` | F* record (KaRaMeL emits a C struct) |
| `external popcount` | `assume val popcount` |

**Step 1:** Transliterate to Low* (~1--2 days, mechanical).
**Step 2:** Add specs as pre/postconditions, guided by
`EliasFanoSpec.v` theorem statements.
**Step 3:** Prove correctness. Z3 discharges arithmetic obligations
inline; hard lemmas (induction, non-linear bounds) need Meta-F* tactics
or helper lemmas from a pure spec module.

This skips the separate "Z-level proofs" phase: you prove correctness
directly on the Low* implementation. The pure spec (Phase 1 below) can
be written incrementally, as needed by the proofs, rather than
up-front. Estimated total effort: **1.5--3 months** (vs 2--4 months
for the top-down path).

### Top-down path (spec first)

### Phase 1: Pure specification (re-port from Rocq)

Translate the 8 conjectures from `EliasFanoSpec.v` into F* type
signatures. This is a specification-only step -- no implementation.

```fstar
(* EliasFano.Spec.fst -- sketch *)

val encode: universe:nat -> vals:seq nat -> Tot encoded
val decode: enc:encoded -> Tot (seq nat)
val access: enc:encoded -> i:nat -> Tot nat

val round_trip:
  u:nat -> vals:seq nat{sorted vals /\ all_bounded u vals} ->
  Lemma (decode (encode u vals) == vals)

val access_correct:
  u:nat -> vals:seq nat{sorted vals /\ all_bounded u vals} ->
  i:nat{i < length vals} ->
  Lemma (access (encode u vals) i == index vals i)
```

**Effort:** 1--2 days. Mechanical translation of types.

### Phase 2: Z-level implementation + proofs

Implement `encode`, `decode`, `access`, `nextGEQ` as pure F* functions
over `int`/`nat`/`Seq.seq`, mirroring `EliasFano.v`. Prove the 8
conjectures.

The key functions to implement:
- `num_lower_bits`, `lower_bits`, `upper_value` (arithmetic)
- `build_upper` (unary bitvector construction)
- `encode`, `decode`, `access_ef` (core operations)
- `rank`, `select` (bitvector primitives)
- `nextGEQ` (successor query)

Z3 should handle most arithmetic lemmas automatically. The inductive
proofs (over `build_upper`, `select_go`, etc.) will need explicit
recursion with fuel or Meta-F* tactics.

**Effort:** 2--4 weeks. Guided by existing Rocq proofs as a roadmap.
Expect ~400--600 lines of F* (vs 773 lines of Rocq), since Z3
eliminates many explicit lemma invocations.

### Phase 3: Low* implementation

Write the machine-level implementation using `UInt64.t` and
`LowStar.Buffer`. This replaces `EliasFanoInt63.v`.

```fstar
(* EliasFano.Low.fst -- sketch *)

type ef_t = {
  lower: B.buffer UInt64.t;
  upper: B.buffer UInt64.t;
  cum_popcnt: B.buffer UInt64.t;
  sel1: B.buffer UInt64.t;
  sel0: B.buffer UInt64.t;
  l: UInt64.t;
  n: UInt64.t;
  upper_bits: UInt64.t;
}
```

This record compiles directly to a C struct via KaRaMeL:

```c
typedef struct {
  uint64_t *lower;
  uint64_t *upper;
  uint64_t *cum_popcnt;
  uint64_t *sel1;
  uint64_t *sel0;
  uint64_t l;
  uint64_t n;
  uint64_t upper_bits;
} EliasFano_Low_ef_t;
```

The refinement proofs connect the Low* implementation to the pure spec
via the `v` function (`UInt64.v : UInt64.t -> int`), just as
`EliasFanoInt63.v` connects Int63 to Z via `to_Z`.

**Effort:** 1--3 months. The bulk of the work. Comparable to the
3451-line `EliasFanoInt63.v`, but potentially shorter due to:
- Native 64-bit words (no 63-bit workarounds)
- C structs (no PArray universe bugs)
- Z3 automation for simple refinement obligations
- No extraction overrides (`ExtractInt63.v` disappears)

### Phase 4: KaRaMeL extraction + benchmark

Extract to C via KaRaMeL. Integrate with the benchmark framework
(see Appendix in `RUPICOLA_FEASIBILITY.md`). The generated C is
self-contained -- no OCaml runtime, no `Obj.magic`, no extraction hacks.

```bash
# Hypothetical build
krml -skip-linking EliasFano.Low.fst -o elias_fano.c
```

**Effort:** 1--2 days for extraction; 1 week for benchmark integration.

### Total estimated effort

| Phase | Effort | Lines (est.) | Rocq equivalent |
|-------|--------|-------------|-----------------|
| 1. Spec | 1--2 days | ~100 | EliasFanoSpec.v (137 lines) |
| 2. Z-level proofs | 2--4 weeks | 400--600 | EliasFano.v (773 lines) |
| 3. Low* refinement | 1--3 months | 1500--2500 | EliasFanoInt63.v (3451 lines) |
| 4. Extraction + bench | 1--2 weeks | ~200 (harness) | ExtractInt63.v + stubs |
| **Total** | **2--4 months** | **2200--3400** | **4430 lines Rocq** |

## Options

### Option F1: Spike -- bv_get in Low*

Write a Low* function that reads one bit from a packed `UInt64.t` buffer.
Extract to C via KaRaMeL. This validates:

- F* toolchain installation and version compatibility
- `UInt64.t` bitwise operations (`logand`, `shift_right`)
- `LowStar.Buffer` array access
- KaRaMeL C output quality
- Z3 handling of bitwise proof obligations

**Effort:** 1--2 days.
**Output:** `bv_get.c` + F* proof, or "blocked by X" report.

### Option F2: Pure spec + Z-level proofs only

Re-prove the 8 conjectures in pure F* (no Low*, no C output). This
validates:

- Whether Z3 can handle the bitvector arithmetic
- Whether inductive proofs over `build_upper`/`select` are tractable
- Proof effort comparison with Rocq (hard data for the benchmark)

**Effort:** 2--4 weeks.
**Output:** `EliasFano.Spec.fst` + `EliasFano.Impl.fst` with all 8
theorems proved. No C output.

### Option F3: Full Low* implementation + C extraction

Complete pipeline from spec to C. Produces a standalone `elias_fano.c`
comparable to what Rupicola Option 3 would produce.

**Effort:** 2--4 months.
**Output:** `elias_fano.c` + `elias_fano.h` with correctness proofs.

### Option F4: Benchmark tier -- F* vs Rocq auto-formalization

Use the F* route as a second benchmark language: given the same 8
conjectures (translated to F* type signatures), can an LLM agent produce
verified proofs in F*? Compare agent performance across proof assistants.

**Effort:** Depends on Option F2 as prerequisite for the reference
solution.
**Output:** Benchmark harness + reference F* solution.

## Preflight checklist

### P0 -- Blocks everything

- [ ] **F* toolchain installs.** Install F* and KaRaMeL in a fresh opam
  switch. Verify that the correct Z3 versions (4.8.5 and 4.13.3) are
  available. F* refuses to run with wrong Z3 versions.

  ```
  opam switch create fstar ocaml-base-compiler.5.3.0
  opam install fstar
  # Install KaRaMeL (version-coupled with F*)
  ```

- [ ] **KaRaMeL produces valid C.** Compile a trivial Low* function
  (e.g., `UInt64.logand` of two buffer elements) to C. Verify the output
  compiles with `gcc -O3` and runs correctly.

### P1 -- Blocks Options F1--F4

- [ ] **`bv_get` spike.** Write a Low* `bv_get` and extract to C.
  Test the same operations as the Rupicola P1 spike (bitwise ops, array
  access, division by word size).

- [ ] **Z3 handles bitwise arithmetic.** Check that Z3 can discharge
  the key bitwise lemmas from `EliasFano.v` when translated to F*:
  `land_ones`, `testbit_land`, `bits_inj`. If these need extensive
  manual proof, the Z3 automation advantage disappears.

### P2 -- Blocks Options F2--F4

- [ ] **Inductive proofs are tractable.** Translate `select_go_rank_gen`
  (the core induction for rank/select correctness) to F*. This is the
  hardest proof in `EliasFano.v`. If Z3 cannot handle it with reasonable
  fuel, and Meta-F* tactics are required, measure the effort against
  the Rocq `induction` tactic equivalent.

- [ ] **`assume val` for popcount.** Declare popcount as an `assume val`
  with the `popcount_spec` axiom. Verify that KaRaMeL generates a clean
  `extern` declaration and that linking with a C stub works.

### P3 -- Blocks Options F3--F4

- [ ] **Buffer-based bitvector abstraction.** Write the `bv_agreement`
  equivalent as an F* predicate relating a `Buffer UInt64.t` to a
  `Seq.seq bool`. This is the foundational abstraction for the Low*
  refinement layer. Assess whether LowStar.Modifies reasoning is
  sufficient or whether Steel/Pulse separation logic is needed.

- [ ] **ef_t struct extracts cleanly.** Define the `ef_t` record in F*
  and verify that KaRaMeL produces the expected C struct. Test that
  buffer fields compile to pointer members and scalar fields compile
  to value members.

### P4 -- Exploration only

- [ ] **Pulse for mutable construction.** If the encoding loop (which
  mutates multiple arrays simultaneously) is hard to verify with
  LowStar.Modifies, assess whether Pulse's separation logic helps.
  Pulse is less mature but offers stronger aliasing reasoning.

- [ ] **Cross-language benchmark (F4).** Assess whether the 8
  conjectures can be translated to F* type signatures automatically
  (or semi-automatically) from the Rocq originals.

## Comparison with the Rupicola route

| Dimension | Rupicola/Bedrock2 | F*/Low*/KaRaMeL |
|-----------|-------------------|-----------------|
| **Proof reuse** | EliasFano.v reused (773 lines) | Nothing reused; full rewrite |
| **Total rewrite** | ~3500 lines (refinement only) | ~2200--3400 lines (everything) |
| **Proof automation** | Manual tactics (deterministic) | Z3 automatic (brittle) |
| **C struct support** | No (flat `uintptr_t` args) | Yes (records -> C structs) |
| **Generated C quality** | Functional but `uintptr_t`-heavy | Readable, production-quality |
| **Ecosystem** | Rocq (familiar) | F* (new language to learn) |
| **Strongest trust path** | Verified RISC-V (no C compiler) | C only (KaRaMeL + gcc trusted) |
| **Production track record** | Fiat-crypto | HACL* (Firefox, Linux kernel) |
| **Maturity** | "Design phase" (Rocq Platform) | 9 years, monthly releases |
| **popcount/ctz** | `interact` + C stub | `assume val` + C stub |
| **64-bit words** | Native | Native |

### When F* is the better choice

- The goal is **production-quality C** with readable output and C structs
- Z3 automation would save significant time on the proof effort
- The project is willing to maintain a **separate F* codebase** alongside
  Rocq (no proof sharing)
- The benchmark perspective (Option F4) is valuable: comparing LLM
  performance across proof assistants

### When Rupicola is the better choice

- **Proof reuse** matters: 773 lines of Z-level proofs carry over
- The strongest possible **trust story** is the goal (verified RISC-V)
- Staying in **one ecosystem** (Rocq) reduces maintenance burden
- Deterministic proofs are preferred over SMT brittleness

## Verdict

**Feasible, but the rewrite cost dominates.** F*/Low*/KaRaMeL is a
mature, production-proven pipeline for verified C. The generated code
quality is excellent (C structs, readable output, no runtime
dependency). Z3 automation would reduce proof effort for arithmetic
lemmas.

However, the inability to reuse *any* existing Rocq proofs means the
F* route is a **complete reimplementation** (~2200--3400 lines), not a
refinement layer swap (~3500 lines for Rupicola). The total effort is
comparable, but the Rupicola path preserves the Z-level investment
while the F* path starts from zero.

**Recommendation:** If considering F*, start with Option F1 (bv_get
spike, 1--2 days) to validate toolchain and Z3 bitwise automation.
Then Option F2 (pure spec + Z-level proofs, 2--4 weeks) to get hard
data on proof effort vs. Rocq -- this is independently valuable for
the benchmark (Option F4) regardless of whether the Low* path is
pursued.

The decision between Rupicola and F* ultimately depends on whether the
goal is:
- **(a) Verified C as a project deliverable** -> F* has the edge
  (better C output, structs, maturity)
- **(b) Deepest possible trust chain** -> Rupicola wins (verified
  RISC-V compiler)
- **(c) Minimizing total effort** -> Rupicola wins (reuses Z-level
  proofs)
- **(d) Benchmark across proof assistants** -> both are needed

## References

1. Swamy, Hri&#x163;cu, Keller, Rastogi, Delignat-Lavaud, Forest, Bhargavan,
   Fournet, Strub, Kohlweiss, Zinzindohoue, Zanella-Beguelin. **Dependent
   Types and Multi-Monadic Effects in F*.** POPL 2016.
   [FStarLang/FStar](https://github.com/FStarLang/FStar)

2. Protzenko, Zinzindohoue, Rastogi, Inber, Wintersteiger, Bhargavan,
   Hri&#x163;cu, Swamy. **Verified Low-Level Programming Embedded in F*.**
   ICFP 2017.
   (Low* and KaRaMeL introduction.)

3. Protzenko, Beurdouche, Merigoux, Bhargavan. **Formally Verified
   Cryptographic Web Applications in WebAssembly.** IEEE S&P 2019.
   [FStarLang/karamel](https://github.com/FStarLang/karamel)

4. Zinzindohoue, Bhargavan, Protzenko, Beurdouche. **HACL*: A Verified
   Modern Cryptographic Library.** CCS 2017.
   [hacl-star/hacl-star](https://github.com/hacl-star/hacl-star)

5. Fromherz, Giannarakis, Hawblitzel, Parno, Rastogi, Swamy.
   **Steel: Proof-Oriented Programming in a Dependently Typed
   Concurrent Separation Logic.** ICFP 2021.
   (Steel separation logic for F*.)

6. Rastogi, Swamy, Fromherz, Merigoux, Martinez. **PulseCore:
   An Impredicative Concurrent Separation Logic for Pulse.** 2025.
   (Latest F* separation logic framework.)
