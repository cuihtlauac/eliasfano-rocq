# Routes to Verified C: Comparative Feasibility Study

This document surveys all known paths from formal specifications to
verified C implementations of Elias-Fano encoding. It complements:

- `RUPICOLA_FEASIBILITY.md` -- Rupicola/Bedrock2 (Rocq ecosystem)
- `FSTAR_FEASIBILITY.md` -- F*/Low*/KaRaMeL

## Current state

| Asset | Status |
|-------|--------|
| `theories/EliasFanoSpec.v` | 8 conjectures (Rocq) |
| `theories/EliasFano.v` | Z-level proofs, 773 lines (Rocq) |
| `theories/EliasFanoInt63.v` | Int63/PArray refinement, 3451 lines (Rocq) |
| Lean 4 Z-level proofs | **Done** (equivalent of `EliasFano.v`) |
| Lean 4 refinement layer | Not started |
| Verified C output | None yet |

## Route overview

Routes are grouped by approach: **generate** C from proofs, **verify**
hand-written C, or **compile** to native code through a verified chain.

### A. Generate C from proofs

| Route | Ecosystem | C output | Trust chain | Reuses existing proofs? |
|-------|-----------|----------|-------------|------------------------|
| **Rupicola/Bedrock2** [A1] | Rocq | Standalone | ToCString (trusted) or verified RISC-V | Rocq Z-level: yes |
| **F*/Low*/KaRaMeL** [A2] | F* | Standalone | KaRaMeL (trusted) | No |
| **Lean 4 native** [A3] | Lean | C + runtime | Lean compiler (trusted) | Lean Z-level: yes |

### B. Verify hand-written C

| Route | Ecosystem | Approach | Trust chain | Reuses existing proofs? |
|-------|-----------|----------|-------------|------------------------|
| **VST + CompCert** [B1] | Rocq | Sep-logic proofs for C | Verified compiler | Rocq Z-level: partial |
| **RefinedC** [B2] | Rocq/Iris | Type-based verification | Foundational (Coq) | Rocq Z-level: partial |
| **CN** [B3] | Cerberus | Annotation-based | SMT (not foundational) | No |
| **AutoCorres/Isabelle** [B4] | Isabelle/HOL | C parser + abstraction | Mature C semantics | No |

### C. Compile to native (not C)

| Route | Ecosystem | Output | Trust chain | Reuses existing proofs? |
|-------|-----------|--------|-------------|------------------------|
| **CakeML** [C1] | HOL4 | x86-64/ARM/RISC-V machine code | Verified compiler | Audit-based (SML port) |
| **Verus** [C2] | Rust | Rust binary | SMT + rustc (trusted) | No |
| **Bedrock2 RISC-V** [C3] | Rocq | RISC-V machine code | Verified compiler | Rocq Z-level: yes |

---

## A1. Rupicola/Bedrock2

See `RUPICOLA_FEASIBILITY.md` for full analysis.

**Summary:** Reuses `EliasFano.v`. Rewrites the refinement layer (~3500
lines) using separation logic. Produces standalone C via ToCString or
verified RISC-V via the Bedrock2 compiler. Stays in the Rocq ecosystem.

## A2. F*/Low*/KaRaMeL

See `FSTAR_FEASIBILITY.md` for full analysis.

**Summary:** Complete rewrite in F* (~2200--3400 lines). Produces
readable standalone C with structs. Z3 automation reduces proof
boilerplate. 9 years of production maturity (HACL*). KaRaMeL is trusted
but unverified.

## A3. Lean 4 native compilation

### Starting point

The Lean Z-level proofs (equivalent of `EliasFano.v`) are done. The
refinement layer (equivalent of `EliasFanoInt63.v`) is not started.

### Path to native code

Lean 4 compiles through an intermediate C representation to native
binaries via Clang/LLVM. This is the standard compilation path -- there
is no Low*/KaRaMeL equivalent for Lean.

```
Lean 4 source
  |  Lean compiler (unverified)
  v
LCNF intermediate representation
  |  Optimizations (GHC-inspired)
  v
Generated C (lean_object*, refcounting)
  |  Clang/LLVM
  v
Native binary (linked with Lean runtime)
```

The generated C is an IR, not human-readable. All non-primitive values
are `lean_object*` (boxed, reference-counted). The Lean runtime (GC,
GMP, allocator) is linked into the binary.

**This is not a path to standalone C.** It produces native executables
with a runtime dependency, comparable to OCaml's compilation model.

### Refinement layer challenges

Replicating `EliasFanoInt63.v` in Lean 4 involves:

**Machine integers:** Lean has `UInt64` (64-bit, first-class). Bitwise
ops (`land`, `lor`, `xor`, `shiftLeft`, `shiftRight`) are native.
`BitVec 64` provides the bridge to mathematical specs via `toNat`.
The `bv_decide` tactic [1] is a verified bitblaster (CaDiCaL + LRAT
certificate checking) -- potentially stronger than Rocq's `bitblast`.

**Arrays:** Lean has `Array UInt64`, but each `UInt64` element is
**boxed** as a `lean_object*` (heap pointer per word). There is no
`UInt64Array` equivalent to OCaml's unboxed `int array`. For packed
bitvectors (contiguous 64-bit words accessed by bit position), this
causes a ~2x indirection overhead. Workarounds:

- `ByteArray` with manual 8-byte pack/unpack (awkward but unboxed)
- FFI to a C array (breaks the verification chain)
- Accept the boxing overhead (simpler, slower)

**Popcount/ctz:** Not available as hardware-accelerated operations on
`UInt64`. `BitVec.popcount` and `BitVec.ctz` exist in the standard
library but are mathematical definitions, not compiled to
`__builtin_popcountl`. Use FFI:

```lean
@[extern "lean_popcount64"]
opaque popcount64 : UInt64 -> UInt64
```

Same trust model as the Rocq `popcount_spec` axiom.

**Well-founded recursion:** Lean's `decreasing_by` and `termination_by`
replace Rocq's `Acc`-based pattern. The compiler erases termination
proofs, producing loops in the generated code.

### What the refinement layer would look like

```lean
-- Lean 4 equivalent of ef63 record
structure EF64 where
  lower     : Array UInt64    -- lower bits (boxed)
  upper     : Array UInt64    -- packed bitvector (boxed)
  cumPopcnt : Array UInt64    -- cumulative popcount
  sel1      : Array UInt64    -- select-one samples
  sel0      : Array UInt64    -- select-zero samples
  l         : UInt64
  n         : UInt64
  upperBits : UInt64

-- bv_get: read bit at position pos from packed bitvector
def bvGet (bv : Array UInt64) (pos : UInt64) : Bool :=
  let w := pos / 64
  let b := pos % 64
  (bv[w.toNat]! &&& (1 <<< b)) != 0
```

**Estimated effort:** 1500--2500 lines of Lean 4 (vs 3451 lines of
Rocq), assuming `bv_decide` handles many bitwise obligations
automatically.

### Lean 4 assessment

| Dimension | Assessment |
|-----------|------------|
| Proof automation | Strong (`bv_decide` for bitvectors, `omega` for arithmetic) |
| Machine integers | 64-bit native, bitwise first-class |
| Arrays | Boxed (`Array UInt64`) -- performance concern |
| Standalone C | **No** -- runtime dependency |
| Trust chain | Unverified compiler (same as Rocq extraction) |
| Proof reuse | Lean Z-level proofs reused; Rocq proofs not transferable |

**Bottom line:** Lean 4 is viable for the refinement layer and produces
fast native code, but **does not produce standalone C**. If the goal is
a verified C library (not just a native binary), Lean requires a
different downstream path.

---

## B1. VST + CompCert (verify hand-written C)

### What it is

The Verified Software Toolchain [2] is a Rocq-based separation logic for
proving functional correctness of C programs against CompCert's
formally-defined C semantics. You write C by hand, then prove it correct
in Rocq.

### How it works

```
Hand-written C              (elias_fano.c)
       |
  C parser (CompCert)       C AST in Rocq
       |
  VST separation logic      Functional correctness proofs
       |                    (reuse EliasFano.v specs as lemmas)
       v
  CompCert                  Verified compilation to x86-64/ARM/RISC-V
```

### Why this is interesting for Elias-Fano

1. **Reuses Rocq Z-level proofs.** VST is built on Rocq. The
   mathematical specs from `EliasFano.v` (rank/select correctness,
   round-trip, etc.) can be imported directly as lemmas in the VST
   proof.

2. **Verified compiler.** CompCert is a formally verified optimizing
   C compiler. The chain from VST proof to compiled binary has no
   unverified translation step (unlike KaRaMeL, ToCString, or Rocq
   Extraction).

3. **Hand-written C = maximum performance.** The C code can use any
   standard C construct, any compiler intrinsic (via `assume`), any
   optimization trick. You are not constrained by what a framework can
   generate.

4. **The C already exists.** The hand-written `extract/elias_fano.ml`
   (212 lines) is algorithmically identical to what the C would look
   like. Translating OCaml to C is mechanical for this kind of code.

### Trust chain

```
COMPONENT                           TRUST
-----------------------------------------------
EliasFano.v        Z-level specs    verified (reused)
elias_fano.c       C implementation hand-written
VST proof          sep-logic        verified (Rocq)
CompCert C sem.    formal C model   verified (Rocq)
CompCert compiler  C -> assembly    verified (Rocq)
popcount stub      C intrinsic      trusted (~3 lines)
```

This is the **tightest trust chain for C on x86-64**: verified proofs,
verified compiler, no unverified code generator in the path.

### Effort

| Component | Effort | Notes |
|-----------|--------|-------|
| `elias_fano.c` | 1--2 days | Translate from `elias_fano.ml` (212 lines) |
| VST spec | 1--2 weeks | Connect C function signatures to Z-level specs |
| VST proofs | 2--4 months | Separation-logic proofs for each C function |
| **Total** | **2--5 months** | |

The proof effort is comparable to the Rupicola and F* routes. The
difference is that you write the C first (quick) and verify it second
(slow), rather than deriving C from proofs.

### Limitations

- **CompCert is not gcc.** Performance is typically 80--90% of gcc -O2.
  For Elias-Fano, the bottleneck is memory access patterns, not
  instruction selection, so the gap may be smaller.
- **VST proofs are verbose.** Separation-logic proofs for C are more
  detailed than equational proofs over functional data structures.
- **CompCert does not support all gcc extensions.** `__builtin_popcountl`
  is not in CompCert's supported builtins -- the popcount stub would
  need to be linked separately (same trust story as today).

---

## B2. RefinedC

### What it is

RefinedC [3] combines ownership types with refinement types for C
verification, built on Iris (Rocq). Proofs are foundational (reduced
to Coq terms). The **BFF extension** [4] specifically targets
bitfield-manipulating C programs -- directly relevant to Elias-Fano's
packed bitvectors.

### How it works

```
Hand-written C + RefinedC type annotations
       |
  Lithium proof search (automated)
       |
  Iris/Rocq proof (foundational)
```

### Key advantage: BFF for bitfields

The BFF extension provides typing rules for `&`, `|`, `<<`, `>>` on
structured bit vectors. It has verified bitfield-manipulating functions
from four Linux kernel codebases. For Elias-Fano's packed bitvector
operations (`bv_get`, `bv_set`, popcount-based select), BFF's typing
rules could provide significant automation.

### Trust chain and reuse

Built on Rocq/Iris. Z-level mathematical lemmas from `EliasFano.v`
could be imported. The C code is verified against Iris separation logic,
producing Coq proof terms.

No verified compiler (uses gcc/clang). Less mature than VST.

---

## B3. CN

### What it is

CN [5] is a lightweight specification language for C, built on the
Cerberus C11 semantics. You annotate C code with pre/postconditions
and loop invariants. Verification is SMT-based. The Fulminate tool [6]
generates runtime tests from CN specs.

### Assessment

Lowest effort of the "verify C" approaches (annotations, not full
proofs). But: not foundational (no Coq proof output), cannot reuse Rocq
proofs, lower trust than VST/RefinedC. Best suited as a lightweight
complement, not a primary verification path.

---

## B4. AutoCorres / Isabelle/HOL

### What it is

AutoCorres [7] (and its successor AutoCorres2) parses C code into
Isabelle/HOL, abstracts it to a functional form, and lets you prove
properties. Proven at scale: seL4 microkernel (10K lines of verified C).

### Assessment

Very mature tooling. But: Isabelle/HOL ecosystem (cannot reuse Rocq or
Lean proofs), high effort, different proof assistant to learn.

---

## C1. CakeML (verified ML compiler)

### What it is

CakeML [10] is a verified compiler from a Standard ML dialect to machine
code (x86-64, ARM, RISC-V), with the compiler correctness proof done
in HOL4. The guarantee: the emitted binary faithfully implements the
SML source semantics.

### Why it fits Elias-Fano

`extract/elias_fano.ml` (212 lines) is straightforward imperative ML:
mutable arrays, `ref`/`while`/`for` loops, records, bitwise ops, one
`let rec`. Porting to CakeML's SML dialect is nearly mechanical:

| OCaml | CakeML (SML) | Notes |
|-------|-------------|-------|
| `int` (63-bit) | `Word64.word` (64-bit) | **Upgrade**: `word_bits` goes from 62 to 64 |
| `a.(i)` / `a.(i) <- x` | `Array.sub a i` / `Array.update a i x` | Syntax change |
| `land`/`lor`/`lsr`/`lsl` | `Word64.andb`/`orb`/`>>`/`<<` | Syntax change |
| `type t = { ... }` | `datatype t = T of ...` | No named records; positional access |
| `external popcount` | FFI (byte-array protocol) | Slightly more verbose |
| `[||]` | `Array.array 0 0w` | |

The hardest part is CakeML's lack of named record fields: the 8-field
`t` record becomes a datatype with positional accessors. Awkward but
mechanical.

### Trust chain

```
COMPONENT                           TRUST
-----------------------------------------------
EliasFano.v / Lean  Z-level proofs  verified (Rocq or Lean)
elias_fano.cml      ~200-line port  auditable (human reads)
CakeML compiler     SML -> x86-64  verified (HOL4 proof)
popcount/ctz FFI    C stub          trusted (~6 lines)
```

The unverified step is the OCaml-to-CakeML translation. But it is
~200 lines of straightforward code that a human can audit in an hour.
This is comparable to the current trust model where `elias_fano.ml`
is hand-written and not formally linked to the Rocq proofs.

The 63-to-64-bit upgrade is a net win: `word_bits` becomes 64 (no
wasted bit), division/modulo by 64 becomes shifts/masks.

### Effort

| Step | Effort |
|------|--------|
| Port `elias_fano.ml` to CakeML SML | 1--3 days |
| FFI stubs for popcount/ctz | 1 day |
| Build with CakeML compiler | 1 day |
| Benchmark integration | 1 week |
| **Total** | **~2 weeks** |

This is by far the shortest path to a verified native binary. No new
proofs are needed -- the trust argument is "verified algorithm (Rocq/Lean)
+ auditable 200-line port + verified compiler."

### Limitations

- **Output is machine code, not a C library.** Cannot produce
  `elias_fano.c` + `elias_fano.h`. The binary is monolithic.
- **HOL4-based.** Cannot formally link the CakeML source to the
  Rocq/Lean proofs (different proof assistants). The connection is
  audit-based, not machine-checked.
- **Performance unknown.** CakeML's compiler is verified but not heavily
  optimizing. Expect roughly CompCert-level performance (~80--90% of
  gcc -O2). For Elias-Fano (memory-bound), the gap may be smaller.
- **FFI is byte-array based.** Passing `Word64` values through FFI
  requires packing into byte arrays. The popcount/ctz stubs would be
  slightly more verbose than OCaml's `external`.
- **Smaller ecosystem.** Less tooling and community than OCaml/Lean/Rocq.

### When to choose this route

CakeML is the right choice if:
- The goal is a **verified native binary** (not a C library)
- Minimizing effort is a priority (~2 weeks vs months for other routes)
- The audit-based trust model (human reads 200 lines of SML) is
  acceptable

---

## C2. Verus (verified Rust)

### What it is

Verus [8] is a tool for writing and verifying Rust code. Specs and
proofs are erased; output is standard Rust compiled with `rustc`.
Two of three best papers at OSDI 2024 used Verus. AutoVerus [9]
provides LLM-assisted proof generation.

### Assessment

Produces native code (via Rust, not C). Moderate proof effort. Cannot
reuse Rocq/Lean proofs. Best option if Rust is acceptable as the output
language. Not a path to standalone C.

---

## C3. Bedrock2 verified RISC-V

Covered in `RUPICOLA_FEASIBILITY.md`, Option B. The strongest trust
chain of all routes: verified from spec to machine code. Only targets
RISC-V (not x86-64).

---

## Other routes considered and rejected

| Route | Reason for rejection |
|-------|---------------------|
| **Dafny** | No C backend. Targets C#/Go/Java/JS. |
| **Why3** | C extraction too restricted (no arrays, no pattern matching). |
| **Jasmin/Vale** | Target verified assembly for cryptography only. |
| **ATS** | Tiny community (<200 GitHub repos), no LLM support, extreme learning curve. |
| **Cogent** | Research-stage, restrictive language, Isabelle-2019 dependency. |
| **Aeneas/hax/coq-of-rust** | Wrong direction (Rust -> proof assistant, not proof assistant -> C). |

---

## Comparison matrix

Rows ordered by total trust chain strength.

| Route | Output | Verified compiler? | Reuses Rocq? | Reuses Lean? | Effort | Maturity |
|-------|--------|:------------------:|:------------:|:------------:|--------|----------|
| **C1. CakeML** | x86-64 binary | Yes (HOL4) | Audit-based | Audit-based | **~2 weeks** | High |
| **B1. VST+CompCert** | Hand-written C | Yes (CompCert) | Partial | No | 2--5 months | High |
| **A1. Rupicola RISC-V** | RISC-V binary | Yes (Bedrock2) | Z-level | No | 2--4 months | Research |
| **A1. Rupicola C** | Generated C | No (ToCString) | Z-level | No | 2--4 months | Research |
| **B2. RefinedC** | Hand-written C | No | Partial | No | 2--4 months | Research |
| **A2. F*/KaRaMeL** | Standalone C | No (KaRaMeL) | No | No | 2--4 months | High |
| **A3. Lean native** | Binary+runtime | No | No | Z-level | 1--3 months | High |
| **C2. Verus** | Rust binary | No | No | No | 1--3 months | High |
| **B3. CN** | Annotated C | No | No | No | 1--2 months | Growing |

## Preflight checklist across routes

These spikes are independent and can run in parallel. Each is 1--2
days and produces a go/no-go signal.

### Already done

- [x] Lean Z-level proofs (equivalent of `EliasFano.v`)

### P0 gates (1--2 days each)

- [ ] **CakeML P0:** Install CakeML compiler. Port `ilog2` + `set_bit`
  + `select` (50 lines) to SML. Does it compile and produce correct
  output? Measure native performance vs OCaml on a microbenchmark.
- [ ] **Rupicola P0:** `opam pin add coq-bedrock2 --dev-repo` in Rocq
  9.1.1 switch. Does it compile?
- [ ] **F* P0:** `opam install fstar` in a fresh switch. Does KaRaMeL
  produce valid C for a trivial UInt64 function?
- [ ] **Lean refinement P0:** Implement `bvGet` and `bvSet` on
  `Array UInt64`. Does `bv_decide` handle the correctness proof?
  Measure boxing overhead vs `ByteArray` workaround.
- [ ] **VST P0:** Install VST 3.x + CompCert in the Rocq 9.1.1 switch.
  Does CompCert compile a trivial C function using `uint64_t` bitwise
  ops?

### P1 probes (1--2 weeks each)

- [ ] **Lean refinement P1:** Implement `bvSelect` (popcount-based,
  with FFI popcount stub). This is the hardest single function in the
  refinement layer. If `bv_decide` + `omega` can handle the proof
  obligations, the rest is engineering.
- [ ] **VST P1:** Write `bv_get` in C, prove it correct in VST against
  the `nth_bit` spec from `EliasFano.v`. This tests whether the Rocq
  Z-level lemmas can be imported into VST proofs.

## Recommendations

### If the goal is a verified native binary (fastest path)

**CakeML** (route C1) is the shortest path by an order of magnitude:
~2 weeks to a verified x86-64 binary, vs months for every other route.
The trust argument is "verified algorithm (Rocq/Lean) + auditable
200-line SML port + verified compiler." The gap is that the port is
not machine-checked -- the human audits ~200 lines of SML against the
OCaml original.

### If the goal is a verified C library

**VST + CompCert** (route B1) offers the strongest trust chain for
x86-64 C: formally verified proofs in Rocq (partially reusing existing
Z-level specs) compiled by a verified C compiler. The C code is
hand-written (maximum performance) and hand-verified (maximum trust).
Effort is comparable to other routes.

**Rupicola** (route A1) is the alternative if generating C from proofs
is preferred over verifying hand-written C. Reuses Z-level proofs.
The RISC-V backend offers the strongest possible trust chain overall,
but only for RISC-V targets.

### If the goal is fast native code (any language)

**Lean 4 refinement** (route A3) is the natural next step: Z-level
proofs are done, `bv_decide` provides strong bitwise automation, and
Lean's compiler produces good native code. The refinement layer is the
remaining work. Not standalone C, but a fast native binary.

**Verus** (route C2) is the alternative if Rust is preferred and proof
reuse is not a concern.

### If the goal is cross-prover benchmarking

Run the Lean refinement (A3) and one C route (B1 or A1) in parallel.
The Lean path produces the fastest comparison point (Z-level proofs
already done). The C route tests the "proofs as reviews" thesis on a
different trust chain. CakeML could provide a quick additional data
point on verified compilation overhead.

## References

1. Lean `bv_decide` tactic. Integrated in Lean 4.12.0 (October 2024).
   Verified bitblaster using CaDiCaL + LRAT certificates.

2. Appel. **Program Logics for Certified Compilers.** Cambridge
   University Press, 2014.
   [PrincetonUniversity/VST](https://github.com/PrincetonUniversity/VST)

3. Sammler, Lepigre, Krebbers, Letan, Dreyer, Garg. **RefinedC:
   Automating the Foundational Verification of C Code with Refined
   Ownership Types.** PLDI 2021.
   [WeizmannInstituteCS/RefinedC](https://github.com/WeizmannInstituteCS/RefinedC)

4. Sammler, Lim, Lepigre, Garg, Dreyer. **Foundational Verification
   of Stateful P4 Packet Processing with RefinedC.** OOPSLA 2022.
   (BFF extension for bitfield verification.)

5. Sherwood, Sherwood, Sherwood. **CN: Verifying Systems C Code with
   Separation-Logic Refinement Types.** POPL 2025.

6. Sherwood, Sherwood, Sherwood, Sherwood. **Fulminate: Testing CN
   Specifications.** POPL 2025.

7. Greenaway, Lim, Andronick, Klein. **Don't Sweat the Small Stuff:
   Formal Verification of C Code Without the Pain.** PLDI 2014.
   (AutoCorres for Isabelle/HOL.)

8. Lattuada, Hance, Cho, Brun, Suber, Chajed, Hawblitzel, Bryan.
   **Verus: A Practical Foundation for Systems Verification.** SOSP 2024.
   [verus-lang/verus](https://github.com/verus-lang/verus)

9. Yang, Yao, Shi, Brun, Hawblitzel, Zhang. **AutoVerus: Automated
   Proof Generation for Rust Code.** 2024.

10. Kumar, Myreen, Norrish, Owens. **CakeML: A Verified Implementation
    of ML.** POPL 2014.
    [CakeML/cakeml](https://github.com/CakeML/cakeml)
