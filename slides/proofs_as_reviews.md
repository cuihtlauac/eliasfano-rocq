---
title: Proofs as Reviews
theme:
  name: dark
---

# Proofs as Reviews

Cuihtlauac Alvarado — Tarides

DevFestNoz, Lannion — 2026-03-12

Tarides Tech Talk — 2026-04-07

<!-- end_slide -->

# Off-Topic?

AI environmental, ethical, political and social concerns.
  - I share them
  - Not a _fan-boy_ — As hyped, vibe-coding is gross negligence
  -  — But — the technology is there

<!-- end_slide -->

# Productivity Explosion?

- LLMs write code 10× to 100× faster than humans
- Not an unquestionable fact, but an unstoppable hype claim
- 16 Claude agents wrote a C compiler that builds Linux
- Code review still at about 150 LOC/hour (Cisco/SmartBear study)
- Everyone is a 10× developer now. Nobody is a 10× reviewer
  - Review isn't a matter of productivity
  - It's a matter of trust and responsibility

<!-- end_slide -->

# Review Wall

- Code compiles, passes tests, but nobody read it
- “Testing shows the presence, not the absence of bugs” — Dijkstra
- *Silent hallucinations*: code looks correct, subtly wrong
- *Garbage-In Garbage-Out*:
  - Context inconsistencies and shortcomings
  - Sycophancy or deference-biased engineering
  - Anthropomorphism
  - Output: subpar to wholly unacceptable
- Lame Responses
  - **More reviewers** but that does not scale
  - **Better tests** but they only cover partial state space
  - LLM-written tests tend to agree with LLM-written code
  - No choice but to trust
- **Machine-checked proofs**, the topic of this talk
- Shift trust from “someone read it” to “math checked it”

<!-- end_slide -->

# Running Example: Compact Sorted Integers

- Sebastiano Vigna modernized Elias-Fano with quasi-succinct indices (2013)
- Store sorted integers compactly with fast access
- Used in inverted indices, graph compression, bioinformatics

<!-- pause -->

- *n* integers in universe [0, *U*)
- Naive storage: *n* × log₂(*U*) bits
- Elias-Fano: *n* × (2 + log₂(*U*/*n*)) bits, **near-optimal**
- Pack more data in cache

<!-- end_slide -->

# Encoding

- Split each value *x* into **upper** and **lower** bits
- Lower ℓ = ⌊log₂(*U*/*n*)⌋ bits, stored concatenated
- Upper bits: **unary** coding with 0-separators

<!-- pause -->

**Example:** values [2, 3, 5, 7], *U*=8, ℓ=1

```
lower bits: [0, 1, 1, 1]           (last bit of each value)

             0  1  2  3  4  5  6
upper bits: [0, 1, 1, 0, 1, 0, 1]
                ^  ^     ^     ^
                1  1     2     3    (pos - rank = prefix)
```

Value prefix (upper bits) count, in _unary_:
- Prefix `00` appears 0   (`0`) times
- Prefix `01` appears 2 (`110`) times (values 2 and 3)
- Prefix `10` appears 1  (`10`) time (value 5)
- Prefix `11` appears 1  (`10`) time (value 7)

Plain:    `010 011 101 111`   (12 bits)

Encoded:  `0111` `0 110 10 1`   (11 bits)
<!-- end_slide -->

# Operations

- `encode(vals, U)` builds the two bitvectors
- `access(i)` selects *i*-th `1` in upper bits, runs in O(1)
- `nextGEQ(v)` finds first value ≥ *v*, O(1) with rank tables
- `decode` iterates access over all elements
- Key primitive: `select(bv, i)` returns position of *i*-th set bit
- My implementation uses popcount-based scan over 63-bit words
- Vigna's Sux code is heavily optimized, broadword tricks and bit hacks

<!-- end_slide -->

# Formal Methods Timeline

- **1969** Hoare logic (Hoare), pre/postcondition reasoning
- **1972** ML and LCF (Milner), tactics with trusted kernel
- **1977** Abstract interpretation (Cousot and Cousot), powers Astrée
- **1981** Model checking (Clarke, Emerson, Sifakis), Turing Award 2007
- **1984** Calculus of Constructions (Coquand), becomes Coq
- **2002** Separation logic (O'Hearn, Reynolds, Yang), reasoning about pointers
- **2017** Meta Infer, separation logic in CI at scale
- 55+ years of foundations, recent and limited industry reach

<!-- end_slide -->

# Why Formal Methods Are Rare

- Mathematical **assurance** that code meets specification
- Not **testing harder**, a different kind of trust
  - Specification says “decode Elias-Fano encoding, get back original list”
  - Proof shows for **all** sorted inputs, `decode(encode(vals)) = vals`
  - Bit manipulation, overflow, select: every corner case covered

<!-- pause -->

| Project | What | Person-years | LOC | Tool |
|---------|------|--------------|-----|------|
| A380 (Airbus, 2004) | Flight control | undisclosed | ~132k | Astrée |
| CompCert (Leroy, 2006) | C compiler | 6 | ~100k | Coq |
| seL4 (Klein, 2009) | OS Microkernel | 20 | ~10k | Isabelle |
| EverParse (Microsoft, 2019) | Binary parsers | 3 | ~50k | F* |

<!-- pause -->

- Common thread: enormous effort, PhD-level expertise
- 10× to 30× cost ratio versus tested and manually reviewed code
- Economics and velocity kill it

<!-- end_slide -->

# Writing Terms *vs* Type-Checking

- What is Rocq?
  - A functional programming language's type checker
  - It's type system is so expressive, maths fits in
  - Trade-off: you can't write non-terminating recursion
- A proof is a well-typed term; verification is type-checking
- Constructing proofs is hard, checking them is mechanical

<!-- pause -->

- Claude writes the terms, about 4,200 lines (I steer the strategy)
- Rocq type-checks every lemma, rejects anything wrong
- **How** the term was written is irrelevant, only that it type-checks
- Language matters: OCaml or Rust easier to verify than Python or JavaScript

<!-- end_slide -->

# Trust Architecture

The *trusted computing base*: know exactly who is responsible for what.

| Layer | LOC | Tool | Reviewed by |
|-------|-----|------|-------------|
| Specification | 129 | Rocq | Human |
| Proof | 4,224 | Rocq | Kernel |
| Extracted OCaml | 238 | Extraction | Nobody |
| C stubs | 14 | GCC | Human |

<!-- pause -->

- Specification defines **what** is correct
- Proof shows **why** it is correct
- Code implements **how** it runs
- This is *verified programming*, not *extraction* in the Paulin-Mohring sense
  - Functions translated from Rocq to OCaml, not synthesised from ∀∃ proofs
  - Think of it as FP purer than Haskell — not even IO
- Human reviews **143 lines** total. Rest is machine-checked.
- TCB boundary: Rocq kernel & runtime, OCaml compiler and `Stdlib`, OS, HW
- Same things you already trust for any OCaml program
- C stubs (`popcount`, `ctz`) are the only project-specific addition

<!-- end_slide -->

# What Is Proved

### Correctness (ℤ level) — 8 theorems

- **Structural**
  - `round_trip` — decode(encode(vals)) = vals
  - `rank_select`, `select_rank` — rank and select are inverses on set-bit positions
- **Functional** (ℤ and Int63)
  - `access_correct` — access(i) returns the i-th value (ℤ only)
  - `nextGEQ_found` — nextGEQ(v) returns a value ≥ v
  - `nextGEQ_smallest` — …and it is the smallest such value
  - `nextGEQ_none` — if no value ≥ v exists, returns None
- **Efficiency**
  - `space_bound` — encoding uses at most n·(2 + log₂(U/n)) bits
- **Agreement** — `Int63` gives the same results as ℤ when values fit in 63 bits
  - `access63_agrees`, `decode63_agrees`

<!-- pause -->

Only axiom: `popcount_spec` — backed by 3-line C shim using `__builtin_popcountl`

<!-- end_slide -->

# Two Numeric Worlds

<!-- column_layout: [1, 1] -->

<!-- column: 0 -->

### Specification: ℕ and ℤ

- Unbounded — no overflow
- Naturals
  - Peano (OCaml: `unit list`)
  - List positions
  - Structural recursion
- Integers
  - OCaml: `bool * bool list`
  - Proof automation
  - Clean math

<!-- column: 1 -->

### Implementation: `Int63` and `PArray`

- Bounded
- OCaml words
- Overflow proofs
- Fast extraction
- `PArray`: immutable array and list of changes

<!-- reset_layout -->

- Algorithmic correctness lives in ℤ
- But ℤ arithmetic is impractical at runtime
- Algorithms and programs are related, but distinct things
- `Int63` gives native performance, but can overflow and wrap
- Bridging lemmas connect both: prove they agree when values fit

<!-- end_slide -->

# *Agrees* Pattern — `access` example

- Prove `Int63` implementation agrees with ℤ specification when inputs fit
- Then derive all properties from ℤ-level theorems
- Same pattern for decode and nextGEQ

Accessing the *i*-th element in the `Int63` encoding gives the same result as in the ℤ encoding. Here `vals` is the input list and `U` the universe bound.

```rocq
Theorem access63_agrees : forall U vals i,
  in_range (to_Z U) (to_Z_list vals) ->
  sorted (to_Z_list vals) ->
  to_Z (access63 (encode63 U vals) i) =
    access_ef (encode (to_Z U) (to_Z_list vals))
              (Z.to_nat (to_Z i)).
```

<!-- end_slide -->

# *Agrees* Pattern — `access` example

- Prove `Int63` implementation agrees with ℤ specification when inputs fit
- Then derive all properties from ℤ-level theorems
- Same pattern for decode and nextGEQ

Accessing the *i*-th element in the `Int63` encoding gives the same result as in the ℤ encoding. Here `vals` is the input list and `U` the universe bound.

```latex +render
\[ \forall\; U,\; \texttt{vals},\; i \]
\[ 0 < U < 2^{63} \quad\wedge\quad \operatorname{length}(\texttt{vals}) + U < 2^{63} \]
\[ \quad\wedge\quad \operatorname{sorted}(\texttt{vals}) \]
\[ \Longrightarrow \]
\[ \operatorname{access63}(\operatorname{encode63}(U, \texttt{vals}),\; i) \quad=\quad \operatorname{access}(\operatorname{encode}(U, \texttt{vals}),\; i) \]
```

<!-- end_slide -->

# Popcount: Explicit Axiom

- Efficient Elias-Fano select needs **popcount** (count set bits)
- CPU provides `popcnt` instruction, but OCaml does not expose it, yet
- Solution: C stub and Rocq axiom tying them together

<!-- pause -->

```rocq
Parameter popcount : int -> int.
```

```latex +render
\[ \forall\; x \in \operatorname{int},\quad \sum_{k=0}^{62} \operatorname{bit}(x, k) \;=\; \texttt{popcount}(x) \]
```

<!-- pause -->

C backing:
```c
CAMLprim value caml_ef_popcount(value v) {
  return Val_long(__builtin_popcountl(Long_val(v)));
}
```

Rocq `Print Assumptions` lists exactly what is trusted.

<!-- end_slide -->

# Effort Breakdown

- **110 lemmas**, 0 Admitted, 1 axiom (`popcount_spec`)
- Specification: 129 LOC, the *contract*
- Proofs: 4,224 LOC, the *proof of contract*
- Extraction glue: 10 LOC
- C stubs: 14 LOC, only unverified logic
- 5 top-level theorems: `access`, `decode`, `nextGEQ` (found/smallest/none)
- Each proved via *agrees* reduction to ℤ-level theorems
- Human effort: about **1 person-day**

<!-- end_slide -->

# Demo Part 1: Specification

Open `EliasFano.v`, the ℤ-level specification:

```rocq
Definition encode (U : Z) (vals : list Z) : encoded := ...
Definition access (enc : encoded) (i : nat) : Z := ...
Definition decode  (enc : encoded) : list Z := ...
Definition nextGEQ (enc : encoded) (v : Z) : option Z := ...
```

<!-- pause -->

About 20 lines of theorem statements define what **correct** means.

This is what you review. Nothing else.

<!-- end_slide -->

# Demo Part 2: Walk Through a Proof

Open `EliasFanoInt63.v`, step through `access63_agrees`:

```
Goal: to_Z (access63 (encode63 U vals) i)
    = access_ef (encode (to_Z U) (to_Z_list vals))
                (Z.to_nat (to_Z i))
```

<!-- pause -->

- Unfold definitions, expose ℤ/ℕ/`Int63` boundaries
- Tactics: `lia` handles arithmetic, `bitblast` handles bitwise
- Watch the goal transform step by step

<!-- end_slide -->

# Demo Part 3: Build and Run

```bash
$ ./build.sh          # 4,353 lines type-checked
$                     # nothing visible, that is the point
$ ./bench/run.sh      # encode, access, decode, nextGEQ
```

<!-- pause -->

The quietest build is the most trustworthy.

<!-- end_slide -->

# Oracle and Performance

- **Ground truth**: Sux (Vigna's C++ library)
- **100% match** at n = 3; 1,000; 10,000; 100,000

| Operation | versus Sux |
|-----------|------------|
| Encode | about 3× slower |
| Access | 1 to 17× slower |
| Decode | about 23× slower |

<!-- pause -->

- Proved correct against machine integers does not mean fast
- Linear-scan `nextGEQ` versus Sux's O(1) rank-based jump
- No precomputed rank tables

<!-- end_slide -->

# Closing the Gap

- `dune -opaque` kills cross-module inlining of `Int63` ops
- Hacked around with C stubs, bypassing OCaml code
- Trading trust in Rocq runtime into our own thin layer
- Vigna's broadword `select` replaces linear `popcount` scan
- Mutable array shim (`Ef_parray`) eliminates `PArray` diff chain
- All still proved correct — only the extraction layer changes

<!-- pause -->

| Operation | before | after  |
|-----------|--------|--------|
| access    | 1–17×  | 1.15×  |
| nextGEQ   | —      | 1.19×  |
| decode    | 23×    | 1.62×  |
| encode    | 3×     | 4.4×   |

Times are versus Sux (Vigna's C++ library, n = 100M)

<!-- pause -->

- From 23× slower to 1.6× — without touching a single proof
- Encode is still slow: list input + fuel-based build (extraction artefact)

<!-- end_slide -->

# Cost of Verification

- About 30× more Rocq code than unverified OCaml, but:
  - Specification is reusable across implementations
  - Bugs found mechanically, not by humans
  - No review needed for extracted code or proofs
  - Refactoring changes proof, not specification

<!-- pause -->

- `Int63` refinement required human steering:
  - Term explosion `Z_count_ones 63` → controlled unfolding
  - Taught LLM "apply atomic conversions, watch the term"
  - LLM proved 30+ bridging lemmas via Model Context Protocol
  - `bv_select_aux_agrees` ground through 3 contexts
  - 4 final theorems fell in hours using established patterns

<!-- end_slide -->

# Human + LLM Workflow

1. Generation of the specification at ℤ/ℕ level
2. Review of the specification
3. LLM autonomous proof search and Rocq verification
4. Extraction and benchmarking: non-performance

<!-- pause -->

5. Expansion of the specification to `Int63` and `PArray`
6. LLM proof search, Rocq verification — I had to help, Claude stucked
7. Extraction and benchmarking: 3× to 23× slower than Sux
8. Proof refactoring — I had to steer, Claude clueless
9. Implementation and verification of Vigna's hacks, automatic again
10. Extraction and benchmarking: 1.15× to 4.4× slower than Sux

<!-- pause -->

Honest truth:
- I had to use my PhD experience in Rocq
- Difficulties Claude could not overcome, yet
  - Rocq performance pathologies on giant proof terms
  - Theory engineering combining extracted performance and provability
- Where Claude shines:
  - Using the tactic language
  - Adding lemmas on the fly
  - Generalizing statements

<!-- end_slide -->

# Takeaways

- LLMs help break through the 10× to 30× verification workload barrier
- Explicit trust beats vibe-coding cargo cult
- Review: from code-level towards specification-level

<!-- pause -->

- 143 lines of human-reviewed code
- 4,353 lines of machine-checked proofs
- 238 lines of extracted OCaml, never read
- 0 admitted, but axioms for trusted assembly instructions

<!-- pause -->

- LLM raises the _best-effort_ software quality bar
  - Yesterday: tests and code reviews
  - Today: formal specs and machine-checked properties
- Next Steps
  - Turn this into a model benchmark
  - Compare with Lean + Mistral

<!-- pause -->

The review wall has a door. Speak *formal*, and enter

<!-- end_slide -->

# Questions?

github.com/cuihtlauac/eliasfano

```
110 lemmas · 0 Admitted · 1 axiom
129 + 773 + 3,451 LOC Rocq
238 LOC OCaml · 14 LOC C
```

<!-- end_slide -->

# Appendix A1: Term Explosions

- `Z_count_ones 63` unfolds into a term of size 2⁶³
- `nia` in large contexts blows up Qed time
- Fix: controlled unfolding, direct lemma application

<!-- pause -->

- `simpl` is the enemy, avoid on recursive definitions
- Use `unfold X at 1; fold X` for surgical control
- `ltac timeout` for early detection

<!-- end_slide -->

# Appendix A2: PArray Universe Bug

- Rocq 9.1 universe polymorphism breaks `rewrite` on PArray lemmas

```rocq
(* FAILS: rewrite get_set_same *)
(* FIX: monomorphic wrappers *)
Local Lemma get_set_same' (t : array int) (i a : int) :
  (i <? PArray.length t)%uint63 = true ->
  t.[i <- a].[i] = a.
Proof. exact (get_set_same int t i a). Qed.
```

<!-- pause -->

- Workaround: specialize polymorphic lemmas to `int`
- Use `exact` when `rewrite` still fails

<!-- end_slide -->

# Appendix A3: Extraction Bugs

- `'a Parray.t` syntax bug in extracted OCaml, fixed with sed
- Popcount sign-extension: bit 62 gives negative int, causes overcount
- Fix: use `Long_val`/`Val_long`, not `Int_val`/`Val_int` in C stubs
- ℤ-roundtrip was O(n²), fixed to O(1) via `Obj.magic`

<!-- pause -->

- OCaml 5.3 `Int_val` casts to 32-bit int, silently truncating
- 3 distinct extraction bugs found and fixed

<!-- end_slide -->

# Appendix A4: Compositionality Gap

- `valid_input` is only a precondition, never a postcondition
- No theorem says decode produces valid output from valid input
- Works here because every proof reduces to ℤ via *agrees*
- Would not compose if chaining Int63-level operations
- A compositional design would prove `valid_input U vals -> valid_output (encode63 U vals)`

<!-- end_slide -->

# Appendix A5: Rocq/Coq Rebranding Friction

- Coq renamed to Rocq in 2024, documentation split
- LLM training data is overwhelmingly “Coq”
- Import paths changed (`From Coq` became `From Stdlib`)
- Version-specific bugs like `PArray` universe polymorphism in 9.1
- Real friction for AI-assisted formal methods
- Model Context Protocol servers `rocq-mcp` help bridge the gap

# Appendix: References

**Studies**
- [Cisco/SmartBear code review study](https://static0.smartbear.co/support/media/resources/cc/book/code-review-cisco-case-study.pdf)
- [Peng et al., 2023 — Copilot productivity](https://arxiv.org/abs/2302.06590)
- [Claude's C compiler](https://github.com/anthropics/claudes-c-compiler)

**Formal methods milestones**
- [Hoare, 1969 — Axiomatic basis](https://dl.acm.org/doi/10.1145/363235.363259) · [LCF](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions) · [Calculus of Constructions](https://www.sciencedirect.com/science/article/pii/0890540188900053)
- [Abstract interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation) · [Model checking](https://en.wikipedia.org/wiki/Model_checking) · [Separation logic](https://en.wikipedia.org/wiki/Separation_logic)
- [CompCert](https://dl.acm.org/doi/10.1145/1538788.1538814) · [seL4](https://dl.acm.org/doi/10.1145/1629575.1629596) · [EverParse](https://project-everest.github.io/everparse/)
- [Astrée](https://www.astree.ens.fr/) · [Meta Infer](https://fbinfer.com/)

**Elias-Fano**
- [Elias, 1974](https://dl.acm.org/doi/10.1145/321812.321820) · [Vigna, 2013 — Quasi-succinct indices](https://vigna.di.unimi.it/ftp/papers/QuasiSuccinctIndices.pdf)
- [Sux library](https://github.com/vigna/sux) · [Succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure)

**Tools**
- [Rocq prover](https://rocq-prover.org/) · [Rocq extraction](https://rocq-prover.org/doc/V9.1.0/refman/addendum/extraction.html)
- [Formal verification](https://en.wikipedia.org/wiki/Formal_verification) · [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) · [Inverted index](https://en.wikipedia.org/wiki/Inverted_index)
