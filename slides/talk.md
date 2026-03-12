---
title: Proofs as Reviews
theme:
  name: dark
---

# Proofs as Reviews

Cuihtlauac Alvarado — Tarides

DevFestNoz, Lannion — 2026-03-12

<!-- end_slide -->

# Off-Topic

AI environmental, ethical, political and social concerns. I share them

<!-- end_slide -->

# Productivity Explosion

- LLMs write code 10× to 100× faster than humans
- GitHub Copilot: 55% faster task completion (Peng et al., 2023)
- 16 Claude agents wrote a C compiler that builds Linux
- Code review still at about 150 LOC/hour (Cisco/SmartBear study)
- Everyone is a 10× developer now. Nobody is a 10× reviewer

<!-- end_slide -->

# Review Wall

- Code compiles, passes tests, but nobody read it
- “Testing shows the presence, not the absence of bugs” — Dijkstra
- *Silent hallucinations*: code looks correct, subtly wrong
- *Garbage-In Garbage-Out*: inconsistencies in the context derail the agent
- No choice but to trust

<!-- end_slide -->

# Some Responses

- **More reviewers** but that does not scale
- **Better tests** but they only cover partial state space
- LLM-written tests tend to agree with LLM-written code
- **Machine-checked proofs**, the topic of this talk
- Shift trust from “someone read it” to “math checked it”

<!-- end_slide -->

# Example Problem: Compact Sorted Integers

- Sebastiano Vigna modernized Elias-Fano with quasi-succinct indices (2013)
- Store sorted integers compactly with fast access
- Used in inverted indices, graph compression, bioinformatics

<!-- pause -->

- *n* integers in universe [0, *U*)
- Naive storage: *n* × log₂(*U*) bits
- Elias-Fano: *n* × (2 + log₂(*U*/*n*)) bits, **near-optimal**
- Compact enough to fit in cache, faster than uncompressed data in RAM

<!-- end_slide -->

# Encoding

- Split each value *x* into **upper** and **lower** bits
- Lower ℓ = ⌊log₂(*U*/*n*)⌋ bits, stored concatenated
- Upper bits: **unary** coding with 0-terminators

<!-- pause -->

**Example:** values [2, 3, 5, 7], *U*=8, ℓ=1

```
lower bits: [0, 1, 1, 1]           (last bit of each value)

             0  1  2  3  4  5  6
upper bits: [0, 1, 1, 0, 1, 0, 1]
                ^  ^     ^     ^
                1  1     2     3    (position - rank = upper prefix)
```

Value upper prefix count, in unary:
- Prefix `00` appears 0 times
- Prefix `01` appears 2 times (values 2 and 3)
- Prefix `10` appears 1 time (value 5)
- Prefix `11` appears 1 time (value 7)

Plain:    `010 011 101 111`   (12 bits)

Encoded:  `0111`  `0110101`     (11 bits)

<!-- end_slide -->

# Operations

- **encode**(*vals*, *U*) builds the two bitvectors
- **access**(*i*) selects *i*-th one in upper bits, runs in O(1)
- **nextGEQ**(*v*) finds first value ≥ *v*, O(1) with rank tables
- **decode** iterates access over all elements
- Key primitive: `select(bv, i)` returns position of *i*-th set bit
- My implementation uses popcount-based scan over 63-bit words
- Vigna's Sux code is heavily optimized, full of broadword tricks and bit hacks

<!-- end_slide -->

# Formal Methods Timeline

- **1969** Hoare logic (Hoare), pre/postcondition reasoning
- **1972** ML and LCF (Milner), tactics with trusted kernel
- **1977** Abstract interpretation (Cousot and Cousot), powers Astrée
- **1981** Model checking (Clarke, Emerson, Sifakis), Turing Award 2007
- **1984** Calculus of Constructions (Coquand), becomes Coq
- **2002** Separation logic (O'Hearn, Reynolds, Yang), reasoning about pointers
- **2017** Meta Infer, separation logic in CI at scale
- 55+ years of foundations, only recently reaching industry

<!-- end_slide -->

# Mathematical Assurance

- Mathematical **assurance** that code meets specification
- Not **testing harder**, a different kind of trust
- Specification says “decode Elias-Fano encoding, get back original list”
- Proof shows for **all** sorted inputs, decode(encode(*vals*)) = *vals*
- Bit manipulation, overflow, select: every corner case covered

<!-- end_slide -->

# Why Formal Methods Are Rare

| Project | What | Person-years | LOC | Tool |
|---------|------|--------------|-----|------|
| A380 (Airbus, 2004) | Flight control | undisclosed | ~132k | Astrée |
| CompCert (Leroy, 2006) | C compiler | 6 | ~100k | Coq |
| seL4 (Klein, 2009) | OS Microkernel | 20 | ~10k | Isabelle |
| EverCrypt (Microsoft, 2019) | Crypto library | 3 | ~107k | F* |

<!-- pause -->

- Common thread: enormous effort, PhD-level expertise
- 10× to 30× cost ratio versus unverified code
- Economics and velocity killed adoption

<!-- end_slide -->

# Finding *vs* Checking

- Rocq is a proof **checker**, not a proof finder
- Writing proofs is hard, checking them is mechanical
- Same asymmetry as cryptography: verify is cheaper than produce

<!-- pause -->

- Claude finds the proofs, about 3,600 lines (I steer the strategy)
- Rocq kernel checks every lemma, rejects anything wrong
- Does not matter **how** the proof was written, only that it passes the checker
- Not all languages equal: OCaml, Rust or C are easier to verify than Python or JavaScript

<!-- end_slide -->

# Trust Architecture

The *trusted computing base*: know exactly who is responsible for what.

| Layer | LOC | Tool | Reviewed by |
|-------|-----|------|-------------|
| Specification | 773 | Rocq | Human |
| Proof | 2,874 | Rocq | Kernel |
| Extracted OCaml | 101 | Extraction | Nobody |
| C stubs | 14 | GCC | Human |

<!-- pause -->

- Specification defines **what** is correct
- Proof shows **why** it is correct
- Rocq *extraction* translates proven code into OCaml automatically
- Code implements **how** it runs
- Human reviews **34 lines** total. Rest is machine-checked.
- You already trust the OS, the compiler, the hardware. This is no different

<!-- end_slide -->

# Three Numeric Worlds

<!-- column_layout: [1, 1, 1] -->

<!-- column: 0 -->

### ℤ (specification)

- Unbounded integers
- Proof automation
- Clean math

<!-- column: 1 -->

### ℕ (indices)

- List positions
- Structural recursion
- No overflow

<!-- column: 2 -->

### `Int63` (implementation)

- Machine words
- Overflow proofs
- Fast extraction

<!-- reset_layout -->

- Algorithmic correctness lives in ℤ: clean math, no overflow
- But ℤ arithmetic is impractical at runtime
- `Int63` gives native performance, but can overflow and wrap
- Bridging lemmas connect both: prove they agree when values fit

<!-- end_slide -->

# *Agrees* Pattern

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

# *Agrees* Pattern

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

# Popcount: Explicit Axioms

- Efficient Elias-Fano select needs **popcount** (count set bits)
- CPU provides `popcnt` instruction, but OCaml does not expose it
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

- **104 lemmas**, 0 Admitted, 2 axioms (`popcount` and `select`)
- Specification: 773 LOC, the *contract*
- Refinement: 2,874 LOC, the *proof of contract*
- Extraction glue: 27 LOC
- C stubs: 14 LOC, only unverified logic
- 4 top-level theorems: decode, nextGEQ (found/smallest/none)
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

About 20 lines of Rocq specification define what **correct** means.

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

- Unfold definitions, expose ℤ/ℕ/Int63 boundaries
- `lia` handles arithmetic, `bitblast` handles bitwise
- Watch the goal transform step by step

<!-- end_slide -->

# Demo Part 3: Build and Run

```bash
$ ./build.sh          # 3,647 lines type-checked
$                     # nothing visible, that is the point
$ ./bench/run.sh      # encode, access, decode, nextGEQ
```

<!-- pause -->

Quietest build is most trustworthy.

<!-- end_slide -->

# Oracle and Performance

- **Ground truth**: Sux (Vigna's C++ library)
- **100% match** at n = 3, 1,000, 10,000, 100,000

| Operation | versus Sux |
|-----------|------------|
| Encode | about 3× slower |
| Access | 1 to 17× slower |
| Decode | about 23× slower |

<!-- pause -->

- Proved correct does not mean fast (yet)
- Linear-scan nextGEQ versus Sux's O(1) rank-based jump
- No precomputed rank tables

<!-- end_slide -->

# Cost of Verification

- About 30× more Rocq code than unverified OCaml
- But:
- Specification is reusable across implementations
- Bugs found mechanically, not by humans
- No review needed for extracted code or proofs
- Refactoring changes proof, not specification

<!-- end_slide -->

# Human + LLM Collaboration

- **Phase 1**: User identified term explosion `Z_count_ones 63`
- **Phase 2**: LLM proved 30+ bridging lemmas via Model Context Protocol
- **Phase 3**: LLM ground through `bv_select_aux_agrees` across 3 contexts
- **Phase 4**: User taught “apply atomic conversions, watch the term”
- **Phase 5**: 4 final theorems fell in hours using established patterns

<!-- pause -->

I cheated you: I used my PhD in Coq for fixing Rocq performance pathologies.

<!-- end_slide -->

# Rocq/Coq Rebranding Friction

- Coq renamed to Rocq in 2024, documentation split
- LLM training data is overwhelmingly “Coq”
- Import paths changed (`From Coq` became `From Stdlib`)
- Version-specific bugs like `PArray` universe polymorphism in 9.1
- Real friction for AI-assisted formal methods
- Model Context Protocol servers `rocq-mcp` help bridge the gap

<!-- end_slide -->

# Takeaways

- LLMs help break through the 10× to 30× verification cost barrier
- Explicit trust beats implicit trust
- Specification is the new code review

<!-- pause -->

- 34 lines of human-reviewed code
- 3,647 lines of machine-checked proofs
- 0 admitted

<!-- pause -->

- The review wall has a door. Speak *formal*, and enter

<!-- end_slide -->

# Questions?

Project: github.com/cuihtlauac/eliasfano

```
104 lemmas · 0 Admitted · 2 axioms
773 + 2,874 LOC Rocq · 14 LOC C
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

# Appendix: References

**Studies**
- [Cisco/SmartBear code review study](https://static0.smartbear.co/support/media/resources/cc/book/code-review-cisco-case-study.pdf)
- [Peng et al., 2023 — Copilot productivity](https://arxiv.org/abs/2302.06590)
- [Claude's C compiler](https://github.com/anthropics/claudes-c-compiler)

**Formal methods milestones**
- [Hoare, 1969 — Axiomatic basis](https://dl.acm.org/doi/10.1145/363235.363259) · [LCF](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions) · [Calculus of Constructions](https://www.sciencedirect.com/science/article/pii/0890540188900053)
- [Abstract interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation) · [Model checking](https://en.wikipedia.org/wiki/Model_checking) · [Separation logic](https://en.wikipedia.org/wiki/Separation_logic)
- [CompCert](https://dl.acm.org/doi/10.1145/1538788.1538814) · [seL4](https://dl.acm.org/doi/10.1145/1629575.1629596) · [EverCrypt](https://project-everest.github.io/)
- [Astrée](https://www.astree.ens.fr/) · [Meta Infer](https://fbinfer.com/)

**Elias-Fano**
- [Elias, 1974](https://dl.acm.org/doi/10.1145/321812.321820) · [Vigna, 2013 — Quasi-succinct indices](https://vigna.di.unimi.it/ftp/papers/QuasiSuccinctIndices.pdf)
- [Sux library](https://github.com/vigna/sux) · [Succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure)

**Tools**
- [Rocq prover](https://rocq-prover.org/) · [Rocq extraction](https://rocq-prover.org/doc/V9.1.0/refman/addendum/extraction.html)
- [Formal verification](https://en.wikipedia.org/wiki/Formal_verification) · [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) · [Inverted index](https://en.wikipedia.org/wiki/Inverted_index)
