# Proof Engineering Notes: Verified Elias-Fano in Rocq

Notes on the difficulties, solutions, and lessons learned while building
the verified Elias-Fano implementation in `EliasFanoInt63.v`. Written
for anyone who wants to understand what went into the proofs and why
certain choices were made.

## The Goal

Prove that `encode63`/`access63`/`decode63`/`nextGEQ63` — implemented
with Int63 machine integers and primitive arrays — agree with the
Z-level specifications in `EliasFano.v`. The trust architecture:

- User reads ~20 lines of theorem statements
- Rocq kernel checks the proofs
- Extracted OCaml is never read
- C stubs (popcount, ctz) are ~6 lines, read by the user
- C stubs (shift, div, clz/ctz) are ~50 lines (`uint63_stubs.c`), read by the user
- Extraction overrides are ~20 lines (`ExtractInt63.v`), read by the user
- `Print Assumptions` lists exactly what remains unproved

## Three Numeric Worlds

The central engineering challenge was bridging three numeric types that
don't compose well.

**Z (integers):** All specification-level reasoning lives here.
`EliasFano.v` defines `encode`, `access`, `decode`, `nextGEQ` on Z
lists. The `lia` and `bitblast` tactics work natively. This is the
comfortable world.

**nat (natural numbers):** List indices, `count_occ`, fuel parameters
for `Fixpoint` recursion, `position_of_ith_one`. Required because Rocq
demands structural recursion — you can't recurse on `int`. `lia` works
after `Nat2Z.inj_*` conversions, but cannot handle `Z.to_nat` at all.

**int (Uint63):** The implementation type. Primitive — no induction, no
delta reduction for `PArray.length`. Every `+`, `*`, `/` on int requires
an overflow proof, a `to_Z` conversion, and `Z.mod_small`. There is no
tactic that works directly on int arithmetic.

Every bridging lemma crosses at least one of these boundaries, generating
conversion boilerplate (`Z2Nat.id`, `Nat2Z.inj_lt`, `to_Z_bounded`,
`of_Z_spec`, `to_Z_of_Z_small`, `add1_to_Z`, ...) that accounts for a
large fraction of proof effort. The `access63_agrees` proof is ~500
lines; perhaps 300 of those are type-boundary plumbing.

### Scope Pitfalls

With `uint63_scope` open, bare `+` resolves to `Uint63.add`, bare `0`
to `0%uint63`, and bare `length` to `PArray.length`. This silently
changes the meaning of goals. Writing `(x + y)%Z` everywhere is
essential but easy to forget. Several proof failures during development
traced back to scope confusion — the goal looked right but `lia` failed
because a `+` was secretly `Uint63.add`.

## The Popcount Axiom: Term Explosions

### The Problem

The popcount specification started as:

```coq
Axiom popcount_spec : forall x,
  Z_count_ones 63 (to_Z x) = to_Z (popcount x).
```

where `Z_count_ones` was defined inline. The problem: on the left side,
delta-expanding both `to_Z` and `Z_count_ones` produces a term that
grows by a factor of 63. Once unfolded, the term is too large for any
tactic to handle. `Qed` would hang. `simpl` would hang. Even stating a
lemma that unfolds both sides would hang.

This was identified by the user, not by Claude. Claude had not
anticipated that a seemingly straightforward counting function would
cause term blow-up.

### The Solution

The user drove the fix through a series of probing questions:

1. "Why not generalize to any number instead of 63 and prove by induction?"
2. "Is it possible to define an `int_count_ones` using a fixpoint?"
3. "Is `to_Z` opaque?"

The answer: extract `Z_count_bits` as a top-level `Fixpoint` on nat
(not a local definition), keep it accumulator-style to enable clean
induction, and bridge to the existing `Z_count_ones` via a separate
lemma `Z_count_bits_eq`. The `popcount_count_ones` proof then became
two lines.

### Lesson

Term size matters more than mathematical complexity. A lemma can be
trivially true but unprovable if the proof term explodes. Any definition
involving a fixed large constant (63, 256, ...) is suspect.

## PArray Universe Bug (Rocq 9.1)

`rewrite` and `apply` with `get_set_same`, `get_set_other`,
`length_set`, `get_make`, and `length_make` fail with a universe
inconsistency error. These are universe-polymorphic lemmas in the PArray
library, and Rocq 9.1's unification cannot instantiate them correctly.

Workaround: monomorphic `Local Lemma` wrappers specialized to `int`:

```coq
Local Lemma get_set_same' (t : array int) (i : int) (a : int) :
  (i <? PArray.length t)%uint63 = true -> t.[i <- a].[i] = a.
Proof. exact (get_set_same int t i a). Qed.
```

Even with wrappers, `rewrite get_set_same'` sometimes fails. In those
cases, `exact (get_set_same' ...)` with explicit arguments works. This
is another instance of Rocq's unifier struggling with primitive types.

Additionally, `simpl` and `cbn` must be avoided on PArray terms — they
unfold into incomprehensible primitive operations. Use `unfold X at 1;
fold X` for controlled reduction.

## `bv_select_aux_agrees`: Three Context Windows

This single lemma consumed three full Claude context windows (the
conversation hit the context limit twice). The difficulty was not
mathematical — the algorithm is a straightforward popcount-based linear
scan — but the Int63 arithmetic plumbing was enormous.

### The Word-Level Loop

`bv_select_aux` walks through array words, subtracting `popcount word`
from `remaining` until it finds the target word, then uses `tail0` and
`clear_n_ones` within that word. The specification function
`position_of_ith_one` walks a flat bool list. Bridging these required:

1. **Chunking:** Splitting the bool list into 63-element chunks
   corresponding to array words.

2. **Counting direction mismatch:** `Z_count_ones` counts bits from high
   to low (bit `j'` first), while `count_occ` on lists counts from low
   to high (head element first). The fix required `removelast`-based
   reasoning — prove for `removelast chunk` by IH, then handle the last
   element separately. This was an unexpected structural incompatibility.

3. **An unanticipated helper:** `position_of_ith_one_app` needed a
   count-shift property of the internal `select_go` function. This
   helper did not exist and required a separate inductive proof.

### MCP Hanging at 100% CPU

During development, the Rocq MCP (petanque) process became unresponsive.
`f_equal` on Int63 terms triggered unbounded unification. The process
consumed all CPU and became a zombie. The MCP was abandoned entirely for
this proof — all subsequent work was done by writing proof scripts
directly and checking with `./build.sh`.

### `wB` and `lia`

The constant `wB = 2^63` caused persistent `lia`/`nia` failures:

- Three overlapping definitions: local `wB`, `Uint63.wB`,
  `Uint63Axioms.wB` — `lia` treats them as different opaque atoms.
- `lia` cannot reason about `2^63` (needs concrete computation).
- `nia` handles nonlinear facts like `a <= a * 63` but is slow or fails
  when `2^63` is in the context.
- `vm_compute` on `(9223372036854775808 - 1) / 63` blew up.

The working pattern: `change Uint63Axioms.wB with (2^63)%Z` to unify
the definitions, then `lia` for linear facts, and direct lemma
application (`Z.div_le_mono` etc.) instead of `nia` for nonlinear ones.

## `access63_agrees`: Decomposition Under Pressure

### The 680-Line Monolith

The first version of `access63_agrees` was a single 680-line proof
script. It compiled but was fragile — any upstream change in a helper
lemma could break it in unpredictable ways. The user intervened: "No
proof script should be that long. Sketch decomposing it into manageable
lemmas."

### Extracted Helpers

- `sorted_map_upper_value` — used 3 times in the original proof
- `Forall_nonneg_map_upper_value` — used 3 times
- `last_map_upper_value` — used 2 times
- `fill_upper_length` — array length preservation through `fill_upper`
- `build_upper_length_eq` — exact length of the upper bitvector
- `build_upper_length_le` — upper bound for array allocation
- `fill_upper_zero_tail` — bits beyond the list are zero

The user warned that one of these would "blow up." That turned out to be
`fill_upper_zero_tail`.

### The `unfold bv0` Explosion

`bv0` was `make (add (div (add n63 max_upper63) wbits) 1) 0`. Unfolding
it produced a deeply nested Int63 expression. Then `rewrite length_make'`
produced an `if-then-else` over the whole expression, and `nia` tried to
process it — with ~50 context hypotheses including the massive
`bv_select_agrees` hypothesis. Result: `Qed` hung for minutes.

The user taught the debugging methodology:

> "You have to apply the atomic beta, delta, iota conversions step by
> step. Don't use any tactic that does recursive conversion. Use
> `Show Proof`. The idea is to watch the term — a repetitive pattern
> will arise if it's the explosive one."

Additional tips from the user:
- "Your timeout 300 is too high, set it at 20"
- "Use the ltac timeout tactical when debugging"
- "It may be a Qed explosion" (meaning the kernel check, not the tactic)

### Root Cause and Fix

The `nia` call in a bounds-checking callback processed all ~50 context
hypotheses, including huge terms. Replacing `nia` with a direct proof
(`Z.div_le_mono; lia`) avoided the search entirely. The final
`access63_agrees` compiles with `Qed` in under 30 seconds.

## `decode63` and `nextGEQ63`: The Reduction Strategy

The four final theorems (`decode63_agrees`, `nextGEQ63_found`,
`nextGEQ63_smallest`, `nextGEQ63_none`) were proved by a "reduction"
strategy: prove an "agrees" lemma that translates the Int63 result to
the Z-level result, then the semantic theorems follow from the Z-level
counterparts in one or two lines.

Key helpers:
- `add1_to_Z`: `to_Z i + 1 < wB -> to_Z (add i 1) = to_Z i + 1`
- `to_Z_of_Z_small`: `0 <= n < wB -> to_Z (of_Z n) = n`
- `encode63_n_agrees`: `Z.to_nat (to_Z (ef63_n (encode63 U xs))) = length xs`
- `access63_agrees_range`: pointwise access agreement for valid indices

The `nextGEQ63_aux_agrees` lemma is representative of the pattern:
induction on nat fuel, bridge comparisons via `leb_spec`/`Z.geb_le`,
and handle the `add i 1` step via `add1_to_Z` with overflow guard.

## Proof Techniques: What Worked and What Didn't

### Worked

- **Prove on Z, refine to Int63.** The Z-level proofs in `EliasFano.v`
  use `lia`, `bitblast`, and `Z.testbit` reasoning freely. The Int63
  layer is purely a refinement — the actual mathematics stays in Z.

- **Monomorphic PArray wrappers.** Once discovered, these work
  reliably. Define them once, use everywhere.

- **Controlled unfolding.** `unfold X at 1; fold X` instead of `simpl`
  or `cbn`. Never let Rocq auto-reduce Int63 or PArray terms.

- **Direct lemma application over `nia`.** When `nia` is slow or
  uncertain, a direct `apply Z.div_le_mono; lia` is both faster and
  more robust.

- **Decomposition into named helpers.** Every subgoal that appears more
  than once, or that involves complex terms, should be a named lemma.

- **The "agrees" pattern** for compound operations: prove functional
  agreement with the Z-level function, then derive semantic properties
  from the Z-level theorems.

### Didn't Work

- **`simpl` on anything involving Int63, PArray, or `Z_count_ones 63`.**
  Causes term explosion every time.

- **`nia` in large contexts.** Processes all hypotheses, including
  irrelevant huge terms. Blows up unpredictably.

- **Rocq MCP (petanque) on Int63 proofs.** Unification on Int63 terms
  causes unbounded CPU usage. Abandoned in favor of batch compilation.

- **Inline proofs of bounds.** Overflow checks for Int63 arithmetic
  accumulate and bloat the proof. Extract them as named lemmas.

- **`vm_compute` on `2^63`.** The kernel cannot efficiently compute with
  such large values.

## Evolution: From Autonomous Loop to Collaborative Debugging

### Phase 1: User-Driven Design

The user identified the term blow-up problem, proposed the fixpoint
refactoring, and dictated the axiom form. Claude executed. The user also
caught scope bugs that Claude missed. Almost all design decisions in this
phase came from the user.

### Phase 2: Claude-Driven Proofs with MCP

Claude proved the intermediate lemmas (`Z_count_ones_clearbit`,
`clear_n_ones_spec`, `select_word_correct`, bridging lemmas) largely
autonomously, using the Rocq MCP for interactive development. The user's
role was task selection ("try proving X") and readiness checks ("do we
have enough bridging lemmas?").

### Phase 3: Grinding Through Arithmetic

`bv_select_aux_agrees` was a war of attrition. Claude worked
autonomously across three context windows but repeatedly hit the same
obstacles: `wB`/`lia` failures, `to_nat`/`to_Z` conversion tangles,
and MCP hangs. The user's interventions were operational ("it's at 100%
CPU", "context window restart").

### Phase 4: User-Rescued Debugging

`access63_agrees` was where autonomous work hit its limits. Claude could
not diagnose the `nia`-context-explosion root cause without the user's
instruction to "apply atomic conversions step by step and watch the
terms." The user pointed out specific explosions in real time during
compilation, taught the `ltac timeout` debugging technique, and mandated
the decomposition into helper lemmas that ultimately made the proof
manageable.

### Phase 5: Smooth Finish

With the `access63_agrees` wall broken, the four remaining theorems
(`decode63_agrees`, `nextGEQ63_found`, `nextGEQ63_smallest`,
`nextGEQ63_none`) fell quickly via the reduction strategy. By this
point, the conversion boilerplate patterns were well-understood and
the helpers were in place.

## Extraction: A Different Kind of Bug

After all proofs were complete, extraction to efficient OCaml revealed
two new bugs:

1. **Rocq PArray extraction type syntax bug (coq/coq#13575).** The
   extraction generates a spurious type variable for universe-polymorphic
   types. Initially fixed with a sed post-processing rule in dune, later
   replaced by `Extract Constant PrimArray.array "'a" => "array"` +
   `Extraction Inline PrimArray.array` directly in `ExtractInt63.v`
   (workaround from the issue discussion).

2. **Popcount sign-extension bug.** The C stub uses `Long_val` which
   sign-extends negative OCaml ints. With `wbits=63` (vs. 62 in the
   hand-written code), bit 62 can be set, making the int negative and
   causing `__builtin_popcountl` to overcount by 1. Fixed by subtracting
   1 when the input is negative.

3. **Z-roundtrip performance.** The extracted `of_Z (Z.of_nat i)` went
   through the `positive` ADT representation (O(n) per call). Adding
   `ExtrOcamlZInt` and shortcutting `to_Z`/`of_Z`/`Z.of_nat`/`Z.to_nat`
   as identity functions brought encode from 57 seconds to 8.5
   milliseconds at n=100000.

4. **Dune `-opaque` blocks cross-module inlining.** Dune hardcodes
   `-opaque` for all library module compilations. This means
   `rocq-runtime`'s `Uint63` functions that lack `[@@ocaml.inline]`
   (namely `l_sl`, `l_sr`, `div`, `rem`, `head0`, `tail0`) become
   opaque closures, called via `caml_apply2` instead of direct calls.
   This caused a 3.3x overhead on decode. Fixed by introducing C stubs
   (`uint63_stubs.c`) exposed via `Ef_uint63_fast`, routed through
   `Extract Inlined Constant` directives. C externals with `[@@noalloc]`
   always get direct calls regardless of `-opaque`. This brought decode
   down to 1.6x and point queries to 1.15-1.19x. Functions already
   marked `[@@ocaml.inline always]` in rocq-runtime (`add`, `sub`,
   `land`, `lor`, `lt`, `le`) were left alone — their inline XOR
   comparison is faster than a C stub's stack-switch overhead.

These are all outside the trusted kernel — they affect only the
extracted code, not the proofs. But they illustrate that the gap between
"proved correct" and "actually works" is nontrivial. The trust perimeter
grows with each extraction shim: `uint63_stubs.c` (~50 lines) and the
`Extract Inlined Constant` directives in `ExtractInt63.v` (~20 lines)
must be reviewed by a human.

## What Would Be Done Differently

1. **Start with a `to_Z`/`of_Z` automation tactic.** Something like
   `int63_to_Z` that rewrites `to_Z (add x y)`, `to_Z (sub x y)`, etc.
   and generates overflow side-goals. This would eliminate half the
   boilerplate.

2. **Avoid `nia` entirely.** Every use of `nia` is a latent time bomb.
   Direct lemma application is always faster and more predictable.

3. **Extract `fill_upper_zero_tail` from the start.** The "zero bits
   beyond the encoded data" property is obviously needed. Not extracting
   it early led to the 680-line monolith and the explosion.

4. **Use `Nat.iter` instead of `Fixpoint` with nat fuel where possible.**
   Some of the nat/Z/int conversion pain comes from needing structural
   recursion. `Nat.iter` can sometimes avoid it.

5. **Define `wB` once and normalize everywhere.** The three overlapping
   `wB` definitions caused days of `lia` frustration.

6. **Anticipate dune's `-opaque` from the start.** Any OCaml function
   that needs to be fast and lives in a separate module will be opaque
   under dune. Plan for C stubs or same-module inlining from day one.
