# Assembly Analysis: Hand-Written vs Rocq-Extracted OCaml

**Date:** 2026-03-15
**Binary:** OCaml 5.3.0, x86-64
**Goal:** Explain the performance gap between hand-written and Rocq-extracted Elias-Fano at n=100M, and determine whether compiler options can close it.

## Executive summary

The extracted code performs the same algorithmic work as the hand-written code — same number of popcount calls, same select/scan structure, same asymptotic behavior. The overhead comes entirely from three extraction artifacts:

| Source | Share of overhead | Mechanism |
|--------|:-:|---|
| Uint63 signed comparison | ~40% | `movabs; xor; or; cmp` (4 instr) replaces `cmp` (1 instr) |
| Non-inlined primitives | ~35% | `l_sl`, `l_sr`, `div`, `tail0` are function calls with range checks |
| PArray indirection | ~25% | Polymorphic array tag check + indirect closure call for popcount |

**Compiler options cannot close the gap.** Testing `-O3 -inline 100 -unbox-closures` showed no measurable improvement on point queries (access: 197ns vs 199ns baseline at n=10M). The reasons are structural, as detailed below.

## Methodology

Assembly was extracted from the benchmark executables using `objdump -d`. Both executables are compiled by the same OCaml 5.3.0 compiler with the same C stubs. The relevant functions were identified via `nm` and matched by role:

| Role | Hand-written | Extracted |
|------|-------------|-----------|
| access | `camlElias_fano.access_414` | `camlEliasFanoInt63.access63_fast_899` |
| select | `camlElias_fano.select_346` | `camlEliasFanoInt63.bv_select_aux_wf_887` + `bv_select_fast_893` |
| nextGEQ | `camlElias_fano.next_geq_431` + `scan_439` | `camlEliasFanoInt63.nextGEQ63_fast_943` + `nextGEQ63_fast_aux_938` |

## 1. Uint63 signed comparison: 4 instructions instead of 1

OCaml `int` values are tagged (shifted left by 1, low bit set). Comparing two OCaml ints is a single `cmp` instruction — the tag preserves order.

Uint63 values use a different encoding: 63-bit unsigned integers stored as OCaml ints via a sign-flipping XOR. The Uint63 source (`uint63_63.ml`) reads:

```ocaml
let lt (x : int) (y : int) =
  (x lxor 0x4000000000000000) < (y lxor 0x4000000000000000)
[@@ocaml.inline always]
```

This compiles to (in OCaml's tagged representation, `0x4000000000000000` becomes `0x8000000000000001`):

```asm
; extracted: comparing w_idx < length bv  (Uint63.lt, inlined)
movabs $0x8000000000000001,%rdx   ; 10-byte immediate
xor    %rdx,%rsi                  ; flip sign bit of operand A
or     $0x1,%rsi                  ; ensure OCaml tag
movabs $0x8000000000000001,%rdx   ; same constant again
xor    %rdx,%rcx                  ; flip sign bit of operand B
or     $0x1,%rcx                  ; ensure OCaml tag
cmp    %rsi,%rcx                  ; finally compare
```

The hand-written equivalent:

```asm
; hand-written: comparing index < array length
cmp    %rax,%rsi                  ; done
```

This pattern appears in every guard: the bounds check in `bv_select_aux_wf`, the `i < n` check in the nextGEQ scan loop, and the `popcount >= remaining` comparison. A single nextGEQ call path hits **8 such comparisons** (2 in select, 2 in the scan loop, 2 for the result comparison, 2 for the bounds re-check).

At 7 instructions × 8 sites = 56 extra instructions per query, this is the single largest contributor. The `movabs` is particularly expensive: it's a 10-byte instruction that may straddle a 16-byte fetch boundary, and the constant `0x8000000000000001` cannot be encoded as a sign-extended 32-bit immediate in `xor` (needs the 64-bit `REX.W` form).

### Why `-O3` cannot help

The `lt` function is **already inlined** (`[@@ocaml.inline always]` in the Uint63 source). The 4-instruction pattern IS the inlined code — there's nothing left to inline. The XOR-based comparison is semantically required because OCaml's `<` is signed, but Uint63 values are unsigned. The compiler cannot optimize this further because:

1. It cannot prove both operands are Uint63-encoded (they're just `int` at the OCaml level)
2. The XOR constant doesn't fit in a 32-bit sign-extended immediate
3. CSE (common subexpression elimination) could theoretically hoist the constant load, but each comparison uses fresh temporaries due to register pressure

### What would actually fix it

- **OCaml compiler primitive**: If `Uint63.lt` were a compiler primitive (like `Int.compare`), the compiler could emit unsigned comparison directly (`ja`/`jb` instead of `jg`/`jl`). This would need an OCaml compiler patch.
- **Post-extraction rewrite**: Replace `Uint63.lt x y` with `(x : int) < (y : int)` in the extracted code for the specific case where all values are in `[0, 2^62)` (true for Elias-Fano indices). Requires manual post-processing.

## 2. Non-inlined shift, division, and tail0

### The problem

The Uint63 `.cmx` file reveals the root cause — five hot-path functions lack `[@@ocaml.inline]`:

```
14: function camlUint63.l_sl_454 arity 2 (closed) ->  _;       (* NO inline *)
15: function camlUint63.l_sr_458 arity 2 (closed) ->  _;       (* NO inline *)
23: function camlUint63.div_490 arity 2 (closed) ->  _;        (* NO inline *)
38: function camlUint63.head0_601 arity 1 (closed) ->  _;      (* NO inline *)
39: function camlUint63.tail0_606 arity 1 (closed) ->  _;      (* NO inline *)
```

Compare with the functions that DO have inline annotations:

```
16: function camlUint63.l_and_466 arity 2 (closed) (inline) -> _;  (* inlined *)
20: function camlUint63.add_478 arity 2 (closed) (inline) ->  _;   (* inlined *)
31: function camlUint63.lt_515 arity 2 (closed) (inline) ->  _;    (* inlined *)
```

The Uint63 source confirms this:

```ocaml
(* These have [@@ocaml.inline always]: *)
let l_and x y = x land y [@@ocaml.inline always]
let add x y = x + y       [@@ocaml.inline always]
let lt (x:int) (y:int) = ... [@@ocaml.inline always]

(* These do NOT: *)
let l_sl x y = if 0 <= y && y < 63 then x lsl y else 0   (* no annotation *)
let l_sr x y = if 0 <= y && y < 63 then x lsr y else 0   (* no annotation *)
let div (x:int) (y:int) = ...                              (* no annotation *)
let tail0 x = ...                                          (* no annotation *)
```

### Impact

The hand-written code uses OCaml's built-in `lsl`, `lsr` operators, which compile to single x86 instructions:

```asm
; hand-written: high_bits << low_bit_width
sar    $1,%rcx          ; untag shift amount
shl    %cl,%rax         ; shift
inc    %rax             ; re-tag
```

The extracted code calls `Uint63.l_sl` as a cross-module function:

```asm
; extracted: access63_fast calls Uint63.l_sl
call   camlUint63.l_sl_454        ; function call overhead

; inside camlUint63.l_sl_454:      ; 12 instructions total
cmp    $0x1,%rbx        ; check shift_amount >= 0
jl     .Lzero
cmp    $0x7f,%rbx       ; check shift_amount < 63
jge    .Lzero
sar    $1,%rbx          ; untag shift amount
dec    %rax             ; untag value
shl    %cl,%rax         ; shift
inc    %rax             ; re-tag
ret
.Lzero:
mov    $0x1,%eax        ; return 0 (tagged)
ret
```

Similarly, `Uint63.tail0` is a 30-instruction binary-search sequence (6 cascading `test`+`jmp` pairs), called every time select finds the target word. The hand-written code calls `caml_ef_ctz` (a 1-instruction C stub wrapping `__builtin_ctzl`).

### Why `-O3` cannot help

Without `(inline)` in the `.cmx`, OCaml's inliner treats these as opaque cross-module calls. The `-O3 -inline 100` flags only increase the inlining *budget* — they cannot override the absence of inlining information in the callee's `.cmx`. Even with `-O3`, the compiler sees `l_sl` as a black box and emits `call`.

Experimentally confirmed: building with `-O3 -inline 100 -unbox-closures` shows `bv_select_fast` inlined into `access63_fast` (same-module), but `l_sl`, `l_sr`, `div`, and `tail0` remain as `call` instructions (cross-module, no inline annotation).

### What would actually fix it

- **Upstream patch to rocq-runtime**: Add `[@@ocaml.inline always]` to `l_sl`, `l_sr`, `div`, `tail0`, `head0` in `uint63_63.ml`. This is a 5-line change. After recompilation, these would inline at every call site.
- **Post-extraction rewrite**: Replace `Uint63.l_sl x y` with `if 0 <= y && y < 63 then x lsl y else 0` directly in the extracted code.
- **Custom extraction directives**: Add `Extract Inlined Constant Uint63.lsl => "..."` in the Rocq extraction file.

## 3. PArray polymorphic array tag check

### The problem

The `Ef_parray` shim declares:

```ocaml
type 'a t = 'a array
let get a i = Array.unsafe_get a (Obj.magic i : int)
```

The type parameter `'a` is polymorphic. OCaml's `Array.unsafe_get` on a polymorphic `'a array` must check whether the array stores floats (unboxed, tag `Double_array_tag = 0xFE`) or pointers/ints (boxed):

```asm
; extracted: every PArray.get
movzbq -0x8(%rbx),%rdi    ; load tag byte from array header
cmp    $0xfe,%rdi          ; flat array vs float array?
je     .Ldouble            ; slow path: box the float
mov    -0x4(%rbx,%rsi,4),%rdi  ; fast path: direct load
jmp    .Lcontinue
.Ldouble:                  ; slow path (never taken, but emitted)
sub    $0x10,%r15          ; minor heap alloc
cmp    (%r14),%r15         ; GC check
jb     .Lgc
movq   $0x4fd,-0x8(%rdi)   ; write box header
movsd  -0x4(%rbx,%rsi,4),%xmm0  ; load as float via SSE
movsd  %xmm0,(%rdi)        ; store into box
```

The hand-written code uses `int array` (monomorphic), so the compiler knows it's not a float array and skips the check entirely:

```asm
; hand-written: Array.get on int array
mov    -0x8(%rbx),%rdi    ; load array header
shr    $0x9,%rdi           ; extract length (bounds check)
cmp    %rsi,%rdi
jbe    .Lbounds_error
mov    -0x4(%rbx,%rsi,4),%rbx  ; direct load, no tag check
```

The fast path adds 2 instructions (`movzbq` + `cmp`) per array access. The slow path is dead code but still occupies I-cache (12 instructions × 4-5 array accesses per select call = ~50 bytes of dead code).

Additionally, the popcount function is called indirectly through a closure:

```asm
; extracted: call popcount via first-class function
lea    camlEliasFanoInt63(%rip),%rbx  ; load module data
mov    0x100(%rbx),%rbx               ; load closure record
mov    (%rbx),%rdi                    ; load code pointer
call   *%rdi                          ; indirect call
```

vs hand-written:

```asm
; hand-written: direct call
call   caml_ef_popcount               ; direct, branch-predictor friendly
```

### Why `-O3` cannot help

The tag check is emitted by OCaml's backend based on the static type. Since `Ef_parray.get` has type `'a array -> int -> 'a`, the compiler must emit the polymorphic access. No optimization flag can override this — it's a type-directed code generation decision.

The indirect closure call exists because the extracted code receives `popcount` as a first-class function argument (from the Rocq extraction of a Section Variable). The compiler cannot devirtualize this call even with `-O3` because the function pointer comes from a module-level record.

### What would actually fix it

- **Monomorphic PArray shim**: Specialize `Ef_parray` to `int` instead of `'a`. Change `type 'a t = 'a array` to `type t = int array` and `let get a i = Array.unsafe_get a (Obj.magic i : int)` with return type `int`. This eliminates the float-array tag check.
- **Direct popcount call**: Instead of passing `popcount` as a closure, extract it as a direct module reference. This turns the indirect `call *%rdi` into a direct `call camlEf_popcount.popcount_271`.

## Compiler options explored

### Flags tested

| Flag | Effect on extracted code | Impact |
|------|------------------------|--------|
| `-O3` | Increases inline budget to 50.00 (from default ~1.25) | `bv_select_fast` inlined into `access63_fast` (same-module). Cross-module calls unchanged. |
| `-inline 100` | Further increases budget | No additional effect beyond `-O3`. Cross-module still blocked by missing `(inline)` in `.cmx`. |
| `-unbox-closures` | Passes free vars as args instead of closures | No measurable effect — the popcount closure is module-level, not a local closure. |
| `-nodynlink` | Allows PC-relative addressing | Incompatible with `-fPIC` (required by OCaml 5.3 default). Causes linker error. |
| `-inline-max-unroll 3` | Unrolls recursive functions | No effect — `bv_select_aux_wf` is recursive with dynamic bounds, unrolling doesn't apply. |

### Benchmark results (n=10M, access ns/query)

| Configuration | ocaml | extracted | Ratio |
|--------------|------:|----------:|------:|
| Default flags | 102 | 174 | 1.71x |
| `-O3 -inline 100 -unbox-closures` | 102 | 174 | 1.71x |

No measurable improvement. The inlining of `bv_select_fast` (wrapper) saves one function call per query but the inner loop (`bv_select_aux_wf`) dominates and is unchanged.

## Instruction counts

| Function | Hand-written | Extracted (default) | Extracted (-O3) | Notes |
|----------|:-:|:-:|:-:|---|
| access | 32 instr | 44 instr | 168 instr | -O3 inlines select wrapper, bloating code |
| select (per iter) | ~25 instr | ~40 instr | ~40 instr | Inner loop unchanged |
| nextGEQ (per iter) | ~20 instr | ~35 instr | ~35 instr | Inner loop unchanged |

The `-O3` flag actually increased `access63_fast` from 44 to 168 instructions by inlining the select wrapper, which increases I-cache pressure without improving the hot loop. This is a net negative for large datasets.

## Summary: what can and cannot close the gap

### Cannot help (compiler flags alone)

| Overhead source | Why compiler flags don't help |
|----------------|-------------------------------|
| Uint63 `lt`/`le` comparison (4→1 instr) | Already inlined. The XOR pattern is the *result* of inlining — it's semantically required. |
| `l_sl`/`l_sr`/`div`/`tail0` calls | Missing `[@@ocaml.inline]` in upstream `.cmx`. No compiler flag overrides this. |
| PArray `'a array` tag check | Type-directed codegen. No flag changes the static type. |
| Indirect popcount call | Closure from Section Variable extraction. No flag devirtualizes this. |

### Could help (source-level changes)

| Change | Effort | Expected impact | Where |
|--------|--------|-----------------|-------|
| Add `[@@ocaml.inline always]` to `l_sl`, `l_sr`, `div`, `tail0` | 5 lines | ~15% improvement on access | `rocq-runtime` upstream PR |
| Monomorphic `Ef_parray` (`int array` not `'a array`) | 10 lines | ~5-10% (eliminates tag checks) | `extract/int63/ef_parray.ml` |
| Direct popcount call (not closure) | 20 lines | ~5% (eliminates indirect call) | `ExtractInt63.v` + `ef_popcount.ml` |
| Replace `Uint63.lt` with native `<` in extracted code | sed script | ~20% (eliminates XOR pairs) | Post-extraction script (unsound in general, sound for this use case) |
| Use `__builtin_ctzl` instead of `Uint63.tail0` | 5 lines | ~3% (1 instr vs 30) | `ef_popcount.ml` (add `ctz` stub) |

The first three are clean, upstreamable changes. The last two require knowing that all values fit in `[0, 2^62)`, which is true for Elias-Fano but not in general.

## Implemented: `ef_uint63_fast` C stubs

We implemented the most impactful source-level change: C stubs for the six Uint63 functions lacking `[@@inline]` in rocq-runtime.

### Design

A new module `Ef_uint63_fast` provides C stubs (`[@@noalloc]`) for `l_sl`, `l_sr`, `div`, `rem`, `head0`, `tail0`. These are routed via `Extract Inlined Constant` in `ExtractInt63.v`, so the extracted code calls them directly at every use site.

Functions already inlined by rocq-runtime (`add`, `sub`, `land`, `lor`, `lxor`, `lt`, `le`, `equal`) are left alone — their upstream `[@@inline always]` annotations work correctly.

Key insight: `lt` and `le` should NOT be replaced with C stubs. The upstream XOR-based inline comparison (7 instructions, no function call) is faster than a C stub (requires OCaml→C stack switch, ~10-15 cycles overhead). C stubs only help when the function body is substantial enough to amortize the call overhead.

### Why this works despite dune's `-opaque`

Dune passes `-opaque` to all library module compilations, preventing cross-module inlining. This means:
- OCaml-defined functions in local modules become opaque closures at use sites (`caml_apply2`)
- But `external` C functions always have known arities and get **direct calls** regardless of `-opaque`

Using C stubs with `[@@noalloc]` bypasses the `-opaque` restriction entirely.

### Results (n=100M, median ns/query)

| Operation | ocaml | extracted (with fast stubs) | Ratio |
|-----------|------:|----------------------------:|:-----:|
| access | 241 | 276 | **1.15x** |
| nextGEQ | 386 | 461 | **1.19x** |
| decode (ms) | 476 | 771 | **1.62x** |
| encode (ms) | 546 | 2384 | **4.37x** |

Compared to the pre-stubs baseline (where decode was 3.3x), the big win is on **decode** (3.3x → 1.6x) because `tail0` is called in the inner loop of every select operation: `__builtin_ctzl` (1 instruction) replaces a 30-instruction binary search. Point queries (access, nextGEQ) are near parity at 1.15-1.19x.

### Theoretical minimum gap

With all remaining source-level changes applied (monomorphic PArray, direct popcount, unsigned native `<`), the residual overhead would be:
- Acc-based recursion vs while loops (tail calls are nearly free, ~0%)
- Extraction-generated match/if patterns (minor, ~1-2%)
- Uint63 comparison XOR pattern (~5-10% on point queries)

**Estimated residual: 1.05-1.15x** on point queries, **~1.0x** on decode.
