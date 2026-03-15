(** * Extraction of Int63/PArray Elias-Fano to OCaml

    Maps Uint63 → [Uint63.t], PArray → [Ef_parray.t], nat → [int],
    Z → [int].  Key conversions (to_Z, of_Z, Z.of_nat, Z.to_nat) are
    shortcut to identity since all four types are [int] at runtime.

    The fast operations ([access63_fast], [decode63_fast], [nextGEQ63_fast])
    use Leroy's Acc-based well-founded recursion pattern, which extraction
    erases completely — no fuel, no sigT packing, no closure dispatch.
    See: Leroy, "Well-founded recursion done right", CoqPL 2024.

    PArray operations are mapped to [Ef_parray] (mutable arrays) rather
    than the default [Parray] (persistent copy-on-write).  This is safe
    because all Elias-Fano operations use arrays linearly (no sharing).
    See: Sakaguchi, "Program Extraction for Mutable Arrays", FLOPS 2018. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt
                           ExtrOcamlZInt ExtrOCamlInt63.
From EliasFano Require Import EliasFanoInt63.

(** Popcount: C stub via [Ef_popcount] (corrects sign-extension). *)
Extract Constant popcount => "Ef_popcount.popcount".

(** PArray → OCaml Array: mutable arrays for performance.
    Replaces the default [ExtrOCamlPArray] which maps to persistent
    [Parray.t].  Direct [Array] operations are safe because all
    Elias-Fano operations use arrays linearly (no sharing).
    See: Sakaguchi, "Program Extraction for Mutable Arrays", FLOPS 2018.

    Since Uint63.t = int at runtime (via ExtrOCamlInt63), no Obj.magic
    is needed for index conversions. *)
(** The body omits ['a] on purpose: [Extraction Inline] prepends the
    actual type argument, so ["'a array"] would produce a spurious
    extra variable (Rocq bug coq/coq#13575).  Workaround from the issue
    discussion (ed-hermoreyes, Aug 2023). *)
Extract Constant PrimArray.array "'a" => "array".
Extraction Inline PrimArray.array.
Extract Constant PrimArray.make => "(fun n v -> Array.make (Obj.magic n) v)".
Extract Constant PrimArray.get => "(fun a i -> Array.unsafe_get a (Obj.magic i))".
Extract Constant PrimArray.default => "(fun a -> Array.unsafe_get a 0)".
Extract Constant PrimArray.set => "(fun a i v -> Array.unsafe_set a (Obj.magic i) v; a)".
Extract Constant PrimArray.length => "(fun a -> Obj.magic (Array.length a))".
Extract Constant PrimArray.copy => "Array.copy".

(** Shortcut Z↔nat↔Uint63 roundtrips.
    With ExtrOcamlNatInt, ExtrOcamlZInt, and ExtrOCamlInt63, all four
    numeric types (nat, Z, positive, Uint63.t) are OCaml [int].
    The default extractions go through O(n) recursion; these are O(1). *)
Extract Constant BinPos.Pos.of_succ_nat => "Stdlib.Int.succ".
Extract Constant BinInt.Z.of_nat => "fun n -> n".
Extract Constant BinInt.Z.to_nat => "fun z -> Stdlib.max 0 z".
Extract Constant Uint63.to_Z => "Obj.magic".
Extract Constant Uint63.of_Z => "Obj.magic".

(** Uint63 fast paths: route slow functions (those lacking
    [@@ocaml.inline] in rocq-runtime) through C stubs in
    [Ef_uint63_fast].  These get direct calls despite dune's [-opaque].
    Functions already inlined by rocq-runtime (add, sub, land, lor, etc.)
    are left alone. *)
Extract Inlined Constant Uint63.lsl => "(fun x y -> Obj.magic (Ef_uint63_fast.l_sl (Obj.magic x) (Obj.magic y)))".
Extract Inlined Constant Uint63.lsr => "(fun x y -> Obj.magic (Ef_uint63_fast.l_sr (Obj.magic x) (Obj.magic y)))".
Extract Inlined Constant Uint63.div => "(fun x y -> Obj.magic (Ef_uint63_fast.div (Obj.magic x) (Obj.magic y)))".
Extract Inlined Constant Uint63.mod => "(fun x y -> Obj.magic (Ef_uint63_fast.rem (Obj.magic x) (Obj.magic y)))".
Extract Inlined Constant Uint63.head0 => "(fun x -> Obj.magic (Ef_uint63_fast.head0 (Obj.magic x)))".
Extract Inlined Constant Uint63.tail0 => "(fun x -> Obj.magic (Ef_uint63_fast.tail0 (Obj.magic x)))".

Set Extraction Output Directory ".".
Extraction "EliasFanoInt63.ml"
  encode63 access63 access63_fast decode63 decode63_fast nextGEQ63 nextGEQ63_fast bit_size63.
