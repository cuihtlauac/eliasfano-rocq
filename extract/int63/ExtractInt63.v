(** * Extraction of Int63/PArray Elias-Fano to OCaml

    Maps Uint63 → [Uint63.t], PArray → [Parray.t], nat → [int], Z → [int].
    Key conversions (to_Z, of_Z, Z.of_nat, Z.to_nat) are shortcut to
    identity since all four types are [int] at runtime. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt
                           ExtrOcamlZInt ExtrOCamlInt63 ExtrOCamlPArray.
From EliasFano Require Import EliasFanoInt63.

(** Popcount: C stub via [Ef_popcount] (corrects sign-extension). *)
Extract Constant popcount => "Ef_popcount.popcount".

(** Shortcut Z↔nat↔Uint63 roundtrips.
    With ExtrOcamlNatInt, ExtrOcamlZInt, and ExtrOCamlInt63, all four
    numeric types (nat, Z, positive, Uint63.t) are OCaml [int].
    The default extractions go through O(n) recursion; these are O(1). *)
Extract Constant BinPos.Pos.of_succ_nat => "Stdlib.Int.succ".
Extract Constant BinInt.Z.of_nat => "fun n -> n".
Extract Constant BinInt.Z.to_nat => "fun z -> Stdlib.max 0 z".
Extract Constant Uint63.to_Z => "Obj.magic".
Extract Constant Uint63.of_Z => "Obj.magic".

Set Extraction Output Directory ".".
Extraction "EliasFanoInt63Ocaml.ml"
  encode63 access63 decode63 nextGEQ63 bit_size63.
