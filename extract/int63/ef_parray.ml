(** Drop-in replacement for Rocq's persistent [Parray] using mutable
    OCaml arrays.  Safe when the extracted code uses arrays linearly
    (no sharing), which is the case for all Elias-Fano operations.
    Uint63.t = int at runtime, so Obj.magic is a no-op.

    Bound to PArray primitives via [Extract Constant] in ExtractInt63.v.
    The spurious universe type variable from Rocq extraction
    (coq/coq#13575) is avoided by omitting ['a] from the body string
    of [Extract Constant PrimArray.array], following the workaround
    by ed-hermoreyes (Aug 2023).

    Ref: Sakaguchi, "Program Extraction for Mutable Arrays", FLOPS 2018 *)

type 'a t = 'a array

let make n v = Array.make (Obj.magic n : int) v
let get a i = Array.unsafe_get a (Obj.magic i : int)
let default a = Array.unsafe_get a 0
let set a i v = Array.unsafe_set a (Obj.magic i : int) v; a
let length a : _ = Obj.magic (Array.length a)
let copy a = Array.copy a
