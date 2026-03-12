(* Popcount wrapper for extracted code.

   The C stub uses Long_val which sign-extends negative OCaml ints.
   Since Uint63 uses all 63 bits, bit 62 can be set, making the
   OCaml int negative and adding a spurious bit via sign extension.
   We correct by subtracting 1 when the input is negative. *)

external popcount_int : int -> int = "caml_ef_popcount" [@@noalloc]

let popcount x =
  let v = (Obj.magic x : int) in
  let raw = popcount_int v in
  Uint63.of_int (if v < 0 then raw - 1 else raw)
