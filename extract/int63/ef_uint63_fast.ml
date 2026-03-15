(* Fast replacements for Uint63 functions that rocq-runtime does NOT
   mark [@@ocaml.inline].  Implemented as C stubs with [@@noalloc] so
   they get direct calls despite dune's [-opaque] on library modules.

   Only covers: l_sl, l_sr, div, rem, head0, tail0.
   All other Uint63 functions (add, sub, land, lor, lt, le, etc.) are
   already inlined by rocq-runtime's .cmx and don't need replacements.

   Bound to Uint63 primitives via [Extract Inlined Constant] in
   ExtractInt63.v. *)

external l_sl : int -> int -> int = "caml_uint63_l_sl" [@@noalloc]
external l_sr : int -> int -> int = "caml_uint63_l_sr" [@@noalloc]
external div : int -> int -> int = "caml_uint63_div" [@@noalloc]
external rem : int -> int -> int = "caml_uint63_rem" [@@noalloc]
external head0 : int -> int = "caml_uint63_head0" [@@noalloc]
external tail0 : int -> int = "caml_uint63_tail0" [@@noalloc]
