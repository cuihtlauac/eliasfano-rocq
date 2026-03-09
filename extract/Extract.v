(** * Extraction of Elias-Fano to OCaml *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
From EliasFano Require Import EliasFano.

(** Extract the public API *)
Extraction "EliasFanoOcaml.ml"
  encode decode access nextGEQ bit_size.
