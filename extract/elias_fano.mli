(** Verified Elias-Fano encoding.

    All operations are proved correct in Rocq.
    See [EliasFano.v] for the proofs. *)

(** Opaque encoded representation. *)
type t

(** [encode ~universe xs] encodes a sorted array of non-negative integers
    all strictly less than [universe]. *)
val encode : universe:int -> int array -> t

(** [decode t] recovers the original sorted array. *)
val decode : t -> int array

(** [access t i] returns the [i]-th element (0-indexed). *)
val access : t -> int -> int

(** [next_geq t v] returns the smallest element [>= v], or [None]. *)
val next_geq : t -> int -> int option

(** [bit_size t] returns the exact encoding size in bits:
    [n * l] lower bits plus the upper bitvector length. *)
val bit_size : t -> int

(** [length t] returns the number of encoded elements. *)
val length : t -> int
