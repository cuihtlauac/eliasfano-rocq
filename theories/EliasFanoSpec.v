(** * Elias-Fano Encoding — Specification

    This file contains the theorem statements that define correctness.
    These are the ONLY lines the human reviews. Everything else
    (implementation, proofs, extraction) is Claude's responsibility
    and checked by the Coq kernel. *)

From Stdlib Require Import ZArith List Bool Sorting.
Import ListNotations.

Open Scope Z_scope.

(** ** Data: a sorted sequence of non-negative integers bounded by U *)

Definition sorted (xs : list Z) : Prop := StronglySorted Z.le xs.

Definition all_nonneg (xs : list Z) : Prop :=
  Forall (fun x => 0 <= x) xs.

Definition bounded_by (U : Z) (xs : list Z) : Prop :=
  Forall (fun x => x < U) xs.

(** ** The encoding is a pair: lower bits array + upper bits bitvector *)

(** We leave the representation abstract at the spec level.
    The implementation will define [encoded] concretely. *)
Parameter encoded : Type.
Parameter encode : Z -> list Z -> encoded.  (** [encode U xs] *)
Parameter decode : encoded -> list Z.
Parameter access : encoded -> nat -> Z.
Parameter bit_size : encoded -> Z.

(** ** Core correctness: round-trip *)

Axiom round_trip :
  forall (U : Z) (xs : list Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    decode (encode U xs) = xs.

(** ** Element access *)

Axiom access_correct :
  forall (U : Z) (xs : list Z) (i : nat),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    (i < length xs)%nat ->
    access (encode U xs) i = nth i xs 0.

(** ** Successor query: smallest element >= v *)

Parameter nextGEQ : encoded -> Z -> option Z.

Axiom nextGEQ_found :
  forall (U : Z) (xs : list Z) (v r : Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    nextGEQ (encode U xs) v = Some r ->
    In r xs /\ r >= v.

Axiom nextGEQ_smallest :
  forall (U : Z) (xs : list Z) (v r : Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    nextGEQ (encode U xs) v = Some r ->
    forall y, In y xs -> y >= v -> r <= y.

Axiom nextGEQ_none :
  forall (U : Z) (xs : list Z) (v : Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    nextGEQ (encode U xs) v = None ->
    forall y, In y xs -> y < v.

(** ** Space bound *)

(** Encoding uses at most n*(2 + log2(U/n)) bits. *)

Axiom space_bound :
  forall (U : Z) (xs : list Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    xs <> [] -> 0 < U ->
    let n := Z.of_nat (length xs) in
    bit_size (encode U xs) <= n * (2 + Z.log2 (U / n)).

(** ** Rank and Select on bitvectors *)

(** Building blocks. Specs are self-contained, verified independently. *)

Fixpoint select_go (bv : list bool) (i : nat) (pos : nat) (count : nat) : nat :=
  match bv with
  | [] => pos
  | b :: bv' =>
      if b then
        if Nat.eqb count i then pos
        else select_go bv' i (S pos) (S count)
      else select_go bv' i (S pos) count
  end.

Definition position_of_ith_one (bv : list bool) (i : nat) : nat :=
  select_go bv i 0 0.

Definition count_ones_up_to (bv : list bool) (pos : nat) : nat :=
  count_occ Bool.bool_dec (firstn pos bv) true.

Axiom rank_select :
  forall (bv : list bool) (i : nat),
    (i < count_occ Bool.bool_dec bv true)%nat ->
    count_ones_up_to bv (position_of_ith_one bv i) = i.

Axiom select_rank :
  forall (bv : list bool) (pos : nat),
    nth pos bv false = true ->
    position_of_ith_one bv (count_ones_up_to bv pos) = pos.

(** ** Popcount (axiomatized, backed by C shim) *)

(** This is the one axiom backed by unverified C code.
    It appears explicitly in [Print Assumptions]. *)

From Stdlib Require Import Uint63.

Parameter popcount : int -> int.

Axiom popcount_spec :
  forall (x : int),
    Z.of_nat (
      let fix count_bits (n : nat) (acc : nat) :=
        match n with
        | O => acc
        | S n' => count_bits n' (if Z.testbit (to_Z x) (Z.of_nat n') then S acc else acc)
        end
      in count_bits 63%nat 0%nat
    ) = to_Z (popcount x).
