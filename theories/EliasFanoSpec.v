(** * Elias-Fano Encoding — Specification

    This file contains the theorem statements that define correctness.
    These are the ONLY lines the human reviews. Everything else
    (implementation, proofs, extraction) is Claude's responsibility
    and checked by the Coq kernel. *)

From Stdlib Require Import ZArith List Bool Sorting.
Import ListNotations.

Open Scope Z_scope.

(** ** Data: a sorted sequence of non-negative integers bounded by U *)

Definition sorted (vals : list Z) : Prop := StronglySorted Z.le vals.

Definition all_nonneg (vals : list Z) : Prop :=
  Forall (fun x => 0 <= x) vals.

Definition bounded_by (U : Z) (vals : list Z) : Prop :=
  Forall (fun x => x < U) vals.

(** ** The encoding is a pair: lower bits array + upper bits bitvector *)

(** We leave the representation abstract at the spec level.
    The implementation will define [encoded] concretely. *)
Parameter encoded : Type.
Parameter encode : Z -> list Z -> encoded.  (** [encode U vals] *)
Parameter decode : encoded -> list Z.
Parameter access : encoded -> nat -> Z.
Parameter bit_size : encoded -> Z.

(** ** Core correctness: round-trip *)

Conjecture round_trip :
  forall (U : Z) (vals : list Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    decode (encode U vals) = vals.

(** ** Element access *)

Conjecture access_correct :
  forall (U : Z) (vals : list Z) (i : nat),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    (i < length vals)%nat ->
    access (encode U vals) i = nth i vals 0.

(** ** Successor query: smallest element >= v *)

Parameter nextGEQ : encoded -> Z -> option Z.

Conjecture nextGEQ_found :
  forall (U : Z) (vals : list Z) (v r : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    nextGEQ (encode U vals) v = Some r ->
    In r vals /\ r >= v.

Conjecture nextGEQ_smallest :
  forall (U : Z) (vals : list Z) (v r : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    nextGEQ (encode U vals) v = Some r ->
    forall y, In y vals -> y >= v -> r <= y.

Conjecture nextGEQ_none :
  forall (U : Z) (vals : list Z) (v : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    nextGEQ (encode U vals) v = None ->
    forall y, In y vals -> y < v.

(** ** Space bound *)

(** FIXME: This conjecture is vacuous as stated. [bit_size] is a
    [Parameter], so the implementation can define it however it likes —
    e.g. [bit_size _ := 0] — and satisfy the bound without compressing
    anything. An agent already exploited this (see results/a-20260321T052925).

    To make this meaningful, [bit_size] should be spec-defined as the
    actual encoding size (n*l + length(ef_upper)), and [num_lower_bits]
    should use ceil (Z.log2_up) so the upper bitvector is guaranteed
    <= 2n bits, matching the standard bound n*(2 + ⌈log₂(U/n)⌉). *)

Conjecture space_bound :
  forall (U : Z) (vals : list Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    vals <> [] -> 0 < U ->
    let n := Z.of_nat (length vals) in
    bit_size (encode U vals) <= n * (2 + Z.log2 (U / n)).

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

Conjecture rank_select :
  forall (bv : list bool) (i : nat),
    (i < count_occ Bool.bool_dec bv true)%nat ->
    count_ones_up_to bv (position_of_ith_one bv i) = i.

Conjecture select_rank :
  forall (bv : list bool) (pos : nat),
    nth pos bv false = true ->
    position_of_ith_one bv (count_ones_up_to bv pos) = pos.

(** ** Popcount (axiomatized, backed by C shim) *)

(** This is the one axiom backed by unverified C code.
    It appears explicitly in [Print Assumptions]. *)

From Stdlib Require Import Uint63.

Parameter popcount : int -> int.

Conjecture popcount_spec :
  forall (x : int),
    Z.of_nat (
      let fix count_bits (n : nat) (acc : nat) :=
        match n with
        | O => acc
        | S n' => count_bits n' (if Z.testbit (to_Z x) (Z.of_nat n') then S acc else acc)
        end
      in count_bits 63%nat 0%nat
    ) = to_Z (popcount x).
