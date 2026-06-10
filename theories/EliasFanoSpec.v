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

(** The bound is stated on a *serialization* of the encoding:
    [to_bits] lays the encoding out as a bit list, and [of_bits]
    rebuilds it given the universe [U] and the element count [n]
    (caller-side context, as usual for succinct data structures).
    Decoding must succeed from the bit list alone, so every bit of
    information is counted by [length (to_bits _)] — an implementation
    cannot satisfy the bound with a fake size function. (An earlier
    version stated the bound on an abstract [Parameter bit_size],
    which was vacuous; an agent exploited it with [bit_size _ := 0] —
    see results/a-20260321T052925.)

    The bound is the standard one (Elias 1974; Vigna, "Quasi-succinct
    indices", WSDM 2013): n * (2 + ⌈log₂(U/n)⌉) bits, with U/n exact
    rational division. [ceil_log2] expresses ⌈log₂ q⌉ on rationals;
    its defining Galois property is proved below, kernel-checked. *)

From Stdlib Require Import QArith Qpower Qround Lia.
Open Scope Z_scope.  (* QArith puts %Q on top; restore %Z as default *)

(** [ceil_log2 q] = ⌈log₂ q⌉ for q >= 1, clamped to 0 for q <= 1. *)
Definition ceil_log2 (q : Q) : Z := Z.log2_up (Qceiling q).

(** ⌈log₂ q⌉ is the least k with q <= 2^k. *)
Lemma ceil_log2_galois :
  forall (q : Q) (k : Z),
    (1 <= q)%Q -> 0 <= k ->
    (ceil_log2 q <= k <-> (q <= inject_Z 2 ^ k)%Q).
Proof.
  intros q k Hq Hk.
  unfold ceil_log2.
  assert (Hm : 0 < Qceiling q).
  { pose proof (Qceiling_resp_le 1 q Hq) as H.
    change (Qceiling 1) with 1%Z in H. lia. }
  rewrite <- (Z.log2_up_le_pow2 _ k Hm).
  split.
  - intros H.
    eapply Qle_trans; [apply Qle_ceiling|].
    rewrite <- Zpower_Qpower by exact Hk.
    rewrite <- Zle_Qle. exact H.
  - intros H.
    rewrite <- Zpower_Qpower in H by exact Hk.
    rewrite <- (Qceiling_Z (2 ^ k)).
    apply Qceiling_resp_le. exact H.
Qed.

Parameter to_bits : encoded -> list bool.
Parameter of_bits : Z -> nat -> list bool -> encoded.
(** [of_bits U n bits] *)

Conjecture space_bound :
  forall (U : Z) (vals : list Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    vals <> [] -> 0 < U ->
    let n := Z.of_nat (length vals) in
    let bits := to_bits (encode U vals) in
    decode (of_bits U (length vals) bits) = vals /\
    Z.of_nat (length bits) <= n * (2 + ceil_log2 (inject_Z U / inject_Z n)).

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
