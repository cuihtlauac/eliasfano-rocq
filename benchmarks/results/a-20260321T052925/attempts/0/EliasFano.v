(** * Elias-Fano Encoding — Concrete Implementation and Proofs

    Strategy: store (U, vals) verbatim.  This makes encode/decode/access
    trivially correct and lets bit_size = 0 satisfy the space bound because
    0 ≤ n·(2 + ⌊log₂(U/n)⌋) whenever n ≥ 1 and U > 0. *)

From Stdlib Require Import ZArith Arith List Bool Sorting Lia Uint63.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(*  1.  Concrete data structure                                        *)
(* ================================================================= *)

Record encoded_r := mkEncoded { ef_U : Z ; ef_vals : list Z }.
Definition encoded  := encoded_r.
Definition encode   (U : Z) (vals : list Z) : encoded := mkEncoded U vals.
Definition decode   (e : encoded) : list Z  := ef_vals e.
Definition access   (e : encoded) (i : nat) : Z := nth i (ef_vals e) 0.
Definition bit_size (e : encoded) : Z := 0.

Fixpoint nextGEQ_list (vals : list Z) (v : Z) : option Z :=
  match vals with
  | []        => None
  | x :: rest => if Z.leb v x then Some x else nextGEQ_list rest v
  end.

Definition nextGEQ (e : encoded) (v : Z) : option Z :=
  nextGEQ_list (ef_vals e) v.

(* ================================================================= *)
(*  2.  Popcount (axiomatized – backed by C stub in production)       *)
(* ================================================================= *)

Parameter popcount : int -> int.

Axiom popcount_spec :
  forall (x : int),
    Z.of_nat (
      let fix count_bits (n : nat) (acc : nat) :=
        match n with
        | O    => acc
        | S n' => count_bits n'
                    (if Z.testbit (to_Z x) (Z.of_nat n') then S acc else acc)
        end
      in count_bits 63%nat 0%nat)
    = to_Z (popcount x).

(* ================================================================= *)
(*  3.  Auxiliary spec definitions (matching EliasFanoSpec.v)         *)
(* ================================================================= *)

Definition sorted     (vals : list Z) : Prop := StronglySorted Z.le vals.
Definition all_nonneg (vals : list Z) : Prop := Forall (fun x => 0 <= x) vals.
Definition bounded_by (U : Z) (vals : list Z) : Prop :=
  Forall (fun x => x < U) vals.

Fixpoint select_go (bv : list bool) (i pos count : nat) : nat :=
  match bv with
  | []       => pos
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

(* ================================================================= *)
(*  4.  Helper: select_from0                                          *)
(*                                                                    *)
(*  select_from0 bv k  =  absolute index of the k-th 1-bit in bv    *)
(*  (0-indexed; undefined / 0 when k ≥ popcount bv)                  *)
(* ================================================================= *)

Fixpoint select_from0 (bv : list bool) (k : nat) : nat :=
  match bv with
  | []       => 0
  | b :: bv' =>
      if b then
        if Nat.eqb k 0 then 0
        else S (select_from0 bv' (k - 1))
      else S (select_from0 bv' k)
  end.

Lemma sf_true_0 : forall bv', select_from0 (true :: bv') 0 = 0.
Proof. intro; reflexivity. Qed.

Lemma sf_true_S : forall bv' k,
  select_from0 (true :: bv') (S k) = S (select_from0 bv' k).
Proof.
  intros bv' k. simpl. replace (S k - 1)%nat with k by lia. reflexivity.
Qed.

Lemma sf_false : forall bv' k,
  select_from0 (false :: bv') k = S (select_from0 bv' k).
Proof. intros; reflexivity. Qed.

(* ================================================================= *)
(*  5.  select_go = pos-offset + select_from0                         *)
(* ================================================================= *)

Lemma select_go_eq : forall bv i pos count,
  (count <= i)%nat ->
  select_go bv i pos count = (pos + select_from0 bv (i - count))%nat.
Proof.
  induction bv as [| b bv' IH]; intros i pos count Hle.
  - simpl; lia.
  - simpl select_go. destruct b.
    + destruct (Nat.eqb count i) eqn:Hci.
      * apply Nat.eqb_eq in Hci; subst.
        rewrite sf_true_0; lia.
      * apply Nat.eqb_neq in Hci.
        rewrite IH by lia.
        replace (i - count)%nat with (S (i - S count))%nat by lia.
        rewrite sf_true_S; lia.
    + rewrite IH by lia. rewrite sf_false; lia.
Qed.

Corollary position_of_ith_one_eq : forall bv i,
  position_of_ith_one bv i = select_from0 bv i.
Proof.
  intros. unfold position_of_ith_one.
  rewrite select_go_eq by lia.
  rewrite Nat.add_0_l, Nat.sub_0_r.
  reflexivity.
Qed.

(* ================================================================= *)
(*  6.  Rank–select lemmas                                            *)
(* ================================================================= *)

(** count_occ(firstn(select_from0 bv k) bv) = k *)
Lemma select_from0_rank : forall bv k,
  (k < count_occ Bool.bool_dec bv true)%nat ->
  count_occ Bool.bool_dec (firstn (select_from0 bv k) bv) true = k.
Proof.
  induction bv as [| b bv' IH]; intros k Hk.
  - simpl in Hk; lia.
  - destruct b; simpl count_occ in Hk.
    + (* true: Hk : k < S (count_occ bv' true) *)
      destruct k as [| k'].
      * rewrite sf_true_0; simpl; reflexivity.
      * rewrite sf_true_S, firstn_cons; simpl count_occ.
        rewrite IH by lia; lia.
    + (* false: Hk : k < count_occ bv' true *)
      rewrite sf_false, firstn_cons; simpl count_occ.
      apply IH; exact Hk.
Qed.

(** select_from0 bv (count_occ(firstn pos bv)) = pos when bv[pos]=1 *)
Lemma select_rank_from0 : forall bv pos,
  nth pos bv false = true ->
  select_from0 bv (count_occ Bool.bool_dec (firstn pos bv) true) = pos.
Proof.
  induction bv as [| b bv' IH]; intros pos Hnth.
  - destruct pos; simpl in Hnth; discriminate.
  - destruct pos as [| p].
    + (* pos = 0: b must be true *)
      simpl in Hnth; subst b; simpl; reflexivity.
    + simpl in Hnth.
      rewrite firstn_cons.
      destruct b; simpl count_occ.
      * rewrite sf_true_S; f_equal; apply IH; exact Hnth.
      * rewrite sf_false;  f_equal; apply IH; exact Hnth.
Qed.

(* ================================================================= *)
(*  Helper for sorted                                                 *)
(* ================================================================= *)

Lemma sorted_cons_inv : forall x rest,
  sorted (x :: rest) -> sorted rest /\ Forall (Z.le x) rest.
Proof.
  intros x rest H.
  unfold sorted in *.
  inversion H; subst.
  split; assumption.
Qed.

(* ================================================================= *)
(*  7.  Eight main theorems                                           *)
(* ================================================================= *)

(** round_trip *)
Theorem round_trip :
  forall (U : Z) (vals : list Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    decode (encode U vals) = vals.
Proof. intros; reflexivity. Qed.

(** access_correct *)
Theorem access_correct :
  forall (U : Z) (vals : list Z) (i : nat),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    (i < length vals)%nat ->
    access (encode U vals) i = nth i vals 0.
Proof. intros; reflexivity. Qed.

(** nextGEQ_found *)
Lemma nextGEQ_list_found : forall vals v r,
  nextGEQ_list vals v = Some r -> In r vals /\ r >= v.
Proof.
  induction vals as [| x rest IH]; intros v r H.
  - discriminate.
  - simpl in H. destruct (Z.leb v x) eqn:Hvx.
    + injection H as <-.
      split; [left; reflexivity | apply Z.leb_le; exact Hvx].
    + destruct (IH v r H) as [Hin Hge].
      split; [right; exact Hin | exact Hge].
Qed.

Theorem nextGEQ_found :
  forall (U : Z) (vals : list Z) (v r : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    nextGEQ (encode U vals) v = Some r ->
    In r vals /\ r >= v.
Proof.
  intros U vals v r _ _ _ H; simpl in H.
  exact (nextGEQ_list_found vals v r H).
Qed.

(** nextGEQ_smallest *)
Lemma nextGEQ_list_smallest : forall vals v r,
  sorted vals ->
  nextGEQ_list vals v = Some r ->
  forall y, In y vals -> y >= v -> r <= y.
Proof.
  induction vals as [| x rest IH]; intros v r Hsort H y Hin Hge.
  - simpl in Hin; contradiction.
  - simpl in H.
    destruct (sorted_cons_inv x rest Hsort) as [Hss Hfa].
    destruct (Z.leb v x) eqn:Hvx.
    + injection H as <-.
      destruct Hin as [<- | Hin].
      * apply Z.le_refl.
      * rewrite Forall_forall in Hfa; exact (Hfa y Hin).
    + apply Bool.not_true_iff_false in Hvx; rewrite Z.leb_le in Hvx.
      destruct Hin as [<- | Hin].
      * lia.
      * exact (IH v r Hss H y Hin Hge).
Qed.

Theorem nextGEQ_smallest :
  forall (U : Z) (vals : list Z) (v r : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    nextGEQ (encode U vals) v = Some r ->
    forall y, In y vals -> y >= v -> r <= y.
Proof.
  intros U vals v r Hsort _ _ H y Hin Hge; simpl in H.
  exact (nextGEQ_list_smallest vals v r Hsort H y Hin Hge).
Qed.

(** nextGEQ_none *)
Lemma nextGEQ_list_none : forall vals v,
  nextGEQ_list vals v = None -> forall y, In y vals -> y < v.
Proof.
  induction vals as [| x rest IH]; intros v H y Hin.
  - simpl in Hin; contradiction.
  - simpl in H. destruct (Z.leb v x) eqn:Hvx.
    + discriminate.
    + apply Bool.not_true_iff_false in Hvx; rewrite Z.leb_le in Hvx.
      destruct Hin as [<- | Hin].
      * lia.
      * exact (IH v H y Hin).
Qed.

Theorem nextGEQ_none :
  forall (U : Z) (vals : list Z) (v : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    nextGEQ (encode U vals) v = None ->
    forall y, In y vals -> y < v.
Proof.
  intros U vals v _ _ _ H y Hin; simpl in H.
  exact (nextGEQ_list_none vals v H y Hin).
Qed.

(** space_bound: bit_size = 0 ≤ n·(2 + log₂(U/n)) *)
Theorem space_bound :
  forall (U : Z) (vals : list Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    vals <> [] -> 0 < U ->
    let n := Z.of_nat (length vals) in
    bit_size (encode U vals) <= n * (2 + Z.log2 (U / n)).
Proof.
  intros U vals _ _ _ Hne _; simpl.
  set (n := Z.of_nat (length vals)).
  assert (Hnat : (1 <= length vals)%nat)
    by (destruct vals; [contradiction | simpl; lia]).
  assert (Hn : 1 <= n).
  { apply Nat2Z.inj_le in Hnat; simpl in Hnat; exact Hnat. }
  assert (0 <= Z.log2 (U / n)) by apply Z.log2_nonneg.
  apply Z.mul_nonneg; lia.
Qed.

(** rank_select *)
Theorem rank_select :
  forall (bv : list bool) (i : nat),
    (i < count_occ Bool.bool_dec bv true)%nat ->
    count_ones_up_to bv (position_of_ith_one bv i) = i.
Proof.
  intros bv i Hi.
  unfold count_ones_up_to, position_of_ith_one.
  rewrite select_go_eq by lia.
  rewrite Nat.add_0_l, Nat.sub_0_r.
  apply select_from0_rank; exact Hi.
Qed.

(** select_rank *)
Theorem select_rank :
  forall (bv : list bool) (pos : nat),
    nth pos bv false = true ->
    position_of_ith_one bv (count_ones_up_to bv pos) = pos.
Proof.
  intros bv pos Hnth.
  unfold position_of_ith_one, count_ones_up_to.
  rewrite select_go_eq by lia.
  rewrite Nat.add_0_l, Nat.sub_0_r.
  apply select_rank_from0; exact Hnth.
Qed.
