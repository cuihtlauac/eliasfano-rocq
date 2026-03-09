(** * Elias-Fano Encoding — Implementation and Proofs *)

From Stdlib Require Import ZArith List Bool Sorting Lia Uint63.
From Stdlib Require Import Permutation.
Import ListNotations.

Open Scope Z_scope.

(* ================================================================= *)
(* Definitions from spec (provided concretely)                        *)
(* ================================================================= *)

Definition sorted (xs : list Z) : Prop := StronglySorted Z.le xs.

Definition all_nonneg (xs : list Z) : Prop :=
  Forall (fun x => 0 <= x) xs.

Definition bounded_by (U : Z) (xs : list Z) : Prop :=
  Forall (fun x => x < U) xs.

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

(* ================================================================= *)
(* Part 1: Rank / Select proofs                                       *)
(* ================================================================= *)

Lemma select_go_shift :
  forall bv i d pos count,
    select_go bv i (pos + d) count = (select_go bv i pos count + d)%nat.
Proof.
  induction bv as [|b bv' IH]; intros; simpl.
  - lia.
  - destruct b; [destruct (Nat.eqb count i)|];
    try (replace (S (pos + d)) with (S pos + d)%nat by lia;
         rewrite IH; lia).
    lia.
Qed.

Corollary select_go_base :
  forall bv i pos count,
    select_go bv i pos count = (select_go bv i 0 count + pos)%nat.
Proof.
  intros. replace pos with (0 + pos)%nat by lia. apply select_go_shift.
Qed.

(* Fully generalized induction for select_go *)
Lemma select_go_rank_gen :
  forall bv i pos count,
    (i >= count)%nat ->
    (i - count < count_occ Bool.bool_dec bv true)%nat ->
    let p := select_go bv i pos count in
    nth (p - pos) bv false = true /\
    count_occ Bool.bool_dec (firstn (p - pos) bv) true = (i - count)%nat /\
    (p >= pos)%nat /\
    (p - pos < length bv)%nat.
Proof.
  induction bv as [|b bv' IH]; intros i pos count Hge Hlt.
  - simpl in Hlt. lia.
  - simpl. destruct b.
    + simpl in Hlt.
      destruct (Nat.eqb count i) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst.
        replace (pos - pos)%nat with 0%nat by lia.
        simpl. replace (i - i)%nat with 0%nat by lia.
        split; [reflexivity|]. split; [reflexivity|]. split; lia.
      * apply Nat.eqb_neq in Heq.
        assert (Hge' : (i >= S count)%nat) by lia.
        assert (Hlt' : (i - S count < count_occ Bool.bool_dec bv' true)%nat) by lia.
        specialize (IH i (S pos) (S count) Hge' Hlt').
        destruct IH as [IH1 [IH2 [IH3 IH4]]].
        replace (select_go bv' i (S pos) (S count) - pos)%nat with
          (S (select_go bv' i (S pos) (S count) - S pos)%nat) by lia.
        simpl.
        repeat split; [exact IH1 | | lia | lia].
        rewrite IH2. lia.
    + simpl in Hlt.
      specialize (IH i (S pos) count Hge Hlt).
      destruct IH as [IH1 [IH2 [IH3 IH4]]].
      replace (select_go bv' i (S pos) count - pos)%nat with
        (S (select_go bv' i (S pos) count - S pos)%nat) by lia.
      simpl.
      repeat split; [exact IH1 | exact IH2 | lia | lia].
Qed.

Theorem rank_select :
  forall (bv : list bool) (i : nat),
    (i < count_occ Bool.bool_dec bv true)%nat ->
    count_ones_up_to bv (position_of_ith_one bv i) = i.
Proof.
  intros bv i Hi.
  unfold position_of_ith_one, count_ones_up_to.
  pose proof (select_go_rank_gen bv i 0 0 (Nat.le_0_l i) ltac:(lia)) as H.
  simpl in H.
  replace (select_go bv i 0 0 - 0)%nat with (select_go bv i 0 0) in H by lia.
  replace (i - 0)%nat with i in H by lia.
  destruct H as [_ [H _]]. exact H.
Qed.

Lemma select_go_at_gen :
  forall bv pos count target offset,
    (pos < length bv)%nat ->
    nth pos bv false = true ->
    count_occ Bool.bool_dec (firstn pos bv) true = (target - count)%nat ->
    (target >= count)%nat ->
    select_go bv target offset count = (offset + pos)%nat.
Proof.
  induction bv as [|b bv' IH]; intros pos count target offset Hpos Hnth Hco Hge.
  - simpl in Hpos. lia.
  - destruct pos as [|pos'].
    + simpl in Hnth. subst b. simpl in Hco |- *.
      assert (target = count) by lia. subst. rewrite Nat.eqb_refl. lia.
    + simpl in Hpos, Hnth. simpl. destruct b.
      * simpl in Hco.
        destruct (Nat.eqb count target) eqn:Heq.
        -- apply Nat.eqb_eq in Heq. lia.
        -- apply Nat.eqb_neq in Heq.
           rewrite IH with (pos := pos') (target := target);
             [lia | lia | exact Hnth | lia | lia].
      * simpl in Hco.
        rewrite IH with (pos := pos') (target := target);
          [lia | lia | exact Hnth | exact Hco | exact Hge].
Qed.

Theorem select_rank :
  forall (bv : list bool) (pos : nat),
    nth pos bv false = true ->
    position_of_ith_one bv (count_ones_up_to bv pos) = pos.
Proof.
  intros bv pos Hnth.
  unfold position_of_ith_one, count_ones_up_to.
  assert (Hpos : (pos < length bv)%nat).
  { destruct (Nat.lt_ge_cases pos (length bv)); [assumption|].
    exfalso. rewrite nth_overflow in Hnth by lia. discriminate. }
  set (target := count_occ Bool.bool_dec (firstn pos bv) true).
  rewrite (select_go_at_gen bv pos 0 target 0 Hpos Hnth ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* ================================================================= *)
(* Part 2: Encoding definitions                                       *)
(* ================================================================= *)

Definition num_lower_bits (U : Z) (n : Z) : Z :=
  if (n <=? 0) then 0
  else if (U <=? 0) then 0
  else Z.log2 (U / n).

Definition lower_bits (l : Z) (x : Z) : Z :=
  Z.land x (Z.ones l).

Definition upper_value (l : Z) (x : Z) : Z :=
  Z.shiftr x l.

Fixpoint build_upper_aux (uppers : list Z) (prev : Z) : list bool :=
  match uppers with
  | [] => []
  | u :: rest =>
      repeat false (Z.to_nat (u - prev)) ++ [true] ++ build_upper_aux rest u
  end.

Definition build_upper (uppers : list Z) : list bool :=
  build_upper_aux uppers 0.

Record ef_encoded := mk_ef {
  ef_lower : list Z;
  ef_upper : list bool;
  ef_l : Z;
  ef_n : nat;
}.

Definition encoded := ef_encoded.

Definition encode (U : Z) (xs : list Z) : encoded :=
  let n := Z.of_nat (length xs) in
  let l := num_lower_bits U n in
  mk_ef
    (map (lower_bits l) xs)
    (build_upper (map (upper_value l) xs))
    l
    (length xs).

Definition access_ef (enc : encoded) (i : nat) : Z :=
  let pos := position_of_ith_one (ef_upper enc) i in
  let u := Z.of_nat pos - Z.of_nat i in
  let l_val := nth i (ef_lower enc) 0 in
  u * 2 ^ (ef_l enc) + l_val.

Definition access := access_ef.

Fixpoint decode_aux (enc : encoded) (i : nat) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => access_ef enc i :: decode_aux enc (S i) n'
  end.

Definition decode (enc : encoded) : list Z :=
  decode_aux enc 0 (ef_n enc).

Definition bit_size (enc : encoded) : Z :=
  Z.of_nat (ef_n enc) * (ef_l enc + 2).

Fixpoint nextGEQ_aux (enc : encoded) (v : Z) (i : nat) (n : nat) : option Z :=
  match n with
  | O => None
  | S n' =>
      let x := access_ef enc i in
      if x >=? v then Some x
      else nextGEQ_aux enc v (S i) n'
  end.

Definition nextGEQ (enc : encoded) (v : Z) : option Z :=
  nextGEQ_aux enc v 0 (ef_n enc).

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

(* ================================================================= *)
(* Part 3: Encoding correctness helpers                               *)
(* ================================================================= *)

Lemma num_lower_bits_nonneg : forall U n, 0 <= num_lower_bits U n.
Proof.
  intros. unfold num_lower_bits.
  destruct (n <=? 0); [lia|]. destruct (U <=? 0); [lia|]. apply Z.log2_nonneg.
Qed.

Lemma recombine :
  forall l x, 0 <= l -> 0 <= x ->
    upper_value l x * 2 ^ l + lower_bits l x = x.
Proof.
  intros l x Hl Hx.
  unfold upper_value, lower_bits.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.land_ones by lia.
  rewrite Z.mul_comm.
  symmetry. apply Z.div_mod.
  assert (0 < 2 ^ l) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma upper_value_nonneg :
  forall l x, 0 <= l -> 0 <= x -> 0 <= upper_value l x.
Proof.
  intros l x Hl Hx. unfold upper_value.
  rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
Qed.

Lemma upper_value_mono :
  forall l x y, 0 <= l -> x <= y -> upper_value l x <= upper_value l y.
Proof.
  intros l x y Hl Hxy. unfold upper_value.
  rewrite !Z.shiftr_div_pow2 by lia.
  apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia | lia].
Qed.

Lemma Forall_map_upper_nonneg :
  forall l xs, 0 <= l -> all_nonneg xs ->
    Forall (fun u => u >= 0) (map (upper_value l) xs).
Proof.
  intros l xs Hl Hnn.
  apply Forall_forall. intros u Hu.
  apply in_map_iff in Hu. destruct Hu as [x [<- Hx]].
  assert (0 <= x).
  { unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn. auto. }
  pose proof (upper_value_nonneg l x Hl H). lia.
Qed.

Lemma Forall_nth :
  forall {A} (P : A -> Prop) (l : list A) (d : A) (i : nat),
    Forall P l -> (i < length l)%nat -> P (nth i l d).
Proof.
  intros A P l d i HF Hi.
  rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hi.
Qed.

Lemma StronglySorted_nth :
  forall {A} (R : A -> A -> Prop) (xs : list A) (d : A) (i j : nat),
    StronglySorted R xs ->
    (i < j)%nat -> (j < length xs)%nat ->
    R (nth i xs d) (nth j xs d).
Proof.
  intros A R xs d i j Hs Hij Hj. revert i j Hij Hj.
  induction Hs as [|a l Hss IH HF]; intros i j Hij Hj.
  - simpl in Hj. lia.
  - destruct i as [|i'], j as [|j']; simpl in *; try lia.
    + apply Forall_nth with (d := d) (i := j') in HF; [exact HF | lia].
    + apply IH; lia.
Qed.

Lemma StronglySorted_map_upper_nth :
  forall l xs, 0 <= l -> sorted xs ->
    forall j k, (j < k)%nat -> (k < length (map (upper_value l) xs))%nat ->
      nth j (map (upper_value l) xs) 0 <= nth k (map (upper_value l) xs) 0.
Proof.
  intros l xs Hl Hs j k Hjk Hk.
  rewrite length_map in Hk.
  rewrite (nth_indep _ _ (upper_value l 0)) by (rewrite length_map; lia).
  rewrite (nth_indep (map _ xs) 0 (upper_value l 0)) by (rewrite length_map; lia).
  rewrite !map_nth.
  apply upper_value_mono; [lia|].
  apply (StronglySorted_nth Z.le xs 0 j k Hs); lia.
Qed.

Lemma Z_to_nat_add :
  forall a b c, b <= a -> a <= c ->
    (Z.to_nat (a - b) + Z.to_nat (c - a))%nat = Z.to_nat (c - b).
Proof.
  intros a b c Hab Hac.
  rewrite <- Z2Nat.inj_add by lia.
  f_equal. lia.
Qed.

(* --- Select on build_upper --- *)

Lemma select_go_repeat_false_app :
  forall k rest i offset count,
    (count <= i)%nat ->
    select_go (repeat false k ++ rest) i offset count =
    select_go rest i (offset + k) count.
Proof.
  induction k as [|k' IH]; intros; simpl.
  - f_equal. lia.
  - rewrite IH by lia. f_equal. lia.
Qed.

Lemma select_build_upper_aux :
  forall uppers prev i offset count,
    Forall (fun u => u >= prev) uppers ->
    (forall j k : nat, (j < k)%nat -> (k < length uppers)%nat ->
       nth j uppers 0%Z <= nth k uppers 0%Z) ->
    (i - count < length uppers)%nat ->
    (i >= count)%nat ->
    select_go (build_upper_aux uppers prev) i offset count =
    (offset + Z.to_nat (nth (i - count) uppers 0%Z - prev) + (i - count))%nat.
Proof.
  induction uppers as [|u rest IH]; intros prev i offset count Hall Hsorted Hlen Hge.
  - simpl in Hlen. lia.
  - inversion Hall; subst.
    simpl build_upper_aux.
    rewrite select_go_repeat_false_app by lia.
    simpl app. simpl select_go.
    destruct (Nat.eqb count i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      replace (i - i)%nat with 0%nat by lia. simpl. lia.
    + apply Nat.eqb_neq in Heq.
      simpl in Hlen.
      replace (i - count)%nat with (S (i - S count))%nat by lia.
      simpl nth.
      assert (Hall': Forall (fun v => v >= u) rest).
      { apply Forall_forall. intros v Hv.
        apply In_nth with (d := 0%Z) in Hv. destruct Hv as [j [Hj Hnth]]. subst.
        assert (u <= nth j rest 0%Z).
        { change u with (nth 0%nat (u :: rest) 0%Z).
          apply (Hsorted 0%nat (S j)); simpl; lia. }
        lia. }
      assert (Hsorted': forall j k, (j < k)%nat -> (k < length rest)%nat ->
        nth j rest 0 <= nth k rest 0).
      { intros j k Hjk Hk. apply (Hsorted (S j) (S k)); simpl; lia. }
      rewrite IH; try assumption; try lia.
      (* Need: offset + Z.to_nat(u-prev) + 1 + Z.to_nat(nth...-u) + (i-Scount)
         = offset + Z.to_nat(nth...-prev) + S(i-Scount) *)
      assert (Hu : prev <= u) by lia.
      assert (Hnu : u <= nth (i - S count) rest 0%Z).
      { change u with (nth 0%nat (u :: rest) 0%Z).
        apply (Hsorted 0%nat (S (i - S count))); simpl; lia. }
      rewrite <- (Z_to_nat_add u prev (nth (i - S count) rest 0%Z) Hu Hnu).
      lia.
Qed.

Lemma position_of_ith_one_build_upper :
  forall uppers i,
    Forall (fun u => u >= 0) uppers ->
    (forall j k : nat, (j < k)%nat -> (k < length uppers)%nat ->
       nth j uppers 0%Z <= nth k uppers 0%Z) ->
    (i < length uppers)%nat ->
    position_of_ith_one (build_upper uppers) i =
    (Z.to_nat (nth i uppers 0%Z) + i)%nat.
Proof.
  intros uppers i Hall Hsorted Hlen.
  unfold position_of_ith_one, build_upper.
  rewrite select_build_upper_aux; try assumption; try lia.
  replace (i - 0)%nat with i by lia. lia.
Qed.

(* --- nth of map helper --- *)
Lemma nth_map_safe :
  forall {A B : Type} (f : A -> B) (xs : list A) (i : nat) (da : A) (db : B),
    (i < length xs)%nat ->
    nth i (map f xs) db = f (nth i xs da).
Proof.
  intros A B f xs i da db Hi.
  revert i Hi. induction xs as [|x xs' IH]; intros.
  - simpl in Hi. lia.
  - destruct i; simpl; [reflexivity | apply IH; simpl in Hi; lia].
Qed.

(* ================================================================= *)
(* Part 4: access_ef correctness                                      *)
(* ================================================================= *)

Theorem access_ef_correct :
  forall U xs i,
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    (i < length xs)%nat ->
    access_ef (encode U xs) i = nth i xs 0.
Proof.
  intros U xs i Hs Hnn Hb Hi.
  unfold access_ef, encode. simpl.
  set (l := num_lower_bits U (Z.of_nat (length xs))).
  assert (Hl : 0 <= l) by apply num_lower_bits_nonneg.
  assert (Hxi_nn : 0 <= nth i xs 0).
  { unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
    apply Hnn. apply nth_In. exact Hi. }
  rewrite position_of_ith_one_build_upper
    by (try apply Forall_map_upper_nonneg; try apply StronglySorted_map_upper_nth;
        try rewrite length_map; assumption).
  (* Goal: (Z.of_nat (Z.to_nat (nth i (map (upper_value l) xs) 0) + i) - Z.of_nat i)
           * 2^l + nth i (map (lower_bits l) xs) 0 = nth i xs 0 *)
  rewrite (nth_map_safe (upper_value l) xs i 0%Z 0%Z) by exact Hi.
  rewrite (nth_map_safe (lower_bits l) xs i 0%Z 0%Z) by exact Hi.
  assert (Huv_nn : 0 <= upper_value l (nth i xs 0))
    by (apply upper_value_nonneg; lia).
  replace (Z.of_nat (Z.to_nat (upper_value l (nth i xs 0)) + i) - Z.of_nat i)
    with (upper_value l (nth i xs 0)).
  2: { rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
  apply recombine; lia.
Qed.

(* ================================================================= *)
(* Part 5: round_trip                                                 *)
(* ================================================================= *)

Lemma decode_aux_nth :
  forall enc start n i,
    (i < n)%nat ->
    nth i (decode_aux enc start n) 0%Z = access_ef enc (start + i).
Proof.
  intros enc start n. revert start.
  induction n as [|n' IH]; intros start i Hi.
  - lia.
  - simpl. destruct i as [|i'].
    + simpl. f_equal. lia.
    + simpl. rewrite IH by lia. f_equal. lia.
Qed.

Lemma decode_aux_length :
  forall enc start n, length (decode_aux enc start n) = n.
Proof.
  intros. revert start. induction n; intros; simpl; [reflexivity | rewrite IHn; lia].
Qed.

Theorem round_trip :
  forall (U : Z) (xs : list Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    decode (encode U xs) = xs.
Proof.
  intros U xs Hs Hnn Hb.
  unfold decode. simpl.
  apply nth_ext with (d := 0%Z) (d' := 0%Z).
  - rewrite decode_aux_length. reflexivity.
  - intros i Hi.
    rewrite decode_aux_length in Hi.
    rewrite decode_aux_nth by lia.
    replace (0 + i)%nat with i by lia.
    apply access_ef_correct; assumption.
Qed.

Theorem access_correct :
  forall (U : Z) (xs : list Z) (i : nat),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    (i < length xs)%nat ->
    access (encode U xs) i = nth i xs 0.
Proof.
  intros. apply access_ef_correct; assumption.
Qed.

(* ================================================================= *)
(* Part 6: nextGEQ proofs                                             *)
(* ================================================================= *)

Lemma nextGEQ_aux_spec :
  forall enc v i n,
    match nextGEQ_aux enc v i n with
    | Some r =>
        exists j, (i <= j < i + n)%nat /\ access_ef enc j = r /\ r >= v /\
        (forall k, (i <= k < j)%nat -> access_ef enc k < v)
    | None =>
        forall j, (i <= j < i + n)%nat -> access_ef enc j < v
    end.
Proof.
  intros enc v i n. revert i. induction n as [|n' IH]; intros i.
  - simpl. intros j Hj. lia.
  - simpl. destruct (access_ef enc i >=? v) eqn:Hge.
    + apply Z.geb_le in Hge.
      exists i. split; [lia|]. split; [reflexivity|]. split; [lia|].
      intros k Hk. lia.
    + assert (Hge' : access_ef enc i < v)
        by (destruct (Z.geb_spec (access_ef enc i) v); [discriminate|lia]).
      clear Hge.
      specialize (IH (S i)).
      destruct (nextGEQ_aux enc v (S i) n').
      * destruct IH as [j [Hj [Haj [Hrv Hbefore]]]].
        exists j. split; [lia|]. split; [assumption|]. split; [assumption|].
        intros k Hk. destruct (Nat.eq_dec k i) as [->|]; [lia|apply Hbefore; lia].
      * intros j Hj.
        destruct (Nat.eq_dec j i) as [->|]; [lia|apply IH; lia].
Qed.

Theorem nextGEQ_found_thm :
  forall (U : Z) (xs : list Z) (v r : Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    nextGEQ (encode U xs) v = Some r ->
    In r xs /\ r >= v.
Proof.
  intros U xs v r Hs Hnn Hb Hfind.
  unfold nextGEQ in Hfind. simpl in Hfind.
  pose proof (nextGEQ_aux_spec (encode U xs) v 0 (length xs)) as Hspec.
  rewrite Hfind in Hspec.
  destruct Hspec as [j [Hj [Haj [Hrv _]]]].
  split.
  - rewrite <- Haj, access_ef_correct by (assumption || lia). apply nth_In. lia.
  - exact Hrv.
Qed.

Theorem nextGEQ_smallest_thm :
  forall (U : Z) (xs : list Z) (v r : Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    nextGEQ (encode U xs) v = Some r ->
    forall y, In y xs -> y >= v -> r <= y.
Proof.
  intros U xs v r Hs Hnn Hb Hfind y Hy Hyv.
  unfold nextGEQ in Hfind. simpl in Hfind.
  pose proof (nextGEQ_aux_spec (encode U xs) v 0 (length xs)) as Hspec.
  rewrite Hfind in Hspec.
  destruct Hspec as [j [Hj [Haj [Hrv Hbefore]]]].
  apply In_nth with (d := 0%Z) in Hy. destruct Hy as [k [Hk Hnth]]. subst y.
  rewrite <- Haj, access_ef_correct by (assumption || lia).
  destruct (Nat.le_gt_cases j k) as [Hjk|Hjk].
  - destruct (Nat.eq_dec j k) as [->|Hne]; [lia|].
    apply (StronglySorted_nth Z.le xs 0%Z j k Hs); lia.
  - exfalso.
    assert (H: access_ef (encode U xs) k < v) by (apply Hbefore; lia).
    rewrite access_ef_correct in H by (assumption || lia). lia.
Qed.

Theorem nextGEQ_none_thm :
  forall (U : Z) (xs : list Z) (v : Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    nextGEQ (encode U xs) v = None ->
    forall y, In y xs -> y < v.
Proof.
  intros U xs v Hs Hnn Hb Hnone y Hy.
  unfold nextGEQ in Hnone. simpl in Hnone.
  pose proof (nextGEQ_aux_spec (encode U xs) v 0 (length xs)) as Hspec.
  rewrite Hnone in Hspec.
  apply In_nth with (d := 0%Z) in Hy. destruct Hy as [k [Hk Hnth]]. subst y.
  assert (H: access_ef (encode U xs) k < v) by (apply Hspec; lia).
  rewrite access_ef_correct in H by (assumption || lia). lia.
Qed.

(* ================================================================= *)
(* Part 7: Space bound                                                *)
(* ================================================================= *)

Theorem space_bound :
  forall (U : Z) (xs : list Z),
    sorted xs -> all_nonneg xs -> bounded_by U xs ->
    xs <> [] -> 0 < U ->
    let n := Z.of_nat (length xs) in
    bit_size (encode U xs) <= n * (2 + Z.log2 (U / n)).
Proof.
  intros U xs Hs Hnn Hb Hne HU n.
  unfold bit_size, encode, num_lower_bits. simpl ef_n. simpl ef_l.
  fold n.
  destruct (n <=? 0) eqn:Hn.
  - apply Z.leb_le in Hn. unfold n in Hn.
    destruct xs; [contradiction|simpl in Hn; lia].
  - apply Z.leb_gt in Hn.
    destruct (U <=? 0) eqn:HU'.
    + apply Z.leb_le in HU'. lia.
    + apply Z.leb_gt in HU'. lia.
Qed.

(* ================================================================= *)
(* Part 8: Compute checks                                             *)
(* ================================================================= *)

(** Sanity checks on concrete examples. These are not proofs —
    they validate that the definitions compute the expected values. *)

(* --- Encoding structure --- *)

(* encode 100 [3; 7; 42] with U=100, n=3, l=log2(100/3)=log2(33)=5 *)
Eval compute in (ef_l (encode 100 [3; 7; 42])).
(* Expected: 5 (lower bits width) *)

Eval compute in (ef_lower (encode 100 [3; 7; 42])).
(* Expected: [3 mod 32; 7 mod 32; 42 mod 32] = [3; 7; 10] *)

Eval compute in (map (upper_value 5) [3; 7; 42]).
(* Expected: [3/32; 7/32; 42/32] = [0; 0; 1] *)

Eval compute in (ef_upper (encode 100 [3; 7; 42])).
(* Expected: unary encoding of [0; 0; 1] from 0:
   gap 0 → true, gap 0 → true, gap 1 → false true
   = [true; true; false; true] *)

(* --- Access --- *)

Eval compute in (access (encode 100 [3; 7; 42]) 0).
(* Expected: 3 *)

Eval compute in (access (encode 100 [3; 7; 42]) 1).
(* Expected: 7 *)

Eval compute in (access (encode 100 [3; 7; 42]) 2).
(* Expected: 42 *)

(* --- Round-trip --- *)

Eval compute in (decode (encode 100 [3; 7; 42])).
(* Expected: [3; 7; 42] *)

Eval compute in (decode (encode 1000 [0; 1; 2; 3; 4; 5])).
(* Expected: [0; 1; 2; 3; 4; 5] *)

Eval compute in (decode (encode 256 [10; 20; 30; 100; 200; 255])).
(* Expected: [10; 20; 30; 100; 200; 255] *)

(* --- Edge cases --- *)

Eval compute in (decode (encode 1 [])).
(* Expected: [] *)

Eval compute in (decode (encode 10 [0])).
(* Expected: [0] *)

Eval compute in (decode (encode 10 [9])).
(* Expected: [9] *)

Eval compute in (decode (encode 100 [0; 0; 0])).
(* Expected: [0; 0; 0] *)

(* --- nextGEQ --- *)

Eval compute in (nextGEQ (encode 100 [3; 7; 42]) 5).
(* Expected: Some 7 *)

Eval compute in (nextGEQ (encode 100 [3; 7; 42]) 42).
(* Expected: Some 42 *)

Eval compute in (nextGEQ (encode 100 [3; 7; 42]) 43).
(* Expected: None *)

Eval compute in (nextGEQ (encode 100 [3; 7; 42]) 0).
(* Expected: Some 3 *)

(* --- Rank / Select --- *)

Eval compute in (position_of_ith_one [true; false; true; false; true] 0).
(* Expected: 0 *)

Eval compute in (position_of_ith_one [true; false; true; false; true] 1).
(* Expected: 2 *)

Eval compute in (position_of_ith_one [true; false; true; false; true] 2).
(* Expected: 4 *)

Eval compute in (count_ones_up_to [true; false; true; false; true] 3).
(* Expected: 2 *)

(* --- Space bound --- *)

Eval compute in (bit_size (encode 100 [3; 7; 42])).
(* Expected: 3 * (5 + 2) = 21 *)
