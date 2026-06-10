(** * Elias-Fano Encoding — Implementation and Proofs *)

From Stdlib Require Import ZArith List Bool Sorting Lia Uint63.
From Stdlib Require Import Permutation.
From Stdlib Require Import QArith Qpower Qround.
Import ListNotations.

Open Scope Z_scope.

(* ================================================================= *)
(* Definitions from spec (provided concretely)                        *)
(* ================================================================= *)

Definition sorted (vals : list Z) : Prop := StronglySorted Z.le vals.

Definition all_nonneg (vals : list Z) : Prop :=
  Forall (fun x => 0 <= x) vals.

Definition bounded_by (U : Z) (vals : list Z) : Prop :=
  Forall (fun x => x < U) vals.

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

Definition encode (U : Z) (vals : list Z) : encoded :=
  let n := Z.of_nat (length vals) in
  let l := num_lower_bits U n in
  mk_ef
    (map (lower_bits l) vals)
    (build_upper (map (upper_value l) vals))
    l
    (length vals).

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

(** Serialization: the encoding laid out as a bit list — lower-bits
    array as fixed-width little-endian chunks, then the upper bitvector.
    [of_bits U n bits] rebuilds the encoding; [U] and [n] are caller
    context, from which the chunk width [l] is recomputed. *)

Fixpoint Z_to_bits (x : Z) (w : nat) : list bool :=
  match w with
  | O => []
  | S w' => Z.odd x :: Z_to_bits (Z.div2 x) w'
  end.

Fixpoint Z_of_bits (bs : list bool) : Z :=
  match bs with
  | [] => 0
  | b :: bs' => (if b then 1 else 0) + 2 * Z_of_bits bs'
  end.

Definition to_bits (enc : encoded) : list bool :=
  concat (map (fun x => Z_to_bits x (Z.to_nat (ef_l enc))) (ef_lower enc))
  ++ ef_upper enc.

Fixpoint chunks (w : nat) (n : nat) (bs : list bool) : list (list bool) :=
  match n with
  | O => []
  | S n' => firstn w bs :: chunks w n' (skipn w bs)
  end.

Definition of_bits (U : Z) (n : nat) (bs : list bool) : encoded :=
  let l := num_lower_bits U (Z.of_nat n) in
  let lw := (n * Z.to_nat l)%nat in
  mk_ef (map Z_of_bits (chunks (Z.to_nat l) n (firstn lw bs)))
        (skipn lw bs) l n.

(** Exact encoding size in bits (kept for extraction). *)
Definition bit_size (enc : encoded) : Z :=
  Z.of_nat (length (to_bits enc)).

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
  forall l vals, 0 <= l -> all_nonneg vals ->
    Forall (fun u => u >= 0) (map (upper_value l) vals).
Proof.
  intros l vals Hl Hnn.
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
  forall {A} (R : A -> A -> Prop) (vals : list A) (d : A) (i j : nat),
    StronglySorted R vals ->
    (i < j)%nat -> (j < length vals)%nat ->
    R (nth i vals d) (nth j vals d).
Proof.
  intros A R vals d i j Hs Hij Hj. revert i j Hij Hj.
  induction Hs as [|a l Hss IH HF]; intros i j Hij Hj.
  - simpl in Hj. lia.
  - destruct i as [|i'], j as [|j']; simpl in *; try lia.
    + apply Forall_nth with (d := d) (i := j') in HF; [exact HF | lia].
    + apply IH; lia.
Qed.

Lemma StronglySorted_map_upper_nth :
  forall l vals, 0 <= l -> sorted vals ->
    forall j k, (j < k)%nat -> (k < length (map (upper_value l) vals))%nat ->
      nth j (map (upper_value l) vals) 0 <= nth k (map (upper_value l) vals) 0.
Proof.
  intros l vals Hl Hs j k Hjk Hk.
  rewrite length_map in Hk.
  rewrite (nth_indep _ _ (upper_value l 0)) by (rewrite length_map; lia).
  rewrite (nth_indep (map _ vals) 0 (upper_value l 0)) by (rewrite length_map; lia).
  rewrite !map_nth.
  apply upper_value_mono; [lia|].
  apply (StronglySorted_nth Z.le vals 0 j k Hs); lia.
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

Lemma count_occ_build_upper_aux :
  forall uppers prev,
    count_occ Bool.bool_dec (build_upper_aux uppers prev) true = length uppers.
Proof.
  induction uppers as [|u rest IH]; intros prev.
  - reflexivity.
  - cbn [build_upper_aux].
    rewrite count_occ_app. simpl count_occ at 1.
    rewrite count_occ_repeat_neq by discriminate.
    destruct (Bool.bool_dec true true) as [_|Habs]; [|contradiction].
    simpl. rewrite IH. lia.
Qed.

Lemma count_occ_build_upper :
  forall uppers,
    count_occ Bool.bool_dec (build_upper uppers) true = length uppers.
Proof.
  intros. unfold build_upper. apply count_occ_build_upper_aux.
Qed.

Lemma length_build_upper_aux :
  forall uppers prev,
    Forall (fun u => prev <= u) uppers ->
    sorted uppers ->
    Z.of_nat (length (build_upper_aux uppers prev)) =
      match uppers with
      | [] => 0
      | _ => last uppers 0 - prev + Z.of_nat (length uppers)
      end.
Proof.
  induction uppers as [|u rest IH]; intros prev Hge Hsort.
  - reflexivity.
  - simpl build_upper_aux. rewrite length_app, repeat_length.
    inversion Hge as [|? ? Hu_ge Hge_rest]; subst.
    inversion Hsort as [|? ? Hsort_rest HF_le]; subst.
    destruct rest as [|v rest'].
    + simpl. simpl last.
      rewrite Nat2Z.inj_add. rewrite Z2Nat.id by lia. simpl. lia.
    + assert (Hv_ge : Forall (fun w => u <= w) (v :: rest')).
      { revert HF_le. apply Forall_impl. lia. }
      (* length = Z.to_nat(u - prev) + length([true] ++ build_upper_aux (v :: rest') u) *)
      (* = Z.to_nat(u - prev) + 1 + length(build_upper_aux (v :: rest') u) *)
      assert (Hlen_rest : Z.of_nat (length (build_upper_aux (v :: rest') u))
        = last (v :: rest') 0%Z - u + Z.of_nat (length (v :: rest'))).
      { exact (IH u Hv_ge Hsort_rest). }
      assert (Hlast_ge_u : u <= last (v :: rest') 0%Z).
      { rewrite Forall_forall in Hv_ge. apply Hv_ge.
        assert (Hne' : v :: rest' <> []) by discriminate.
        rewrite (app_removelast_last 0%Z Hne') at 2.
        apply in_or_app. right. left. reflexivity. }
      (* Goal: Z.of_nat(Z.to_nat(u-prev) + length([true]++bua(v::rest', u)))
              = last(v::rest') 0 - prev + Z.of_nat(length(u::v::rest')) *)
      rewrite Nat2Z.inj_add. rewrite Z2Nat.id by lia.
      change (length (true :: build_upper_aux (v :: rest') u))
        with (S (length (build_upper_aux (v :: rest') u))).
      rewrite Nat2Z.inj_succ. rewrite Hlen_rest.
      change (last (u :: v :: rest') 0%Z) with (last (v :: rest') 0%Z).
      change (length (u :: v :: rest')) with (S (length (v :: rest'))).
      rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma length_build_upper :
  forall uppers,
    uppers <> [] ->
    Forall (fun u => 0 <= u) uppers ->
    sorted uppers ->
    Z.of_nat (length (build_upper uppers)) =
      last uppers 0 + Z.of_nat (length uppers).
Proof.
  intros uppers Hne Hnn Hsort.
  unfold build_upper. rewrite (length_build_upper_aux uppers 0 Hnn Hsort).
  destruct uppers; [contradiction|]. simpl. lia.
Qed.

(* --- nth of map helper --- *)
Lemma nth_map_safe :
  forall {A B : Type} (f : A -> B) (vals : list A) (i : nat) (da : A) (db : B),
    (i < length vals)%nat ->
    nth i (map f vals) db = f (nth i vals da).
Proof.
  intros A B f vals i da db Hi.
  revert i Hi. induction vals as [|x vals' IH]; intros.
  - simpl in Hi. lia.
  - destruct i; simpl; [reflexivity | apply IH; simpl in Hi; lia].
Qed.

(* ================================================================= *)
(* Part 4: access_ef correctness                                      *)
(* ================================================================= *)

Theorem access_ef_correct :
  forall U vals i,
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    (i < length vals)%nat ->
    access_ef (encode U vals) i = nth i vals 0.
Proof.
  intros U vals i Hs Hnn Hb Hi.
  unfold access_ef, encode. simpl.
  set (l := num_lower_bits U (Z.of_nat (length vals))).
  assert (Hl : 0 <= l) by apply num_lower_bits_nonneg.
  assert (Hxi_nn : 0 <= nth i vals 0).
  { unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
    apply Hnn. apply nth_In. exact Hi. }
  rewrite position_of_ith_one_build_upper
    by (try apply Forall_map_upper_nonneg; try apply StronglySorted_map_upper_nth;
        try rewrite length_map; assumption).
  (* Goal: (Z.of_nat (Z.to_nat (nth i (map (upper_value l) vals) 0) + i) - Z.of_nat i)
           * 2^l + nth i (map (lower_bits l) vals) 0 = nth i vals 0 *)
  rewrite (nth_map_safe (upper_value l) vals i 0%Z 0%Z) by exact Hi.
  rewrite (nth_map_safe (lower_bits l) vals i 0%Z 0%Z) by exact Hi.
  assert (Huv_nn : 0 <= upper_value l (nth i vals 0))
    by (apply upper_value_nonneg; lia).
  replace (Z.of_nat (Z.to_nat (upper_value l (nth i vals 0)) + i) - Z.of_nat i)
    with (upper_value l (nth i vals 0)).
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
  forall (U : Z) (vals : list Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    decode (encode U vals) = vals.
Proof.
  intros U vals Hs Hnn Hb.
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
  forall (U : Z) (vals : list Z) (i : nat),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    (i < length vals)%nat ->
    access (encode U vals) i = nth i vals 0.
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
  forall (U : Z) (vals : list Z) (v r : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    nextGEQ (encode U vals) v = Some r ->
    In r vals /\ r >= v.
Proof.
  intros U vals v r Hs Hnn Hb Hfind.
  unfold nextGEQ in Hfind. simpl in Hfind.
  pose proof (nextGEQ_aux_spec (encode U vals) v 0 (length vals)) as Hspec.
  rewrite Hfind in Hspec.
  destruct Hspec as [j [Hj [Haj [Hrv _]]]].
  split.
  - rewrite <- Haj, access_ef_correct by (assumption || lia). apply nth_In. lia.
  - exact Hrv.
Qed.

Theorem nextGEQ_smallest_thm :
  forall (U : Z) (vals : list Z) (v r : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    nextGEQ (encode U vals) v = Some r ->
    forall y, In y vals -> y >= v -> r <= y.
Proof.
  intros U vals v r Hs Hnn Hb Hfind y Hy Hyv.
  unfold nextGEQ in Hfind. simpl in Hfind.
  pose proof (nextGEQ_aux_spec (encode U vals) v 0 (length vals)) as Hspec.
  rewrite Hfind in Hspec.
  destruct Hspec as [j [Hj [Haj [Hrv Hbefore]]]].
  apply In_nth with (d := 0%Z) in Hy. destruct Hy as [k [Hk Hnth]]. subst y.
  rewrite <- Haj, access_ef_correct by (assumption || lia).
  destruct (Nat.le_gt_cases j k) as [Hjk|Hjk].
  - destruct (Nat.eq_dec j k) as [->|Hne]; [lia|].
    apply (StronglySorted_nth Z.le vals 0%Z j k Hs); lia.
  - exfalso.
    assert (H: access_ef (encode U vals) k < v) by (apply Hbefore; lia).
    rewrite access_ef_correct in H by (assumption || lia). lia.
Qed.

Theorem nextGEQ_none_thm :
  forall (U : Z) (vals : list Z) (v : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    nextGEQ (encode U vals) v = None ->
    forall y, In y vals -> y < v.
Proof.
  intros U vals v Hs Hnn Hb Hnone y Hy.
  unfold nextGEQ in Hnone. simpl in Hnone.
  pose proof (nextGEQ_aux_spec (encode U vals) v 0 (length vals)) as Hspec.
  rewrite Hnone in Hspec.
  apply In_nth with (d := 0%Z) in Hy. destruct Hy as [k [Hk Hnth]]. subst y.
  assert (H: access_ef (encode U vals) k < v) by (apply Hspec; lia).
  rewrite access_ef_correct in H by (assumption || lia). lia.
Qed.

(* ================================================================= *)
(* Part 7: Space bound                                                *)
(* ================================================================= *)

(* --- Serialization round-trip --- *)

Lemma Z_to_bits_length : forall w x, length (Z_to_bits x w) = w.
Proof.
  induction w as [|w IH]; intros; simpl; [reflexivity | now rewrite IH].
Qed.

Lemma Z_of_Z_to_bits :
  forall w x, 0 <= x < 2 ^ Z.of_nat w -> Z_of_bits (Z_to_bits x w) = x.
Proof.
  induction w as [|w IH]; intros x Hx; simpl.
  - simpl in Hx. lia.
  - rewrite IH.
    + pose proof (Z.div2_odd x) as Hdo.
      destruct (Z.odd x) eqn:Ho; rewrite ?Ho in Hdo; simpl in Hdo; lia.
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
      rewrite Z.div2_div.
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma lower_bits_range :
  forall l x, 0 <= l -> 0 <= lower_bits l x < 2 ^ l.
Proof.
  intros l x Hl. unfold lower_bits.
  rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma length_concat_same :
  forall (xss : list (list bool)) (w : nat),
    Forall (fun xs => length xs = w) xss ->
    length (concat xss) = (length xss * w)%nat.
Proof.
  induction xss as [|xs xss IH]; intros w HF; simpl; [reflexivity|].
  inversion HF as [|? ? Hx HF']; subst.
  rewrite length_app, (IH _ HF'). lia.
Qed.

Lemma chunks_concat :
  forall (xss : list (list bool)) (w : nat) (rest : list bool),
    Forall (fun xs => length xs = w) xss ->
    chunks w (length xss) (concat xss ++ rest) = xss.
Proof.
  induction xss as [|xs xss IH]; intros w rest HF; simpl; [reflexivity|].
  inversion HF as [|? ? Hlen HF']; subst.
  rewrite <- app_assoc.
  rewrite firstn_app, firstn_all2 by lia.
  rewrite Nat.sub_diag. simpl. rewrite app_nil_r.
  rewrite skipn_app, skipn_all2 by lia.
  rewrite Nat.sub_diag. simpl.
  now rewrite IH by assumption.
Qed.

Lemma of_bits_to_bits :
  forall (U : Z) (vals : list Z),
    all_nonneg vals ->
    of_bits U (length vals) (to_bits (encode U vals)) = encode U vals.
Proof.
  intros U vals Hnn.
  unfold of_bits, to_bits, encode. simpl.
  set (l := num_lower_bits U (Z.of_nat (length vals))).
  assert (Hl : 0 <= l) by apply num_lower_bits_nonneg.
  set (low := map (lower_bits l) vals).
  set (xss := map (fun x => Z_to_bits x (Z.to_nat l)) low).
  assert (Hwidth : Forall (fun xs => length xs = Z.to_nat l) xss).
  { apply Forall_forall. intros xs Hxs.
    apply in_map_iff in Hxs. destruct Hxs as [x [<- _]].
    apply Z_to_bits_length. }
  assert (Hlenc : length (concat xss) = (length vals * Z.to_nat l)%nat).
  { rewrite (length_concat_same xss (Z.to_nat l) Hwidth).
    unfold xss, low. now rewrite !length_map. }
  rewrite firstn_app, skipn_app, Hlenc, Nat.sub_diag.
  rewrite firstn_all2 by lia.
  rewrite skipn_all2 by lia.
  simpl. rewrite app_nil_r.
  f_equal.
  replace (length vals) with (length xss)
    by (unfold xss, low; now rewrite !length_map).
  rewrite <- (app_nil_r (concat xss)).
  rewrite (chunks_concat xss (Z.to_nat l) [] Hwidth).
  unfold xss, low. rewrite map_map.
  etransitivity; [|apply map_id].
  apply map_ext_in.
  intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [x0 [<- _]].
  apply Z_of_Z_to_bits.
  rewrite Z2Nat.id by exact Hl.
  apply lower_bits_range. exact Hl.
Qed.

(* --- Length of the serialization --- *)

Lemma sorted_map_upper :
  forall l vals, 0 <= l -> sorted vals -> sorted (map (upper_value l) vals).
Proof.
  intros l vals Hl Hs. induction Hs as [|x xs Hs IH HF]; simpl; constructor.
  - exact IH.
  - apply Forall_map. revert HF. apply Forall_impl.
    intros y Hy. apply upper_value_mono; assumption.
Qed.

Lemma last_map_upper :
  forall l vals, vals <> [] ->
    last (map (upper_value l) vals) 0 = upper_value l (last vals 0).
Proof.
  intros l vals Hne.
  induction vals as [|x [|y vals'] IH]; [contradiction| reflexivity |].
  simpl in *. apply IH. discriminate.
Qed.

Lemma to_bits_length :
  forall (U : Z) (vals : list Z),
    sorted vals -> all_nonneg vals -> vals <> [] ->
    let n := Z.of_nat (length vals) in
    let l := num_lower_bits U n in
    Z.of_nat (length (to_bits (encode U vals)))
      = n * l + (upper_value l (last vals 0) + n).
Proof.
  intros U vals Hs Hnn Hne n l.
  unfold to_bits, encode. simpl.
  fold n. fold l.
  rewrite length_app.
  assert (Hl : 0 <= l) by apply num_lower_bits_nonneg.
  set (xss := map (fun x => Z_to_bits x (Z.to_nat l)) (map (lower_bits l) vals)).
  assert (Hwidth : Forall (fun xs => length xs = Z.to_nat l) xss).
  { apply Forall_forall. intros xs Hxs.
    apply in_map_iff in Hxs. destruct Hxs as [x [<- _]].
    apply Z_to_bits_length. }
  rewrite (length_concat_same xss (Z.to_nat l) Hwidth).
  replace (length xss) with (length vals)
    by (unfold xss; now rewrite !length_map).
  assert (Hup : Z.of_nat (length (build_upper (map (upper_value l) vals)))
                = upper_value l (last vals 0) + n).
  { rewrite length_build_upper.
    - rewrite last_map_upper by exact Hne.
      unfold n. now rewrite length_map.
    - destruct vals; [contradiction | discriminate].
    - pose proof (Forall_map_upper_nonneg l vals Hl Hnn) as H.
      revert H. apply Forall_impl. lia.
    - apply sorted_map_upper; assumption. }
  rewrite Nat2Z.inj_add, Hup.
  rewrite Nat2Z.inj_mul, Z2Nat.id by exact Hl.
  unfold n. lia.
Qed.

(* --- The bound, parameterized by any k with U <= n * 2^k --- *)

Lemma last_In_list :
  forall (xs : list Z) (d : Z), xs <> [] -> In (last xs d) xs.
Proof.
  induction xs as [|x [|y xs'] IH]; intros d Hne;
    [contradiction | left; reflexivity |].
  right. apply IH. discriminate.
Qed.

(** Core arithmetic: with l = ⌊log₂(U/n)⌋ (floor!), the size fits in
    n * (2 + k) bits for ANY k >= 0 with U/n <= 2^k. The two cases:
    - k = log2(U/n): forces U = n * 2^k exactly, last upper <= n - 1;
    - k > log2(U/n): U/n < 2^(l+1) gives last upper <= 2n - 1. *)
Lemma space_bound_k :
  forall (U : Z) (vals : list Z) (k : Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    vals <> [] -> 0 < U ->
    0 <= k -> U <= Z.of_nat (length vals) * 2 ^ k ->
    Z.of_nat (length (to_bits (encode U vals)))
      <= Z.of_nat (length vals) * (2 + k).
Proof.
  intros U vals k Hs Hnn Hb Hne HU Hk HUk.
  rewrite (to_bits_length U vals Hs Hnn Hne).
  set (n := Z.of_nat (length vals)) in *.
  set (l := num_lower_bits U n) in *.
  assert (Hn : 1 <= n).
  { unfold n. destruct vals; [contradiction | simpl; lia]. }
  assert (Hl : 0 <= l) by apply num_lower_bits_nonneg.
  assert (Hpow_l : 0 < 2 ^ l) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow_k : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  (* last vals 0 <= U - 1 *)
  assert (Hin : In (last vals 0) vals) by (apply last_In_list; exact Hne).
  assert (Hlast : last vals 0 <= U - 1).
  { unfold bounded_by in Hb. rewrite Forall_forall in Hb.
    specialize (Hb _ Hin). lia. }
  assert (Hlast_nn : 0 <= last vals 0).
  { unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn. auto. }
  assert (Hup : upper_value l (last vals 0) <= (U - 1) / 2 ^ l).
  { unfold upper_value. rewrite Z.shiftr_div_pow2 by exact Hl.
    apply Z.div_le_mono; lia. }
  (* enough: (U-1)/2^l <= n * (k - l + 1) *)
  enough (Hgoal : (U - 1) / 2 ^ l <= n * (k - l + 1)) by nia.
  unfold l, num_lower_bits in *.
  destruct (n <=? 0) eqn:Hn0; [apply Z.leb_le in Hn0; lia|].
  destruct (U <=? 0) eqn:HU0; [apply Z.leb_le in HU0; lia|].
  apply Z.leb_gt in Hn0, HU0.
  set (m := U / n) in *.
  destruct (Z.eq_dec m 0) as [Hm0 | Hm].
  - (* U < n: l = log2 0 = 0, last value < n *)
    assert (HUn : U < n).
    { unfold m in Hm0. destruct (Z.lt_ge_cases U n); [assumption|].
      assert (1 <= U / n) by (apply Z.div_le_lower_bound; lia). lia. }
    rewrite Hm0. simpl (Z.log2 0).
    rewrite Z.pow_0_r, Z.div_1_r. nia.
  - assert (Hm1 : 1 <= m).
    { unfold m. assert (0 <= U / n) by (apply Z.div_pos; lia). lia. }
    pose proof (Z.log2_spec m ltac:(lia)) as [Hlo Hhi].
    set (lg := Z.log2 m) in *.
    assert (Hlg_nn : 0 <= lg) by (unfold lg; apply Z.log2_nonneg).
    assert (Hpow_lg : 0 < 2 ^ lg) by (apply Z.pow_pos_nonneg; lia).
    assert (Hnm : n * 2 ^ lg <= U).
    { apply Z.le_trans with (n * m); [nia|].
      unfold m. pose proof (Z.mul_div_le U n ltac:(lia)). lia. }
    (* lg <= k, else n*2^lg <= U <= n*2^k < n*2^lg *)
    assert (Hlk : lg <= k).
    { destruct (Z.lt_ge_cases k lg) as [Hkl | ]; [|assumption].
      exfalso.
      assert (2 ^ (k + 1) <= 2 ^ lg) by (apply Z.pow_le_mono_r; lia).
      assert (2 ^ (k + 1) = 2 * 2 ^ k) by (rewrite Z.pow_add_r by lia; lia).
      nia. }
    destruct (Z.eq_dec lg k) as [Heq | Hneq].
    + (* k = lg: forces U = n * 2^lg *)
      assert (HUeq : U = n * 2 ^ lg) by (rewrite Heq in *; lia).
      replace (k - lg + 1) with 1 by lia.
      rewrite Z.mul_1_r.
      apply Z.div_le_upper_bound; [lia | nia].
    + (* lg + 1 <= k: U < n * 2^(lg+1), so (U-1)/2^lg < 2n *)
      assert (Hk1 : lg + 1 <= k) by lia.
      assert (HUub : U <= n * (2 * 2 ^ lg) - 1).
      { rewrite Z.pow_succ_r in Hhi by lia.
        destruct (Z.lt_ge_cases U (n * (2 * 2 ^ lg))) as [|Hge]; [lia|].
        exfalso.
        assert (2 * 2 ^ lg <= m) by (apply Z.div_le_lower_bound; lia).
        lia. }
      assert (Hdiv : (U - 1) / 2 ^ lg < 2 * n).
      { apply Z.div_lt_upper_bound; [lia | nia]. }
      nia.
Qed.

(* --- Instantiation at k = ⌈log₂(U/n)⌉ --- *)

Lemma ceil_log2_nonneg : forall q, 0 <= ceil_log2 q.
Proof. intros q. apply Z.log2_up_nonneg. Qed.

Lemma U_le_pow_ceil_log2 :
  forall (U n : Z), 0 < U -> 0 < n ->
    U <= n * 2 ^ ceil_log2 (inject_Z U / inject_Z n).
Proof.
  intros U n HU Hn.
  set (q := (inject_Z U / inject_Z n)%Q).
  set (k := ceil_log2 q).
  assert (Hk : 0 <= k) by apply ceil_log2_nonneg.
  assert (Hpow : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.le_gt_cases U n) as [HUn | HUn].
  - nia.
  - (* n < U: 1 <= q, Galois applies *)
    assert (Hn_pos : (0 < inject_Z n)%Q).
    { change 0%Q with (inject_Z 0). rewrite <- Zlt_Qlt. lia. }
    assert (Hq1 : (1 <= q)%Q).
    { unfold q. apply Qle_shift_div_l; [exact Hn_pos|].
      rewrite Qmult_1_l. rewrite <- Zle_Qle. lia. }
    pose proof (ceil_log2_galois q k Hq1 Hk) as [Hgal _].
    specialize (Hgal (Z.le_refl k)).
    (* q <= 2^k  ->  U <= n * 2^k *)
    assert (HUq : (inject_Z U == inject_Z n * q)%Q).
    { unfold q. field.
      intro H. unfold Qeq in H. simpl in H. lia. }
    assert (Hmul : (inject_Z U <= inject_Z n * inject_Z 2 ^ k)%Q).
    { rewrite HUq.
      apply (proj2 (Qmult_le_l q (inject_Z 2 ^ k) (inject_Z n) Hn_pos)).
      exact Hgal. }
    rewrite <- Zpower_Qpower in Hmul by exact Hk.
    rewrite <- inject_Z_mult, <- Zle_Qle in Hmul.
    exact Hmul.
Qed.

Theorem space_bound :
  forall (U : Z) (vals : list Z),
    sorted vals -> all_nonneg vals -> bounded_by U vals ->
    vals <> [] -> 0 < U ->
    let n := Z.of_nat (length vals) in
    let bits := to_bits (encode U vals) in
    decode (of_bits U (length vals) bits) = vals /\
    Z.of_nat (length bits) <= n * (2 + ceil_log2 (inject_Z U / inject_Z n)).
Proof.
  intros U vals Hs Hnn Hb Hne HU n bits.
  assert (Hn : 0 < n).
  { unfold n. destruct vals; [contradiction | simpl; lia]. }
  split.
  - unfold bits. rewrite (of_bits_to_bits U vals Hnn).
    apply round_trip; assumption.
  - unfold bits, n.
    apply space_bound_k; try assumption.
    + apply ceil_log2_nonneg.
    + apply U_le_pow_ceil_log2; [exact HU | exact Hn].
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

(* --- Space bound / serialization --- *)

Eval compute in (bit_size (encode 100 [3; 7; 42])).
(* Expected: 3*5 lower bits + 4 upper bits = 19 *)

Eval compute in (decode (of_bits 100 3 (to_bits (encode 100 [3; 7; 42])))).
(* Expected: [3; 7; 42] — round-trip through the serialized bits *)

Eval compute in (3 * (2 + ceil_log2 (inject_Z 100 / inject_Z 3))).
(* Expected: 3 * (2 + 6) = 24 >= 19, the conjectured bound *)
