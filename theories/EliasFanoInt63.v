(** * Elias-Fano Encoding — Int63/PArray Refinement

    Efficient implementation using machine integers and primitive arrays.
    Agreement with the Z/list proofs in [EliasFano.v] is established
    via axioms (to be filled in incrementally).

    [Print Assumptions] on each top-level theorem shows exactly
    which axioms remain. *)

From Stdlib Require Import ZArith List Bool Uint63 PArray Lia.
From coqutil Require Import Z.BitOps.
From EliasFano Require Import EliasFano.

Import ListNotations.
Open Scope Z_scope.
Open Scope uint63_scope.
Open Scope array_scope.

(* ================================================================= *)
(* Part 1: Utilities                                                   *)
(* ================================================================= *)

Definition wB := 2 ^ 63.
Definition wbits : int := 63.

Definition in_range (U : Z) (xs : list Z) : Prop :=
  0 < U /\ U < wB /\
  Z.of_nat (List.length xs) < wB /\
  Z.of_nat (List.length xs) + U < wB /\
  Z.of_nat (List.length xs) <= to_Z max_length /\
  Z.of_nat (List.length xs) + U <= to_Z max_length * to_Z wbits.

Definition to_Z_list (xs : list int) : list Z := map to_Z xs.

(** Integer log2 via [head0] (count leading zeros). *)
Definition ilog2_63 (x : int) : int :=
  if eqb x 0 then 0 else sub 62 (head0 x).

(** Subtraction known to be non-negative. *)
Lemma sub_nonneg : forall x y : int,
  to_Z y <= to_Z x -> to_Z x < wB ->
  to_Z (Uint63.sub x y) = (to_Z x - to_Z y)%Z.
Proof.
  intros x y Hle Hx.
  rewrite Uint63.sub_spec. rewrite Z.mod_small.
  - lia.
  - pose proof (to_Z_bounded y).
    unfold wB in Hx. change Uint63.wB with (2 ^ 63)%Z. lia.
Qed.

(* ================================================================= *)
(* Part 2: Packed bitvector                                            *)
(* ================================================================= *)

Definition bv_get (bv : array int) (pos : int) : bool :=
  negb (eqb ((bv.[pos / wbits]) land (1 << (pos mod wbits))) 0).

Definition bv_set (bv : array int) (pos : int) : array int :=
  let w := pos / wbits in
  let b := pos mod wbits in
  bv.[w <- (bv.[w]) lor (1 << b)].

(** Popcount: the only operation backed by unverified C code. *)
Parameter popcount : int -> int.

(** Clear the lowest [n] one-bits from a word. *)
Fixpoint clear_n_ones (word : int) (n : nat) : int :=
  match n with
  | O => word
  | S n' => clear_n_ones (word land (Uint63.sub word 1)) n'
  end.

(** Select: find position of the [target]-th one bit (0-indexed). *)
Fixpoint bv_select_aux (bv : array int) (remaining w_idx : int)
    (fuel : nat) : int :=
  match fuel with
  | O => 0
  | S fuel' =>
      let word := bv.[w_idx] in
      let pc := popcount word in
      if leb remaining pc then
        add (mul w_idx wbits)
            (tail0 (clear_n_ones word (Z.to_nat (to_Z remaining))))
      else
        bv_select_aux bv (sub remaining pc) (add w_idx 1) fuel'
  end.

Definition bv_select (bv : array int) (target : int) : int :=
  bv_select_aux bv target 0 (Z.to_nat (to_Z (length bv))).

(* ================================================================= *)
(* Part 3: Encoding                                                    *)
(* ================================================================= *)

Record ef63 := mk_ef63 {
  ef63_lower : array int;
  ef63_upper : array int;
  ef63_l     : int;
  ef63_n     : int;
}.

(** Fill the lower-bits array. *)
Fixpoint fill_lower (xs : list int) (mask : int) (arr : array int)
    (i : nat) : array int :=
  match xs with
  | [] => arr
  | x :: xs' =>
      fill_lower xs' mask (arr.[of_Z (Z.of_nat i) <- x land mask]) (S i)
  end.

(** Fill the upper bitvector (unary-coded gaps). *)
Fixpoint fill_upper (xs : list int) (l : int) (bv : array int)
    (pos prev : int) : array int :=
  match xs with
  | [] => bv
  | x :: xs' =>
      let u := x >> l in
      let new_pos := add pos (sub u prev) in
      fill_upper xs' l (bv_set bv new_pos) (add new_pos 1) u
  end.

Definition encode63 (U : int) (xs : list int) : ef63 :=
  let n_nat := List.length xs in
  let n := of_Z (Z.of_nat n_nat) in
  let l := if eqb n 0 then 0 else ilog2_63 (U / n) in
  let mask := sub (1 << l) 1 in
  let lower := fill_lower xs mask (make n 0) 0 in
  let max_upper :=
    match xs with
    | [] => 0
    | _ => (List.last xs 0) >> l
    end in
  let upper_words := add (div (add n max_upper) wbits) 1 in
  let upper := fill_upper xs l (make upper_words 0) 0 0 in
  mk_ef63 lower upper l n.

(* ================================================================= *)
(* Part 4: Access, Decode, NextGEQ                                     *)
(* ================================================================= *)

Definition access63 (enc : ef63) (i : int) : int :=
  let pos := bv_select (ef63_upper enc) i in
  let upper_val := sub pos i in
  (upper_val << ef63_l enc) lor ((ef63_lower enc).[i]).

Fixpoint decode63_aux (enc : ef63) (i : int) (n : nat) : list int :=
  match n with
  | O => []
  | S n' => access63 enc i :: decode63_aux enc (add i 1) n'
  end.

Definition decode63 (enc : ef63) : list int :=
  decode63_aux enc 0 (Z.to_nat (to_Z (ef63_n enc))).

Fixpoint nextGEQ63_aux (enc : ef63) (v i : int) (n : nat) : option int :=
  match n with
  | O => None
  | S n' =>
      let x := access63 enc i in
      if leb v x then Some x
      else nextGEQ63_aux enc v (add i 1) n'
  end.

Definition nextGEQ63 (enc : ef63) (v : int) : option int :=
  nextGEQ63_aux enc v 0 (Z.to_nat (to_Z (ef63_n enc))).

Definition bit_size63 (enc : ef63) : int :=
  mul (ef63_n enc) (add (ef63_l enc) 2).

(* ================================================================= *)
(* Part 5: Axioms — hard lemmas, to be proved incrementally            *)
(* ================================================================= *)

(** Each axiom is an independent work item. [Print Assumptions]
    on the final theorems lists exactly which remain open. *)

(** A1: popcount counts one-bits correctly. *)
Axiom popcount_spec : forall (x : int),
  Z.of_nat (
    let fix count_bits (n : nat) (acc : nat) :=
      match n with
      | O => acc
      | S n' => count_bits n' (if Z.testbit (to_Z x) (Z.of_nat n') then S acc else acc)
      end
    in count_bits 63%nat 0%nat
  ) = to_Z (popcount x).

(** A2: [ilog2_63] agrees with [Z.log2]. *)
Lemma ilog2_63_spec : forall x : int,
  (0 < to_Z x)%Z -> (to_Z x < wB)%Z ->
  to_Z (ilog2_63 x) = Z.log2 (to_Z x).
Proof.
  intros x Hpos Hx.
  unfold ilog2_63.
  (* x <> 0 since 0 < to_Z x *)
  assert (Hne : eqb x 0 = false).
  { apply not_true_is_false. intro Heq.
    apply eqb_spec in Heq.
    assert (to_Z x = 0%Z) by (rewrite Heq; reflexivity). lia. }
  rewrite Hne.
  (* Now goal: to_Z (sub 62 (head0 x)) = Z.log2 (to_Z x) *)
  pose proof (head0_spec x Hpos) as [Hlo Hhi].
  pose proof (to_Z_bounded (head0 x)) as [Hh0 Hh1].
  change Uint63.wB with (2 ^ 63)%Z in *.
  unfold wB in *.
  (* From head0_spec: 2^62 <= 2^h * x < 2^63 *)
  (* So 2^(62-h) <= x < 2^(63-h), hence log2(x) = 62 - h *)
  set (h := to_Z (head0 x)) in *.
  assert (Hh62 : (h <= 62)%Z).
  { destruct (Z.le_gt_cases h 62); [lia|].
    (* If h > 62 then h >= 63, so 2^h >= 2^63 > 2^62 * x ... contradiction *)
    exfalso. assert (2 ^ 63 <= 2 ^ h)%Z by (apply Z.pow_le_mono_r; lia).
    nia. }
  assert (Hlog_x : Z.log2 (to_Z x) = (62 - h)%Z).
  { apply Z.log2_unique; [lia|].
    (* 2^h * 2^(62-h) = 2^62 and 2^h * 2^(63-h) = 2^63 *)
    assert (Hpow62 : (2 ^ 62 = 2 ^ h * 2 ^ (62 - h))%Z)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hpow_succ : (2 ^ 63 = 2 ^ h * 2 ^ Z.succ (62 - h))%Z)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (H2h_pos : (0 < 2 ^ h)%Z) by (apply Z.pow_pos_nonneg; lia).
    change (2 ^ 63 / 2)%Z with (2 ^ 62)%Z in Hlo.
    split.
    - (* 2^(62-h) <= x *)
      rewrite Hpow62 in Hlo.
      rewrite Hpow_succ in Hhi.
      nia.
    - (* x < 2^(Z.succ(62-h)) *)
      rewrite Hpow_succ in Hhi.
      nia. }
  rewrite sub_nonneg.
  - change (to_Z 62) with 62%Z. lia.
  - change (to_Z 62) with 62%Z. lia.
  - change (to_Z 62) with 62%Z. unfold wB.
    assert (H63 : (2 ^ 63 = 9223372036854775808)%Z) by reflexivity. lia.
Qed.

(** A3: mask [2^l - 1] agrees with [Z.ones l]. *)
Lemma mask63_spec : forall l : int,
  (0 <= to_Z l)%Z -> (to_Z l < 63)%Z ->
  to_Z (sub (1 << l) 1) = Z.ones (to_Z l).
Proof.
  intros l Hl Hlt.
  rewrite Uint63.sub_spec, Uint63.lsl_spec.
  change (to_Z 1) with 1%Z.
  rewrite Z.mul_1_l.
  change Uint63.wB with (2 ^ 63)%Z.
  assert (H1 : (1 <= 2 ^ to_Z l)%Z).
  { change 1%Z with (2 ^ 0)%Z. apply Z.pow_le_mono_r; lia. }
  assert (H2 : (2 ^ to_Z l < 2 ^ 63)%Z).
  { apply Z.pow_lt_mono_r; lia. }
  rewrite (Z.mod_small (2 ^ to_Z l) (2 ^ 63)) by lia.
  rewrite (Z.mod_small (2 ^ to_Z l - 1) (2 ^ 63)) by lia.
  rewrite Z.ones_equiv. unfold Z.pred. lia.
Qed.

(** Monomorphic wrappers for PArray lemmas (universe bug in Rocq 9.1). *)
Local Lemma get_set_same' (t : array int) (i : int) (a : int) :
  (i <? PArray.length t)%uint63 = true -> t.[i <- a].[i] = a.
Proof. exact (get_set_same int t i a). Qed.
Local Lemma get_set_other' (t : array int) (i j : int) (a : int) :
  i <> j -> t.[i <- a].[j] = t.[j].
Proof. exact (get_set_other int t i j a). Qed.
Local Lemma length_set' (t : array int) (i : int) (a : int) :
  PArray.length (t.[i <- a]) = PArray.length t.
Proof. exact (length_set int t i a). Qed.
Local Lemma get_make' (a : int) (n i : int) : (make n a).[i] = a.
Proof. exact (get_make int a n i). Qed.
Local Lemma length_make' (n : int) (a : int) :
  PArray.length (make n a) = if (n <=? max_length)%uint63 then n else max_length.
Proof. exact (length_make int n a). Qed.

(** [1 << k] as Z. *)
Lemma lsl1_to_Z : forall k : int,
  to_Z k < 63 -> to_Z (1 << k) = (2 ^ to_Z k)%Z.
Proof.
  intros k Hk. pose proof (to_Z_bounded k).
  rewrite lsl_spec. change (to_Z 1) with 1%Z. rewrite Z.mul_1_l.
  change Uint63.wB with (2 ^ 63)%Z. apply Z.mod_small.
  split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
Qed.

(** [1 << k <> 0] when [k < 63]. *)
Lemma lsl1_nonzero : forall k : int,
  to_Z k < 63 -> (1 << k =? 0)%uint63 = false.
Proof.
  intros k Hk.
  apply not_true_is_false. intro H.
  pose proof (eqb_spec (1 << k) 0) as [Hf _]. specialize (Hf H).
  assert (Hc : to_Z (1 << k) = 0%Z) by (rewrite Hf; reflexivity).
  rewrite lsl1_to_Z in Hc by assumption.
  pose proof (to_Z_bounded k).
  assert (0 < 2 ^ to_Z k)%Z by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

(** Z-level: [lor] with a power-of-2 bit preserves that bit under [land]. *)
Lemma lor_land_same_bit : forall a k,
  (0 <= k)%Z -> Z.land (Z.lor a (2 ^ k)) (2 ^ k) = (2 ^ k)%Z.
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.lor_spec.
  destruct (Z.eq_dec n k) as [->|Hne].
  - rewrite Z.pow2_bits_true by lia. now rewrite orb_true_r.
  - rewrite !(Z.pow2_bits_false k n) by lia. now rewrite andb_false_r.
Qed.

(** Z-level: [lor] with a different power-of-2 bit is invisible to [land]. *)
Lemma lor_land_diff_bit : forall a j k,
  (0 <= j)%Z -> (0 <= k)%Z -> j <> k ->
  Z.land (Z.lor a (2 ^ j)) (2 ^ k) = Z.land a (2 ^ k).
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, Z.lor_spec.
  destruct (Z.eq_dec n j) as [->|Hne].
  - rewrite (Z.pow2_bits_false k j) by lia. now rewrite !andb_false_r.
  - rewrite (Z.pow2_bits_false j n) by lia. now rewrite orb_false_r.
Qed.

(** [wbits]-related facts. *)
Lemma wbits_val : to_Z wbits = 63%Z.
Proof. reflexivity. Qed.

Lemma mod_wbits_bound : forall p, to_Z (p mod wbits) < 63.
Proof.
  intros. rewrite mod_spec. rewrite wbits_val.
  pose proof (to_Z_bounded p). pose proof (Z.mod_pos_bound (to_Z p) 63). lia.
Qed.

Lemma div_mod_recover : forall p : int,
  to_Z p = (to_Z (p / wbits) * 63 + to_Z (p mod wbits))%Z.
Proof.
  intros. rewrite div_spec, mod_spec, wbits_val.
  pose proof (to_Z_bounded p).
  pose proof (Zdiv.Z_div_mod_eq_full (to_Z p) 63). lia.
Qed.

Lemma div_mod_unique : forall p q : int,
  p / wbits = q / wbits -> p mod wbits = q mod wbits -> p = q.
Proof.
  intros p q Hdiv Hmod. apply to_Z_inj.
  rewrite (div_mod_recover p), (div_mod_recover q).
  rewrite Hdiv, Hmod. reflexivity.
Qed.

Lemma div_mod_neq : forall p q : int,
  p <> q -> p / wbits = q / wbits -> p mod wbits <> q mod wbits.
Proof.
  intros p q Hne Hdiv Hmod. apply Hne. exact (div_mod_unique p q Hdiv Hmod).
Qed.

(** [bv_get (bv_set bv p) p = true]. *)
Lemma bv_get_bv_set_same : forall bv pos,
  (pos / wbits <? PArray.length bv)%uint63 = true ->
  bv_get (bv_set bv pos) pos = true.
Proof.
  intros bv pos Hb.
  unfold bv_get, bv_set.
  set (w := pos / wbits). set (b := pos mod wbits).
  set (v := bv.[w] lor (1 << b)).
  (* Step 1: (bv.[w <- v]).[w] land (1<<b) = v land (1<<b) via f_equal *)
  assert (Hrd := get_set_same' bv w v Hb).
  assert (Heq : (bv.[w <- v]).[w] land (1 << b) = v land (1 << b))
    by (f_equal; exact Hrd).
  rewrite Heq.
  (* Show v land (1<<b) <> 0 *)
  destruct ((v land (1 << b) =? 0)%uint63) eqn:E; [|reflexivity].
  exfalso. apply eqb_spec in E.
  assert (Hc : to_Z (v land (1 << b)) = 0%Z) by (rewrite E; reflexivity).
  unfold v in Hc. rewrite land_spec', lor_spec', lsl1_to_Z in Hc by apply mod_wbits_bound.
  rewrite lor_land_same_bit in Hc by (pose proof (to_Z_bounded b); lia).
  pose proof (to_Z_bounded b).
  assert (0 < 2 ^ to_Z b)%Z by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

(** [bv_get (bv_set bv p) q = bv_get bv q] when [p <> q]. *)
Lemma bv_get_bv_set_other : forall bv p q,
  p <> q ->
  (p / wbits <? PArray.length bv)%uint63 = true ->
  bv_get (bv_set bv p) q = bv_get bv q.
Proof.
  intros bv p q Hne Hb.
  unfold bv_get, bv_set.
  destruct (Uint63.eq_dec (p / wbits) (q / wbits)) as [Hwq|Hwq].
  - (* Same word: the modified word is read, but different bit *)
    rewrite <- Hwq.
    assert (Hrd := get_set_same' bv (p / wbits) (bv.[p / wbits] lor (1 << (p mod wbits))) Hb).
    assert (Heq : (bv.[p / wbits <- bv.[p / wbits] lor (1 << (p mod wbits))]).[p / wbits]
                    land (1 << (q mod wbits)) =
                  (bv.[p / wbits] lor (1 << (p mod wbits))) land (1 << (q mod wbits)))
      by (f_equal; exact Hrd).
    assert (Hmod_ne : to_Z (p mod wbits) <> to_Z (q mod wbits)).
    { intro Hbeq. apply Hne.
      apply div_mod_unique; [exact Hwq|apply to_Z_inj; exact Hbeq]. }
    assert (Htz : to_Z ((bv.[p / wbits] lor (1 << (p mod wbits))) land (1 << (q mod wbits))) =
                  to_Z (bv.[p / wbits] land (1 << (q mod wbits)))).
    { rewrite !land_spec', lor_spec', !lsl1_to_Z by apply mod_wbits_bound.
      rewrite lor_land_diff_bit
        by (pose proof (to_Z_bounded (p mod wbits));
            pose proof (to_Z_bounded (q mod wbits)); lia).
      reflexivity. }
    assert (Heq2 : (bv.[p / wbits] lor (1 << (p mod wbits))) land (1 << (q mod wbits)) =
                    bv.[p / wbits] land (1 << (q mod wbits)))
      by (apply to_Z_inj; exact Htz).
    rewrite Heq, Heq2. reflexivity.
  - (* Different word: the unmodified word is read *)
    assert (Hrd := get_set_other' bv (p / wbits) (q / wbits)
                     (bv.[p / wbits] lor (1 << (p mod wbits))) Hwq).
    assert (Heq : (bv.[p / wbits <- bv.[p / wbits] lor (1 << (p mod wbits))]).[q / wbits]
                    land (1 << (q mod wbits)) =
                  bv.[q / wbits] land (1 << (q mod wbits)))
      by (f_equal; exact Hrd).
    rewrite Heq. reflexivity.
Qed.

(** [bv_get] on a zero array returns false. *)
Lemma bv_get_make_zero : forall n pos,
  bv_get (make n (0 : int)) pos = false.
Proof.
  intros. unfold bv_get.
  assert (Hrd := get_make' (0 : int) n (pos / wbits)).
  assert (Heq : (make n (0 : int)).[pos / wbits] land (1 << (pos mod wbits)) =
                 (0 : int) land (1 << (pos mod wbits)))
    by (f_equal; exact Hrd).
  assert (H0 : (0 : int) land (1 << (pos mod wbits)) = 0).
  { apply to_Z_inj. rewrite land_spec'. change (to_Z 0) with 0%Z.
    rewrite Z.land_0_l. reflexivity. }
  rewrite Heq, H0. reflexivity.
Qed.

(** Helper: [of_Z] is injective on [0, wB). *)
Lemma of_Z_inj : forall a b,
  (0 <= a < wB)%Z -> (0 <= b < wB)%Z ->
  of_Z a = of_Z b -> a = b.
Proof.
  intros a b Ha Hb Heq.
  assert (to_Z (of_Z a) = to_Z (of_Z b)) by (f_equal; exact Heq).
  rewrite !of_Z_spec in H. change Uint63.wB with (2 ^ 63)%Z in H.
  unfold wB in *. rewrite !Z.mod_small in H by lia. exact H.
Qed.

(** Helper: [fill_lower] doesn't touch indices outside its range. *)
Lemma fill_lower_get_out : forall xs mask arr start j,
  (forall k, (start <= k < start + List.length xs)%nat ->
    of_Z (Z.of_nat k) <> j) ->
  (fill_lower xs mask arr start).[j] = arr.[j].
Proof.
  induction xs as [|x xs' IH]; intros mask arr start j Hout.
  - reflexivity.
  - unfold fill_lower; fold fill_lower.
    rewrite IH; [|intros k Hk; apply Hout; cbn [List.length]; lia].
    rewrite get_set_other'; [reflexivity|].
    apply Hout. cbn [List.length]. lia.
Qed.

(** Helper: [fill_lower] stores [x land mask] at each index. *)
Lemma fill_lower_get_in : forall xs mask arr start i,
  (i < List.length xs)%nat ->
  (* All indices in range are distinct *)
  (forall j k, (start <= j)%nat -> (start <= k)%nat ->
    (j < start + List.length xs)%nat -> (k < start + List.length xs)%nat ->
    j <> k -> of_Z (Z.of_nat j) <> of_Z (Z.of_nat k)) ->
  (* All indices fit in the array *)
  (forall k, (start <= k < start + List.length xs)%nat ->
    (of_Z (Z.of_nat k) <? PArray.length arr)%uint63 = true) ->
  (fill_lower xs mask arr start).[of_Z (Z.of_nat (start + i))] =
    List.nth i xs 0 land mask.
Proof.
  induction xs as [|x xs' IH]; intros mask arr start i Hi Hdist Hbounds.
  - simpl in Hi. lia.
  - destruct i as [|i'].
    + (* i = 0: the value was written at position [start] *)
      change (List.nth 0 (x :: xs') 0) with x.
      rewrite Nat.add_0_r.
      unfold fill_lower at 1; fold fill_lower.
      rewrite fill_lower_get_out.
      * assert (Hb : (of_Z (Z.of_nat start) <? PArray.length arr)%uint63 = true)
          by (apply Hbounds; cbn [List.length]; lia).
        exact (get_set_same' arr (of_Z (Z.of_nat start)) (x land mask) Hb).
      * intros k Hk.
        apply Hdist; cbn [List.length] in *; lia.
    + (* i = S i': by induction on xs' starting at S start *)
      unfold fill_lower at 1; fold fill_lower.
      change (List.nth (S i') (x :: xs') 0) with (List.nth i' xs' 0).
      replace (start + S i')%nat with (S start + i')%nat by lia.
      apply IH.
      * cbn [List.length] in Hi. lia.
      * intros j k Hj Hk Hj' Hk' Hne.
        apply Hdist; cbn [List.length] in *; lia.
      * intros k Hk. rewrite length_set'. apply Hbounds. cbn [List.length] in *. lia.
Qed.

(** A4: [fill_lower] agrees with [map (lower_bits l)]. *)
Lemma fill_lower_agrees : forall xs mask arr l,
  to_Z mask = Z.ones (to_Z l) ->
  (0 <= to_Z l)%Z ->
  (Z.of_nat (List.length xs) < wB)%Z ->
  (forall k, (k < List.length xs)%nat ->
    (of_Z (Z.of_nat k) <? PArray.length arr)%uint63 = true) ->
  forall i, (i < List.length xs)%nat ->
    to_Z ((fill_lower xs mask arr 0).[of_Z (Z.of_nat i)]) =
      lower_bits (to_Z l) (to_Z (List.nth i xs 0)).
Proof.
  intros xs mask arr l Hmask Hl Hlen Hbounds i Hi.
  replace i with (0 + i)%nat by lia.
  rewrite fill_lower_get_in.
  - (* to_Z (nth i xs 0 land mask) = lower_bits ... *)
    rewrite land_spec'. unfold lower_bits. rewrite Hmask. reflexivity.
  - exact Hi.
  - intros j k Hj Hk Hj' Hk' Hne.
    intro Heq. apply Hne.
    apply of_Z_inj in Heq; unfold wB in *; lia.
  - intros k Hk. apply Hbounds. lia.
Qed.

(** Helper: [fill_upper] only sets bits at positions [>= pos]; earlier bits unchanged. *)
(** Helper: [x >> l] agrees with [upper_value]. *)
Lemma lsr_upper_value : forall x l,
  0 <= to_Z l ->
  to_Z (x >> l) = upper_value (to_Z l) (to_Z x).
Proof.
  intros. unfold upper_value. rewrite lsr_spec. symmetry. apply Z.shiftr_div_pow2. assumption.
Qed.

(** Helper: [nth] on [repeat false k ++ [true] ++ tail]. *)
Lemma nth_repeat_app_gap : forall k (tail : list bool) i,
  (i < k)%nat ->
  List.nth i (repeat false k ++ [true] ++ tail) false = false.
Proof.
  intros. rewrite app_nth1 by (rewrite repeat_length; lia).
  apply nth_repeat.
Qed.

Lemma nth_repeat_app_one : forall k (tail : list bool),
  List.nth k (repeat false k ++ [true] ++ tail) false = true.
Proof.
  intros. rewrite app_nth2 by (rewrite repeat_length; lia).
  rewrite repeat_length. replace (k - k)%nat with 0%nat by lia.
  reflexivity.
Qed.

Lemma nth_repeat_app_tail : forall k (tail : list bool) j,
  List.nth (k + 1 + j) (repeat false k ++ [true] ++ tail) false = List.nth j tail false.
Proof.
  intros. rewrite app_nth2 by (rewrite repeat_length; lia).
  rewrite repeat_length. replace (k + 1 + j - k)%nat with (S j) by lia.
  reflexivity.
Qed.

(** Helper: [fill_upper] doesn't touch positions [< pos]. *)
Lemma fill_upper_get_lt : forall xs l bv pos prev q,
  to_Z pos + Z.of_nat (List.length
    (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) xs) (to_Z prev))) < wB ->
  Forall (fun x => to_Z prev <= upper_value (to_Z l) (to_Z x)) xs ->
  sorted (map (fun x => upper_value (to_Z l) (to_Z x)) xs) ->
  0 <= to_Z l ->
  (forall p', to_Z pos <= to_Z p' ->
     to_Z p' < to_Z pos + Z.of_nat (List.length
       (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) xs) (to_Z prev))) ->
     (p' / wbits <? PArray.length bv)%uint63 = true) ->
  to_Z q < to_Z pos ->
  bv_get (fill_upper xs l bv pos prev) q = bv_get bv q.
Proof.
  induction xs as [|x xs' IH]; intros l bv pos prev q Hovf HFA Hsorted Hl Hbounds Hq.
  - reflexivity.
  - (* Decompose Forall *)
    rewrite Forall_cons_iff in HFA; destruct HFA as [Hhead HFA_tail].
    (* Decompose StronglySorted *)
    unfold sorted in Hsorted; cbn [map] in Hsorted.
    inversion Hsorted as [|? ? Hsorted_tail HFA_ge]; subst.
    (* Arithmetic setup *)
    pose proof (to_Z_bounded pos) as Hpos_bnd.
    pose proof (to_Z_bounded prev) as Hprev_bnd.
    pose proof (to_Z_bounded (x >> l)) as Hu_bnd.
    assert (Hu_eq : to_Z (x >> l) = upper_value (to_Z l) (to_Z x))
      by (apply lsr_upper_value; exact Hl).
    assert (Hprev_le_u : to_Z prev <= to_Z (x >> l))
      by (rewrite Hu_eq; exact Hhead).
    (* Abbreviation for the tail length *)
    remember (Z.of_nat (List.length
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) xs')
         (upper_value (to_Z l) (to_Z x))))) as tail_len eqn:Htl_def.
    pose proof (Nat2Z.is_nonneg (List.length
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) xs')
         (upper_value (to_Z l) (to_Z x))))) as Htl_nn.
    (* Length decomposition: cons = gap + 1 + tail *)
    assert (Hlen_decomp :
      Z.of_nat (List.length
        (build_upper_aux
           (map (fun x0 => upper_value (to_Z l) (to_Z x0)) (x :: xs'))
           (to_Z prev))) =
      ((to_Z (x >> l) - to_Z prev) + 1 + tail_len)%Z).
    { rewrite Htl_def, Hu_eq.
      cbn [map build_upper_aux].
      rewrite !length_app, repeat_length.
      simpl Datatypes.length.
      rewrite !Nat2Z.inj_add, Z2Nat.id by lia. lia. }
    (* Int63 arithmetic *)
    assert (Hgap : to_Z (sub (x >> l) prev) = (to_Z (x >> l) - to_Z prev)%Z).
    { apply sub_nonneg; [lia|].
      unfold wB; change Uint63.wB with (2^63)%Z in *; lia. }
    assert (Hnp : to_Z (add pos (sub (x >> l) prev)) =
                  (to_Z pos + (to_Z (x >> l) - to_Z prev))%Z).
    { rewrite Uint63.add_spec, Hgap. rewrite Z.mod_small; [lia|].
      change Uint63.wB with (2^63)%Z; unfold wB in *; lia. }
    assert (Hnp1 : to_Z (add (add pos (sub (x >> l) prev)) 1) =
                   (to_Z pos + (to_Z (x >> l) - to_Z prev) + 1)%Z).
    { rewrite Uint63.add_spec; change (to_Z 1) with 1%Z.
      rewrite Hnp. rewrite Z.mod_small; [lia|].
      change Uint63.wB with (2^63)%Z; unfold wB in *; lia. }
    (* Forall for IH: upper values in tail >= to_Z (x >> l) *)
    assert (HFA' : Forall (fun x0 => to_Z (x >> l) <=
                     upper_value (to_Z l) (to_Z x0)) xs').
    { rewrite Hu_eq. apply Forall_map. exact HFA_ge. }
    (* Length of bv_set *)
    assert (Hlen_bv : PArray.length (bv_set bv (add pos (sub (x >> l) prev))) =
                      PArray.length bv)
      by (unfold bv_set; apply length_set').
    (* Unfold one step of fill_upper *)
    cbn [fill_upper].
    (* Main proof: IH then bv_get_bv_set_other *)
    transitivity (bv_get (bv_set bv (add pos (sub (x >> l) prev))) q).
    + apply IH.
      * (* overflow *)
        rewrite Hnp1, Hu_eq, <- Htl_def.
        rewrite Hlen_decomp in Hovf. unfold wB in *. lia.
      * exact HFA'.
      * exact Hsorted_tail.
      * exact Hl.
      * (* bounds *) intros p' Hp'1 Hp'2. rewrite Hlen_bv.
        rewrite Hu_eq, <- Htl_def in Hp'2.
        apply Hbounds.
        -- rewrite Hnp1 in Hp'1; lia.
        -- rewrite Hlen_decomp. rewrite Hnp1 in Hp'1. lia.
      * (* q < add np 1 *) rewrite Hnp1; lia.
    + apply bv_get_bv_set_other.
      * intro Heq.
        assert (Hc : to_Z (add pos (sub (x >> l) prev)) = to_Z q)
          by (rewrite Heq; reflexivity).
        rewrite Hnp in Hc; lia.
      * apply Hbounds; [rewrite Hnp; lia|].
        rewrite Hlen_decomp. rewrite Hnp. lia.
Qed.

(** Generalized [fill_upper] agreement — induction-ready version. *)
Lemma fill_upper_agrees_gen : forall xs l bv pos prev,
  0 <= to_Z l ->
  (* all positions fit in the bitvector: *)
  (forall p, to_Z pos <= to_Z p ->
     to_Z p < to_Z pos + Z.of_nat (List.length
       (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) xs) (to_Z prev))) ->
     (p / wbits <? PArray.length bv)%uint63 = true) ->
  (* no overflow: *)
  (to_Z pos + Z.of_nat (List.length
     (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) xs) (to_Z prev))) < wB)%Z ->
  (* upper values are >= prev: *)
  Forall (fun x => to_Z prev <= upper_value (to_Z l) (to_Z x)) xs ->
  (* sorted upper values: *)
  sorted (map (fun x => upper_value (to_Z l) (to_Z x)) xs) ->
  (* positions < pos in bv are correct: *)
  (forall i, (i < List.length
     (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) xs) (to_Z prev)))%nat ->
    bv_get bv (of_Z (to_Z pos + Z.of_nat i)) = false) ->
  forall i, (i < List.length
     (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) xs) (to_Z prev)))%nat ->
    bv_get (fill_upper xs l bv pos prev) (of_Z (to_Z pos + Z.of_nat i)) =
      List.nth i (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) xs) (to_Z prev)) false.
Proof.
  induction xs as [|x xs' IH];
    intros l bv pos prev Hl Hbounds Hovf HFA Hsorted Hzero i Hi.
  - (* Base: build_upper_aux [] _ = [], Hi : i < 0 *)
    simpl in Hi. lia.
  - (* Inductive step *)
    (* Decompose hypotheses *)
    rewrite Forall_cons_iff in HFA; destruct HFA as [Hhead HFA_tail].
    unfold sorted in Hsorted; cbn [map] in Hsorted.
    inversion Hsorted as [|? ? Hsorted_tail HFA_ge]; subst.
    (* Arithmetic setup *)
    pose proof (to_Z_bounded pos) as Hpos_bnd.
    pose proof (to_Z_bounded prev) as Hprev_bnd.
    pose proof (to_Z_bounded (x >> l)) as Hu_bnd.
    assert (Hu_eq : to_Z (x >> l) = upper_value (to_Z l) (to_Z x))
      by (apply lsr_upper_value; exact Hl).
    assert (Hprev_le_u : to_Z prev <= to_Z (x >> l))
      by (rewrite Hu_eq; exact Hhead).
    set (gap_nat := Z.to_nat (to_Z (x >> l) - to_Z prev)).
    assert (Hgap_nat_Z : Z.of_nat gap_nat = (to_Z (x >> l) - to_Z prev)%Z)
      by (unfold gap_nat; rewrite Z2Nat.id; lia).
    remember (Z.of_nat (List.length
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) xs')
         (upper_value (to_Z l) (to_Z x))))) as tail_len eqn:Htl_def.
    pose proof (Nat2Z.is_nonneg (List.length
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) xs')
         (upper_value (to_Z l) (to_Z x))))) as Htl_nn.
    assert (Hlen_decomp :
      Z.of_nat (List.length
        (build_upper_aux
           (map (fun x0 => upper_value (to_Z l) (to_Z x0)) (x :: xs'))
           (to_Z prev))) =
      ((to_Z (x >> l) - to_Z prev) + 1 + tail_len)%Z).
    { rewrite Htl_def, Hu_eq.
      cbn [map build_upper_aux].
      rewrite !length_app, repeat_length.
      simpl Datatypes.length.
      rewrite !Nat2Z.inj_add, Z2Nat.id by lia. lia. }
    assert (Hgap : to_Z (sub (x >> l) prev) = (to_Z (x >> l) - to_Z prev)%Z).
    { apply sub_nonneg; [lia|].
      unfold wB; change Uint63.wB with (2^63)%Z in *; lia. }
    set (np := add pos (sub (x >> l) prev)).
    assert (Hnp : to_Z np = (to_Z pos + (to_Z (x >> l) - to_Z prev))%Z).
    { unfold np. rewrite Uint63.add_spec, Hgap. rewrite Z.mod_small; [lia|].
      change Uint63.wB with (2^63)%Z; unfold wB in *; lia. }
    assert (Hnp1 : to_Z (add np 1) = (to_Z np + 1)%Z).
    { rewrite Uint63.add_spec; change (to_Z 1) with 1%Z.
      rewrite Z.mod_small; [lia|].
      change Uint63.wB with (2^63)%Z; rewrite Hnp; unfold wB in *; lia. }
    assert (HFA' : Forall (fun x0 => to_Z (x >> l) <=
                     upper_value (to_Z l) (to_Z x0)) xs').
    { rewrite Hu_eq. apply Forall_map. exact HFA_ge. }
    assert (Hlen_bv : PArray.length (bv_set bv np) = PArray.length bv)
      by (unfold bv_set, np; apply length_set').
    (* of_Z roundtrip for positions in range *)
    assert (Hof_Z_rt : forall j,
      (Z.of_nat j < (to_Z (x >> l) - to_Z prev) + 1 + tail_len)%Z ->
      to_Z (of_Z (to_Z pos + Z.of_nat j)) = (to_Z pos + Z.of_nat j)%Z).
    { intros j Hj. rewrite of_Z_spec. rewrite Z.mod_small; [lia|].
      change Uint63.wB with (2^63)%Z; unfold wB in *; lia. }
    (* Unfold one step *)
    cbn [fill_upper]. fold np.
    (* Simplify build_upper_aux in Hi and goal *)
    cbn [map] in |- *.
    change (build_upper_aux (upper_value (to_Z l) (to_Z x)
              :: map (fun x0 => upper_value (to_Z l) (to_Z x0)) xs') (to_Z prev))
      with (repeat false (Z.to_nat (upper_value (to_Z l) (to_Z x) - to_Z prev))
            ++ [true]
            ++ build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) xs')
                 (upper_value (to_Z l) (to_Z x))) in |- *.
    rewrite <- Hu_eq in |- *.
    change (Z.to_nat (to_Z (x >> l) - to_Z prev)) with gap_nat in |- *.
    (* Three-way case split *)
    destruct (Nat.lt_ge_cases i gap_nat) as [Hcase_gap | Hcase_ge].
    + (* Case A: gap — i < gap_nat, bit is false *)
      rewrite nth_repeat_app_gap by exact Hcase_gap.
      transitivity (bv_get (bv_set bv np) (of_Z (to_Z pos + Z.of_nat i))).
      * apply fill_upper_get_lt.
        -- (* overflow *) rewrite Hnp1, Hnp, Hu_eq, <- Htl_def.
           rewrite Hlen_decomp in Hovf. unfold wB in *. lia.
        -- exact HFA'.
        -- exact Hsorted_tail.
        -- exact Hl.
        -- intros p' Hp'1 Hp'2. rewrite Hlen_bv.
           rewrite Hu_eq, <- Htl_def in Hp'2.
           apply Hbounds.
           ++ rewrite Hnp1, Hnp in Hp'1. lia.
           ++ rewrite Hlen_decomp. rewrite Hnp1, Hnp in Hp'1. lia.
        -- rewrite Hof_Z_rt by lia. rewrite Hnp1, Hnp. lia.
      * rewrite bv_get_bv_set_other.
        -- apply Hzero. exact Hi.
        -- intro Heq.
           assert (Hc : to_Z np = to_Z (of_Z (to_Z pos + Z.of_nat i)))
             by (rewrite Heq; reflexivity).
           rewrite Hnp, Hof_Z_rt in Hc by lia. lia.
        -- apply Hbounds; [rewrite Hnp; lia|].
           rewrite Hlen_decomp, Hnp. lia.
    + destruct (Nat.eq_dec i gap_nat) as [Hcase_one | Hcase_tail].
      * (* Case B: one-bit — i = gap_nat *)
        subst i.
        rewrite nth_repeat_app_one.
        assert (Hpos_eq : of_Z (to_Z pos + Z.of_nat gap_nat) = np).
        { apply to_Z_inj. rewrite Hof_Z_rt by lia.
          rewrite Hgap_nat_Z. rewrite Hnp. lia. }
        rewrite Hpos_eq.
        transitivity (bv_get (bv_set bv np) np).
        -- apply fill_upper_get_lt.
           ++ rewrite Hnp1, Hnp, Hu_eq, <- Htl_def.
              rewrite Hlen_decomp in Hovf. unfold wB in *. lia.
           ++ exact HFA'.
           ++ exact Hsorted_tail.
           ++ exact Hl.
           ++ intros p' Hp'1 Hp'2. rewrite Hlen_bv.
              rewrite Hu_eq, <- Htl_def in Hp'2.
              apply Hbounds.
              ** rewrite Hnp1, Hnp in Hp'1. lia.
              ** rewrite Hlen_decomp. rewrite Hnp1, Hnp in Hp'1. lia.
           ++ rewrite Hnp, Hnp1. lia.
        -- apply bv_get_bv_set_same.
           apply Hbounds; [rewrite Hnp; lia|].
           rewrite Hlen_decomp, Hnp. lia.
      * (* Case C: tail — i > gap_nat *)
        assert (Hge : (i >= gap_nat + 1)%nat) by lia.
        set (j := (i - gap_nat - 1)%nat).
        assert (Hi_decomp : i = (gap_nat + 1 + j)%nat) by (unfold j; lia).
        rewrite Hi_decomp.
        rewrite nth_repeat_app_tail.
        (* Align positions: pos + (gap_nat + 1 + j) = (add np 1) + j *)
        assert (Hpos_shift :
          (to_Z pos + Z.of_nat (gap_nat + 1 + j))%Z =
          (to_Z (add np 1) + Z.of_nat j)%Z).
        { rewrite Hnp1, Hnp, !Nat2Z.inj_add, Hgap_nat_Z. simpl. lia. }
        rewrite Hpos_shift.
        apply IH.
        -- exact Hl.
        -- (* bounds *) intros p' Hp'1 Hp'2. rewrite Hlen_bv.
           rewrite Hu_eq, <- Htl_def in Hp'2.
           apply Hbounds.
           ++ rewrite Hnp1, Hnp in Hp'1. lia.
           ++ rewrite Hlen_decomp. rewrite Hnp1, Hnp in Hp'1. lia.
        -- (* overflow *)
           rewrite Hnp1, Hnp, Hu_eq, <- Htl_def.
           rewrite Hlen_decomp in Hovf. unfold wB in *. lia.
        -- exact HFA'.
        -- exact Hsorted_tail.
        -- (* zero precondition for bv_set bv np *)
           intros k Hk.
           assert (Hk_eq :
             (to_Z (add np 1) + Z.of_nat k)%Z =
             (to_Z pos + Z.of_nat (gap_nat + 1 + k))%Z).
           { rewrite Hnp1, Hnp, !Nat2Z.inj_add, Hgap_nat_Z. simpl. lia. }
           rewrite Hk_eq.
           transitivity (bv_get bv (of_Z (to_Z pos + Z.of_nat (gap_nat + 1 + k)))).
           ++ apply bv_get_bv_set_other.
              ** intro Heq.
                 assert (Hc : to_Z np = to_Z (of_Z (to_Z pos + Z.of_nat (gap_nat + 1 + k))))
                   by (rewrite Heq; reflexivity).
                 rewrite Hnp, Hof_Z_rt in Hc.
                 --- lia.
                 --- rewrite Hu_eq in Hk. rewrite Htl_def.
                     rewrite !Nat2Z.inj_add, Hgap_nat_Z. simpl. lia.
              ** apply Hbounds; [rewrite Hnp; lia|].
                 rewrite Hlen_decomp, Hnp. lia.
           ++ apply Hzero. rewrite Hu_eq in Hk. lia.
        -- (* j < tail length *)
           rewrite Hi_decomp in Hi. rewrite Hu_eq. lia.
Qed.

(** A5: [fill_upper] agrees with [build_upper] pointwise. *)
Lemma fill_upper_agrees : forall xs l bv,
  0 <= to_Z l ->
  (* all upper values are nonneg and sorted *)
  all_nonneg (to_Z_list xs) ->
  sorted (to_Z_list xs) ->
  (* positions fit in the bitvector: *)
  (forall p, 0 <= to_Z p ->
     to_Z p < Z.of_nat (List.length
       (build_upper (map (fun x => upper_value (to_Z l) (to_Z x)) xs))) ->
     (p / wbits <? PArray.length bv)%uint63 = true) ->
  (* no overflow: *)
  (Z.of_nat (List.length
     (build_upper (map (fun x => upper_value (to_Z l) (to_Z x)) xs))) < wB)%Z ->
  (* initial bv is zero: *)
  (forall q, bv_get bv q = false) ->
  let uppers := map (fun x => upper_value (to_Z l) (to_Z x)) xs in
  let bv_list := build_upper uppers in
  forall i, (i < List.length bv_list)%nat ->
    bv_get (fill_upper xs l bv 0 0) (of_Z (Z.of_nat i)) =
      List.nth i bv_list false.
Proof.
  intros xs l bv Hl Hnn Hsorted Hfit Hno_ovf Hzero uppers bv_list i Hi.
  change (of_Z (Z.of_nat i)) with (of_Z (to_Z 0 + Z.of_nat i)).
  apply fill_upper_agrees_gen.
  - exact Hl.
  - intros p Hp1 Hp2. apply Hfit. exact Hp1. exact Hp2.
  - unfold build_upper in *. change (to_Z 0) with 0%Z. exact Hno_ovf.
  - change (to_Z 0) with 0%Z. rewrite Forall_forall. intros x Hx.
    apply upper_value_nonneg; [lia|].
    unfold all_nonneg, to_Z_list in Hnn. rewrite Forall_forall in Hnn.
    apply Hnn. apply in_map. exact Hx.
  - (* sorted upper values *)
    unfold sorted, to_Z_list in Hsorted |- *. clear -Hsorted Hl.
    induction xs as [|x0 xs0 IHx]; [constructor|].
    simpl map in *. inversion Hsorted as [|? ? Hs' HF]; subst.
    constructor.
    + apply IHx. exact Hs'.
    + rewrite Forall_map in HF |- *.
      revert HF. apply Forall_impl.
      intros a Ha. apply upper_value_mono; lia.
  - intros j Hj. apply Hzero.
  - exact Hi.
Qed.

(** A6: [bv_select] agrees with [position_of_ith_one]. *)
Axiom bv_select_agrees : forall bv bv_list target,
  (forall i, (i < List.length bv_list)%nat ->
    bv_get bv (of_Z (Z.of_nat i)) = List.nth i bv_list false) ->
  (Z.to_nat (to_Z target) < count_occ Bool.bool_dec bv_list true)%nat ->
  to_Z (bv_select bv target) =
    Z.of_nat (position_of_ith_one bv_list (Z.to_nat (to_Z target))).

(** A7: [lor (u << l) lo] recombines upper and lower bits. *)
Lemma recombine63 : forall u l lo,
  (0 <= to_Z u)%Z -> (0 <= to_Z l)%Z -> (0 <= to_Z lo)%Z ->
  (to_Z lo < 2 ^ to_Z l)%Z ->
  (to_Z u * 2 ^ to_Z l + to_Z lo < wB)%Z ->
  to_Z ((u << l) lor lo) = (to_Z u * 2 ^ to_Z l + to_Z lo)%Z.
Proof.
  intros u l lo Hu Hl Hlo Hlo_bound Hsum.
  rewrite lor_spec', lsl_spec.
  change Uint63.wB with (2 ^ 63)%Z.
  rewrite Z.mod_small.
  2: { split.
       - apply Z.mul_nonneg_nonneg; [exact Hu|apply Z.pow_nonneg; lia].
       - unfold wB in Hsum. lia. }
  rewrite or_to_plus.
  - lia.
  - apply Z.bits_inj'. intros n Hn.
    rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n (to_Z l)).
    + (* n < to_Z l: high part has 0 bit *)
      rewrite Z.mul_pow2_bits_low by lia.
      reflexivity.
    + (* n >= to_Z l: low part has 0 bit *)
      destruct (Z.eq_dec (to_Z lo) 0) as [Hz|Hnz].
      * rewrite Hz, Z.testbit_0_l.
        destruct (Z.testbit _ _); reflexivity.
      * assert (Hlo_pos : (0 < to_Z lo)%Z) by lia.
        assert (Hlog_lo : (Z.log2 (to_Z lo) < n)%Z).
        { eapply Z.lt_le_trans; [|eassumption].
          apply Z.log2_lt_pow2; [exact Hlo_pos | exact Hlo_bound]. }
        rewrite (Z.bits_above_log2 (to_Z lo) n) by lia.
        destruct (Z.testbit _ _); reflexivity.
Qed.

(* ================================================================= *)
(* Part 6: Agreement theorems — proved from axioms                     *)
(* ================================================================= *)

(** The [ef63_l] field agrees with the Z-level [ef_l]. *)
Lemma encode63_l_agrees : forall U xs,
  in_range (to_Z U) (to_Z_list xs) ->
  xs <> [] ->
  to_Z (ef63_l (encode63 U xs)) = ef_l (encode (to_Z U) (to_Z_list xs)).
Proof.
  intros U xs Hir Hne.
  destruct Hir as (HU_pos & HU_bound & Hn_bound & Hsum & Hn_max & Hmax).
  destruct xs as [|x xs']; [contradiction|].
  (* Unfold both sides, then normalize *)
  unfold encode63, ef63_l, encode, ef_l, num_lower_bits, to_Z_list.
  rewrite !length_map.
  set (k := Datatypes.length (x :: xs')).
  set (n63 := of_Z (Z.of_nat k)).
  (* Key facts *)
  assert (Hk_pos : (0 < Z.of_nat k)%Z) by (unfold k; simpl; lia).
  assert (Hk_bound : (Z.of_nat k < wB)%Z).
  { fold k in Hn_bound. unfold to_Z_list in Hn_bound.
    rewrite length_map in Hn_bound. fold k in Hn_bound. exact Hn_bound. }
  assert (Hn63_val : to_Z n63 = Z.of_nat k).
  { unfold n63. rewrite of_Z_spec. apply Z.mod_small.
    change Uint63.wB with (2 ^ 63)%Z. unfold wB in Hk_bound. lia. }
  assert (Hn63_ne : eqb n63 0 = false).
  { apply not_true_is_false. intro Heq. apply eqb_spec in Heq.
    assert (to_Z n63 = 0%Z) by (rewrite Heq; reflexivity). lia. }
  rewrite Hn63_ne.
  replace (Z.of_nat k <=? 0)%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (to_Z U <=? 0)%Z with false by (symmetry; apply Z.leb_gt; lia).
  (* Both sides: ilog2_63(U/n63) vs Z.log2(to_Z U / Z.of_nat k) *)
  set (q := (to_Z U / Z.of_nat k)%Z).
  assert (Hq63 : to_Z (U / n63) = q).
  { unfold q. rewrite div_spec, Hn63_val. reflexivity. }
  destruct (Z.eq_dec q 0) as [Hq0|Hq_pos].
  - (* q = 0: both sides return 0 *)
    unfold ilog2_63.
    assert (Heq0 : eqb (U / n63) 0 = true).
    { apply eqb_spec. apply to_Z_inj. rewrite Hq63, Hq0. reflexivity. }
    rewrite Heq0. change (to_Z 0) with 0%Z.
    rewrite Hq0. symmetry. apply Z.log2_nonpos. lia.
  - (* q > 0 *)
    rewrite ilog2_63_spec.
    + rewrite Hq63. reflexivity.
    + rewrite Hq63. unfold q.
      assert (0 <= to_Z U / Z.of_nat k)%Z by (apply Z.div_pos; lia). lia.
    + rewrite Hq63. unfold wB, q.
      pose proof (to_Z_bounded U). change Uint63.wB with (2 ^ 63)%Z in *.
      apply Z.div_lt_upper_bound; lia.
Qed.

(** Main access agreement. *)
Theorem access63_agrees : forall U xs i,
  in_range (to_Z U) (to_Z_list xs) ->
  sorted (to_Z_list xs) ->
  all_nonneg (to_Z_list xs) ->
  bounded_by (to_Z U) (to_Z_list xs) ->
  0 <= to_Z i ->
  (Z.to_nat (to_Z i) < List.length xs)%nat ->
  to_Z (access63 (encode63 U xs) i) =
    access_ef (encode (to_Z U) (to_Z_list xs)) (Z.to_nat (to_Z i)).
Proof.
  intros U xs i Hir Hs Hnn Hb Hi Hlen.
  destruct xs as [|x0 xs']; [simpl in Hlen; lia|].
  assert (Hne : (x0 :: xs') <> []) by discriminate.
  set (enc63 := encode63 U (x0 :: xs')).
  set (encZ := encode (to_Z U) (to_Z_list (x0 :: xs'))).
  set (l63 := ef63_l enc63).
  set (lZ := ef_l encZ).
  unfold access63, access_ef.
  fold enc63 encZ l63 lZ.
  (* ---- Step 0: basic facts ---- *)
  destruct Hir as (HU_pos & HU_wB & Hn_wB & Hsum_wB & Hn_max & Hmax).
  assert (Hl_agree : to_Z l63 = lZ).
  { unfold l63, lZ. exact (encode63_l_agrees U (x0 :: xs')
      (conj HU_pos (conj HU_wB (conj Hn_wB (conj Hsum_wB (conj Hn_max Hmax))))) Hne). }
  assert (Hl_nn : (0 <= lZ)%Z).
  { unfold lZ, encZ. simpl. apply num_lower_bits_nonneg. }
  assert (Hl63_nn : (0 <= to_Z l63)%Z) by lia.
  set (i_nat := Z.to_nat (to_Z i)).
  assert (Hi_nat : Z.of_nat i_nat = to_Z i).
  { unfold i_nat. rewrite Z2Nat.id; lia. }
  pose proof (to_Z_bounded i) as Hi_bnd.
  set (uppers := map (upper_value lZ) (to_Z_list (x0 :: xs'))).
  (* n63 = of_Z (length xs) *)
  set (n_nat := List.length (x0 :: xs')).
  assert (Hn_nat : (0 < Z.of_nat n_nat)%Z) by (unfold n_nat; simpl; lia).
  set (n63 := of_Z (Z.of_nat n_nat)).
  assert (Hn_wB' : (Z.of_nat n_nat < wB)%Z).
  { unfold to_Z_list in Hn_wB. rewrite length_map in Hn_wB. exact Hn_wB. }
  assert (Hn63_val : to_Z n63 = Z.of_nat n_nat).
  { unfold n63. rewrite of_Z_spec. apply Z.mod_small.
    change Uint63.wB with (2^63)%Z. unfold wB in Hn_wB'. lia. }
  (* The mask in encode63 *)
  set (mask := sub (1 << l63) 1).
  (* ---- map form agreement ---- *)
  assert (Hmap_eq :
    map (fun x : int => upper_value (to_Z l63) (to_Z x)) (x0 :: xs') =
    map (upper_value lZ) (to_Z_list (x0 :: xs'))).
  { unfold to_Z_list. rewrite map_map. apply map_ext.
    intros a. rewrite Hl_agree. reflexivity. }
  assert (Hbuild_eq :
    build_upper (map (fun x => upper_value (to_Z l63) (to_Z x)) (x0 :: xs')) =
    ef_upper encZ).
  { change (ef_upper encZ) with
      (build_upper (map (upper_value lZ) (to_Z_list (x0 :: xs')))).
    f_equal. exact Hmap_eq. }
  (* ---- upper bitvector agreement ---- *)
  set (bv0 := make (add (div (add n63 ((List.last (x0 :: xs') 0) >> l63)) wbits) 1) 0).
  assert (Hupper_raw : forall j,
    (j < List.length (build_upper (map (fun x => upper_value (to_Z l63) (to_Z x)) (x0 :: xs'))))%nat ->
    bv_get (fill_upper (x0 :: xs') l63 bv0 0 0) (of_Z (Z.of_nat j)) =
      List.nth j (build_upper (map (fun x => upper_value (to_Z l63) (to_Z x)) (x0 :: xs'))) false).
  { apply fill_upper_agrees.
    - exact Hl63_nn.
    - exact Hnn.
    - exact Hs.
    - (* bounds: positions fit in bitvector *)
      intros p Hp_nn Hp_lt.
      (* We need: (p / wbits <? PArray.length bv0) = true *)
      (* Strategy: show p / wbits < bv0 size at Z level *)
      set (last_u := to_Z (List.last (x0 :: xs') 0 >> l63)).
      set (bv_size := add (div (add n63 (List.last (x0 :: xs') 0 >> l63)) wbits) 1).
      (* Step 1: last >> l < U *)
      assert (Hlast_u_bound : last_u < to_Z U).
      { unfold last_u.
        rewrite lsr_spec.
        (* last element is bounded by U *)
        assert (Hlast_in : In (List.last (x0 :: xs') 0) (x0 :: xs')).
        { rewrite (app_removelast_last 0 Hne) at 2.
          apply in_or_app. right. left. reflexivity. }
        assert (Hlast_bnd : to_Z (List.last (x0 :: xs') 0) < to_Z U).
        { unfold bounded_by in Hb. rewrite Forall_forall in Hb.
          apply Hb. unfold to_Z_list. apply in_map. exact Hlast_in. }
        assert (Hlast_nn : 0 <= to_Z (List.last (x0 :: xs') 0)).
        { unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
          apply Hnn. unfold to_Z_list. apply in_map. exact Hlast_in. }
        assert (H2l : 0 < 2 ^ to_Z l63) by (apply Z.pow_pos_nonneg; lia).
        apply Z.div_lt_upper_bound; [lia|].
        apply Z.lt_le_trans with (to_Z U * 2 ^ to_Z l63)%Z.
        - nia.
        - assert (to_Z (List.last (x0 :: xs') 0) < to_Z U) by exact Hlast_bnd.
          nia. }
      (* Step 2: n + last_u < n + U <= max_length * wbits (no int overflow) *)
      assert (Hn_last_u : Z.of_nat n_nat + last_u < to_Z max_length * to_Z wbits).
      { unfold to_Z_list in Hmax. rewrite length_map in Hmax. fold n_nat in Hmax. lia. }
      assert (Hn_last_u_wB : Z.of_nat n_nat + last_u < wB).
      { unfold to_Z_list in Hsum_wB. rewrite length_map in Hsum_wB. fold n_nat in Hsum_wB. lia. }
      (* Step 3: bound on bv_size *)
      (* Key fact: last_u = upper_value l63 (last element), and
         length(build_upper uppers) = last_upper + n.
         bv0 has (n + last_u) / 63 + 1 words, fitting any position < last_u + n. *)
      (* last_u is nonneg *)
      assert (Hlast_u_nn : 0 <= last_u).
      { unfold last_u. rewrite lsr_spec. apply Z.div_pos;
        [|apply Z.pow_pos_nonneg; lia].
        unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
        apply Hnn. unfold to_Z_list. apply in_map.
        rewrite (app_removelast_last 0 Hne) at 2.
        apply in_or_app. right. left. reflexivity. }
      (* First: n + last_u fits in int without overflow *)
      assert (Hadd_ok : to_Z (add n63 (List.last (x0 :: xs') 0 >> l63)) =
        (Z.of_nat n_nat + last_u)%Z).
      { rewrite add_spec, Hn63_val. fold last_u.
        rewrite Z.mod_small; [reflexivity|].
        split; [lia|]. exact Hn_last_u_wB. }
      (* Division and +1 don't overflow *)
      assert (Hdiv_ok : to_Z (div (add n63 (List.last (x0 :: xs') 0 >> l63)) wbits) =
        ((Z.of_nat n_nat + last_u) / 63)%Z).
      { rewrite div_spec by discriminate. rewrite Hadd_ok.
        change (to_Z wbits) with (63 : Z). reflexivity. }
      assert (Hmax_val : to_Z max_length = (4194303 : Z)) by reflexivity.
      assert (Hwbits_val : to_Z wbits = (63 : Z)) by reflexivity.
      assert (Hdiv_bound : ((Z.of_nat n_nat + last_u) / 63 < (4194303 : Z))%Z).
      { apply Z.div_lt_upper_bound; [lia|].
        rewrite Hwbits_val in Hn_last_u. rewrite Hmax_val in Hn_last_u. lia. }
      assert (Hsize_ok : to_Z bv_size = ((Z.of_nat n_nat + last_u) / 63 + 1)%Z).
      { unfold bv_size. rewrite add_spec, Hdiv_ok.
        change (to_Z 1) with (1 : Z).
        rewrite Z.mod_small; [reflexivity|].
        assert (0 <= (Z.of_nat n_nat + last_u) / 63)%Z by (apply Z.div_pos; lia).
        split; [lia|]. change Uint63.wB with (2^63)%Z. lia. }
      assert (Hbv_le_max : to_Z bv_size <= to_Z max_length).
      { rewrite Hsize_ok, Hmax_val. lia. }
      (* Apply ltb_spec *)
      apply ltb_spec. rewrite div_spec by discriminate.
      unfold bv0. rewrite length_make'.
      fold bv_size.
      assert (Hle : (bv_size <=? max_length)%uint63 = true).
      { apply leb_spec. exact Hbv_le_max. }
      rewrite Hle. rewrite Hsize_ok. change (to_Z wbits) with (63 : Z).
      (* Need: to_Z p / 63 < (n + last_u) / 63 + 1 *)
      (* From Hp_lt: to_Z p < length(build_upper ...) *)
      (* build_upper length bound: length <= n + last_u (last upper value) *)
      assert (Hp_bound : to_Z p <= Z.of_nat n_nat + last_u - 1).
      { (* Use length_build_upper: length = last(uppers) + length(uppers) *)
        set (ups := map (fun x : int => upper_value (to_Z l63) (to_Z x)) (x0 :: xs')).
        assert (Hups_ne : ups <> []) by (unfold ups; discriminate).
        assert (Hups_nn : Forall (fun u => 0 <= u) ups).
        { unfold ups. rewrite Forall_forall. intros u Hu.
          apply in_map_iff in Hu. destruct Hu as [x [Hux Hx]]. subst u.
          unfold upper_value. rewrite Z.shiftr_div_pow2 by lia.
          apply Z.div_pos; [|apply Z.pow_pos_nonneg; lia].
          unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
          apply Hnn. unfold to_Z_list. apply in_map. exact Hx. }
        assert (Hups_sorted : sorted ups).
        { unfold ups. rewrite Hmap_eq. unfold uppers.
          assert (Hgen : forall zs, sorted zs ->
            sorted (map (upper_value lZ) zs)).
          { intros zs. induction zs as [|a rest' IHs].
            - constructor.
            - intros Hsrt. inversion Hsrt as [|? ? Hsort_rest HF_le]; subst.
              constructor; [exact (IHs Hsort_rest)|].
              rewrite Forall_forall. intros u Hu.
              apply in_map_iff in Hu. destruct Hu as [b [Hub Hbin]]. subst u.
              unfold upper_value. rewrite !Z.shiftr_div_pow2 by lia.
              apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia|].
              rewrite Forall_forall in HF_le. exact (HF_le _ Hbin). }
          exact (Hgen _ Hs). }
        assert (Hlen_eq : (Z.of_nat (List.length (build_upper ups)) =
          last ups 0%Z + Z.of_nat (List.length ups))%Z).
        { exact (length_build_upper ups Hups_ne Hups_nn Hups_sorted). }
        (* last ups = last_u *)
        assert (Hlast_ups : last ups 0%Z = last_u).
        { unfold ups, last_u. unfold upper_value.
          (* Prove: last (map (Z.shiftr _ (to_Z l63)) (x0 :: xs')) 0 =
                    to_Z (last (x0 :: xs') 0) / 2^(to_Z l63) *)
          rewrite lsr_spec.
          (* Need: last (map f (x0::xs')) 0 = f (last (x0::xs') 0) *)
          assert (Hml : forall (A B : Type) (f : A -> B) (l : list A) (da : A) (db : B),
            l <> [] -> last (map f l) db = f (last l da)).
          { intros A B f l da db Hne'.
            rewrite (app_removelast_last da Hne').
            rewrite map_app. simpl map.
            rewrite !last_last. reflexivity. }
          rewrite (Hml int Z _ _ 0 0%Z Hne).
          rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
        (* length ups = n_nat *)
        assert (Hlen_ups : List.length ups = n_nat).
        { unfold ups. rewrite length_map. reflexivity. }
        rewrite Hlast_ups, Hlen_ups in Hlen_eq.
        fold ups in Hp_lt.
        (* Hp_lt: to_Z p < Z.of_nat(List.length(build_upper ups))
           Hlen_eq: Z.of_nat(List.length(build_upper ups)) = last_u + n_nat
           Goal: to_Z p <= n_nat + last_u - 1 *)
        lia. }
      assert (to_Z p / 63 <= (Z.of_nat n_nat + last_u - 1) / 63)%Z.
      { apply Z.div_le_mono; lia. }
      assert ((Z.of_nat n_nat + last_u - 1) / 63 < (Z.of_nat n_nat + last_u) / 63 + 1)%Z.
      { assert (HH := Z.div_mod (Z.of_nat n_nat + last_u - 1) 63 ltac:(lia)).
        assert (HH2 := Z.div_mod (Z.of_nat n_nat + last_u) 63 ltac:(lia)).
        assert (0 <= (Z.of_nat n_nat + last_u - 1) mod 63 < 63)%Z
          by (apply Z.mod_pos_bound; lia).
        assert (0 <= (Z.of_nat n_nat + last_u) mod 63 < 63)%Z
          by (apply Z.mod_pos_bound; lia).
        nia. }
      lia.
    - (* no overflow *)
      (* Bound: length(build_upper_aux us prev) <= max_element - prev + length us *)
      (* For build_upper from 0: length <= last_upper + n *)
      (* We prove a bound: each element of build_upper_aux adds at most gap + 1 booleans *)
      enough (Hsuff :
        Z.of_nat (Datatypes.length
          (build_upper (map (fun x : int => upper_value (to_Z l63) (to_Z x)) (x0 :: xs')))) <=
        Z.of_nat n_nat + to_Z U).
      { assert (Hsum' : Z.of_nat n_nat + to_Z U < wB).
        { unfold to_Z_list in Hsum_wB. rewrite length_map in Hsum_wB.
          fold n_nat in Hsum_wB. exact Hsum_wB. }
        lia. }
      (* Prove the bound using Forall to bound all upper values *)
      rewrite Hmap_eq. unfold build_upper.
      (* We need: length(build_upper_aux uppers 0) <= n_nat + to_Z U *)
      (* where uppers = map (upper_value lZ) (to_Z_list (x0 :: xs')),
         all uppers are in [0, to_Z U), and length uppers = n_nat *)
      fold uppers.
      (* Use an inductive bound *)
      assert (Hbd : forall (us : list Z) (prev : Z),
        Forall (fun u : Z => (u >= prev)%Z) us ->
        Forall (fun u : Z => (u < to_Z U)%Z) us ->
        sorted us ->
        (0 <= prev)%Z ->
        (Z.of_nat (Datatypes.length (build_upper_aux us prev)) <=
          Z.of_nat (Datatypes.length us) + Z.max (0%Z) (to_Z U - prev))%Z).
      { intros us prev Hge0 Hbd0 HSS Hprev0.
        revert prev Hge0 Hprev0. induction us as [|u rest IHu]; intros prev Hge0 Hprev0.
        - simpl. lia.
        - inversion Hge0 as [|? ? Hu_ge Hge_rest]; subst.
          inversion Hbd0 as [|? ? Hu_bd Hbd_rest]; subst.
          unfold sorted in HSS.
          inversion HSS as [|? ? HSS_rest HF_le]; subst.
          simpl build_upper_aux.
          rewrite length_app, repeat_length.
          assert (Hrest_ge : Forall (fun v : Z => (v >= u)%Z) rest).
          { revert HF_le. apply Forall_impl. intros a Ha. lia. }
          assert (Hu_nn : (0 <= u)%Z) by lia.
          assert (HSS_rest' : sorted rest) by exact HSS_rest.
          specialize (IHu Hbd_rest HSS_rest' u Hrest_ge Hu_nn).
          change (Datatypes.length (true :: build_upper_aux rest u))
            with (S (Datatypes.length (build_upper_aux rest u))).
          change (Datatypes.length (u :: rest)) with (S (Datatypes.length rest)).
          rewrite !Nat2Z.inj_add, !Nat2Z.inj_succ.
          rewrite (Z2Nat.id (u - prev)%Z) by lia.
          rewrite Z.max_r in IHu by lia.
          rewrite Z.max_r by lia.
          lia. }
      (* Prove sorted uppers *)
      assert (HSS_uppers : sorted uppers).
      { unfold uppers, sorted, to_Z_list.
        unfold sorted in Hs. unfold to_Z_list in Hs.
        assert (Hl_nn' : (0 <= lZ)%Z) by lia.
        generalize Hl_nn' (map to_Z (x0 :: xs')) Hs. clear.
        intros Hl_nn zs Hs.
        induction zs as [|z zs' IHz].
        - constructor.
        - inversion Hs as [|? ? HSS' HF_le]; subst.
          constructor.
          + exact (IHz HSS').
          + rewrite Forall_forall in HF_le |- *.
            intros a Ha. apply in_map_iff in Ha.
            destruct Ha as [x [<- Hx]].
            apply upper_value_mono; [lia | apply HF_le; exact Hx]. }
      apply Z.le_trans with (Z.of_nat (Datatypes.length uppers) + Z.max 0 (to_Z U - 0))%Z.
      { apply Hbd.
        - unfold uppers. apply Forall_forall. intros u Hu.
          apply in_map_iff in Hu. destruct Hu as [z [<- Hz]].
          assert (Hnn_z : (0 <= z)%Z).
          { unfold all_nonneg, to_Z_list in Hnn. rewrite Forall_forall in Hnn.
            apply Hnn. exact Hz. }
          pose proof (upper_value_nonneg lZ z Hl_nn Hnn_z). lia.
        - unfold uppers. apply Forall_forall. intros u Hu.
          apply in_map_iff in Hu. destruct Hu as [z [<- Hz]].
          unfold upper_value. rewrite Z.shiftr_div_pow2 by lia.
          unfold bounded_by, to_Z_list in Hb. rewrite Forall_forall in Hb.
          assert (Hz_bnd : z < to_Z U) by (apply Hb; exact Hz).
          apply Z.le_lt_trans with z; [|exact Hz_bnd].
          apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
          assert (Hznn : (0 <= z)%Z).
          { unfold all_nonneg, to_Z_list in Hnn. rewrite Forall_forall in Hnn.
            apply Hnn. exact Hz. }
          assert (1 <= 2 ^ lZ)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia).
          nia.
        - exact HSS_uppers.
        - lia. }
      unfold uppers, to_Z_list. rewrite !length_map. fold n_nat. lia.
    - (* initial bv is zero *)
      intro q. apply bv_get_make_zero. }
  assert (Henc_upper : ef63_upper enc63 = fill_upper (x0 :: xs') l63 bv0 0 0).
  { unfold enc63, encode63, bv0, l63, n63, n_nat. reflexivity. }
  assert (Hupper : forall j, (j < List.length (ef_upper encZ))%nat ->
    bv_get (ef63_upper enc63) (of_Z (Z.of_nat j)) =
      List.nth j (ef_upper encZ) false).
  { intros j Hj. rewrite Henc_upper, <- Hbuild_eq.
    apply Hupper_raw. rewrite Hbuild_eq. exact Hj. }
  (* ---- lower array agreement ---- *)
  assert (Hlo : to_Z ((ef63_lower enc63).[i]) = nth i_nat (ef_lower encZ) 0%Z).
  { change (ef_lower encZ) with (map (lower_bits lZ) (to_Z_list (x0 :: xs'))).
    rewrite (nth_map_safe (lower_bits lZ) (to_Z_list (x0 :: xs')) i_nat 0%Z 0%Z).
    2: { unfold to_Z_list. rewrite length_map. exact Hlen. }
    unfold to_Z_list.
    rewrite (nth_map_safe to_Z (x0 :: xs') i_nat 0 0%Z) by exact Hlen.
    replace i with (of_Z (Z.of_nat i_nat)).
    2: { apply to_Z_inj. rewrite of_Z_spec. rewrite Z.mod_small.
         - exact Hi_nat.
         - change Uint63.wB with (2^63)%Z. unfold wB in *. lia. }
    assert (Henc_lower : ef63_lower enc63 = fill_lower (x0 :: xs') mask (make n63 0) 0).
    { unfold enc63, encode63, mask, l63, n63, n_nat. reflexivity. }
    rewrite Henc_lower.
    replace lZ with (to_Z l63) by exact Hl_agree.
    rewrite (fill_lower_agrees _ _ _ l63).
    - reflexivity.
    - (* mask = Z.ones (to_Z l63) *)
      assert (Hl63_lt : to_Z l63 < 63).
      { rewrite Hl_agree. unfold lZ, encZ, encode, ef_l, num_lower_bits.
        unfold to_Z_list. rewrite length_map. fold n_nat.
        destruct (Z.of_nat n_nat <=? 0)%Z eqn:Hn0; [lia|].
        destruct (to_Z U <=? 0)%Z eqn:HU0; [lia|].
        apply Z.leb_gt in Hn0. apply Z.leb_gt in HU0.
        destruct (Z.eq_dec (to_Z U / Z.of_nat n_nat) 0) as [Hq0|Hq_pos].
        - rewrite Hq0. simpl. lia.
        - assert (0 < to_Z U / Z.of_nat n_nat)%Z.
          { assert (0 <= to_Z U / Z.of_nat n_nat)%Z
              by (apply Z.div_pos; lia). lia. }
          apply Z.log2_lt_pow2; [lia|].
          apply Z.le_lt_trans with (to_Z U).
          { apply Z.div_le_upper_bound; [lia|]. nia. }
          { unfold wB in HU_wB; lia. } }
      exact (mask63_spec l63 Hl63_nn Hl63_lt).
    - exact Hl63_nn.
    - exact Hn_wB'.
    - (* array bounds: of_Z k < PArray.length (make n63 0) for k < n *)
      intros k Hk.
      apply ltb_spec.
      rewrite length_make'.
      (* n63 <= max_length *)
      assert (Hn63_le_max : (n63 <=? max_length)%uint63 = true).
      { apply leb_spec. rewrite Hn63_val.
        unfold to_Z_list in Hn_max. rewrite length_map in Hn_max.
        fold n_nat in Hn_max. exact Hn_max. }
      rewrite Hn63_le_max. rewrite Hn63_val.
      simpl length in Hk.
      rewrite of_Z_spec. rewrite Z.mod_small.
      { lia. }
      { split; [lia|]. change Uint63.wB with wB. lia. }
    - exact Hlen. }
  (* ---- bv_select agreement ---- *)
  assert (Hsel : to_Z (bv_select (ef63_upper enc63) i) =
    Z.of_nat (position_of_ith_one (ef_upper encZ) i_nat)).
  { apply bv_select_agrees.
    - intros j Hj.
      change (ef_upper encZ) with (build_upper uppers) in Hj.
      exact (Hupper j Hj).
    - change (ef_upper encZ) with (build_upper uppers).
      rewrite count_occ_build_upper.
      unfold uppers. rewrite length_map. unfold to_Z_list. rewrite length_map.
      exact Hlen. }
  (* ---- position_of_ith_one value ---- *)
  assert (Hpos_val : position_of_ith_one (ef_upper encZ) i_nat =
    (Z.to_nat (nth i_nat uppers 0%Z) + i_nat)%nat).
  { unfold uppers. change (ef_upper encZ) with (build_upper uppers).
    unfold uppers. apply position_of_ith_one_build_upper.
    - apply Forall_map_upper_nonneg; [lia|exact Hnn].
    - apply StronglySorted_map_upper_nth; [lia|exact Hs].
    - rewrite length_map. unfold to_Z_list. rewrite length_map. exact Hlen. }
  (* ---- sub agrees ---- *)
  assert (Hu_val : to_Z (sub (bv_select (ef63_upper enc63) i) i) =
    (Z.of_nat (position_of_ith_one (ef_upper encZ) i_nat) - to_Z i)%Z).
  { assert (Hupper_nn : (0 <= nth i_nat uppers 0)%Z).
    { unfold uppers. rewrite (nth_map_safe (upper_value lZ) (to_Z_list (x0 :: xs')) i_nat 0%Z 0%Z).
      - apply upper_value_nonneg; [lia|].
        unfold to_Z_list. rewrite (nth_map_safe to_Z (x0 :: xs') i_nat 0 0%Z) by exact Hlen.
        pose proof (to_Z_bounded (nth i_nat (x0 :: xs') (0 : int))). lia.
      - unfold to_Z_list. rewrite length_map. exact Hlen. }
    rewrite sub_nonneg.
    - rewrite Hsel. lia.
    - rewrite Hsel, Hpos_val. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
      rewrite <- Hi_nat. lia.
    - rewrite Hsel, Hpos_val. unfold wB.
      (* position = Z.to_nat (nth i_nat uppers 0) + i_nat < wB *)
      (* upper_value lZ (to_Z xi) < to_Z U *)
      rewrite Nat2Z.inj_add, Z2Nat.id by lia.
      (* nth i_nat uppers 0 = upper_value lZ (to_Z (nth i_nat (x0::xs') 0)) *)
      unfold uppers. rewrite (nth_map_safe (upper_value lZ) (to_Z_list (x0 :: xs')) i_nat 0%Z 0%Z).
      2: { unfold to_Z_list. rewrite length_map. exact Hlen. }
      unfold to_Z_list.
      rewrite (nth_map_safe to_Z (x0 :: xs') i_nat 0 0%Z) by exact Hlen.
      set (xi := nth i_nat (x0 :: xs') (0 : int)).
      assert (Hxi_bnd : to_Z xi < to_Z U).
      { unfold bounded_by in Hb. rewrite Forall_forall in Hb.
        apply Hb. unfold to_Z_list. apply in_map. apply nth_In. exact Hlen. }
      assert (Huv_le : upper_value lZ (to_Z xi) <= to_Z xi).
      { unfold upper_value. rewrite Z.shiftr_div_pow2 by lia.
        apply Z.div_le_upper_bound.
        - apply Z.pow_pos_nonneg; lia.
        - pose proof (to_Z_bounded xi).
          assert (1 <= 2 ^ lZ)%Z.
        { change 1%Z with (2 ^ 0)%Z. apply Z.pow_le_mono_r; lia. }
        nia. }
      assert (Hi_nat_lt : Z.of_nat i_nat < Z.of_nat n_nat)
        by (apply Nat2Z.inj_lt; exact Hlen).
      assert (Hsum' : Z.of_nat n_nat + to_Z U < wB).
      { unfold to_Z_list in Hsum_wB. rewrite length_map in Hsum_wB.
        fold n_nat in Hsum_wB. exact Hsum_wB. }
      unfold wB in Hsum' |- *. lia. }
  (* ---- recombine ---- *)
  rewrite recombine63.
  - (* main equation *)
    rewrite Hu_val, Hlo, Hl_agree, Hpos_val.
    unfold uppers.
    rewrite (nth_map_safe (upper_value lZ) (to_Z_list (x0 :: xs')) i_nat 0%Z 0%Z).
    2: { unfold to_Z_list. rewrite length_map. exact Hlen. }
    unfold to_Z_list.
    rewrite (nth_map_safe to_Z (x0 :: xs') i_nat 0 0%Z) by exact Hlen.
    assert (Huv_nn : (0 <= upper_value lZ (to_Z (nth i_nat (x0 :: xs') (0 : int))))%Z)
      by (apply upper_value_nonneg; [lia | pose proof (to_Z_bounded (nth i_nat (x0 :: xs') (0 : int))); lia]).
    rewrite !Nat2Z.inj_add, !Z2Nat.id by lia. lia.
  - (* 0 <= to_Z u *)
    rewrite Hu_val, Hpos_val.
    assert (Hupper_nn : (0 <= nth i_nat uppers 0)%Z).
    { unfold uppers. rewrite (nth_map_safe (upper_value lZ) (to_Z_list (x0 :: xs')) i_nat 0%Z 0%Z).
      - apply upper_value_nonneg; [lia|].
        unfold to_Z_list. rewrite (nth_map_safe to_Z (x0 :: xs') i_nat 0 0%Z) by exact Hlen.
        pose proof (to_Z_bounded (nth i_nat (x0 :: xs') (0 : int))). lia.
      - unfold to_Z_list. rewrite length_map. exact Hlen. }
    rewrite Nat2Z.inj_add, Z2Nat.id by lia. rewrite <- Hi_nat. lia.
  - (* 0 <= to_Z l *)
    lia.
  - (* 0 <= to_Z lo *)
    pose proof (to_Z_bounded ((ef63_lower enc63).[i])). lia.
  - (* to_Z lo < 2^(to_Z l) *)
    rewrite Hl_agree, Hlo.
    change (ef_lower encZ) with (map (lower_bits lZ) (to_Z_list (x0 :: xs'))).
    rewrite (nth_map_safe (lower_bits lZ) (to_Z_list (x0 :: xs')) i_nat 0%Z 0%Z).
    2: { unfold to_Z_list. rewrite length_map. exact Hlen. }
    unfold to_Z_list.
    rewrite (nth_map_safe to_Z (x0 :: xs') i_nat 0 0%Z) by exact Hlen.
    unfold lower_bits. rewrite Z.land_ones by lia. apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
  - (* sum < wB — the value is bounded_by U < wB *)
    set (xi := nth i_nat (x0 :: xs') (0 : int)).
    assert (Hxi_bnd := to_Z_bounded xi).
    (* The sum u*2^l + lo reconstructs to_Z xi by recombine *)
    enough (Hrec : (to_Z (sub (bv_select (ef63_upper enc63) i) i) *
      2 ^ to_Z l63 + to_Z ((ef63_lower enc63).[i]) = to_Z xi)%Z).
    { unfold wB. change Uint63.wB with (2^63)%Z in *. lia. }
    (* Use the Z-level access_ef_correct *)
    rewrite Hu_val, Hl_agree, Hlo, Hpos_val.
    change (ef_lower encZ) with (map (lower_bits lZ) (to_Z_list (x0 :: xs'))).
    unfold uppers.
    rewrite (nth_map_safe (lower_bits lZ) (to_Z_list (x0 :: xs')) i_nat 0%Z 0%Z).
    2: { unfold to_Z_list. rewrite length_map. exact Hlen. }
    rewrite (nth_map_safe (upper_value lZ) (to_Z_list (x0 :: xs')) i_nat 0%Z 0%Z).
    2: { unfold to_Z_list. rewrite length_map. exact Hlen. }
    unfold to_Z_list.
    rewrite !(nth_map_safe to_Z (x0 :: xs') i_nat 0 0%Z) by exact Hlen.
    fold xi.
    assert (Huv_nn : (0 <= upper_value lZ (to_Z xi))%Z)
      by (apply upper_value_nonneg; [lia|lia]).
    rewrite !Nat2Z.inj_add, !Z2Nat.id by lia.
    replace ((upper_value lZ (to_Z xi) + Z.of_nat i_nat - to_Z i)%Z)
      with (upper_value lZ (to_Z xi)) by (rewrite Hi_nat; lia).
    apply recombine; [lia|lia].
Qed.

(** Access correctness — the payoff. *)
Corollary access63_correct : forall U xs i,
  in_range (to_Z U) (to_Z_list xs) ->
  sorted (to_Z_list xs) ->
  all_nonneg (to_Z_list xs) ->
  bounded_by (to_Z U) (to_Z_list xs) ->
  0 <= to_Z i ->
  (Z.to_nat (to_Z i) < List.length xs)%nat ->
  to_Z (access63 (encode63 U xs) i) = List.nth (Z.to_nat (to_Z i)) (to_Z_list xs) 0%Z.
Proof.
  intros U xs i Hir Hs Hnn Hb Hi Hlen.
  rewrite access63_agrees by assumption.
  apply access_ef_correct; try assumption.
  unfold to_Z_list. rewrite length_map. exact Hlen.
Qed.

(* ================================================================= *)
(* Part 6b: Helpers for decode63/nextGEQ63 proofs                      *)
(* ================================================================= *)

(* Proof pattern cookbook for Int63 refinement lemmas:
 *
 * 1. INDUCTION ON FUEL (nat): decode63_aux and nextGEQ63_aux use a
 *    nat fuel parameter.  Induction follows the Z-level structure.
 *
 * 2. ADD OVERFLOW GUARD: each inductive step does (add i 1).
 *    Use add1_to_Z, guarded by (to_Z i + 1 < wB)%Z from in_range.
 *    SCOPE PITFALL: always write (to_Z i + 1)%Z — with uint63_scope
 *    open, bare + resolves to Uint63.add, causing type errors.
 *
 * 3. BRIDGE VIA access63_agrees / access63_correct: convert Int63
 *    access to Z values, then reuse Z-level theorems.
 *
 * 4. of_Z / to_Z ROUND-TRIP: of_to_Z gives of_Z (to_Z i) = i.
 *    For the converse, to_Z_of_Z_small: 0 <= n < wB -> to_Z(of_Z n)
 *    = n  (from of_Z_spec + Z.mod_small).
 *
 * 5. Z <-> nat CONVERSIONS: Z2Nat.id, Nat2Z.id, Z2Nat.inj_add.
 *
 * 6. COMPARISON BRIDGE: leb v x = true <-> to_Z v <= to_Z x
 *    (via leb_spec).  Maps to Z-level (x >=? v) via Z.geb_le.
 *
 * 7. REDUCTION STRATEGY: for compound operations (decode, nextGEQ),
 *    prove an "agrees" lemma that reduces Int63 result to Z-level
 *    result.  Then the semantic theorems (correctness, minimality,
 *    completeness) follow directly from Z-level counterparts. *)

(** Safe increment. *)
Lemma add1_to_Z : forall i : int,
  (to_Z i + 1 < wB)%Z ->
  to_Z (add i 1) = (to_Z i + 1)%Z.
Proof.
  intros i Hi.
  rewrite add_spec. change (to_Z 1) with 1%Z.
  rewrite Z.mod_small.
  - lia.
  - pose proof (to_Z_bounded i). unfold wB in Hi.
    change Uint63.wB with (2 ^ 63)%Z. lia.
Qed.

(** of_Z round-trip for values in range. *)
Lemma to_Z_of_Z_small : forall n : Z,
  (0 <= n < wB)%Z -> to_Z (of_Z n) = n.
Proof.
  intros n Hn. rewrite of_Z_spec.
  rewrite Z.mod_small; [lia | unfold wB in Hn; change Uint63.wB with (2^63)%Z; lia].
Qed.

(** Length of decode63_aux. *)
Lemma decode63_aux_length : forall enc i n,
  List.length (decode63_aux enc i n) = n.
Proof.
  intros enc i n. revert i. induction n as [|n' IH]; intros i; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

(** Index access for decode63_aux. *)
Lemma decode63_aux_nth : forall enc n i j,
  (j < n)%nat ->
  (to_Z i + Z.of_nat n < wB)%Z ->
  (0 <= to_Z i)%Z ->
  nth j (decode63_aux enc i n) 0 = access63 enc (of_Z (to_Z i + Z.of_nat j)).
Proof.
  intros enc n. revert enc. induction n as [|n' IH]; intros enc i j Hj Hov Hi0.
  - lia.
  - simpl. destruct j as [|j'].
    + simpl. f_equal. rewrite Z.add_0_r. symmetry. apply of_to_Z.
    + simpl.
      assert (Hadd : to_Z (add i 1) = (to_Z i + 1)%Z) by (apply add1_to_Z; lia).
      transitivity (access63 enc (of_Z (to_Z (add i 1) + Z.of_nat j'))).
      * apply IH; lia.
      * f_equal. f_equal. lia.
Qed.

(** Functional agreement: nextGEQ63_aux mirrors nextGEQ_aux on Z.

    The hypothesis Hacc asserts pointwise access agreement over the
    scan range.  This is discharged by access63_agrees at call sites. *)
Lemma nextGEQ63_aux_agrees : forall enc63 encZ v i n,
  (forall k, (Z.to_nat (to_Z i) <= k < Z.to_nat (to_Z i) + n)%nat ->
    to_Z (access63 enc63 (of_Z (Z.of_nat k))) = access_ef encZ k) ->
  (to_Z i + Z.of_nat n < wB)%Z ->
  (0 <= to_Z i)%Z ->
  option_map to_Z (nextGEQ63_aux enc63 v i n) =
    nextGEQ_aux encZ (to_Z v) (Z.to_nat (to_Z i)) n.
Proof.
  intros enc63 encZ v i n. revert i.
  induction n as [|n' IH]; intros i Hacc Hov Hi0.
  - simpl. reflexivity.
  - simpl.
    (* Bridge: access63 at i agrees with access_ef at Z.to_nat(to_Z i) *)
    assert (Hacc_i : to_Z (access63 enc63 i) = access_ef encZ (Z.to_nat (to_Z i))).
    { pose proof (Hacc (Z.to_nat (to_Z i))) as H.
      rewrite Z2Nat.id in H by lia. rewrite of_to_Z in H.
      apply H. lia. }
    (* Bridge the comparison: leb v x <-> access_ef >= to_Z v *)
    set (x63 := access63 enc63 i).
    set (xZ := access_ef encZ (Z.to_nat (to_Z i))).
    assert (HxZ : to_Z x63 = xZ) by exact Hacc_i.
    destruct (leb v x63) eqn:Hleb.
    + (* leb v x63 = true, so to_Z v <= to_Z x63, so xZ >= to_Z v *)
      apply leb_spec in Hleb.
      replace (xZ >=? to_Z v) with true.
      * simpl. f_equal. exact HxZ.
      * symmetry. apply Z.geb_le. lia.
    + (* leb v x63 = false, so to_Z v > to_Z x63, so xZ < to_Z v *)
      assert (Hlt : (to_Z x63 < to_Z v)%Z).
      { assert (Hnle : ~ (to_Z v <= to_Z x63)%Z).
        { intro Habs. apply leb_spec in Habs. rewrite Habs in Hleb. discriminate. }
        lia. }
      replace (xZ >=? to_Z v) with false.
      2:{ symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
      (* Recurse with add i 1 *)
      assert (Hadd : to_Z (add i 1) = (to_Z i + 1)%Z) by (apply add1_to_Z; lia).
      replace (S (Z.to_nat (to_Z i))) with (Z.to_nat (to_Z (add i 1)))
        by (rewrite Hadd; rewrite Z2Nat.inj_add by lia; simpl; lia).
      apply IH.
      * intros k Hk. apply Hacc.
        rewrite Hadd in Hk. rewrite Z2Nat.inj_add in Hk by lia. simpl in Hk. lia.
      * lia.
      * lia.
Qed.

(** Encode agreement: ef63_n and ef_n produce the same length. *)
Lemma encode63_n_agrees : forall U xs,
  in_range (to_Z U) (to_Z_list xs) ->
  Z.to_nat (to_Z (ef63_n (encode63 U xs))) = List.length xs.
Proof.
  intros U xs Hir.
  unfold encode63. simpl.
  rewrite to_Z_of_Z_small.
  - rewrite Nat2Z.id. reflexivity.
  - destruct Hir as [_ [_ [Hn _]]].
    unfold to_Z_list in Hn. rewrite length_map in Hn. lia.
Qed.

(** Helper: discharge the access agreement hypothesis of nextGEQ63_aux_agrees. *)
Lemma access63_agrees_range : forall U xs k,
  in_range (to_Z U) (to_Z_list xs) ->
  sorted (to_Z_list xs) ->
  all_nonneg (to_Z_list xs) ->
  bounded_by (to_Z U) (to_Z_list xs) ->
  (k < List.length xs)%nat ->
  to_Z (access63 (encode63 U xs) (of_Z (Z.of_nat k))) =
    access_ef (encode (to_Z U) (to_Z_list xs)) k.
Proof.
  intros U xs k Hir Hs Hnn Hb Hk.
  rewrite access63_agrees; try assumption.
  - rewrite to_Z_of_Z_small.
    + rewrite Nat2Z.id. reflexivity.
    + destruct Hir as [_ [_ [Hn _]]]. unfold to_Z_list in Hn. rewrite length_map in Hn. lia.
  - rewrite to_Z_of_Z_small.
    + lia.
    + destruct Hir as [_ [_ [Hn _]]]. unfold to_Z_list in Hn. rewrite length_map in Hn. lia.
  - rewrite to_Z_of_Z_small.
    + rewrite Nat2Z.id. lia.
    + destruct Hir as [_ [_ [Hn _]]]. unfold to_Z_list in Hn. rewrite length_map in Hn. lia.
Qed.

(* ================================================================= *)
(* Part 6c: Top-level theorems                                         *)
(* ================================================================= *)

(** Round-trip. *)
Theorem decode63_agrees : forall U xs,
  in_range (to_Z U) (to_Z_list xs) ->
  sorted (to_Z_list xs) ->
  all_nonneg (to_Z_list xs) ->
  bounded_by (to_Z U) (to_Z_list xs) ->
  map to_Z (decode63 (encode63 U xs)) = to_Z_list xs.
Proof.
  intros U xs Hir Hs Hnn Hb.
  unfold decode63.
  set (enc63 := encode63 U xs).
  set (n_nat := Z.to_nat (to_Z (ef63_n enc63))).
  assert (Hn : n_nat = List.length xs) by (apply encode63_n_agrees; exact Hir).
  apply nth_ext with (d := 0%Z) (d' := 0%Z).
  - rewrite map_length, decode63_aux_length. unfold to_Z_list. rewrite map_length. lia.
  - intros j Hj.
    rewrite map_length, decode63_aux_length in Hj.
    change 0%Z with (to_Z 0) at 1.
    rewrite map_nth.
    rewrite decode63_aux_nth.
    + change (to_Z 0) with 0%Z. rewrite Z.add_0_l.
      assert (Hj_wB : (Z.of_nat j < wB)%Z).
      { destruct Hir as [_ [_ [Hn' _]]]. unfold to_Z_list in Hn'. rewrite map_length in Hn'. lia. }
      assert (HtoZ : to_Z (of_Z (Z.of_nat j)) = Z.of_nat j)
        by (apply to_Z_of_Z_small; lia).
      subst enc63.
      replace j with (Z.to_nat (to_Z (of_Z (Z.of_nat j)))) at 2
        by (rewrite HtoZ, Nat2Z.id; lia).
      apply access63_correct; try assumption.
      * rewrite HtoZ. lia.
      * rewrite HtoZ. rewrite Nat2Z.id. lia.
    + lia.
    + change (to_Z 0) with 0%Z.
      destruct Hir as [_ [_ [Hn' _]]]. unfold to_Z_list in Hn'. rewrite map_length in Hn'. lia.
    + change (to_Z 0) with 0%Z. lia.
Qed.

(** Shared setup: reduce nextGEQ63 to Z-level nextGEQ via agrees lemma. *)
Lemma nextGEQ63_to_Z : forall U xs v,
  in_range (to_Z U) (to_Z_list xs) ->
  sorted (to_Z_list xs) ->
  all_nonneg (to_Z_list xs) ->
  bounded_by (to_Z U) (to_Z_list xs) ->
  option_map to_Z (nextGEQ63 (encode63 U xs) v) =
    nextGEQ (encode (to_Z U) (to_Z_list xs)) (to_Z v).
Proof.
  intros U xs v Hir Hs Hnn Hb.
  unfold nextGEQ63, nextGEQ.
  assert (Hn : Z.to_nat (to_Z (ef63_n (encode63 U xs))) = List.length xs)
    by (apply encode63_n_agrees; exact Hir).
  assert (Hlen : ef_n (encode (to_Z U) (to_Z_list xs)) = List.length xs).
  { simpl. unfold to_Z_list. apply length_map. }
  rewrite Hn, Hlen.
  apply nextGEQ63_aux_agrees.
  - intros k Hk. simpl in Hk. apply access63_agrees_range; assumption || lia.
  - change (to_Z 0) with 0%Z.
    destruct Hir as [_ [_ [Hn' _]]]. unfold to_Z_list in Hn'. rewrite length_map in Hn'. lia.
  - change (to_Z 0) with 0%Z. lia.
Qed.

(** nextGEQ found. *)
Theorem nextGEQ63_found : forall U xs v r,
  in_range (to_Z U) (to_Z_list xs) ->
  sorted (to_Z_list xs) ->
  all_nonneg (to_Z_list xs) ->
  bounded_by (to_Z U) (to_Z_list xs) ->
  nextGEQ63 (encode63 U xs) v = Some r ->
  In (to_Z r) (to_Z_list xs) /\ to_Z r >= to_Z v.
Proof.
  intros U xs v r Hir Hs Hnn Hb Hfind.
  pose proof (nextGEQ63_to_Z U xs v Hir Hs Hnn Hb) as Hagree.
  rewrite Hfind in Hagree. simpl in Hagree.
  exact (nextGEQ_found_thm (to_Z U) (to_Z_list xs) (to_Z v) (to_Z r)
    Hs Hnn Hb (eq_sym Hagree)).
Qed.

(** nextGEQ smallest. *)
Theorem nextGEQ63_smallest : forall U xs v r,
  in_range (to_Z U) (to_Z_list xs) ->
  sorted (to_Z_list xs) ->
  all_nonneg (to_Z_list xs) ->
  bounded_by (to_Z U) (to_Z_list xs) ->
  nextGEQ63 (encode63 U xs) v = Some r ->
  forall y, In y (to_Z_list xs) -> y >= to_Z v -> to_Z r <= y.
Proof.
  intros U xs v r Hir Hs Hnn Hb Hfind y Hy Hyv.
  pose proof (nextGEQ63_to_Z U xs v Hir Hs Hnn Hb) as Hagree.
  rewrite Hfind in Hagree. simpl in Hagree.
  exact (nextGEQ_smallest_thm (to_Z U) (to_Z_list xs) (to_Z v) (to_Z r)
    Hs Hnn Hb (eq_sym Hagree) y Hy Hyv).
Qed.

(** nextGEQ none. *)
Theorem nextGEQ63_none : forall U xs v,
  in_range (to_Z U) (to_Z_list xs) ->
  sorted (to_Z_list xs) ->
  all_nonneg (to_Z_list xs) ->
  bounded_by (to_Z U) (to_Z_list xs) ->
  nextGEQ63 (encode63 U xs) v = None ->
  forall y, In y (to_Z_list xs) -> y < to_Z v.
Proof.
  intros U xs v Hir Hs Hnn Hb Hnone y Hy.
  pose proof (nextGEQ63_to_Z U xs v Hir Hs Hnn Hb) as Hagree.
  rewrite Hnone in Hagree. simpl in Hagree.
  exact (nextGEQ_none_thm (to_Z U) (to_Z_list xs) (to_Z v)
    Hs Hnn Hb (eq_sym Hagree) y Hy).
Qed.

(* ================================================================= *)
(* Part 7: Audit                                                       *)
(* ================================================================= *)

(* Audit: which axioms remain?
   Only popcount_spec (C-backed) and bv_select_agrees (popcount-based
   scan) plus Uint63/PArray primitives. *)
Print Assumptions access63_correct.
Print Assumptions decode63_agrees.
Print Assumptions nextGEQ63_found.
Print Assumptions nextGEQ63_smallest.
Print Assumptions nextGEQ63_none.
