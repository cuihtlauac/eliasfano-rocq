(** * Elias-Fano Encoding — Int63/PArray Refinement

    Efficient implementation using machine integers and primitive arrays.
    Agreement with the Z/list proofs in [EliasFano.v] is established
    for all operations.

    The only remaining axiom is [popcount_spec] (backed by a C stub).
    [bv_select_agrees] is a proved lemma.  All decrease obligations
    for Acc-based recursion are proved (no Admitted).

    [Print Assumptions] on each top-level theorem shows exactly
    which axioms remain. *)

From Stdlib Require Import ZArith List Bool Uint63 PArray Lia Wf_nat.
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

Definition in_range (U : Z) (vals : list Z) : Prop :=
  0 < U /\ U < wB /\
  Z.of_nat (List.length vals) < wB /\
  Z.of_nat (List.length vals) + U < wB /\
  Z.of_nat (List.length vals) <= to_Z max_length /\
  Z.of_nat (List.length vals) + U <= to_Z max_length * to_Z wbits.

Definition to_Z_list (vals : list int) : list Z := map to_Z vals.

(** Bundled precondition: inputs fit in Int63 and satisfy the Z-level invariants. *)
Definition valid_input (U : int) (vals : list int) : Prop :=
  in_range (to_Z U) (to_Z_list vals) /\
  sorted (to_Z_list vals) /\
  all_nonneg (to_Z_list vals) /\
  bounded_by (to_Z U) (to_Z_list vals).

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

(** Clear the lowest [n] one-bits from a word (nat version, for proofs). *)
Fixpoint clear_n_ones (word : int) (n : nat) : int :=
  match n with
  | O => word
  | S n' => clear_n_ones (word land (Uint63.sub word 1)) n'
  end.

(** Decidable equality on [int] (in [Set], for clean extraction). *)
Definition int_eq_dec (x y : int) : {x = y} + {x <> y}.
Proof.
  destruct (x =? y) eqn:E.
  - left. apply eqb_correct. exact E.
  - right. intro H. subst. rewrite eqb_refl in E. discriminate.
Defined.
Global Arguments int_eq_dec : simpl never.

(** Clear the lowest [n] one-bits (int version, for fast extraction).
    Uses Acc-based recursion so extraction produces a clean loop
    instead of the closure-heavy nat dispatch pattern. *)
Section ClearNOnesInt.
  Let measure (n : int) : nat := Z.to_nat (to_Z n).

  Lemma clear_n_decrease : forall n : int,
    n <> 0 ->
    (measure (Uint63.sub n 1) < measure n)%nat.
  Proof.
    intros n Hne. unfold measure.
    pose proof (to_Z_bounded n) as Hb.
    change Uint63Axioms.wB with (2 ^ 63)%Z in Hb.
    assert (Hpos : (0 < to_Z n)%Z).
    { destruct (Z.eq_dec (to_Z n) 0) as [Hz|Hz];
        [exfalso; apply Hne; apply to_Z_inj; exact Hz | lia]. }
    rewrite Uint63.sub_spec.
    change (to_Z 1) with 1%Z.
    change Uint63Axioms.wB with (2 ^ 63)%Z.
    rewrite Z.mod_small; [| lia].
    apply Z2Nat.inj_lt; lia.
  Qed.

  Fixpoint clear_n_ones_int (word n : int)
      (ACC : Acc lt (measure n)) {struct ACC} : int :=
    match int_eq_dec n 0 with
    | left _ => word
    | right Hne =>
        clear_n_ones_int (word land (Uint63.sub word 1)) (Uint63.sub n 1)
              (Acc_inv ACC (clear_n_decrease n Hne))
    end.
End ClearNOnesInt.

(** [clear_n_ones_int] agrees with [clear_n_ones] on valid inputs.
    This bridges the fast extraction path with the proof-facing nat version. *)
Lemma clear_n_ones_int_eq : forall (word n : int),
  (0 <= to_Z n)%Z ->
  clear_n_ones_int word n (lt_wf _) = clear_n_ones word (Z.to_nat (to_Z n)).
Proof.
  enough (H : forall m word n (acc : Acc lt (to_nat n)),
    to_nat n = m -> (0 <= to_Z n)%Z ->
    clear_n_ones_int word n acc = clear_n_ones word m).
  { intros. apply H; auto. }
  induction m as [|m' IH]; intros word n acc Hm Hnn.
  - (* m = 0, so n = 0 *)
    assert (Hn0 : to_Z n = 0%Z).
    { unfold to_nat in Hm. destruct (to_Z n) eqn:E; simpl in Hm; lia. }
    assert (Heq : n = 0) by (apply to_Z_inj; exact Hn0). subst n.
    destruct acc as [acc']. simpl.
    destruct (int_eq_dec 0 0) as [_|Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
  - (* m = S m' *)
    assert (Hn_pos : (0 < to_Z n)%Z).
    { unfold to_nat in Hm. destruct (to_Z n) eqn:E; simpl in Hm; lia. }
    destruct acc as [acc']. simpl.
    destruct (int_eq_dec n 0) as [Heq|Hne].
    + rewrite Heq in Hn_pos. change (to_Z 0) with 0%Z in Hn_pos. lia.
    + apply IH.
      * unfold to_nat in *. rewrite sub_spec.
        pose proof (to_Z_bounded n) as Hb.
        change (to_Z 1) with 1%Z.
        change Uint63Axioms.wB with (2^63)%Z in *.
        rewrite Z.mod_small by lia.
        destruct (to_Z n) eqn:En; try lia. simpl in *.
        destruct p; simpl in *; lia.
      * rewrite sub_spec. pose proof (to_Z_bounded n) as Hb.
        change (to_Z 1) with 1%Z.
        change Uint63Axioms.wB with (2^63)%Z in *.
        rewrite Z.mod_small by lia. lia.
Qed.

(** Select: find position of the [target]-th one bit (0-indexed). *)
Fixpoint bv_select_aux (bv : array int) (remaining w_idx : int)
    (fuel : nat) : int :=
  match fuel with
  | O => 0
  | S fuel' =>
      let word := bv.[w_idx] in
      let pc := popcount word in
      if ltb remaining pc then
        add (mul w_idx wbits)
            (tail0 (clear_n_ones word (Z.to_nat (to_Z remaining))))
      else
        bv_select_aux bv (sub remaining pc) (add w_idx 1) fuel'
  end.

Definition bv_select (bv : array int) (target : int) : int :=
  bv_select_aux bv target 0 (Z.to_nat (to_Z (length bv))).

(** Bundled predicate: a bitvector array agrees with a bool list. *)
Record bv_agreement (bv : array int) (bv_list : list bool) : Prop := mk_bva {
  bva_agree : forall i, (i < List.length bv_list)%nat ->
    bv_get bv (of_nat i) = List.nth i bv_list false;
  bva_zero  : forall i,
    (List.length bv_list <= i < to_nat (length bv) * 63)%nat ->
    bv_get bv (of_nat i) = false;
  bva_covers : (List.length bv_list <= to_nat (length bv) * 63)%nat;
  bva_overflow : (to_Z (length bv) * 63 < wB)%Z;
}.

(* ================================================================= *)
(* Part 3: Encoding                                                    *)
(* ================================================================= *)

Record ef63 := mk_ef63 {
  ef63_lower      : array int;
  ef63_upper      : array int;
  ef63_l          : int;
  ef63_n          : int;
  ef63_upper_bits : int;            (* total bit count in upper bv *)
  ef63_cum_popcnt : array int;      (* cum_popcnt[w] = ones in words 0..w-1 *)
  ef63_sel1       : array int;      (* sel1[k] = word containing (k*K)-th one *)
  ef63_sel0       : array int;      (* sel0[k] = word containing (k*K)-th zero *)
}.

(** Fill the lower-bits array. *)
Fixpoint fill_lower (vals : list int) (mask : int) (arr : array int)
    (i : nat) : array int :=
  match vals with
  | [] => arr
  | x :: vals' =>
      fill_lower vals' mask (arr.[of_Z (Z.of_nat i) <- x land mask]) (S i)
  end.

(** Fill the upper bitvector (unary-coded gaps). *)
Fixpoint fill_upper (vals : list int) (l : int) (bv : array int)
    (pos prev : int) : array int :=
  match vals with
  | [] => bv
  | x :: vals' =>
      let u := x >> l in
      let new_pos := add pos (sub u prev) in
      fill_upper vals' l (bv_set bv new_pos) (add new_pos 1) u
  end.

Definition sampling_period : int := 512.

(** Build cumulative popcount: [cum_popcnt[w] = ones in words 0..w-1]. *)
Fixpoint build_cum_popcnt_aux (upper acc : array int) (w cum : int)
    (fuel : nat) : array int :=
  match fuel with
  | O => acc
  | S fuel' =>
      let new_cum := add cum (popcount upper.[w]) in
      build_cum_popcnt_aux upper (acc.[add w 1 <- new_cum]) (add w 1) new_cum fuel'
  end.

Definition build_cum_popcnt (upper : array int) : array int :=
  build_cum_popcnt_aux upper (make (add (length upper) 1) 0) 0 0
    (Z.to_nat (to_Z (length upper))).

(** Build [sel1]: [sel1[k] = word containing the (k*K)-th one]. *)
Fixpoint build_sel1_aux (cum_popcnt sel : array int) (w next nw n_sel : int)
    (fuel : nat) : array int :=
  match fuel with
  | O => sel
  | S fuel' =>
      if orb (negb (ltb w nw)) (negb (ltb next n_sel)) then sel
      else if ltb (mul next sampling_period) (cum_popcnt.[add w 1]) then
        build_sel1_aux cum_popcnt (sel.[next <- w]) w (add next 1) nw n_sel fuel'
      else
        build_sel1_aux cum_popcnt sel (add w 1) next nw n_sel fuel'
  end.

(** Build [sel0]: [sel0[k] = word containing the (k*K)-th zero]. *)
Fixpoint build_sel0_aux (cum_popcnt sel : array int) (w next nw n_sel upper_bits : int)
    (fuel : nat) : array int :=
  match fuel with
  | O => sel
  | S fuel' =>
      if orb (negb (ltb w nw)) (negb (ltb next n_sel)) then sel
      else
        let cum_zeros :=
          if eqb (add w 1) nw then
            sub upper_bits (cum_popcnt.[add w 1])
          else
            sub (mul (add w 1) wbits) (cum_popcnt.[add w 1]) in
        if ltb (mul next sampling_period) cum_zeros then
          build_sel0_aux cum_popcnt (sel.[next <- w]) w (add next 1) nw n_sel upper_bits fuel'
        else
          build_sel0_aux cum_popcnt sel (add w 1) next nw n_sel upper_bits fuel'
  end.

Definition encode63 (U : int) (vals : list int) : ef63 :=
  let n_nat := List.length vals in
  let n := of_Z (Z.of_nat n_nat) in
  let l := if eqb n 0 then 0 else ilog2_63 (U / n) in
  let mask := sub (1 << l) 1 in
  let lower := fill_lower vals mask (make n 0) 0 in
  let max_upper :=
    match vals with
    | [] => 0
    | _ => (List.last vals 0) >> l
    end in
  let upper_words := add (div (add n max_upper) wbits) 1 in
  let upper := fill_upper vals l (make upper_words 0) 0 0 in
  let upper_bits := add (add n max_upper) 1 in
  let cum_popcnt := build_cum_popcnt upper in
  let nw := length upper in
  let total_ones := cum_popcnt.[nw] in
  let total_zeros := sub upper_bits total_ones in
  let n_sel1 := div (add total_ones (sub sampling_period 1)) sampling_period in
  let n_sel0 := div (add total_zeros (sub sampling_period 1)) sampling_period in
  let sel1_size := if eqb n_sel1 0 then 1 else n_sel1 in
  let sel0_size := if eqb n_sel0 0 then 1 else n_sel0 in
  let sel1 := build_sel1_aux cum_popcnt (make sel1_size 0) 0 0 nw n_sel1
    (Z.to_nat (to_Z (add nw n_sel1))) in
  let sel0 := build_sel0_aux cum_popcnt (make sel0_size 0) 0 0 nw n_sel0 upper_bits
    (Z.to_nat (to_Z (add nw n_sel0))) in
  mk_ef63 lower upper l n upper_bits cum_popcnt sel1 sel0.

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
(* Part 4b: Fast operations using sampling indices                     *)
(*                                                                     *)
(* Following Leroy, "Well-founded recursion done right" (CoqPL 2024,  *)
(* https://xavierleroy.org/publi/wf-recursion.pdf):                   *)
(* recursive functions are defined by structural induction on [Acc]    *)
(* (accessibility) proofs. Since [Acc] has sort [Prop], extraction     *)
(* erases it entirely, producing clean OCaml code — no [nat] fuel,    *)
(* no [sigT] tuple packing, no closure dispatch.                       *)
(*                                                                     *)
(* Non-changing arguments live in [Section] variables so they become   *)
(* curried OCaml parameters (not packed into tuples).                  *)
(*                                                                     *)
(* Decrease obligations are proved with appropriate preconditions.     *)
(* They ensure totality of the extracted functions on valid inputs.    *)
(* Fixpoints that scan arrays include bounds checks (returning 0 for  *)
(* out-of-bounds, dead code on valid inputs) to supply the proofs.    *)
(*                                                                     *)
(* See also:                                                           *)
(*   Letouzey, "Extraction in Coq: an Overview", CiE 2008            *)
(*   Monniaux & Boulme, "The CompCert Verified Compiler TCB", ESOP 22 *)
(*   Forster, Sozeau, Tabareau, "Verified Extraction", PLDI 2024      *)
(* ================================================================= *)

(** ** Select with sampling (O(1) via [sel1]) *)

Section BvSelectFast.
  Variable bv : array int.

  Let measure (w_idx : int) : nat :=
    (Z.to_nat (to_Z (length bv)) - Z.to_nat (to_Z w_idx))%nat.

  Lemma bv_sel_decrease : forall w_idx : int,
    (to_Z w_idx < to_Z (length bv))%Z ->
    (measure (add w_idx 1) < measure w_idx)%nat.
  Proof.
    intros w_idx Hw. unfold measure.
    pose proof (to_Z_bounded w_idx) as Hb.
    pose proof (to_Z_bounded (length bv)) as Hlen.
    change Uint63Axioms.wB with (2^63)%Z in *.
    assert (Hadd : to_Z (add w_idx 1) = (to_Z w_idx + 1)%Z).
    { rewrite add_spec. change (to_Z 1) with 1%Z.
      change Uint63Axioms.wB with (2^63)%Z.
      rewrite Z.mod_small; [lia | lia]. }
    rewrite Hadd.
    rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. lia.
  Qed.

  Fixpoint bv_select_aux_wf (remaining w_idx : int)
      (ACC : Acc lt (measure w_idx)) {struct ACC} : int :=
    match ltb w_idx (length bv) as b
      return (ltb w_idx (length bv) = b -> int) with
    | false => fun _ => 0
    | true => fun Hlt =>
        let word := bv.[w_idx] in
        let pc := popcount word in
        if ltb remaining pc then
          add (mul w_idx wbits)
              (tail0 (clear_n_ones_int word remaining (lt_wf _)))
        else
          bv_select_aux_wf (sub remaining pc) (add w_idx 1)
            (Acc_inv ACC (bv_sel_decrease w_idx
               (proj1 (ltb_spec _ _) Hlt)))
    end eq_refl.
End BvSelectFast.

Definition bv_select_fast (enc : ef63) (target : int) : int :=
  let start := (ef63_sel1 enc).[target / sampling_period] in
  let remaining := sub target (ef63_cum_popcnt enc).[start] in
  bv_select_aux_wf (ef63_upper enc) remaining start (lt_wf _).

(** O(1) access using fast select. *)
Definition access63_fast (enc : ef63) (i : int) : int :=
  let pos := bv_select_fast enc i in
  let upper_val := sub pos i in
  (upper_val << ef63_l enc) lor ((ef63_lower enc).[i]).

(** ** Linear-scan decode (O(n)) *)

Section DecodeScan.
  Variable enc : ef63.

  Let measure (elem_idx w_idx : int) : nat :=
    (Z.to_nat (to_Z (ef63_n enc) - to_Z elem_idx) +
     Z.to_nat (to_Z (length (ef63_upper enc)) - to_Z w_idx))%nat.

  Lemma decode_decrease_w : forall elem_idx w_idx : int,
    to_Z elem_idx < to_Z (ef63_n enc) ->
    to_Z w_idx < to_Z (length (ef63_upper enc)) ->
    (measure elem_idx (add w_idx 1) < measure elem_idx w_idx)%nat.
  Proof.
    intros elem_idx w_idx Hi Hw. unfold measure.
    pose proof (to_Z_bounded w_idx) as Hbw.
    pose proof (to_Z_bounded (length (ef63_upper enc))) as Hlen.
    change Uint63Axioms.wB with (2^63)%Z in *.
    assert (Hadd : to_Z (add w_idx 1) = (to_Z w_idx + 1)%Z).
    { rewrite add_spec. change (to_Z 1) with 1%Z.
      change Uint63Axioms.wB with (2^63)%Z.
      rewrite Z.mod_small; [lia | lia]. }
    rewrite Hadd.
    enough (Z.to_nat (to_Z (length (ef63_upper enc)) - (to_Z w_idx + 1)) <
            Z.to_nat (to_Z (length (ef63_upper enc)) - to_Z w_idx))%nat by lia.
    apply Z2Nat.inj_lt; lia.
  Qed.

  Lemma decode_decrease_e : forall elem_idx w_idx : int,
    to_Z elem_idx < to_Z (ef63_n enc) ->
    (measure (add elem_idx 1) w_idx < measure elem_idx w_idx)%nat.
  Proof.
    intros elem_idx w_idx Hi. unfold measure.
    pose proof (to_Z_bounded elem_idx) as He.
    pose proof (to_Z_bounded (ef63_n enc)) as Hn.
    change Uint63Axioms.wB with (2^63)%Z in *.
    assert (Hadd : to_Z (add elem_idx 1) = (to_Z elem_idx + 1)%Z).
    { rewrite add_spec. change (to_Z 1) with 1%Z.
      change Uint63Axioms.wB with (2^63)%Z.
      rewrite Z.mod_small; [lia | lia]. }
    rewrite Hadd.
    enough (Z.to_nat (to_Z (ef63_n enc) - (to_Z elem_idx + 1)) <
            Z.to_nat (to_Z (ef63_n enc) - to_Z elem_idx))%nat by lia.
    apply Z2Nat.inj_lt; lia.
  Qed.

  Fixpoint decode63_scan (w_idx bits elem_idx : int) (result : array int)
      (ACC : Acc lt (measure elem_idx w_idx)) {struct ACC} : array int :=
    match ltb elem_idx (ef63_n enc) as b
      return (ltb elem_idx (ef63_n enc) = b -> array int) with
    | false => fun _ => result
    | true => fun Hlt =>
        if eqb bits 0 then
          match ltb w_idx (length (ef63_upper enc)) as bw
            return (ltb w_idx (length (ef63_upper enc)) = bw -> array int) with
          | false => fun _ => result
          | true => fun Hwlt =>
              let next_w := add w_idx 1 in
              decode63_scan next_w ((ef63_upper enc).[next_w]) elem_idx result
                (Acc_inv ACC (decode_decrease_w elem_idx w_idx
                   (proj1 (ltb_spec _ _) Hlt)
                   (proj1 (ltb_spec _ _) Hwlt)))
          end eq_refl
        else
          let bit_pos := tail0 bits in
          let pos := add (mul w_idx wbits) bit_pos in
          let upper_val := sub pos elem_idx in
          let v := (upper_val << ef63_l enc) lor ((ef63_lower enc).[elem_idx]) in
          decode63_scan w_idx (bits land (sub bits 1)) (add elem_idx 1)
            (result.[elem_idx <- v])
            (Acc_inv ACC (decode_decrease_e elem_idx w_idx
               (proj1 (ltb_spec _ _) Hlt)))
    end eq_refl.
End DecodeScan.

Definition decode63_fast (enc : ef63) : array int :=
  let n := ef63_n enc in
  if eqb n 0 then make 0 0
  else
    decode63_scan enc 0 ((ef63_upper enc).[0]) 0 (make n 0) (lt_wf _).

(** ** Select-zero with sampling (O(1) via [sel0]) *)

Section BvSelectZero.
  Variable upper : array int.
  Variable upper_bits : int.

  Let measure (w_idx : int) : nat :=
    (Z.to_nat (to_Z (length upper)) - Z.to_nat (to_Z w_idx))%nat.

  Lemma bv_sel0_decrease : forall w_idx : int,
    (to_Z w_idx < to_Z (length upper))%Z ->
    (measure (add w_idx 1) < measure w_idx)%nat.
  Proof.
    intros w_idx Hw. unfold measure.
    pose proof (to_Z_bounded w_idx) as Hb.
    pose proof (to_Z_bounded (length upper)) as Hlen.
    change Uint63Axioms.wB with (2^63)%Z in *.
    assert (Hadd : to_Z (add w_idx 1) = (to_Z w_idx + 1)%Z).
    { rewrite add_spec. change (to_Z 1) with 1%Z.
      change Uint63Axioms.wB with (2^63)%Z.
      rewrite Z.mod_small; [lia | lia]. }
    rewrite Hadd.
    rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. lia.
  Qed.

  Fixpoint bv_select_zero_aux (remaining w_idx : int)
      (ACC : Acc lt (measure w_idx)) {struct ACC} : int :=
    match ltb w_idx (length upper) as b
      return (ltb w_idx (length upper) = b -> int) with
    | false => fun _ => 0
    | true => fun Hlt =>
        let nw := length upper in
        let effective :=
          if ltb (add w_idx 1) nw then wbits
          else let r := upper_bits mod wbits in
               if eqb r 0 then wbits else r in
        let zeros := sub effective (popcount upper.[w_idx]) in
        if ltb remaining zeros then
          let mask := if eqb effective wbits then max_int
                      else sub (1 << effective) 1 in
          let inverted := (Uint63.lxor upper.[w_idx] max_int) land mask in
          add (mul w_idx wbits)
              (tail0 (clear_n_ones_int inverted remaining (lt_wf _)))
        else
          bv_select_zero_aux (sub remaining zeros) (add w_idx 1)
            (Acc_inv ACC (bv_sel0_decrease w_idx
               (proj1 (ltb_spec _ _) Hlt)))
    end eq_refl.
End BvSelectZero.

Definition bv_select_zero (enc : ef63) (target : int) : int :=
  let start := (ef63_sel0 enc).[target / sampling_period] in
  let cum_zeros := sub (mul start wbits) ((ef63_cum_popcnt enc).[start]) in
  let remaining := sub target cum_zeros in
  bv_select_zero_aux (ef63_upper enc) (ef63_upper_bits enc) remaining start
    (lt_wf _).

(** ** NextGEQ with select-zero jump (O(1)) *)

Section NextGEQFast.
  Variable enc : ef63.
  Variable v : int.

  Let measure (i : int) : nat :=
    (Z.to_nat (to_Z (ef63_n enc)) - Z.to_nat (to_Z i))%nat.

  Lemma next_geq_decrease : forall i : int,
    to_Z i < to_Z (ef63_n enc) ->
    (measure (add i 1) < measure i)%nat.
  Proof.
    intros i Hi. unfold measure.
    pose proof (to_Z_bounded i) as Hb.
    pose proof (to_Z_bounded (ef63_n enc)) as Hn.
    assert (Hadd : to_Z (add i 1) = (to_Z i + 1)%Z).
    { rewrite add_spec. change (to_Z 1) with 1%Z.
      change Uint63Axioms.wB with (2^63)%Z in *.
      rewrite Z.mod_small; [lia | lia]. }
    rewrite Hadd. lia.
  Qed.

  Fixpoint nextGEQ63_fast_aux (i : int)
      (ACC : Acc lt (measure i)) {struct ACC} : option int :=
    match ltb i (ef63_n enc) as b
      return (ltb i (ef63_n enc) = b -> option int) with
    | false => fun _ => None
    | true => fun Hlt =>
        let x := access63_fast enc i in
        if leb v x then Some x
        else nextGEQ63_fast_aux (add i 1)
          (Acc_inv ACC (next_geq_decrease i
             (proj1 (ltb_spec _ _) Hlt)))
    end eq_refl.
End NextGEQFast.

Definition nextGEQ63_fast (enc : ef63) (v : int) : option int :=
  let n := ef63_n enc in
  if eqb n 0 then None
  else
    let uv := v >> ef63_l enc in
    let max_upper_val := sub (ef63_upper_bits enc) n in
    if ltb max_upper_val uv then None
    else
      let start_idx :=
        if eqb uv 0 then 0
        else
          let zero_pos := bv_select_zero enc (sub uv 1) in
          sub (add zero_pos 1) uv in
      nextGEQ63_fast_aux enc v start_idx (lt_wf _).

(** Refinement predicate: an [ef63] faithfully represents an [ef_encoded]. *)
Record valid_encoding (enc63 : ef63) (encZ : ef_encoded) : Prop := mk_ve {
  ve_l : to_Z (ef63_l enc63) = ef_l encZ;
  ve_n : Z.to_nat (to_Z (ef63_n enc63)) = ef_n encZ;
  ve_lower : forall i, (i < ef_n encZ)%nat ->
    to_Z ((ef63_lower enc63).[of_Z (Z.of_nat i)]) = nth i (ef_lower encZ) 0%Z;
  ve_upper : forall j, (j < List.length (ef_upper encZ))%nat ->
    bv_get (ef63_upper enc63) (of_Z (Z.of_nat j)) = nth j (ef_upper encZ) false;
  ve_zero_tail : forall j,
    (List.length (ef_upper encZ) <= j < to_nat (PArray.length (ef63_upper enc63)) * 63)%nat ->
    bv_get (ef63_upper enc63) (of_nat j) = false;
  ve_covers :
    (List.length (ef_upper encZ) <= to_nat (PArray.length (ef63_upper enc63)) * 63)%nat;
  ve_overflow :
    (to_Z (PArray.length (ef63_upper enc63)) * 63 < wB)%Z;
  ve_l_nn : 0 <= ef_l encZ;
  ve_ones : count_occ Bool.bool_dec (ef_upper encZ) true = ef_n encZ;
  ve_lower_bnd : forall i, (i < ef_n encZ)%nat ->
    0 <= nth i (ef_lower encZ) 0%Z < 2 ^ ef_l encZ;
  ve_access_bnd : forall i, (i < ef_n encZ)%nat ->
    (0 <= access_ef encZ i < wB)%Z;
  ve_pos_ge : forall i, (i < ef_n encZ)%nat ->
    (i <= position_of_ith_one (ef_upper encZ) i)%nat;
}.

Lemma bva_of_ve : forall enc63 encZ,
  valid_encoding enc63 encZ ->
  bv_agreement (ef63_upper enc63) (ef_upper encZ).
Proof.
  intros enc63 encZ Hve.
  exact (mk_bva _ _ (ve_upper _ _ Hve) (ve_zero_tail _ _ Hve)
    (ve_covers _ _ Hve) (ve_overflow _ _ Hve)).
Qed.

(* ================================================================= *)
(* Part 5: Axioms and specification lemmas                             *)
(* ================================================================= *)

(** Count one-bits in positions [0..n) of [z], accumulator style. *)
Fixpoint Z_count_bits (z : Z) (n : nat) (acc : nat) : nat :=
  match n with
  | O => acc
  | S n' => Z_count_bits z n' (if Z.testbit z (Z.of_nat n') then S acc else acc)
  end.

(** A1: popcount counts one-bits correctly. *)
Axiom popcount_spec : forall (x : int),
  Z.of_nat (Z_count_bits (to_Z x) 63%nat 0%nat) = to_Z (popcount x).

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
Lemma fill_lower_get_out : forall vals mask arr start j,
  (forall k, (start <= k < start + List.length vals)%nat ->
    of_Z (Z.of_nat k) <> j) ->
  (fill_lower vals mask arr start).[j] = arr.[j].
Proof.
  induction vals as [|x vals' IH]; intros mask arr start j Hout.
  - reflexivity.
  - unfold fill_lower; fold fill_lower.
    rewrite IH; [|intros k Hk; apply Hout; cbn [List.length]; lia].
    rewrite get_set_other'; [reflexivity|].
    apply Hout. cbn [List.length]. lia.
Qed.

(** Helper: [fill_lower] stores [x land mask] at each index. *)
Lemma fill_lower_get_in : forall vals mask arr start i,
  (i < List.length vals)%nat ->
  (* All indices in range are distinct *)
  (forall j k, (start <= j)%nat -> (start <= k)%nat ->
    (j < start + List.length vals)%nat -> (k < start + List.length vals)%nat ->
    j <> k -> of_Z (Z.of_nat j) <> of_Z (Z.of_nat k)) ->
  (* All indices fit in the array *)
  (forall k, (start <= k < start + List.length vals)%nat ->
    (of_Z (Z.of_nat k) <? PArray.length arr)%uint63 = true) ->
  (fill_lower vals mask arr start).[of_Z (Z.of_nat (start + i))] =
    List.nth i vals 0 land mask.
Proof.
  induction vals as [|x vals' IH]; intros mask arr start i Hi Hdist Hbounds.
  - simpl in Hi. lia.
  - destruct i as [|i'].
    + (* i = 0: the value was written at position [start] *)
      change (List.nth 0 (x :: vals') 0) with x.
      rewrite Nat.add_0_r.
      unfold fill_lower at 1; fold fill_lower.
      rewrite fill_lower_get_out.
      * assert (Hb : (of_Z (Z.of_nat start) <? PArray.length arr)%uint63 = true)
          by (apply Hbounds; cbn [List.length]; lia).
        exact (get_set_same' arr (of_Z (Z.of_nat start)) (x land mask) Hb).
      * intros k Hk.
        apply Hdist; cbn [List.length] in *; lia.
    + (* i = S i': by induction on vals' starting at S start *)
      unfold fill_lower at 1; fold fill_lower.
      change (List.nth (S i') (x :: vals') 0) with (List.nth i' vals' 0).
      replace (start + S i')%nat with (S start + i')%nat by lia.
      apply IH.
      * cbn [List.length] in Hi. lia.
      * intros j k Hj Hk Hj' Hk' Hne.
        apply Hdist; cbn [List.length] in *; lia.
      * intros k Hk. rewrite length_set'. apply Hbounds. cbn [List.length] in *. lia.
Qed.

(** A4: [fill_lower] agrees with [map (lower_bits l)]. *)
Lemma fill_lower_agrees : forall vals mask arr l,
  to_Z mask = Z.ones (to_Z l) ->
  (0 <= to_Z l)%Z ->
  (Z.of_nat (List.length vals) < wB)%Z ->
  (forall k, (k < List.length vals)%nat ->
    (of_Z (Z.of_nat k) <? PArray.length arr)%uint63 = true) ->
  forall i, (i < List.length vals)%nat ->
    to_Z ((fill_lower vals mask arr 0).[of_Z (Z.of_nat i)]) =
      lower_bits (to_Z l) (to_Z (List.nth i vals 0)).
Proof.
  intros vals mask arr l Hmask Hl Hlen Hbounds i Hi.
  replace i with (0 + i)%nat by lia.
  rewrite fill_lower_get_in.
  - (* to_Z (nth i vals 0 land mask) = lower_bits ... *)
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
Lemma fill_upper_get_lt : forall vals l bv pos prev q,
  to_Z pos + Z.of_nat (List.length
    (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev))) < wB ->
  Forall (fun x => to_Z prev <= upper_value (to_Z l) (to_Z x)) vals ->
  sorted (map (fun x => upper_value (to_Z l) (to_Z x)) vals) ->
  0 <= to_Z l ->
  (forall p', to_Z pos <= to_Z p' ->
     to_Z p' < to_Z pos + Z.of_nat (List.length
       (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev))) ->
     (p' / wbits <? PArray.length bv)%uint63 = true) ->
  to_Z q < to_Z pos ->
  bv_get (fill_upper vals l bv pos prev) q = bv_get bv q.
Proof.
  induction vals as [|x vals' IH]; intros l bv pos prev q Hovf HFA Hsorted Hl Hbounds Hq.
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
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) vals')
         (upper_value (to_Z l) (to_Z x))))) as tail_len eqn:Htl_def.
    pose proof (Nat2Z.is_nonneg (List.length
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) vals')
         (upper_value (to_Z l) (to_Z x))))) as Htl_nn.
    (* Length decomposition: cons = gap + 1 + tail *)
    assert (Hlen_decomp :
      Z.of_nat (List.length
        (build_upper_aux
           (map (fun x0 => upper_value (to_Z l) (to_Z x0)) (x :: vals'))
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
                     upper_value (to_Z l) (to_Z x0)) vals').
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

(** Helper: [fill_upper] doesn't touch positions [>= pos + len(build_upper)]. *)
Lemma fill_upper_get_ge : forall vals l bv pos prev q,
  to_Z pos + Z.of_nat (List.length
    (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev))) < wB ->
  Forall (fun x => to_Z prev <= upper_value (to_Z l) (to_Z x)) vals ->
  sorted (map (fun x => upper_value (to_Z l) (to_Z x)) vals) ->
  0 <= to_Z l ->
  (forall p', to_Z pos <= to_Z p' ->
     to_Z p' < to_Z pos + Z.of_nat (List.length
       (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev))) ->
     (p' / wbits <? PArray.length bv)%uint63 = true) ->
  (to_Z pos + Z.of_nat (List.length
    (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev))) <= to_Z q)%Z ->
  bv_get (fill_upper vals l bv pos prev) q = bv_get bv q.
Proof.
  induction vals as [|x vals' IH]; intros l bv pos prev q Hovf HFA Hsorted Hl Hbounds Hq.
  - reflexivity.
  - rewrite Forall_cons_iff in HFA; destruct HFA as [Hhead HFA_tail].
    unfold sorted in Hsorted; cbn [map] in Hsorted.
    inversion Hsorted as [|? ? Hsorted_tail HFA_ge]; subst.
    pose proof (to_Z_bounded pos) as Hpos_bnd.
    pose proof (to_Z_bounded prev) as Hprev_bnd.
    pose proof (to_Z_bounded (x >> l)) as Hu_bnd.
    assert (Hu_eq : to_Z (x >> l) = upper_value (to_Z l) (to_Z x))
      by (apply lsr_upper_value; exact Hl).
    assert (Hprev_le_u : to_Z prev <= to_Z (x >> l))
      by (rewrite Hu_eq; exact Hhead).
    remember (Z.of_nat (List.length
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) vals')
         (upper_value (to_Z l) (to_Z x))))) as tail_len eqn:Htl_def.
    pose proof (Nat2Z.is_nonneg (List.length
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) vals')
         (upper_value (to_Z l) (to_Z x))))) as Htl_nn.
    assert (Hlen_decomp :
      Z.of_nat (List.length
        (build_upper_aux
           (map (fun x0 => upper_value (to_Z l) (to_Z x0)) (x :: vals'))
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
    assert (Hnp : to_Z (add pos (sub (x >> l) prev)) =
                  (to_Z pos + (to_Z (x >> l) - to_Z prev))%Z).
    { rewrite Uint63.add_spec, Hgap. rewrite Z.mod_small; [lia|].
      change Uint63.wB with (2^63)%Z; unfold wB in *; lia. }
    assert (Hnp1 : to_Z (add (add pos (sub (x >> l) prev)) 1) =
                   (to_Z pos + (to_Z (x >> l) - to_Z prev) + 1)%Z).
    { rewrite Uint63.add_spec; change (to_Z 1) with 1%Z.
      rewrite Hnp. rewrite Z.mod_small; [lia|].
      change Uint63.wB with (2^63)%Z; unfold wB in *; lia. }
    assert (HFA' : Forall (fun x0 => to_Z (x >> l) <=
                     upper_value (to_Z l) (to_Z x0)) vals').
    { rewrite Hu_eq. apply Forall_map. exact HFA_ge. }
    assert (Hlen_bv : PArray.length (bv_set bv (add pos (sub (x >> l) prev))) =
                      PArray.length bv)
      by (unfold bv_set; apply length_set').
    cbn [fill_upper].
    transitivity (bv_get (bv_set bv (add pos (sub (x >> l) prev))) q).
    + apply IH.
      * rewrite Hnp1, Hu_eq, <- Htl_def.
        rewrite Hlen_decomp in Hovf. unfold wB in *. lia.
      * exact HFA'.
      * exact Hsorted_tail.
      * exact Hl.
      * intros p' Hp'1 Hp'2. rewrite Hlen_bv.
        rewrite Hu_eq, <- Htl_def in Hp'2.
        apply Hbounds.
        -- rewrite Hnp1 in Hp'1; lia.
        -- rewrite Hlen_decomp. rewrite Hnp1 in Hp'1. lia.
      * rewrite Hnp1, Hu_eq, <- Htl_def. rewrite Hlen_decomp in Hq. lia.
    + apply bv_get_bv_set_other.
      * intro Heq.
        assert (Hc : to_Z (add pos (sub (x >> l) prev)) = to_Z q)
          by (rewrite Heq; reflexivity).
        rewrite Hnp in Hc. rewrite Hlen_decomp in Hq. lia.
      * apply Hbounds; [rewrite Hnp; lia|].
        rewrite Hlen_decomp. rewrite Hnp. lia.
Qed.

(** Generalized [fill_upper] agreement — induction-ready version. *)
Lemma fill_upper_agrees_gen : forall vals l bv pos prev,
  0 <= to_Z l ->
  (* all positions fit in the bitvector: *)
  (forall p, to_Z pos <= to_Z p ->
     to_Z p < to_Z pos + Z.of_nat (List.length
       (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev))) ->
     (p / wbits <? PArray.length bv)%uint63 = true) ->
  (* no overflow: *)
  (to_Z pos + Z.of_nat (List.length
     (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev))) < wB)%Z ->
  (* upper values are >= prev: *)
  Forall (fun x => to_Z prev <= upper_value (to_Z l) (to_Z x)) vals ->
  (* sorted upper values: *)
  sorted (map (fun x => upper_value (to_Z l) (to_Z x)) vals) ->
  (* positions < pos in bv are correct: *)
  (forall i, (i < List.length
     (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev)))%nat ->
    bv_get bv (of_Z (to_Z pos + Z.of_nat i)) = false) ->
  forall i, (i < List.length
     (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev)))%nat ->
    bv_get (fill_upper vals l bv pos prev) (of_Z (to_Z pos + Z.of_nat i)) =
      List.nth i (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) (to_Z prev)) false.
Proof.
  induction vals as [|x vals' IH];
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
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) vals')
         (upper_value (to_Z l) (to_Z x))))) as tail_len eqn:Htl_def.
    pose proof (Nat2Z.is_nonneg (List.length
      (build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) vals')
         (upper_value (to_Z l) (to_Z x))))) as Htl_nn.
    assert (Hlen_decomp :
      Z.of_nat (List.length
        (build_upper_aux
           (map (fun x0 => upper_value (to_Z l) (to_Z x0)) (x :: vals'))
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
                     upper_value (to_Z l) (to_Z x0)) vals').
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
              :: map (fun x0 => upper_value (to_Z l) (to_Z x0)) vals') (to_Z prev))
      with (repeat false (Z.to_nat (upper_value (to_Z l) (to_Z x) - to_Z prev))
            ++ [true]
            ++ build_upper_aux (map (fun x0 => upper_value (to_Z l) (to_Z x0)) vals')
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
Lemma fill_upper_agrees : forall vals l bv,
  0 <= to_Z l ->
  (* all upper values are nonneg and sorted *)
  all_nonneg (to_Z_list vals) ->
  sorted (to_Z_list vals) ->
  (* positions fit in the bitvector: *)
  (forall p, 0 <= to_Z p ->
     to_Z p < Z.of_nat (List.length
       (build_upper (map (fun x => upper_value (to_Z l) (to_Z x)) vals))) ->
     (p / wbits <? PArray.length bv)%uint63 = true) ->
  (* no overflow: *)
  (Z.of_nat (List.length
     (build_upper (map (fun x => upper_value (to_Z l) (to_Z x)) vals))) < wB)%Z ->
  (* initial bv is zero: *)
  (forall q, bv_get bv q = false) ->
  let uppers := map (fun x => upper_value (to_Z l) (to_Z x)) vals in
  let bv_list := build_upper uppers in
  forall i, (i < List.length bv_list)%nat ->
    bv_get (fill_upper vals l bv 0 0) (of_Z (Z.of_nat i)) =
      List.nth i bv_list false.
Proof.
  intros vals l bv Hl Hnn Hsorted Hfit Hno_ovf Hzero uppers bv_list i Hi.
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
    induction vals as [|x0 xs0 IHx]; [constructor|].
    simpl map in *. inversion Hsorted as [|? ? Hs' HF]; subst.
    constructor.
    + apply IHx. exact Hs'.
    + rewrite Forall_map in HF |- *.
      revert HF. apply Forall_impl.
      intros a Ha. apply upper_value_mono; lia.
  - intros j Hj. apply Hzero.
  - exact Hi.
Qed.

(* ================================================================= *)
(* Part 5b: bv_select proof infrastructure                            *)
(* ================================================================= *)

(** Z-level: for odd q and n >= 1, subtracting 1 doesn't change
    the quotient by 2^n. *)
Lemma div_odd_sub1 : forall q n,
  (q mod 2 = 1)%Z -> (1 <= n)%Z ->
  ((q - 1) / 2 ^ n = q / 2 ^ n)%Z.
Proof.
  intros q n Hodd Hn.
  assert (Hp : (0 < 2 ^ n)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : (2 | 2 ^ n)%Z).
  { exists (2 ^ (n - 1))%Z. rewrite Z.mul_comm.
    change 2%Z with (2 ^ 1)%Z. rewrite <- Z.pow_add_r by lia.
    replace (1 + (n - 1))%Z with n by lia. reflexivity. }
  symmetry.
  apply (Z.div_unique (q - 1) (2 ^ n) (q / 2 ^ n) (q mod 2 ^ n - 1)).
  - left. split.
    + assert (Hqmod_ne0 : (q mod 2 ^ n <> 0)%Z).
      { intro Habs.
        assert (H2 : (q mod 2 ^ n mod 2 = 0)%Z) by (rewrite Habs; reflexivity).
        rewrite Z.mod_mod_divide in H2 by exact Hdiv. lia. }
      pose proof (Z.mod_pos_bound q (2 ^ n) ltac:(lia)). lia.
    + pose proof (Z.mod_pos_bound q (2 ^ n) ltac:(lia)). lia.
  - pose proof (Z.div_mod q (2 ^ n) ltac:(lia)). lia.
Qed.

(** Z-level: [Z.land x (x-1)] clears the lowest set bit. *)
Lemma kernighan_clearbit : forall x k,
  (0 < x)%Z -> (0 <= k)%Z ->
  Z.testbit x k = true ->
  (forall j, (0 <= j < k)%Z -> Z.testbit x j = false) ->
  Z.land x (x - 1) = Z.clearbit x k.
Proof.
  intros x k Hpos Hk Hbit Hbelow.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.clearbit_spec', Z.ldiff_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.testbit x i) eqn:Hxi; simpl.
  2: reflexivity.
  assert (Hik : i = k \/ k < i).
  { destruct (Z.eq_dec i k); [left; auto | right].
    destruct (Z.lt_ge_cases i k);
      [exfalso; rewrite Hbelow in Hxi; [discriminate | lia] | lia]. }
  assert (Hp2k : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hxmod : (x mod 2 ^ k = 0)%Z).
  { rewrite <- Z.land_ones by lia.
    apply Z.bits_inj'. intros j Hj.
    rewrite Z.land_spec, Z.bits_0, Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec j k);
      [rewrite andb_true_r; apply Hbelow; lia
      |rewrite andb_false_r; reflexivity]. }
  set (q := (x / 2 ^ k)%Z).
  assert (Hx_eq : x = (2 ^ k * q)%Z)
    by (apply Z.div_exact in Hxmod; [exact Hxmod | lia]).
  assert (Hq_odd : (q mod 2 = 1)%Z)
    by (apply Z.testbit_true in Hbit; [|lia];
        change ((x / 2 ^ k) mod 2 = 1)%Z in Hbit; fold q in Hbit;
        exact Hbit).
  assert (Hq_pos : (0 < q)%Z).
  { rewrite Hx_eq in Hpos. apply Z.lt_0_mul in Hpos.
    destruct Hpos; lia. }
  assert (Hsub : (x - 1 = (q - 1) * 2 ^ k + (2 ^ k - 1))%Z) by lia.
  destruct Hik as [<- | Hgt].
  - rewrite Z.eqb_refl. simpl.
    apply Z.testbit_false; [lia|].
    rewrite Hsub.
    rewrite Z_div_plus_full_l by lia.
    rewrite Z.div_small by lia.
    rewrite Z.add_0_r, Zminus_mod, Hq_odd. simpl. reflexivity.
  - assert (Hne : (k =? i)%Z = false) by (apply Z.eqb_neq; lia).
    rewrite Hne. simpl.
    apply Z.testbit_true; [lia|].
    apply Z.testbit_true in Hxi; [|lia].
    rewrite Hx_eq in Hxi.
    replace (2 ^ i)%Z with (2 ^ k * 2 ^ (i - k))%Z in Hxi.
    2: { change 2%Z with (2 ^ 1)%Z. rewrite <- Z.pow_add_r by lia.
         f_equal. lia. }
    rewrite Z.div_mul_cancel_l in Hxi
      by (try apply Z.pow_nonzero; lia).
    rewrite Hsub.
    replace (2 ^ i)%Z with (2 ^ k * 2 ^ (i - k))%Z.
    2: { change 2%Z with (2 ^ 1)%Z. rewrite <- Z.pow_add_r by lia.
         f_equal. lia. }
    rewrite <- Z.div_div by lia.
    rewrite Z_div_plus_full_l by lia.
    rewrite Z.div_small with (a := (2 ^ k - 1)%Z) by lia.
    rewrite Z.add_0_r.
    rewrite div_odd_sub1 by (exact Hq_odd || lia).
    exact Hxi.
Qed.

(** [tail0] characterization: it gives the position of the lowest set bit. *)
Lemma tail0_lowest_bit : forall x : int,
  (0 < to_Z x)%Z ->
  Z.testbit (to_Z x) (to_Z (tail0 x)) = true /\
  (forall k, (0 <= k < to_Z (tail0 x))%Z -> Z.testbit (to_Z x) k = false).
Proof.
  intros x Hpos.
  destruct (tail0_spec x Hpos) as [y [Hy Hfact]].
  set (t := to_Z (tail0 x)) in *.
  assert (Ht_nn : (0 <= t)%Z) by (pose proof (to_Z_bounded (tail0 x)); lia).
  split.
  - (* bit t is set *)
    apply Z.testbit_true; [lia|].
    rewrite Hfact.
    rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
    rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. reflexivity.
  - (* bits below t are clear *)
    intros k Hk.
    apply Z.testbit_false; [lia|].
    rewrite Hfact.
    replace t with (k + (t - k))%Z by lia.
    rewrite Z.pow_add_r by lia.
    rewrite (Z.mul_comm (2 ^ k) (2 ^ (t - k))).
    rewrite Z.mul_assoc.
    rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
    replace (t - k)%Z with (1 + (t - k - 1))%Z by lia.
    rewrite Z.pow_add_r by lia. simpl (2 ^ 1)%Z.
    change (Z.pow_pos 2 1) with 2%Z.
    rewrite (Z.mul_comm 2 (2 ^ (t - k - 1))).
    rewrite Z.mul_assoc.
    rewrite Z_mod_mult. reflexivity.
Qed.

(** Count one-bits in positions [0..j) of [x]. *)
Fixpoint Z_count_ones (j : nat) (x : Z) : nat :=
  match j with
  | O => O
  | S j' => (if Z.testbit x (Z.of_nat j') then S else id) (Z_count_ones j' x)
  end.

(** The accumulator-based [Z_count_bits] equals [Z_count_ones]. *)
Lemma Z_count_bits_eq : forall j z acc,
  Z_count_bits z j acc = (Z_count_ones j z + acc)%nat.
Proof.
  induction j as [|j' IH]; intros z acc; simpl.
  - lia.
  - rewrite IH. destruct (Z.testbit z (Z.of_nat j')); unfold id; lia.
Qed.

Local Open Scope Z_scope.

Lemma Z_count_ones_S : forall j x,
  Z.of_nat (Z_count_ones (S j) x) =
  Z.of_nat (Z_count_ones j x) + (if Z.testbit x (Z.of_nat j) then 1 else 0).
Proof.
  intros; simpl; destruct (Z.testbit x (Z.of_nat j)).
    rewrite Nat2Z.inj_succ; lia.
    unfold id; lia.
Qed.

Lemma Z_count_ones_step : forall j' x,
  Z.of_nat (Z_count_ones (S j') x) =
  (Z.of_nat (Z_count_ones j' x) + (if Z.testbit x (Z.of_nat j') then 1 else 0))%Z.
Proof.
  intros; simpl; destruct (Z.testbit x (Z.of_nat j')).
    rewrite Nat2Z.inj_succ; lia.
    unfold id; lia.
Qed.
(** Popcount restated: [popcount x = Z_count_ones 63 (to_Z x)]. *)
Lemma popcount_count_ones : forall x : int,
  Z.of_nat (Z_count_ones 63 (to_Z x)) = to_Z (popcount x).
Proof.
  intros.
  rewrite <- popcount_spec.
  f_equal.
  rewrite Z_count_bits_eq. lia.
Qed.

(** Lift [kernighan_clearbit] to Int63: [x land (x-1)] at Int63 level
    clears the lowest set bit, provided no overflow. *)
Lemma kernighan_clears_lowest_bit63 : forall (x : int),
  (0 < to_Z x)%Z ->
  to_Z (x land (x - 1)) = Z.land (to_Z x) (to_Z x - 1).
Proof.
  intros x Hpos.
  rewrite land_spec'.
  rewrite sub_spec.
  change (to_Z 1) with 1%Z.
  rewrite Z.mod_small.
  - reflexivity.
  - pose proof (to_Z_bounded x). lia.
Qed.

(** Bits other than [k] are unchanged by [clearbit]. *)
Lemma Z_count_ones_clearbit_other : forall j x k,
  (j <= Z.to_nat k)%nat ->
  Z_count_ones j (Z.clearbit x k) = Z_count_ones j x.
Proof.
  induction j as [|j' IH]; intros x k Hle; simpl.
  - reflexivity.
  - rewrite Z.clearbit_neq by lia. rewrite IH by lia. reflexivity.
Qed.

(** [Z_count_ones] decreases by 1 when the lowest set bit is cleared. *)
Lemma Z_count_ones_clearbit : forall j x k,
  (0 <= k)%Z ->
  (Z.to_nat k < j)%nat ->
  Z.testbit x k = true ->
  (forall i, (0 <= i < k)%Z -> Z.testbit x i = false) ->
  Z_count_ones j (Z.clearbit x k) = Nat.pred (Z_count_ones j x).
Proof.
  induction j as [|j' IH]; intros x k Hk Hlt Hbit Hbelow.
  - lia.
  - simpl.
    destruct (Nat.eq_dec (Z.to_nat k) j') as [Heq | Hneq].
    + (* k = j' *)
      assert (Hk_eq : k = Z.of_nat j') by lia.
      subst k. rewrite Z.clearbit_eq. rewrite Hbit.
      rewrite Z_count_ones_clearbit_other by lia.
      unfold id. lia.
    + (* k < j' *)
      assert (Hlt' : (Z.to_nat k < j')%nat) by lia.
      rewrite Z.clearbit_neq by lia.
      rewrite IH by assumption.
      assert (Hpos : (0 < Z_count_ones j' x)%nat).
      { clear IH Hlt Hneq.
        induction j' as [|j'' IH2].
        - lia.
        - simpl. destruct (Nat.eq_dec (Z.to_nat k) j'') as [Heq2|Hneq2].
          + assert (k = Z.of_nat j'') by lia. subst k.
            rewrite Hbit. lia.
          + assert ((Z.to_nat k < j'')%nat) by lia.
            specialize (IH2 H). destruct (Z.testbit x (Z.of_nat j'')); unfold id; lia. }
      destruct (Z.testbit x (Z.of_nat j')); unfold id; lia.
Qed.

(** [clear_n_ones word n] at the Z level clears the lowest [n] one-bits. *)
Lemma clear_n_ones_spec : forall n (word : int),
  (0 <= to_Z word)%Z ->
  (n <= Z_count_ones 63 (to_Z word))%nat ->
  Z_count_ones 63 (to_Z (clear_n_ones word n)) =
    (Z_count_ones 63 (to_Z word) - n)%nat /\
  (forall k, (0 <= k)%Z ->
    Z.testbit (to_Z (clear_n_ones word n)) k = true ->
    Z.testbit (to_Z word) k = true).
Proof.
  induction n as [|n' IH]; intros word Hnn Hle.
  - simpl. split. + lia. + auto.
  - change (clear_n_ones word (S n')) with (clear_n_ones (word land (word - 1)) n').
    set (word' := word land (word - 1)).
    assert (Hpos : (0 < to_Z word)%Z).
    { destruct (Z.eq_dec (to_Z word) 0) as [Hz|Hnz]; [|lia].
      exfalso. assert (Hc : Z_count_ones 63 (to_Z word) = 0%nat)
        by (rewrite Hz; reflexivity). lia. }
    pose proof (tail0_lowest_bit word Hpos) as [Htbit Htbelow].
    set (t := to_Z (tail0 word)) in *.
    assert (Ht_nn : (0 <= t)%Z) by (pose proof (to_Z_bounded (tail0 word)); lia).
    assert (Hword'Z : to_Z word' = Z.clearbit (to_Z word) t).
    { unfold word'. rewrite kernighan_clears_lowest_bit63 by exact Hpos.
      apply kernighan_clearbit; assumption. }
    assert (Ht_lt63 : (Z.to_nat t < 63)%nat).
    { enough (t < 63)%Z by lia.
      destruct (Z_lt_dec t 63) as [|Hge]; [assumption|exfalso].
      pose proof (to_Z_bounded word) as Hb.
      assert (Hlog : (Z.log2 (to_Z word) < 63)%Z).
      { apply Z.log2_lt_pow2; [lia|].
        change Uint63Axioms.wB with (2 ^ 63)%Z in Hb. lia. }
      assert (Hf : Z.testbit (to_Z word) t = false).
      { apply Z.bits_above_log2; lia. }
      rewrite Hf in Htbit. discriminate. }
    assert (Hcount' : Z_count_ones 63 (to_Z word') = Nat.pred (Z_count_ones 63 (to_Z word))).
    { rewrite Hword'Z. apply Z_count_ones_clearbit; assumption. }
    assert (Hnn' : (0 <= to_Z word')%Z) by (pose proof (to_Z_bounded word'); lia).
    assert (Hle' : (n' <= Z_count_ones 63 (to_Z word'))%nat) by lia.
    destruct (IH word' Hnn' Hle') as [IHcount IHbits].
    split.
    + rewrite IHcount. lia.
    + intros k Hk0 Hkbit. apply IHbits in Hkbit; [|exact Hk0].
      rewrite Hword'Z in Hkbit.
      rewrite Z.clearbit_spec' in Hkbit.
      rewrite Z.ldiff_spec in Hkbit.
      destruct (Z.testbit (to_Z word) k); simpl in Hkbit; [reflexivity | discriminate].
Qed.

(** The position found by [tail0 (clear_n_ones word n)] is the
    position of the [n]-th one-bit in [word]. *)
Lemma select_word_correct : forall n (word : int),
  (0 < to_Z word)%Z ->
  (n < Z_count_ones 63 (to_Z word))%nat ->
  Z.testbit (to_Z word) (to_Z (tail0 (clear_n_ones word n))) = true /\
  Z_count_ones (Z.to_nat (to_Z (tail0 (clear_n_ones word n)))) (to_Z word) = n.
Proof.
  induction n as [|n' IH]; intros word Hpos Hn.
  - (* n = 0 *)
    simpl.
    pose proof (tail0_lowest_bit word Hpos) as [Htbit Htbelow].
    split; [exact Htbit|].
    set (p := to_Z (tail0 word)) in *.
    assert (Hp_nn : (0 <= p)%Z) by (pose proof (to_Z_bounded (tail0 word)); lia).
    enough (H : forall m, (m <= Z.to_nat p)%nat -> Z_count_ones m (to_Z word) = 0%nat)
      by (apply H; lia).
    induction m as [|m' IHm].
    + intros _. reflexivity.
    + intros Hm. simpl. replace (Z.testbit (to_Z word) (Z.of_nat m')) with false.
      * unfold id. apply IHm. lia.
      * symmetry. apply Htbelow. lia.
  - (* n = S n' *)
    change (clear_n_ones word (S n')) with (clear_n_ones (word land (word - 1)) n').
    set (word1 := word land (word - 1)).
    pose proof (tail0_lowest_bit word Hpos) as [Ht0bit Ht0below].
    set (t0 := to_Z (tail0 word)) in *.
    assert (Ht0_nn : (0 <= t0)%Z) by (pose proof (to_Z_bounded (tail0 word)); lia).
    assert (Hw1Z : to_Z word1 = Z.clearbit (to_Z word) t0).
    { unfold word1. rewrite kernighan_clears_lowest_bit63 by exact Hpos.
      apply kernighan_clearbit; assumption. }
    assert (Ht0_lt63 : (Z.to_nat t0 < 63)%nat).
    { enough (t0 < 63)%Z by lia.
      destruct (Z_lt_dec t0 63) as [|Hge]; [assumption|exfalso].
      pose proof (to_Z_bounded word) as Hb.
      assert (Hlog : (Z.log2 (to_Z word) < 63)%Z).
      { apply Z.log2_lt_pow2; [lia|].
        change Uint63Axioms.wB with (2 ^ 63)%Z in Hb. lia. }
      assert (Hf : Z.testbit (to_Z word) t0 = false) by (apply Z.bits_above_log2; lia).
      rewrite Hf in Ht0bit. discriminate. }
    assert (Hcount1 : Z_count_ones 63 (to_Z word1) = Nat.pred (Z_count_ones 63 (to_Z word))).
    { rewrite Hw1Z. apply Z_count_ones_clearbit; assumption. }
    assert (Hw1_pos : (0 < to_Z word1)%Z).
    { destruct (Z.eq_dec (to_Z word1) 0) as [Hz|Hnz]; [|pose proof (to_Z_bounded word1); lia].
      exfalso. assert (Z_count_ones 63 (to_Z word1) = 0%nat) by (rewrite Hz; reflexivity). lia. }
    assert (Hn' : (n' < Z_count_ones 63 (to_Z word1))%nat) by lia.
    destruct (IH word1 Hw1_pos Hn') as [IHbit IHcount].
    set (p := to_Z (tail0 (clear_n_ones word1 n'))) in *.
    assert (Hp_nn : (0 <= p)%Z)
      by (pose proof (to_Z_bounded (tail0 (clear_n_ones word1 n'))); lia).
    assert (Hword_p : Z.testbit (to_Z word) p = true).
    { rewrite Hw1Z in IHbit.
      rewrite Z.clearbit_spec' in IHbit.
      rewrite Z.ldiff_spec in IHbit.
      destruct (Z.testbit (to_Z word) p); simpl in IHbit; [reflexivity|discriminate]. }
    split; [exact Hword_p|].
    assert (Ht0_lt_p : (t0 < p)%Z).
    { destruct (Z.eq_dec t0 p) as [Heq|Hneq].
      - exfalso. rewrite Hw1Z in IHbit. rewrite <- Heq in IHbit.
        rewrite Z.clearbit_eq in IHbit. discriminate.
      - assert (Hp_ne_t0 : p <> t0) by (intro; apply Hneq; lia).
        assert (Hw1_below_t0 : forall k, (0 <= k < t0)%Z -> Z.testbit (to_Z word1) k = false).
        { intros k Hk. rewrite Hw1Z. rewrite Z.clearbit_spec'.
          rewrite Z.ldiff_spec. rewrite Ht0below by lia. reflexivity. }
        destruct (Z_lt_dec p t0); [|lia].
        exfalso. assert (Z.testbit (to_Z word1) p = false) by (apply Hw1_below_t0; lia).
        congruence. }
    rewrite <- IHcount. rewrite Hw1Z.
    assert (Hclear : Z_count_ones (Z.to_nat p) (Z.clearbit (to_Z word) t0) =
                     Nat.pred (Z_count_ones (Z.to_nat p) (to_Z word))).
    { apply Z_count_ones_clearbit; [assumption | lia | assumption | assumption]. }
    rewrite Hclear.
    enough (Hpos_count : (0 < Z_count_ones (Z.to_nat p) (to_Z word))%nat) by lia.
    clear -Ht0bit Ht0_nn Ht0_lt_p.
    enough (H : forall m, (Z.to_nat t0 < m)%nat -> (m <= Z.to_nat p)%nat ->
      (0 < Z_count_ones m (to_Z word))%nat).
    { apply H; lia. }
    induction m as [|m' IHm].
    { lia. }
    intros Hlt Hle. simpl.
    destruct (Nat.eq_dec (Z.to_nat t0) m') as [Heq|Hneq].
    { replace (Z.of_nat m') with t0 by lia. rewrite Ht0bit. lia. }
    { assert ((Z.to_nat t0 < m')%nat) by lia.
      specialize (IHm ltac:(lia) ltac:(lia)).
      destruct (Z.testbit (to_Z word) (Z.of_nat m')); unfold id; lia. }
Qed.

(* ================================================================= *)
(* Part 5c: bv_select bridging lemmas                                  *)
(* ================================================================= *)

(** [bv_get] is [Z.testbit] on the appropriate word. *)
Lemma bv_get_testbit : forall bv pos,
  bv_get bv pos = Z.testbit (to_Z bv.[pos / wbits]) (to_Z (pos mod wbits)).
Proof.
  intros. unfold bv_get.
  set (w := bv.[pos / wbits]). set (b := (pos mod wbits)%uint63).
  pose proof (mod_wbits_bound pos) as Hblt.
  assert (Hb_nn : (0 <= to_Z b)%Z) by (pose proof (to_Z_bounded b); lia).
  assert (Heq : to_Z (w land (1 << b)) = Z.land (to_Z w) (2 ^ to_Z b)).
  { rewrite land_spec'. rewrite lsl1_to_Z by exact Hblt. reflexivity. }
  destruct (Z.testbit (to_Z w) (to_Z b)) eqn:Ebit.
  - apply negb_true_iff. apply not_true_is_false. intro H.
    apply eqb_spec in H.
    assert (Hz : to_Z (w land (1 << b)) = 0%Z) by (rewrite H; reflexivity).
    rewrite Heq in Hz.
    assert (Hf : Z.testbit (Z.land (to_Z w) (2 ^ to_Z b)) (to_Z b) = false).
    { rewrite Hz. apply Z.bits_0. }
    rewrite Z.land_spec in Hf. rewrite Z.pow2_bits_true in Hf by lia.
    rewrite andb_true_r in Hf. congruence.
  - apply negb_false_iff. apply eqb_spec. apply to_Z_inj.
    rewrite Heq.
    apply Z.bits_inj'. intros n Hn.
    rewrite Z.bits_0. rewrite Z.land_spec.
    destruct (Z.eq_dec n (to_Z b)) as [->|Hne].
    + rewrite Ebit. reflexivity.
    + rewrite Z.pow2_bits_false by lia. rewrite andb_false_r. reflexivity.
Qed.

(** Slice extraction: [list_chunk start len l] = [firstn len (skipn start l)]. *)
Definition list_chunk (start len : nat) (l : list bool) : list bool :=
  firstn len (skipn start l).

(** [Z_count_ones] agrees with [count_occ] on a chunk, given bit-by-bit agreement. *)
Lemma Z_count_ones_count_occ : forall (j : nat) (w : Z) (chunk : list bool),
  List.length chunk = j ->
  (forall k, (k < j)%nat -> Z.testbit w (Z.of_nat k) = nth k chunk false) ->
  Z_count_ones j w = count_occ Bool.bool_dec chunk true.
Proof.
  induction j as [|j' IH]; intros w chunk Hlen Hagree.
  - destruct chunk; [reflexivity | simpl in Hlen; discriminate].
  - simpl Z_count_ones.
    assert (Hne : chunk <> []) by (intro; subst; simpl in Hlen; discriminate).
    set (rl := removelast chunk). set (lst := last chunk false).
    assert (Hchunk : chunk = rl ++ [lst]) by (apply app_removelast_last; exact Hne).
    assert (Hrl : List.length rl = j').
    { unfold rl. rewrite removelast_firstn_len. rewrite length_firstn. lia. }
    assert (Hagree_rl : forall k, (k < j')%nat ->
      Z.testbit w (Z.of_nat k) = nth k rl false).
    { intros k Hk. rewrite (Hagree k ltac:(lia)).
      rewrite Hchunk. rewrite app_nth1 by lia. reflexivity. }
    assert (Hlast : Z.testbit w (Z.of_nat j') = lst).
    { rewrite (Hagree j' ltac:(lia)). rewrite Hchunk.
      rewrite app_nth2 by lia.
      replace (j' - List.length rl)%nat with 0%nat by lia.
      reflexivity. }
    rewrite Hchunk. rewrite count_occ_app. simpl count_occ.
    rewrite <- (IH w rl Hrl Hagree_rl).
    rewrite Hlast.
    destruct lst; simpl.
    + destruct (bool_dec true true); [|contradiction]. unfold id. lia.
    + destruct (bool_dec false true); [discriminate|]. unfold id. lia.
Qed.

(** [select_go] on [prefix ++ rest]: if target >= prefix count, skip the prefix. *)
Lemma select_go_app :
  forall prefix rest target offset count,
  (count + count_occ Bool.bool_dec prefix true <= target)%nat ->
  select_go (prefix ++ rest) target offset count =
  select_go rest target (offset + List.length prefix) (count + count_occ Bool.bool_dec prefix true).
Proof.
  induction prefix as [|b prefix' IH]; intros rest target offset count Hge.
  - simpl. f_equal; lia.
  - simpl. destruct b.
    + simpl in Hge.
      destruct (Nat.eqb count target) eqn:Heq.
      * apply Nat.eqb_eq in Heq. lia.
      * rewrite IH.
        -- destruct (bool_dec true true); [f_equal; lia | contradiction].
        -- lia.
    + rewrite IH.
      * destruct (bool_dec false true); [discriminate | f_equal; lia].
      * simpl in Hge. lia.
Qed.

(** Shifting both target and count by the same amount is identity. *)
Lemma select_go_count_shift :
  forall bv target pos count d,
  (d <= count)%nat -> (count <= target)%nat ->
  select_go bv target pos count = select_go bv (target - d) pos (count - d).
Proof.
  induction bv as [|b bv' IH]; intros target pos count d Hd Hct.
  - reflexivity.
  - simpl. destruct b.
    + destruct (Nat.eqb count target) eqn:Heq1;
        destruct (Nat.eqb (count - d) (target - d)) eqn:Heq2.
      * reflexivity.
      * apply Nat.eqb_eq in Heq1. apply Nat.eqb_neq in Heq2. lia.
      * apply Nat.eqb_neq in Heq1. apply Nat.eqb_eq in Heq2. lia.
      * apply Nat.eqb_neq in Heq1.
        replace (S (count - d))%nat with (S count - d)%nat by lia.
        apply IH; lia.
    + apply IH; lia.
Qed.

(** [position_of_ith_one] on [prefix ++ rest] when target is in the rest. *)
Lemma position_of_ith_one_app :
  forall prefix rest target,
  (count_occ Bool.bool_dec prefix true <= target)%nat ->
  position_of_ith_one (prefix ++ rest) target =
  (position_of_ith_one rest (target - count_occ Bool.bool_dec prefix true)
    + List.length prefix)%nat.
Proof.
  intros prefix rest target Hge. unfold position_of_ith_one.
  rewrite select_go_app. 2: lia.
  replace (0 + count_occ Bool.bool_dec prefix true)%nat
    with (count_occ Bool.bool_dec prefix true) by lia.
  replace (0 + List.length prefix)%nat
    with (List.length prefix) by lia.
  replace (List.length prefix)
    with (0 + List.length prefix)%nat at 1 by lia.
  rewrite select_go_shift. f_equal.
  rewrite (select_go_count_shift _ _ _ _ (count_occ Bool.bool_dec prefix true));
    [| lia | lia].
  replace (count_occ Bool.bool_dec prefix true -
           count_occ Bool.bool_dec prefix true)%nat with 0%nat by lia.
  reflexivity.
Qed.

(** Reading bit [k] from word [w_idx] via [bv_get]. *)
Lemma bv_get_word_bit : forall (bv : array int) (w_idx : int) (k : nat),
  (k < 63)%nat ->
  (to_Z w_idx * 63 + Z.of_nat k < wB)%Z ->
  (0 <= to_Z w_idx)%Z ->
  bv_get bv (of_nat (Z.to_nat (to_Z w_idx) * 63 + k)) =
    Z.testbit (to_Z bv.[w_idx]) (Z.of_nat k).
Proof.
  intros bv w_idx k Hk63 Hno_ov Hw_nn.
  rewrite bv_get_testbit.
  set (pos := of_nat (Z.to_nat (to_Z w_idx) * 63 + k)).
  assert (Hpos_Z : Z.of_nat (Z.to_nat (to_Z w_idx) * 63 + k) =
                    (to_Z w_idx * 63 + Z.of_nat k)%Z).
  { rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id; lia. }
  assert (Hpos_val : to_Z pos = (to_Z w_idx * 63 + Z.of_nat k)%Z).
  { unfold pos. rewrite of_Z_spec.
    rewrite Z.mod_small; [exact Hpos_Z | rewrite Hpos_Z; split; [lia | change Uint63.wB with wB; lia]]. }
  assert (Hdiv : (pos / wbits)%uint63 = w_idx).
  { apply to_Z_inj. rewrite div_spec. rewrite Hpos_val.
    change (to_Z wbits) with 63%Z.
    rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia. lia. }
  assert (Hmod : to_Z ((pos mod wbits)%uint63) = Z.of_nat k).
  { rewrite mod_spec. rewrite Hpos_val.
    change (to_Z wbits) with 63%Z.
    rewrite Z.add_comm. rewrite Z.mod_add by lia.
    rewrite Z.mod_small; lia. }
  rewrite Hdiv. rewrite Hmod. reflexivity.
Qed.

(** Generalized loop invariant for [bv_select_aux]. *)
Lemma bv_select_aux_agrees :
  forall fuel (bv : array int) (bv_list : list bool) (remaining w_idx : int),
  bv_agreement bv bv_list ->
  (to_nat remaining < count_occ Bool.bool_dec
    (skipn (to_nat w_idx * 63) bv_list) true)%nat ->
  (to_nat (length bv) <= to_nat w_idx + fuel)%nat ->
  to_nat (bv_select_aux bv remaining w_idx fuel) =
    (position_of_ith_one (skipn (to_nat w_idx * 63) bv_list) (to_nat remaining)
    + to_nat w_idx * 63)%nat.
Proof.
  induction fuel as [|fuel' IH];
    intros bv bv_list remaining w_idx [Hagree Hzero Hcov Hov] Hrem Hfuel.
  (* Base case: fuel = 0 — contradiction *)
  { simpl. exfalso.
    rewrite skipn_all2 in Hrem by lia. simpl in Hrem. lia. }
  (* Inductive case: fuel = S fuel' *)
  simpl bv_select_aux.
  set (word := bv.[w_idx]).
  set (pc := popcount word).
  set (chunk := list_chunk (to_nat w_idx * 63) 63 bv_list).
  set (suffix := skipn (to_nat w_idx * 63) bv_list).
  (* w_idx is in bounds *)
  assert (Hw_bound : (to_nat w_idx < to_nat (length bv))%nat).
  { destruct (Nat.lt_ge_cases (to_nat w_idx) (to_nat (length bv))); [assumption|].
    exfalso. rewrite skipn_all2 in Hrem by lia. simpl in Hrem. lia. }
  assert (Hlt_Z : (to_Z w_idx < to_Z (length bv))%Z).
  { pose proof (to_Z_bounded w_idx). pose proof (to_Z_bounded (length bv)). lia. }
  assert (Hwx63 : (to_Z w_idx * 63 < wB)%Z).
  { assert (to_Z w_idx * 63 < to_Z (length bv) * 63)%Z by nia. lia. }
  assert (Hw_nn : (0 <= to_Z w_idx)%Z) by (pose proof (to_Z_bounded w_idx); lia).
  assert (Hmul_no_ov : to_Z (w_idx * wbits) = to_Z w_idx * 63).
  { rewrite mul_spec. change (to_Z wbits) with 63%Z.
    rewrite Z.mod_small; [reflexivity|].
    pose proof (to_Z_bounded w_idx). split; [apply Z.mul_nonneg_nonneg; lia | exact Hwx63]. }
  (* suffix = chunk ++ rest *)
  assert (Hsuff_split : suffix = chunk ++ skipn 63 suffix).
  { unfold chunk, list_chunk, suffix. rewrite firstn_skipn. reflexivity. }
  (* chunk length *)
  assert (Hchunk_len : (List.length chunk <= 63)%nat).
  { unfold chunk, list_chunk. rewrite length_firstn. lia. }
  (* bit agreement: word[k] = chunk[k] *)
  assert (Hchunk_agree : forall k, (k < List.length chunk)%nat ->
    Z.testbit (to_Z word) (Z.of_nat k) = nth k chunk false).
  { intros k Hk.
    assert (Hk63 : (k < 63)%nat) by lia.
    assert (Habs : (to_nat w_idx * 63 + k < List.length bv_list)%nat).
    { unfold chunk, list_chunk in Hk. rewrite length_firstn in Hk.
      rewrite length_skipn in Hk. lia. }
    pose proof (Hagree (to_nat w_idx * 63 + k)%nat Habs) as Hag.
    unfold chunk, list_chunk. rewrite nth_firstn by lia. rewrite nth_skipn.
    rewrite <- Hag.
    destruct (Nat.ltb_spec k 63); [|lia].
    unfold word. symmetry. apply bv_get_word_bit; [lia | | lia].
    assert ((to_Z w_idx + 1) * 63 <= to_Z (length bv) * 63)%Z by nia. lia. }
  (* Extra bits beyond chunk are zero *)
  assert (Hextra_zero : forall k, (List.length chunk <= k < 63)%nat ->
    Z.testbit (to_Z word) (Z.of_nat k) = false).
  { intros k [Hklo Hkhi].
    assert (Hpos : (to_nat w_idx * 63 + k < to_nat (length bv) * 63)%nat).
    { assert ((to_Z w_idx + 1) * 63 <= to_Z (length bv) * 63)%Z by nia. lia. }
    assert (Hge_len : (List.length bv_list <= to_nat w_idx * 63 + k)%nat).
    { unfold chunk, list_chunk in Hklo. rewrite length_firstn in Hklo.
      rewrite length_skipn in Hklo. lia. }
    pose proof (Hzero (to_nat w_idx * 63 + k)%nat ltac:(lia)) as Hz.
    unfold word. rewrite <- bv_get_word_bit; [exact Hz | lia | | lia].
    assert ((to_Z w_idx + 1) * 63 <= to_Z (length bv) * 63)%Z by nia. lia. }
  (* popcount = count_occ of chunk *)
  assert (Hpc_eq : Z_count_ones 63 (to_Z word) =
    count_occ Bool.bool_dec chunk true).
  { (* Z_count_ones 63 = Z_count_ones (length chunk) because extra bits are 0 *)
    assert (Hpart : Z_count_ones (List.length chunk) (to_Z word) =
      count_occ Bool.bool_dec chunk true).
    { apply Z_count_ones_count_occ; [reflexivity | exact Hchunk_agree]. }
    rewrite <- Hpart.
    (* Show Z_count_ones 63 = Z_count_ones (length chunk) *)
    assert (Hext : forall j, (List.length chunk <= j <= 63)%nat ->
      Z_count_ones j (to_Z word) = Z_count_ones (List.length chunk) (to_Z word)).
    { intros j. induction j as [|j' IHj].
      - intros. assert (List.length chunk = 0)%nat by lia. rewrite H0. reflexivity.
      - intros [Hlo Hhi].
        destruct (Nat.eq_dec (List.length chunk) (S j')) as [->|Hne].
        + reflexivity.
        + simpl. rewrite Hextra_zero by lia. unfold id. apply IHj. lia. }
    apply Hext. lia. }
  assert (Hpc_nat : to_nat pc = count_occ Bool.bool_dec chunk true).
  { rewrite <- Hpc_eq.
    assert (Hpop : Z.of_nat (Z_count_ones 63 (to_Z word)) = to_Z pc).
    { unfold pc. exact (popcount_count_ones word). }
    apply Nat2Z.inj. rewrite Z2Nat.id by (pose proof (to_Z_bounded pc); lia).
    lia. }
  (* Case split: remaining <? pc *)
  destruct (remaining <? pc)%uint63 eqn:Hltb.
  + (* FOUND: remaining < pc — answer is in this word *)
    apply ltb_spec in Hltb.
    (* remaining < pc implies remaining < count_ones = count_occ chunk *)
    assert (Hlt_nat : (to_nat remaining < to_nat pc)%nat).
    { apply Nat2Z.inj_lt.
      repeat rewrite Z2Nat.id by (pose proof (to_Z_bounded remaining);
        pose proof (to_Z_bounded pc); lia). lia. }
    assert (Hrem_co : (to_nat remaining < count_occ Bool.bool_dec chunk true)%nat).
    { rewrite <- Hpc_nat. exact Hlt_nat. }
    assert (Hrem_z : (to_nat remaining < Z_count_ones 63 (to_Z word))%nat).
    { rewrite Hpc_eq. exact Hrem_co. }
    (* word must be positive — it has ones *)
    assert (Hword_pos : (0 < to_Z word)%Z).
    { destruct (Z.eq_dec (to_Z word) 0) as [Hz|Hnz].
      - exfalso. rewrite Hz in Hrem_z.
        change (to_nat remaining < Z_count_ones 63 0)%nat in Hrem_z.
        vm_compute in Hrem_z. lia.
      - pose proof (to_Z_bounded word). lia. }
    (* select_word_correct gives position and count *)
    pose proof (select_word_correct (to_nat remaining) word Hword_pos Hrem_z)
      as [Hbit_set Hcount_below].
    set (bit_pos := tail0 (clear_n_ones word (to_nat remaining))) in *.
    (* bit_pos < 63 *)
    assert (Hbp_bound : (to_Z bit_pos < 63)%Z).
    { pose proof (to_Z_bounded bit_pos).
      pose proof (to_Z_bounded word).
      destruct (Z.lt_ge_cases (to_Z bit_pos) 63) as [|Hge]; [lia|].
      exfalso.
      assert (Hfalse : Z.testbit (to_Z word) (to_Z bit_pos) = false).
      { apply Z.bits_above_log2; [lia|].
        enough (Z.log2 (to_Z word) < 63)%Z by lia.
        apply Z.log2_lt_pow2; [exact Hword_pos|].
        change 63%Z with (Z.of_nat 63).
        change (2 ^ Z.of_nat 63)%Z with Uint63Axioms.wB. lia. }
      rewrite Hbit_set in Hfalse. discriminate. }
    assert (Hbp_nat : (Z.to_nat (to_Z bit_pos) < 63)%nat) by lia.
    (* Convert to_Z bit_pos to Z.of_nat form for compatibility with chunk lemmas *)
    assert (Hbp_conv : to_Z bit_pos = Z.of_nat (Z.to_nat (to_Z bit_pos))).
    { rewrite Z2Nat.id; [reflexivity|]. pose proof (to_Z_bounded bit_pos). lia. }
    rewrite Hbp_conv in Hbit_set, Hcount_below.
    (* bit_pos < length chunk *)
    assert (Hbp_chunk : (Z.to_nat (to_Z bit_pos) < List.length chunk)%nat).
    { destruct (Nat.lt_ge_cases (Z.to_nat (to_Z bit_pos)) (List.length chunk)); [assumption|].
      exfalso.
      assert (Heb : Z.testbit (to_Z word) (Z.of_nat (Z.to_nat (to_Z bit_pos))) = false).
      { apply Hextra_zero. lia. }
      rewrite Heb in Hbit_set. discriminate. }
    (* nth bit_pos chunk = true *)
    assert (Hnth_chunk : nth (Z.to_nat (to_Z bit_pos)) chunk false = true).
    { rewrite <- Hchunk_agree by exact Hbp_chunk. exact Hbit_set. }
    (* count_occ of firstn bit_pos chunk = to_nat remaining *)
    assert (Hco_prefix : count_occ Bool.bool_dec
      (firstn (Z.to_nat (to_Z bit_pos)) chunk) true = to_nat remaining).
    { (* Use Z_count_ones_count_occ on the prefix *)
      rewrite <- Hcount_below.
      rewrite Nat2Z.id.
      symmetry. apply Z_count_ones_count_occ.
      - rewrite length_firstn. apply Nat.min_l. lia.
      - intros k Hk.
        assert (Hk' : (k < Z.to_nat (to_Z bit_pos))%nat).
        { assert (List.length (firstn (Z.to_nat (to_Z bit_pos)) chunk) =
            Z.to_nat (to_Z bit_pos)).
          { apply firstn_length_le. lia. }
          lia. }
        rewrite nth_firstn.
        destruct (Nat.ltb_spec k (Z.to_nat (to_Z bit_pos))); [|lia].
        rewrite <- Hchunk_agree; [reflexivity|lia]. }
    (* suffix = chunk ++ rest, and bit_pos < length chunk, so nth in suffix = nth in chunk *)
    assert (Hnth_suffix : nth (Z.to_nat (to_Z bit_pos)) suffix false = true).
    { rewrite Hsuff_split. rewrite app_nth1 by exact Hbp_chunk. exact Hnth_chunk. }
    (* firstn bit_pos suffix = firstn bit_pos chunk when bit_pos < length chunk *)
    assert (Hfirstn_eq : firstn (Z.to_nat (to_Z bit_pos)) suffix =
      firstn (Z.to_nat (to_Z bit_pos)) chunk).
    { rewrite Hsuff_split. rewrite firstn_app.
      replace (Z.to_nat (to_Z bit_pos) - List.length chunk)%nat with 0%nat by lia.
      simpl. rewrite app_nil_r. reflexivity. }
    (* count_occ of firstn in suffix *)
    assert (Hco_suffix : count_occ Bool.bool_dec
      (firstn (Z.to_nat (to_Z bit_pos)) suffix) true = to_nat remaining).
    { rewrite Hfirstn_eq. exact Hco_prefix. }
    (* bit_pos < length suffix *)
    assert (Hbp_suffix : (Z.to_nat (to_Z bit_pos) < List.length suffix)%nat).
    { (* chunk = firstn 63 suffix, so length chunk <= length suffix *)
      assert (List.length chunk <= List.length suffix)%nat.
      { enough (List.length chunk <= List.length suffix)%nat by lia.
        assert (Htmp := Hsuff_split).
        apply (f_equal (@List.length bool)) in Htmp.
        rewrite length_app in Htmp. lia. }
      lia. }
    (* Apply select_go_at_gen *)
    assert (Hsel : select_go suffix (to_nat remaining) 0 0 =
      Z.to_nat (to_Z bit_pos)).
    { rewrite (select_go_at_gen suffix (Z.to_nat (to_Z bit_pos)) 0 (to_nat remaining) 0);
        [lia | exact Hbp_suffix | exact Hnth_suffix | | lia].
      simpl. rewrite Hco_suffix. lia. }
    (* Now relate the Int63 expression to nat *)
    unfold position_of_ith_one. rewrite Hsel.
    (* Goal: to_nat (w_idx * wbits + bit_pos) = Z.to_nat (to_Z bit_pos) + to_nat w_idx * 63 *)
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_add.
    repeat rewrite Z2Nat.id by (pose proof (to_Z_bounded bit_pos);
      pose proof (to_Z_bounded w_idx); lia).
    (* to_Z (w_idx * wbits + bit_pos) = to_Z w_idx * 63 + to_Z bit_pos *)
    rewrite add_spec. rewrite Hmul_no_ov.
    assert (HwB_eq : Uint63.wB = wB) by reflexivity.
    rewrite HwB_eq.
    rewrite Z.mod_small.
    2: { pose proof (to_Z_bounded bit_pos). split; [nia|].
         assert ((to_Z w_idx + 1) * 63 <= to_Z (length bv) * 63)%Z by nia.
         unfold wB in *. change (2^63)%Z with 9223372036854775808%Z in *. lia. }
    lia.
  + (* SKIP: remaining >= pc — recurse to next word *)
    assert (Hge_rem : (to_Z pc <= to_Z remaining)%Z).
    { destruct (Z_lt_ge_dec (to_Z remaining) (to_Z pc)) as [Hlt|]; [|lia].
      exfalso. apply ltb_spec in Hlt. rewrite Hlt in Hltb. discriminate. }
    assert (Hge_nat : (to_nat pc <= to_nat remaining)%nat).
    { unfold to_nat. apply Z2Nat.inj_le.
      - pose proof (to_Z_bounded pc). lia.
      - pose proof (to_Z_bounded remaining). lia.
      - lia. }
    (* Int63 arithmetic for sub and add *)
    assert (Hsub_val : to_Z (remaining - pc) = (to_Z remaining - to_Z pc)%Z).
    { rewrite sub_spec. rewrite Z.mod_small; [reflexivity|].
      pose proof (to_Z_bounded remaining). pose proof (to_Z_bounded pc). lia. }
    assert (Hadd_val : to_Z (w_idx + 1) = (to_Z w_idx + 1)%Z).
    { rewrite add_spec.
      rewrite Z.mod_small; [reflexivity|].
      pose proof (to_Z_bounded w_idx).
      pose proof (to_Z_bounded (length bv)).
      rewrite to_Z_1.
      assert (HwB_val : Uint63Axioms.wB = (2^63)%Z) by reflexivity.
      rewrite HwB_val. lia. }
    assert (Hsub_nat : to_nat (remaining - pc) = (to_nat remaining - to_nat pc)%nat).
    { apply Nat2Z.inj. rewrite Nat2Z.inj_sub by lia.
      repeat rewrite Z2Nat.id by (pose proof (to_Z_bounded remaining);
        pose proof (to_Z_bounded pc); lia).
      exact Hsub_val. }
    assert (Hadd_nat : to_nat (w_idx + 1) = (to_nat w_idx + 1)%nat).
    { apply Nat2Z.inj. rewrite Nat2Z.inj_add.
      repeat rewrite Z2Nat.id by (pose proof (to_Z_bounded w_idx); lia).
      exact Hadd_val. }
    (* suffix decomposition *)
    assert (Hskip63 : skipn 63 suffix = skipn ((to_nat w_idx + 1) * 63) bv_list).
    { unfold suffix. rewrite skipn_skipn. f_equal. lia. }
    (* count in chunk *)
    assert (Hchunk_count : (count_occ Bool.bool_dec chunk true <=
      to_nat remaining)%nat).
    { rewrite <- Hpc_nat. exact Hge_nat. }
    (* remaining ones after skipping chunk *)
    assert (Hrem_rest :
      (to_nat (remaining - pc) <
       count_occ Bool.bool_dec (skipn ((to_nat w_idx + 1) * 63) bv_list) true)%nat).
    { rewrite Hsub_nat.
      fold suffix in Hrem. rewrite Hsuff_split in Hrem.
      rewrite count_occ_app in Hrem.
      rewrite <- Hskip63. lia. }
    (* Apply IH *)
    assert (IH_applied :
      to_nat (bv_select_aux bv (remaining - pc) (w_idx + 1) fuel') =
      (position_of_ith_one (skipn (to_nat (w_idx + 1) * 63) bv_list) (to_nat (remaining - pc))
       + to_nat (w_idx + 1) * 63)%nat).
    { apply IH.
      - exact (mk_bva _ _ Hagree Hzero Hcov Hov).
      - rewrite Hadd_nat. exact Hrem_rest.
      - rewrite Hadd_nat. lia. }
    rewrite IH_applied. rewrite Hadd_nat.
    (* Relate position_of_ith_one on suffix to next suffix *)
    fold suffix. rewrite Hsuff_split.
    rewrite position_of_ith_one_app by (rewrite <- Hpc_nat; exact Hge_nat).
    rewrite Hsub_nat, <- Hpc_nat.
    rewrite Hskip63.
    (* chunk must be full (63 bits) in the SKIP case *)
    assert (Hchunk_full : List.length chunk = 63%nat).
    { (* If chunk < 63, suffix < 63, so rest is empty, contradicting Hrem_rest *)
      unfold chunk, list_chunk.
      rewrite length_firstn.
      assert (Hsl : List.length suffix = (List.length bv_list - to_nat w_idx * 63)%nat)
        by (unfold suffix; apply length_skipn).
      destruct (Nat.lt_ge_cases (List.length suffix) 63) as [Hshort|Hlong].
      - exfalso.
        assert (skipn 63 suffix = @nil bool) by (apply skipn_all2; lia).
        rewrite H in Hskip63.
        rewrite <- Hskip63 in Hrem_rest. simpl in Hrem_rest. lia.
      - apply Nat.min_l. exact Hlong. }
    lia.
Qed.

(** A6: [bv_select] agrees with [position_of_ith_one]. *)
Lemma bv_select_agrees : forall bv bv_list target,
  bv_agreement bv bv_list ->
  (to_nat target < count_occ Bool.bool_dec bv_list true)%nat ->
  to_nat (bv_select bv target) =
    position_of_ith_one bv_list (to_nat target).
Proof.
  intros bv bv_list target Hbva Hcount.
  unfold bv_select.
  rewrite (bv_select_aux_agrees (to_nat (length bv)) bv bv_list target 0);
    try assumption.
  - simpl. lia.
  - simpl. lia.
Qed.

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
Lemma encode63_l_agrees : forall U vals,
  in_range (to_Z U) (to_Z_list vals) ->
  vals <> [] ->
  to_Z (ef63_l (encode63 U vals)) = ef_l (encode (to_Z U) (to_Z_list vals)).
Proof.
  intros U vals Hir Hne.
  destruct Hir as (HU_pos & HU_bound & Hn_bound & Hsum & Hn_max & Hmax).
  destruct vals as [|x vals']; [contradiction|].
  (* Unfold both sides, then normalize *)
  unfold encode63, ef63_l, encode, ef_l, num_lower_bits, to_Z_list.
  rewrite !length_map.
  set (k := Datatypes.length (x :: vals')).
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

(* ================================================================= *)
(* Helper lemmas for access63_agrees                                  *)
(* ================================================================= *)

Lemma sorted_map_upper_value :
  forall l (vals : list Z), 0 <= l -> sorted vals -> sorted (map (upper_value l) vals).
Proof.
  intros l vals Hl. induction vals as [|a rest IH].
  - constructor.
  - intros Hsrt. inversion Hsrt as [|? ? Hsrt_rest HF_le]; subst.
    constructor; [exact (IH Hsrt_rest)|].
    rewrite Forall_forall. intros u Hu.
    apply in_map_iff in Hu. destruct Hu as [b [<- Hb]].
    unfold upper_value. rewrite !Z.shiftr_div_pow2 by lia.
    apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia|].
    rewrite Forall_forall in HF_le. exact (HF_le _ Hb).
Qed.

Lemma Forall_nonneg_map_upper_value :
  forall l (vals : list Z), 0 <= l -> Forall (fun z => 0 <= z) vals ->
  Forall (fun u => 0 <= u) (map (upper_value l) vals).
Proof.
  intros l vals Hl Hnn. rewrite Forall_forall. intros u Hu.
  apply in_map_iff in Hu. destruct Hu as [z [<- Hz]].
  apply upper_value_nonneg; [lia|].
  rewrite Forall_forall in Hnn. exact (Hnn _ Hz).
Qed.

Lemma last_map_upper_value :
  forall l (vals : list int),
  vals <> [] -> 0 <= l ->
  last (map (fun x => upper_value l (to_Z x)) vals) 0 =
    to_Z (last vals 0%uint63) / 2 ^ l.
Proof.
  intros l vals Hne Hl.
  assert (Hml : forall (A B : Type) (f : A -> B) (l0 : list A) (da : A) (db : B),
    l0 <> [] -> last (map f l0) db = f (last l0 da)).
  { intros A B f l0 da db Hne'.
    rewrite (app_removelast_last da Hne').
    rewrite map_app. simpl map. rewrite !last_last. reflexivity. }
  rewrite (Hml int Z _ _ 0%uint63 0%Z Hne).
  unfold upper_value. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma fill_upper_length : forall vals l bv pos prev,
  PArray.length (fill_upper vals l bv pos prev) = PArray.length bv.
Proof.
  induction vals as [|x rest IH]; intros; [reflexivity|].
  simpl. rewrite IH. unfold bv_set. apply length_set'.
Qed.

Lemma build_upper_length_eq :
  forall l (vals : list int),
  vals <> [] -> 0 <= l ->
  sorted (to_Z_list vals) -> all_nonneg (to_Z_list vals) ->
  Z.of_nat (List.length (build_upper (map (upper_value l) (to_Z_list vals)))) =
    (to_Z (last vals 0%uint63) / 2 ^ l + Z.of_nat (List.length vals))%Z.
Proof.
  intros l vals Hne Hl Hs Hnn.
  set (ups := map (upper_value l) (to_Z_list vals)).
  assert (Hups_ne : ups <> []) by (unfold ups, to_Z_list; destruct vals; [contradiction|discriminate]).
  assert (Hups_nn : Forall (fun u => 0 <= u) ups).
  { unfold ups. apply Forall_nonneg_map_upper_value; [lia|].
    unfold all_nonneg in Hnn. exact Hnn. }
  assert (Hups_sorted : sorted ups).
  { unfold ups. apply sorted_map_upper_value; [lia|exact Hs]. }
  assert (Hlen_eq := length_build_upper ups Hups_ne Hups_nn Hups_sorted).
  assert (Hlast_ups : last ups 0%Z = to_Z (last vals 0%uint63) / 2 ^ l).
  { unfold ups, to_Z_list. rewrite map_map.
    apply last_map_upper_value; [exact Hne|lia]. }
  assert (Hlen_ups : List.length ups = List.length vals).
  { unfold ups, to_Z_list. rewrite !length_map. reflexivity. }
  rewrite Hlen_eq, Hlast_ups, Hlen_ups. lia.
Qed.

Lemma build_upper_aux_length_bound :
  forall (U : Z) (us : list Z) (prev : Z),
  Forall (fun u => u >= prev) us ->
  Forall (fun u => u < U) us ->
  sorted us ->
  0 <= prev ->
  (Z.of_nat (Datatypes.length (build_upper_aux us prev)) <=
    Z.of_nat (Datatypes.length us) + Z.max 0 (U - prev))%Z.
Proof.
  intros U us prev Hge Hbd Hss Hprev.
  revert prev Hge Hprev. induction us as [|u rest IH]; intros prev Hge Hprev.
  - simpl. lia.
  - inversion Hge as [|? ? Hu_ge Hge_rest]; subst.
    inversion Hbd as [|? ? Hu_bd Hbd_rest]; subst.
    inversion Hss as [|? ? Hss_rest HF_le]; subst.
    simpl build_upper_aux.
    rewrite length_app, repeat_length.
    assert (Hrest_ge : Forall (fun v => v >= u) rest).
    { revert HF_le. apply Forall_impl. intros a Ha. lia. }
    specialize (IH Hbd_rest Hss_rest u Hrest_ge ltac:(lia)).
    change (Datatypes.length (true :: build_upper_aux rest u))
      with (S (Datatypes.length (build_upper_aux rest u))).
    change (Datatypes.length (u :: rest)) with (S (Datatypes.length rest)).
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_succ.
    rewrite (Z2Nat.id (u - prev)) by lia.
    rewrite Z.max_r in IH by lia.
    rewrite Z.max_r by lia. lia.
Qed.

Lemma build_upper_length_le :
  forall l (U : Z) (vals : list int),
  vals <> [] -> 0 <= l -> 0 < U ->
  sorted (to_Z_list vals) -> all_nonneg (to_Z_list vals) ->
  bounded_by U (to_Z_list vals) ->
  (Z.of_nat (Datatypes.length
    (build_upper (map (upper_value l) (to_Z_list vals)))) <=
    Z.of_nat (List.length vals) + U)%Z.
Proof.
  intros l U vals Hne Hl HU Hs Hnn Hb.
  set (uppers := map (upper_value l) (to_Z_list vals)).
  assert (HSS : sorted uppers) by (apply sorted_map_upper_value; [lia|exact Hs]).
  unfold build_upper.
  apply Z.le_trans with
    (Z.of_nat (Datatypes.length uppers) + Z.max 0 (U - 0))%Z.
  { apply build_upper_aux_length_bound.
    - apply Forall_forall. intros u Hu.
      apply in_map_iff in Hu. destruct Hu as [z [<- Hz]].
      assert (Hnn_z : 0 <= z).
      { unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn. exact (Hnn _ Hz). }
      pose proof (upper_value_nonneg l z ltac:(lia) Hnn_z). lia.
    - apply Forall_forall. intros u Hu.
      apply in_map_iff in Hu. destruct Hu as [z [<- Hz]].
      unfold upper_value. rewrite Z.shiftr_div_pow2 by lia.
      unfold bounded_by in Hb. rewrite Forall_forall in Hb.
      assert (Hz_bnd : z < U) by (apply Hb; exact Hz).
      apply Z.le_lt_trans with z; [|exact Hz_bnd].
      apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      assert (Hznn : 0 <= z).
      { unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn. exact (Hnn _ Hz). }
      assert (1 <= 2 ^ l)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia).
      nia.
    - exact HSS.
    - lia. }
  unfold uppers, to_Z_list. rewrite !length_map. rewrite Z.max_r by lia. lia.
Qed.

(** Positions beyond the build_upper list read as zero in fill_upper. *)
Lemma fill_upper_zero_tail : forall vals l bv,
  0 <= to_Z l ->
  sorted (to_Z_list vals) -> all_nonneg (to_Z_list vals) ->
  vals <> [] ->
  (Z.of_nat (List.length
    (build_upper (map (upper_value (to_Z l)) (to_Z_list vals)))) < wB)%Z ->
  PArray.length bv =
    add (div (add (of_Z (Z.of_nat (List.length vals)))
                  (List.last vals 0%uint63 >> l)) wbits) 1 ->
  (to_Z (PArray.length bv) * 63 < wB)%Z ->
  (forall p, 0 <= to_Z p ->
    to_Z p < Z.of_nat (List.length
      (build_upper (map (upper_value (to_Z l)) (to_Z_list vals)))) ->
    (p / wbits <? PArray.length bv)%uint63 = true) ->
  (forall q, bv_get bv q = false) ->
  forall j,
    (List.length (build_upper (map (upper_value (to_Z l)) (to_Z_list vals))) <= j <
      to_nat (PArray.length (fill_upper vals l bv 0 0)) * 63)%nat ->
    bv_get (fill_upper vals l bv 0 0) (of_nat j) = false.
Proof.
  intros vals l bv Hl Hs Hnn Hne Hovf Hlen_bv Hbv_ov Hbounds Hzero j [Hj_lo Hj_hi].
  (* Bridge the two map forms *)
  assert (Hmap_conv : map (fun x => upper_value (to_Z l) (to_Z x)) vals =
    map (upper_value (to_Z l)) (to_Z_list vals)).
  { unfold to_Z_list. rewrite map_map. reflexivity. }
  assert (Hba_eq : build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) 0 =
    build_upper (map (upper_value (to_Z l)) (to_Z_list vals))).
  { unfold build_upper. rewrite Hmap_conv. reflexivity. }
  assert (Hj_Z : (Z.of_nat (List.length
    (build_upper_aux (map (fun x => upper_value (to_Z l) (to_Z x)) vals) 0))
    <= Z.of_nat j)%Z).
  { rewrite Hba_eq. lia. }
  rewrite (fill_upper_get_ge vals l bv 0%uint63 0%uint63 (of_nat j)).
  - apply Hzero.
  - (* overflow *)
    change (to_Z 0) with 0%Z. rewrite Z.add_0_l.
    rewrite Hba_eq. exact Hovf.
  - (* Forall prev <= upper *)
    apply Forall_forall. intros x Hx.
    change (to_Z 0) with 0%Z.
    unfold upper_value. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_pos; [|apply Z.pow_pos_nonneg; lia].
    unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
    apply Hnn. unfold to_Z_list. apply in_map. exact Hx.
  - (* sorted *)
    rewrite Hmap_conv. apply sorted_map_upper_value; [lia|exact Hs].
  - exact Hl.
  - (* bounds *)
    intros p' Hp'1 Hp'2.
    change (to_Z 0%uint63) with 0%Z in Hp'1, Hp'2.
    rewrite Z.add_0_l in Hp'2.
    rewrite Hba_eq in Hp'2.
    apply Hbounds; lia.
  - (* q >= list length *)
    change (to_Z 0) with 0%Z. rewrite Z.add_0_l.
    rewrite Hba_eq.
    rewrite of_Z_spec.
    rewrite Z.mod_small.
    + lia.
    + split; [lia|].
      rewrite fill_upper_length in Hj_hi.
      enough (Z.of_nat j < wB)%Z by (change Uint63.wB with wB; unfold wB in *; lia).
      assert (Hnat_Z : Z.of_nat (Z.to_nat (to_Z (PArray.length bv))) =
                        to_Z (PArray.length bv)).
      { rewrite Z2Nat.id; [reflexivity|].
        pose proof (to_Z_bounded (PArray.length bv)). lia. }
      apply Z.lt_le_trans with (Z.of_nat (Z.to_nat (to_Z (PArray.length bv))) * 63)%Z.
      { apply Nat2Z.inj_lt in Hj_hi. rewrite Nat2Z.inj_mul in Hj_hi. exact Hj_hi. }
      rewrite Hnat_Z. lia.
Qed.

(** of_Z round-trip for values in range. *)
Lemma to_Z_of_Z_small : forall n : Z,
  (0 <= n < wB)%Z -> to_Z (of_Z n) = n.
Proof.
  intros n Hn. rewrite of_Z_spec.
  rewrite Z.mod_small; [lia | unfold wB in Hn; change Uint63.wB with (2^63)%Z; lia].
Qed.

(** Encode agreement: ef63_n and ef_n produce the same length. *)
Lemma encode63_n_agrees : forall U vals,
  in_range (to_Z U) (to_Z_list vals) ->
  Z.to_nat (to_Z (ef63_n (encode63 U vals))) = List.length vals.
Proof.
  intros U vals Hir.
  unfold encode63. simpl.
  rewrite to_Z_of_Z_small.
  - rewrite Nat2Z.id. reflexivity.
  - destruct Hir as [_ [_ [Hn _]]].
    unfold to_Z_list in Hn. rewrite length_map in Hn. lia.
Qed.

(* ================================================================= *)
(* encode63_valid_encoding: split into 4 component lemmas             *)
(* ================================================================= *)

Section encode63_components.
  Variables (U : int) (vals' : list int) (x0 : int).
  Let vals := x0 :: vals'.
  Hypothesis Hir : in_range (to_Z U) (to_Z_list vals).
  Hypothesis Hs  : sorted (to_Z_list vals).
  Hypothesis Hnn : all_nonneg (to_Z_list vals).
  Hypothesis Hb  : bounded_by (to_Z U) (to_Z_list vals).

  Let Hne : vals <> [] := ltac:(discriminate).
  Let enc63 := encode63 U vals.
  Let encZ := encode (to_Z U) (to_Z_list vals).
  Let l63 := ef63_l enc63.
  Let lZ := ef_l encZ.
  Let n_nat := List.length vals.
  Let n63 := of_Z (Z.of_nat n_nat).
  Let uppers := map (upper_value lZ) (to_Z_list vals).
  Let mask := sub (1 << l63) 1.
  Let bv0 := make (add (div (add n63 ((List.last vals 0%uint63) >> l63)) wbits) 1) 0%uint63.
  Let last_u := to_Z (List.last vals 0%uint63 >> l63).
  Let bv_size := add (div (add n63 (List.last vals 0%uint63 >> l63)) wbits) 1.

  (* ---- shared facts ---- *)

  Let HU_pos : (0 < to_Z U)%Z.
  Proof. destruct Hir as (H & _). exact H. Qed.
  Let HU_wB : (to_Z U < wB)%Z.
  Proof. destruct Hir as (_ & H & _). exact H. Qed.
  Let Hn_wB : (Z.of_nat (List.length (to_Z_list vals)) < wB)%Z.
  Proof. destruct Hir as (_ & _ & H & _). exact H. Qed.
  Let Hsum_wB : (Z.of_nat (List.length (to_Z_list vals)) + to_Z U < wB)%Z.
  Proof. destruct Hir as (_ & _ & _ & H & _). exact H. Qed.
  Let Hn_max : (Z.of_nat (List.length (to_Z_list vals)) <= to_Z max_length)%Z.
  Proof. destruct Hir as (_ & _ & _ & _ & H & _). exact H. Qed.
  Let Hmax : (Z.of_nat (List.length (to_Z_list vals)) + to_Z U <= to_Z max_length * to_Z wbits)%Z.
  Proof. destruct Hir as (_ & _ & _ & _ & _ & H). exact H. Qed.

  Let Hl_agree : to_Z l63 = lZ.
  Proof.
    unfold l63, lZ. exact (encode63_l_agrees U vals
      (conj HU_pos (conj HU_wB (conj Hn_wB (conj Hsum_wB (conj Hn_max Hmax))))) Hne).
  Qed.
  Let Hl_nn : (0 <= lZ)%Z.
  Proof. unfold lZ, encZ. simpl. apply num_lower_bits_nonneg. Qed.
  Let Hl63_nn : (0 <= to_Z l63)%Z.
  Proof. lia. Qed.
  Let Hn_nat : (0 < Z.of_nat n_nat)%Z.
  Proof. unfold n_nat; simpl; lia. Qed.
  Let Hn_wB' : (Z.of_nat n_nat < wB)%Z.
  Proof. unfold to_Z_list in Hn_wB. rewrite length_map in Hn_wB. exact Hn_wB. Qed.
  Let Hn63_val : to_Z n63 = Z.of_nat n_nat.
  Proof.
    unfold n63. rewrite of_Z_spec. apply Z.mod_small.
    change Uint63.wB with (2^63)%Z. unfold wB in Hn_wB'. lia.
  Qed.
  Let Hmap_eq :
    map (fun x : int => upper_value (to_Z l63) (to_Z x)) vals =
    map (upper_value lZ) (to_Z_list vals).
  Proof.
    unfold to_Z_list. rewrite map_map. apply map_ext.
    intros a. rewrite Hl_agree. reflexivity.
  Qed.
  Let Hbuild_eq :
    build_upper (map (fun x => upper_value (to_Z l63) (to_Z x)) vals) =
    ef_upper encZ.
  Proof.
    change (ef_upper encZ) with
      (build_upper (map (upper_value lZ) (to_Z_list vals))).
    f_equal. exact Hmap_eq.
  Qed.
  Let Henc_upper : ef63_upper enc63 = fill_upper vals l63 bv0 0%uint63 0%uint63.
  Proof. unfold enc63, encode63, bv0, l63, n63, n_nat. reflexivity. Qed.
  Let Hlast_u_eq : last_u = upper_value (to_Z l63) (to_Z (List.last vals 0%uint63)).
  Proof. unfold last_u. apply lsr_upper_value. exact Hl63_nn. Qed.
  Let Hlast_u_bound : (last_u < to_Z U)%Z.
  Proof.
    rewrite Hlast_u_eq. unfold upper_value.
    rewrite Z.shiftr_div_pow2 by lia.
    apply Z.le_lt_trans with (to_Z (List.last vals 0%uint63)); [|].
    - apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      assert (1 <= 2 ^ to_Z l63)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia).
      pose proof (to_Z_bounded (List.last vals 0%uint63)). nia.
    - unfold bounded_by, to_Z_list in Hb. rewrite Forall_forall in Hb.
      apply Hb. apply in_map.
      rewrite (app_removelast_last 0%uint63 Hne) at 2.
      apply in_or_app. right. left. reflexivity.
  Qed.
  Let Hlast_u_nn : (0 <= last_u)%Z.
  Proof. unfold last_u. pose proof (to_Z_bounded (List.last vals 0%uint63 >> l63)). lia. Qed.
  Let Hn_last_u_wB : (Z.of_nat n_nat + last_u < wB)%Z.
  Proof.
    unfold to_Z_list in Hsum_wB. rewrite length_map in Hsum_wB.
    fold n_nat in Hsum_wB. lia.
  Qed.
  Let Hn_last_u_max : (Z.of_nat n_nat + last_u < to_Z max_length * 63)%Z.
  Proof.
    unfold to_Z_list in Hmax. rewrite length_map in Hmax.
    fold n_nat in Hmax. change (to_Z wbits) with (63 : Z) in Hmax. lia.
  Qed.
  Let HwB_concrete : wB = 9223372036854775808%Z.
  Proof. reflexivity. Qed.
  Let HUwB_concrete : Uint63.wB = 9223372036854775808%Z.
  Proof. reflexivity. Qed.
  Let HAUwB_concrete : Uint63Axioms.wB = 9223372036854775808%Z.
  Proof. reflexivity. Qed.
  Let Hsize_ok : to_Z bv_size = ((Z.of_nat n_nat + last_u) / 63 + 1)%Z.
  Proof.
    unfold bv_size. rewrite add_spec.
    assert (Hdiv_ok : to_Z (div (add n63 (List.last vals 0%uint63 >> l63)) wbits) =
      ((Z.of_nat n_nat + last_u) / 63)%Z).
    { rewrite div_spec by discriminate. change (to_Z wbits) with (63 : Z).
      rewrite add_spec. unfold last_u. rewrite Hn63_val.
      rewrite Z.mod_small; [reflexivity|].
      pose proof (to_Z_bounded (List.last vals 0%uint63 >> l63)) as Htmp.
      rewrite HAUwB_concrete in Htmp. rewrite HwB_concrete in Hn_last_u_wB.
      change Uint63.wB with 9223372036854775808%Z. split; lia. }
    rewrite Hdiv_ok. change (to_Z 1) with (1 : Z).
    rewrite Z.mod_small; [reflexivity|].
    assert (Hdiv_nn : (0 <= (Z.of_nat n_nat + last_u) / 63)%Z) by (apply Z.div_pos; lia).
    assert (Hml0 : to_Z max_length = 4194303%Z) by reflexivity.
    rewrite Hml0 in Hn_last_u_max.
    assert ((Z.of_nat n_nat + last_u) / 63 < 4194303)%Z
      by (apply Z.div_lt_upper_bound; lia).
    change Uint63.wB with 9223372036854775808%Z. lia.
  Qed.
  Let Hbv_le_max : (to_Z bv_size <= to_Z max_length)%Z.
  Proof.
    rewrite Hsize_ok.
    assert (Hml : to_Z max_length = 4194303%Z) by reflexivity.
    rewrite Hml.
    change (to_Z wbits) with (63 : Z) in Hmax.
    rewrite Hml in Hn_last_u_max.
    assert ((Z.of_nat n_nat + last_u) / 63 < 4194303)%Z.
    { apply Z.div_lt_upper_bound; lia. }
    lia.
  Qed.
  Let Hbv_len : PArray.length (ef63_upper enc63) = bv_size.
  Proof.
    rewrite Henc_upper, fill_upper_length. unfold bv0. rewrite length_make'.
    fold bv_size.
    assert (Hleb : (bv_size <=? max_length)%uint63 = true) by (apply leb_spec; lia).
    rewrite Hleb. reflexivity.
  Qed.
  Let Hbv_size_Z : to_Z (PArray.length (ef63_upper enc63)) = to_Z bv_size.
  Proof. rewrite Hbv_len; reflexivity. Qed.
  Let Hbv_size_ov : (to_Z bv_size * 63 < wB)%Z.
  Proof.
    rewrite Hsize_ok.
    assert (Hml2 : to_Z max_length = 4194303%Z) by reflexivity.
    rewrite Hml2 in Hn_last_u_max.
    assert (Hd : ((Z.of_nat n_nat + last_u) / 63 < 4194303)%Z)
      by (apply Z.div_lt_upper_bound; lia).
    assert (((Z.of_nat n_nat + last_u) / 63 + 1) * 63 <= 4194303 * 63)%Z by lia.
    unfold wB. change (2^63)%Z with 9223372036854775808%Z. lia.
  Qed.
  Let Hbu_len : Z.of_nat (List.length (build_upper uppers)) =
    (last_u + Z.of_nat n_nat)%Z.
  Proof.
    unfold uppers. rewrite <- Hl_agree.
    rewrite (build_upper_length_eq (to_Z l63) vals Hne Hl63_nn Hs Hnn).
    unfold last_u. rewrite lsr_spec.
    unfold n_nat. lia.
  Qed.

  (* ---- upper bitvector agreement ---- *)
  Let Hupper_raw : forall j,
    (j < List.length (build_upper (map (fun x => upper_value (to_Z l63) (to_Z x)) vals)))%nat ->
    bv_get (fill_upper vals l63 bv0 0%uint63 0%uint63) (of_Z (Z.of_nat j)) =
      List.nth j (build_upper (map (fun x => upper_value (to_Z l63) (to_Z x)) vals)) false.
  Proof.
    apply fill_upper_agrees.
    - exact Hl63_nn.
    - exact Hnn.
    - exact Hs.
    - intros p Hp_nn Hp_lt.
      set (last_u' := to_Z (List.last vals 0%uint63 >> l63)).
      set (bv_size' := add (div (add n63 (List.last vals 0%uint63 >> l63)) wbits) 1).
      assert (Hlast_u_bound' : last_u' < to_Z U).
      { unfold last_u'.
        rewrite lsr_spec.
        assert (Hlast_in : In (List.last vals 0%uint63) vals).
        { rewrite (app_removelast_last 0%uint63 Hne) at 2.
          apply in_or_app. right. left. reflexivity. }
        assert (Hlast_bnd : to_Z (List.last vals 0%uint63) < to_Z U).
        { unfold bounded_by in Hb. rewrite Forall_forall in Hb.
          apply Hb. unfold to_Z_list. apply in_map. exact Hlast_in. }
        assert (Hlast_nn : 0 <= to_Z (List.last vals 0%uint63)).
        { unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
          apply Hnn. unfold to_Z_list. apply in_map. exact Hlast_in. }
        assert (H2l : 0 < 2 ^ to_Z l63) by (apply Z.pow_pos_nonneg; lia).
        apply Z.div_lt_upper_bound; [lia|].
        apply Z.lt_le_trans with (to_Z U * 2 ^ to_Z l63)%Z.
        - nia.
        - nia. }
      assert (Hn_last_u' : Z.of_nat n_nat + last_u' < to_Z max_length * to_Z wbits).
      { unfold to_Z_list in Hmax. rewrite length_map in Hmax. fold n_nat in Hmax. lia. }
      assert (Hn_last_u_wB' : Z.of_nat n_nat + last_u' < wB).
      { unfold to_Z_list in Hsum_wB. rewrite length_map in Hsum_wB. fold n_nat in Hsum_wB. lia. }
      assert (Hlast_u_nn' : 0 <= last_u').
      { unfold last_u'. rewrite lsr_spec. apply Z.div_pos;
        [|apply Z.pow_pos_nonneg; lia].
        unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
        apply Hnn. unfold to_Z_list. apply in_map.
        rewrite (app_removelast_last 0%uint63 Hne) at 2.
        apply in_or_app. right. left. reflexivity. }
      assert (Hadd_ok : to_Z (add n63 (List.last vals 0%uint63 >> l63)) =
        (Z.of_nat n_nat + last_u')%Z).
      { rewrite add_spec, Hn63_val. fold last_u'.
        rewrite Z.mod_small; [reflexivity|].
        split; [lia|]. exact Hn_last_u_wB'. }
      assert (Hdiv_ok : to_Z (div (add n63 (List.last vals 0%uint63 >> l63)) wbits) =
        ((Z.of_nat n_nat + last_u') / 63)%Z).
      { rewrite div_spec by discriminate. rewrite Hadd_ok.
        change (to_Z wbits) with (63 : Z). reflexivity. }
      assert (Hmax_val : to_Z max_length = (4194303 : Z)) by reflexivity.
      assert (Hwbits_val : to_Z wbits = (63 : Z)) by reflexivity.
      assert (Hdiv_bound : ((Z.of_nat n_nat + last_u') / 63 < (4194303 : Z))%Z).
      { apply Z.div_lt_upper_bound; [lia|].
        rewrite Hwbits_val in Hn_last_u'. rewrite Hmax_val in Hn_last_u'. lia. }
      assert (Hsize_ok' : to_Z bv_size' = ((Z.of_nat n_nat + last_u') / 63 + 1)%Z).
      { unfold bv_size'. rewrite add_spec, Hdiv_ok.
        change (to_Z 1) with (1 : Z).
        rewrite Z.mod_small; [reflexivity|].
        assert (0 <= (Z.of_nat n_nat + last_u') / 63)%Z by (apply Z.div_pos; lia).
        split; [lia|]. change Uint63.wB with (2^63)%Z. lia. }
      assert (Hbv_le_max' : to_Z bv_size' <= to_Z max_length).
      { rewrite Hsize_ok', Hmax_val. lia. }
      apply ltb_spec. rewrite div_spec by discriminate.
      unfold bv0. rewrite length_make'.
      fold bv_size'.
      assert (Hle : (bv_size' <=? max_length)%uint63 = true).
      { apply leb_spec. exact Hbv_le_max'. }
      rewrite Hle. rewrite Hsize_ok'. change (to_Z wbits) with (63 : Z).
      assert (Hp_bound : to_Z p <= Z.of_nat n_nat + last_u' - 1).
      { assert (Hlen_eq : Z.of_nat (List.length
          (build_upper (map (fun x => upper_value (to_Z l63) (to_Z x)) vals))) =
          last_u' + Z.of_nat n_nat).
        { rewrite Hmap_eq.
          rewrite (build_upper_length_eq lZ vals Hne Hl_nn Hs Hnn).
          unfold last_u', n_nat. rewrite lsr_spec.
          rewrite Hl_agree. reflexivity. }
        lia. }
      assert (to_Z p / 63 <= (Z.of_nat n_nat + last_u' - 1) / 63)%Z.
      { apply Z.div_le_mono; lia. }
      assert ((Z.of_nat n_nat + last_u' - 1) / 63 < (Z.of_nat n_nat + last_u') / 63 + 1)%Z.
      { enough ((Z.of_nat n_nat + last_u' - 1) / 63 <= (Z.of_nat n_nat + last_u') / 63)%Z by lia.
        apply Z.div_le_mono; lia. }
      lia.
    - assert (Hsuff :
        Z.of_nat (Datatypes.length
          (build_upper (map (fun x : int => upper_value (to_Z l63) (to_Z x)) vals))) <=
        Z.of_nat n_nat + to_Z U).
      { rewrite Hmap_eq.
        pose proof (build_upper_length_le lZ (to_Z U) vals Hne Hl_nn HU_pos Hs Hnn Hb).
        unfold n_nat, to_Z_list in *. rewrite length_map in *. lia. }
      assert (Hsum' : Z.of_nat n_nat + to_Z U < wB).
      { unfold to_Z_list in Hsum_wB. rewrite length_map in Hsum_wB.
        fold n_nat in Hsum_wB. exact Hsum_wB. }
      lia.
    - intro q. apply bv_get_make_zero.
  Qed.

  (* ---- Layer A: trivial fields ---- *)
  Lemma ve_trivial_component :
    (0 <= ef_l encZ) /\
    count_occ Bool.bool_dec (ef_upper encZ) true = ef_n encZ /\
    (forall i, (i < ef_n encZ)%nat ->
      0 <= nth i (ef_lower encZ) 0%Z < 2 ^ ef_l encZ).
  Proof.
    split; [| split].
    - (* ve_l_nn *) exact Hl_nn.
    - (* ve_ones *)
      change (ef_upper encZ) with (build_upper uppers).
      rewrite count_occ_build_upper.
      unfold uppers. rewrite length_map. unfold to_Z_list. rewrite length_map.
      change (ef_n encZ) with (List.length (to_Z_list vals)).
      unfold to_Z_list. rewrite length_map. reflexivity.
    - (* ve_lower_bnd *)
      intros i Hi.
      change (ef_lower encZ) with (map (lower_bits lZ) (to_Z_list vals)).
      assert (Hlen : (i < List.length vals)%nat).
      { change (ef_n encZ) with (List.length (to_Z_list vals)) in Hi.
        unfold to_Z_list in Hi. rewrite length_map in Hi. exact Hi. }
      rewrite (nth_map_safe (lower_bits lZ) (to_Z_list vals) i 0%Z 0%Z).
      2: { unfold to_Z_list. rewrite length_map. exact Hlen. }
      unfold to_Z_list.
      rewrite (nth_map_safe to_Z vals i 0%uint63 0%Z) by exact Hlen.
      unfold lower_bits. rewrite Z.land_ones by lia.
      split;
        apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia.
  Qed.

  (* ---- Layer B: in_range-dependent fields ---- *)
  Lemma ve_lower_component :
    to_Z l63 = lZ /\
    Z.to_nat (to_Z (ef63_n enc63)) = ef_n encZ /\
    (forall i, (i < ef_n encZ)%nat ->
      to_Z ((ef63_lower enc63).[of_Z (Z.of_nat i)]) = nth i (ef_lower encZ) 0%Z).
  Proof.
    repeat split.
    - (* ve_l *) exact Hl_agree.
    - (* ve_n *)
      change (ef_n encZ) with (List.length (to_Z_list vals)).
      unfold to_Z_list. rewrite length_map.
      apply encode63_n_agrees. exact (conj HU_pos (conj HU_wB (conj Hn_wB (conj Hsum_wB (conj Hn_max Hmax))))).
    - (* ve_lower *)
      intros i Hi.
      assert (Hlen : (i < List.length vals)%nat).
      { change (ef_n encZ) with (List.length (to_Z_list vals)) in Hi.
        unfold to_Z_list in Hi. rewrite length_map in Hi. exact Hi. }
      change (ef_lower encZ) with (map (lower_bits lZ) (to_Z_list vals)).
      rewrite (nth_map_safe (lower_bits lZ) (to_Z_list vals) i 0%Z 0%Z).
      2: { unfold to_Z_list. rewrite length_map. exact Hlen. }
      unfold to_Z_list.
      rewrite (nth_map_safe to_Z vals i 0%uint63 0%Z) by exact Hlen.
      assert (Henc_lower : ef63_lower enc63 = fill_lower vals mask (make n63 0%uint63) 0%nat).
      { unfold enc63, encode63, mask, l63, n63, n_nat. reflexivity. }
      rewrite Henc_lower.
      replace lZ with (to_Z l63) by exact Hl_agree.
      rewrite (fill_lower_agrees _ _ _ l63).
      + reflexivity.
      + assert (Hl63_lt : to_Z l63 < 63).
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
      + exact Hl63_nn.
      + exact Hn_wB'.
      + intros k Hk.
        apply ltb_spec.
        rewrite length_make'.
        assert (Hn63_le_max : (n63 <=? max_length)%uint63 = true).
        { apply leb_spec. rewrite Hn63_val.
          unfold to_Z_list in Hn_max. rewrite length_map in Hn_max.
          fold n_nat in Hn_max. exact Hn_max. }
        rewrite Hn63_le_max. rewrite Hn63_val.
        simpl length in Hk.
        rewrite of_Z_spec. rewrite Z.mod_small.
        { lia. }
        { split; [lia|]. change Uint63.wB with wB. lia. }
      + exact Hlen.
  Qed.

  (* ---- Layer C: valid_input-dependent upper fields ---- *)
  Lemma ve_upper_component :
    (forall j, (j < List.length (ef_upper encZ))%nat ->
      bv_get (ef63_upper enc63) (of_Z (Z.of_nat j)) = nth j (ef_upper encZ) false) /\
    (forall j,
      (List.length (ef_upper encZ) <= j < to_nat (PArray.length (ef63_upper enc63)) * 63)%nat ->
      bv_get (ef63_upper enc63) (of_nat j) = false) /\
    (List.length (ef_upper encZ) <= to_nat (PArray.length (ef63_upper enc63)) * 63)%nat /\
    (to_Z (PArray.length (ef63_upper enc63)) * 63 < wB)%Z.
  Proof.
    repeat split.
    - (* ve_upper *)
      intros j Hj. rewrite Henc_upper, <- Hbuild_eq.
      apply Hupper_raw. rewrite Hbuild_eq. exact Hj.
    - (* ve_zero_tail *)
      intros j Hj.
      assert (Heu_eq : ef_upper encZ = build_upper uppers).
      { reflexivity. }
      rewrite Heu_eq in Hj.
      rewrite Henc_upper in Hj. rewrite fill_upper_length in Hj.
      rewrite Henc_upper.
      assert (Hmap_conv : map (fun x => upper_value (to_Z l63) (to_Z x)) vals =
        map (upper_value (to_Z l63)) (to_Z_list vals)).
      { unfold to_Z_list. rewrite map_map. reflexivity. }
      assert (Huppers_eq : map (upper_value (to_Z l63)) (to_Z_list vals) = uppers).
      { unfold uppers. rewrite Hl_agree. reflexivity. }
      assert (Hba_eq : build_upper_aux (map (fun x => upper_value (to_Z l63) (to_Z x)) vals) 0 =
        build_upper uppers).
      { unfold build_upper. rewrite Hmap_conv, Huppers_eq. reflexivity. }
      assert (Hj_Z : (Z.of_nat (List.length
        (build_upper_aux (map (fun x => upper_value (to_Z l63) (to_Z x)) vals) 0))
        <= Z.of_nat j)%Z).
      { rewrite Hba_eq. lia. }
      rewrite (fill_upper_get_ge vals l63 bv0 0%uint63 0%uint63 (of_nat j)).
      + apply bv_get_make_zero.
      + change (to_Z 0) with 0%Z. rewrite Z.add_0_l.
        rewrite Hba_eq. rewrite Hbu_len. lia.
      + apply Forall_forall. intros x Hx.
        change (to_Z 0) with 0%Z.
        unfold upper_value. rewrite Z.shiftr_div_pow2 by lia.
        apply Z.div_pos; [|apply Z.pow_pos_nonneg; lia].
        unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
        apply Hnn. unfold to_Z_list. apply in_map. exact Hx.
      + rewrite Hmap_conv. apply sorted_map_upper_value; [lia|exact Hs].
      + exact Hl63_nn.
      + intros p' Hp'1 Hp'2.
        change (to_Z 0%uint63) with 0%Z in Hp'1, Hp'2.
        rewrite Z.add_0_l in Hp'2.
        rewrite Hba_eq in Hp'2.
        rewrite Hbu_len in Hp'2.
        assert (Hbv0_len : PArray.length bv0 = bv_size).
        { rewrite <- Hbv_len, Henc_upper. rewrite fill_upper_length. reflexivity. }
        apply ltb_spec. rewrite div_spec by discriminate.
        rewrite Hbv0_len. rewrite Hsize_ok. change (to_Z wbits) with (63 : Z).
        assert (to_Z p' / 63 <= (last_u + Z.of_nat n_nat - 1) / 63)%Z.
        { apply Z.div_le_mono; lia. }
        assert ((last_u + Z.of_nat n_nat - 1) / 63 <= (Z.of_nat n_nat + last_u) / 63)%Z.
        { apply Z.div_le_mono; lia. }
        lia.
      + change (to_Z 0) with 0%Z. rewrite Z.add_0_l.
        rewrite Hba_eq.
        rewrite of_Z_spec.
        rewrite Z.mod_small.
        * lia.
        * split; [lia|].
          enough (Z.of_nat j < wB)%Z by (change Uint63.wB with wB; unfold wB in *; lia).
          assert (Hbv0_len : PArray.length bv0 = bv_size).
          { rewrite <- Hbv_len, Henc_upper. rewrite fill_upper_length. reflexivity. }
          rewrite Hbv0_len in Hj. destruct Hj as [Hj_lo Hj_hi].
          apply Z.lt_le_trans with (Z.of_nat (Z.to_nat (to_Z bv_size)) * 63)%Z.
          { apply Nat2Z.inj_lt in Hj_hi. rewrite Nat2Z.inj_mul in Hj_hi. exact Hj_hi. }
          rewrite Z2Nat.id by (pose proof (to_Z_bounded bv_size); lia). lia.
    - (* ve_covers *)
      apply Nat2Z.inj_le.
      change (ef_upper encZ) with (build_upper uppers).
      rewrite Hbu_len.
      rewrite Nat2Z.inj_mul.
      rewrite Z2Nat.id by (rewrite Hbv_size_Z, Hsize_ok; apply Z.le_le_succ_r; apply Z.div_pos; lia).
      rewrite Hbv_size_Z, Hsize_ok.
      assert (Hdm := Z.div_mod (Z.of_nat n_nat + last_u) 63 ltac:(lia)).
      assert (Hmod_bnd := Z.mod_pos_bound (Z.of_nat n_nat + last_u) 63 ltac:(lia)).
      nia.
    - (* ve_overflow *)
      rewrite Hbv_size_Z. exact Hbv_size_ov.
  Qed.

  (* ---- Layer D: derived fields ---- *)
  Lemma ve_derived_component :
    (forall i, (i < ef_n encZ)%nat ->
      (0 <= access_ef encZ i < wB)%Z) /\
    (forall i, (i < ef_n encZ)%nat ->
      (i <= position_of_ith_one (ef_upper encZ) i)%nat).
  Proof.
    split.
    - (* ve_access_bnd *)
      intros i Hi.
      assert (Hlen : (i < List.length vals)%nat).
      { change (ef_n encZ) with (List.length (to_Z_list vals)) in Hi.
        unfold to_Z_list in Hi. rewrite length_map in Hi. exact Hi. }
      assert (Hlen_tz : (i < List.length (to_Z_list vals))%nat).
      { unfold to_Z_list. rewrite length_map. exact Hlen. }
      change (access_ef encZ i) with (access_ef (encode (to_Z U) (to_Z_list vals)) i).
      rewrite (access_ef_correct (to_Z U) (to_Z_list vals) i Hs Hnn Hb Hlen_tz).
      set (xi := nth i (to_Z_list vals) 0%Z).
      assert (Hxi_nn : 0 <= xi).
      { unfold all_nonneg in Hnn. rewrite Forall_forall in Hnn.
        apply Hnn. apply nth_In. exact Hlen_tz. }
      assert (Hxi_lt : xi < to_Z U).
      { unfold bounded_by in Hb. rewrite Forall_forall in Hb.
        apply Hb. apply nth_In. exact Hlen_tz. }
      split; [lia|].
      pose proof (to_Z_bounded U). unfold wB. lia.
    - (* ve_pos_ge *)
      intros i Hi.
      assert (Hlen : (i < List.length vals)%nat).
      { change (ef_n encZ) with (List.length (to_Z_list vals)) in Hi.
        unfold to_Z_list in Hi. rewrite length_map in Hi. exact Hi. }
      change (ef_upper encZ) with (build_upper uppers).
      assert (Hpos_val : position_of_ith_one (build_upper uppers) i =
        (Z.to_nat (nth i uppers 0%Z) + i)%nat).
      { apply position_of_ith_one_build_upper.
        - apply Forall_map_upper_nonneg; [lia|exact Hnn].
        - apply StronglySorted_map_upper_nth; [lia|exact Hs].
        - unfold uppers, to_Z_list. rewrite !length_map. exact Hlen. }
      rewrite Hpos_val.
      assert (Hupper_nn : (0 <= nth i uppers 0)%Z).
      { unfold uppers. rewrite (nth_map_safe (upper_value lZ) (to_Z_list vals) i 0%Z 0%Z).
        - apply upper_value_nonneg; [lia|].
          unfold to_Z_list. rewrite (nth_map_safe to_Z vals i 0%uint63 0%Z) by exact Hlen.
          pose proof (to_Z_bounded (nth i vals (0 : int))). lia.
        - unfold to_Z_list. rewrite length_map. exact Hlen. }
      lia.
  Qed.

End encode63_components.

(** [encode63] produces a [valid_encoding] w.r.t. the Z-level [encode]. *)
Lemma encode63_valid_encoding : forall U vals,
  valid_input U vals ->
  valid_encoding (encode63 U vals) (encode (to_Z U) (to_Z_list vals)).
Proof.
  intros U vals (Hir & Hs & Hnn & Hb).
  destruct vals as [|x0 vals'].
  { (* Empty case: most fields vacuously true since ef_n = 0 *)
    change (to_Z_list []) with (@nil Z).
    constructor.
    all: change (ef_n (encode (to_Z U) [])) with 0%nat.
    all: try (intros i Hi; lia).
    - (* ve_l *) reflexivity.
    - (* ve_n *) reflexivity.
    - (* ve_upper *)
      change (ef_upper (encode (to_Z U) [])) with (build_upper (@nil Z)).
      simpl. intros j Hj. lia.
    - (* ve_zero_tail *)
      assert (Henc : ef63_upper (encode63 U []) = make 1 0%uint63) by reflexivity.
      rewrite Henc. intros j Hj. apply bv_get_make_zero.
    - (* ve_covers *)
      change (ef_upper (encode (to_Z U) [])) with (build_upper (@nil Z)).
      simpl. lia.
    - (* ve_overflow *)
      assert (Henc : ef63_upper (encode63 U []) = make 1 0%uint63) by reflexivity.
      rewrite Henc. rewrite length_make'.
      change ((1 <=? max_length)%uint63) with true. simpl.
      change (to_Z 1) with 1%Z. unfold wB. lia.
    - (* ve_l_nn *)
      change (ef_l (encode (to_Z U) [])) with (num_lower_bits (to_Z U) 0).
      unfold num_lower_bits. simpl. lia.
    - (* ve_ones *)
      change (ef_upper (encode (to_Z U) [])) with (build_upper (@nil Z)).
      simpl. reflexivity. }
  destruct (ve_trivial_component U vals' x0 Hir) as (Hnn' & Ho & Hlb).
  destruct (ve_lower_component U vals' x0 Hir Hs Hnn Hb) as (Hl & Hn & Hlo).
  destruct (ve_upper_component U vals' x0 Hir Hs Hnn Hb) as (Hu & Hzt & Hcov & Hov).
  destruct (ve_derived_component U vals' x0 Hir Hs Hnn Hb) as (Hab & Hpg).
  exact (mk_ve _ _ Hl Hn Hlo Hu Hzt Hcov Hov Hnn' Ho Hlb Hab Hpg).
Qed.

(** Access agreement from valid_encoding — the core access proof. *)
Lemma access63_agrees_ve : forall enc63 encZ i,
  valid_encoding enc63 encZ ->
  (0 <= to_Z i)%Z ->
  (Z.to_nat (to_Z i) < ef_n encZ)%nat ->
  to_Z (access63 enc63 i) = access_ef encZ (Z.to_nat (to_Z i)).
Proof.
  intros enc63 encZ i Hve Hi Hlen.
  set (Hl_agree := ve_l _ _ Hve).
  set (Hn_agree := ve_n _ _ Hve).
  set (Hlo_agree := ve_lower _ _ Hve).
  set (Hl_nn := ve_l_nn _ _ Hve).
  set (Hones := ve_ones _ _ Hve).
  set (Hlo_bnd := ve_lower_bnd _ _ Hve).
  set (Hacc_bnd := ve_access_bnd _ _ Hve).
  set (Hpos_ge := ve_pos_ge _ _ Hve).
  unfold access63, access_ef.
  set (i_nat := Z.to_nat (to_Z i)).
  assert (Hi_nat : Z.of_nat i_nat = to_Z i).
  { unfold i_nat. rewrite Z2Nat.id; lia. }
  pose proof (to_Z_bounded i) as Hi_bnd.
  (* ---- bv_select agreement ---- *)
  assert (Hsel : to_Z (bv_select (ef63_upper enc63) i) =
    Z.of_nat (position_of_ith_one (ef_upper encZ) i_nat)).
  { replace i_nat with (to_nat i) by (unfold i_nat; reflexivity).
    pose proof (bv_select_agrees (ef63_upper enc63) (ef_upper encZ) i
      (bva_of_ve _ _ Hve)) as H.
    assert (Hbsel := to_Z_bounded (bv_select (ef63_upper enc63) i)).
    rewrite <- (Z2Nat.id (to_Z (bv_select (ef63_upper enc63) i))) by lia.
    f_equal. apply H.
    rewrite Hones. exact Hlen. }
  (* ---- sub agrees ---- *)
  assert (Hpos_nn : (i_nat <= position_of_ith_one (ef_upper encZ) i_nat)%nat)
    by (apply Hpos_ge; exact Hlen).
  assert (Hu_val : to_Z (sub (bv_select (ef63_upper enc63) i) i) =
    (Z.of_nat (position_of_ith_one (ef_upper encZ) i_nat) - to_Z i)%Z).
  { rewrite sub_nonneg.
    - rewrite Hsel. lia.
    - rewrite Hsel. rewrite <- Hi_nat. lia.
    - pose proof (to_Z_bounded (bv_select (ef63_upper enc63) i)).
      unfold wB; change Uint63.wB with (2^63)%Z in *; lia. }
  (* ---- lower agreement ---- *)
  assert (Hlo : to_Z ((ef63_lower enc63).[i]) = nth i_nat (ef_lower encZ) 0%Z).
  { replace i with (of_Z (Z.of_nat i_nat)).
    2: { apply to_Z_inj. rewrite of_Z_spec. rewrite Z.mod_small.
         - exact Hi_nat.
         - rewrite Hi_nat. exact Hi_bnd. }
    exact (Hlo_agree i_nat Hlen). }
  (* ---- recombine ---- *)
  rewrite recombine63.
  - (* main equation *)
    rewrite Hu_val, Hlo, Hl_agree. lia.
  - (* 0 <= upper *)
    rewrite Hu_val. rewrite <- Hi_nat. lia.
  - (* 0 <= l *)
    lia.
  - (* 0 <= lo *)
    pose proof (to_Z_bounded ((ef63_lower enc63).[i])). lia.
  - (* lo < 2^l *)
    rewrite Hl_agree, Hlo. exact (proj2 (Hlo_bnd i_nat Hlen)).
  - (* sum < wB *)
    enough (Hrec : to_Z (sub (bv_select (ef63_upper enc63) i) i) *
      2 ^ to_Z (ef63_l enc63) + to_Z ((ef63_lower enc63).[i]) =
      access_ef encZ i_nat).
    { rewrite Hrec. exact (proj2 (Hacc_bnd i_nat Hlen)). }
    unfold access_ef. rewrite Hu_val, Hlo, Hl_agree. rewrite <- Hi_nat. ring.
Qed.

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

(* ================================================================= *)
(* Part 6a: Compositional agreement — from [valid_encoding]            *)
(* ================================================================= *)

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
  nth j (decode63_aux enc i n) 0%uint63 = access63 enc (of_Z (to_Z i + Z.of_nat j)).
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

(** Functional agreement: nextGEQ63_aux mirrors nextGEQ_aux on Z. *)
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
    assert (Hacc_i : to_Z (access63 enc63 i) = access_ef encZ (Z.to_nat (to_Z i))).
    { pose proof (Hacc (Z.to_nat (to_Z i))) as H.
      rewrite Z2Nat.id in H by lia. rewrite of_to_Z in H.
      apply H. lia. }
    set (x63 := access63 enc63 i).
    set (xZ := access_ef encZ (Z.to_nat (to_Z i))).
    assert (HxZ : to_Z x63 = xZ) by exact Hacc_i.
    destruct (leb v x63) eqn:Hleb.
    + apply leb_spec in Hleb.
      replace (xZ >=? to_Z v) with true.
      * simpl. f_equal. exact HxZ.
      * symmetry. apply Z.geb_le. lia.
    + assert (Hlt : (to_Z x63 < to_Z v)%Z).
      { assert (Hnle : ~ (to_Z v <= to_Z x63)%Z).
        { intro Habs. apply leb_spec in Habs. rewrite Habs in Hleb. discriminate. }
        lia. }
      replace (xZ >=? to_Z v) with false.
      2:{ symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
      assert (Hadd : to_Z (add i 1) = (to_Z i + 1)%Z) by (apply add1_to_Z; lia).
      replace (S (Z.to_nat (to_Z i))) with (Z.to_nat (to_Z (add i 1)))
        by (rewrite Hadd; rewrite Z2Nat.inj_add by lia; simpl; lia).
      apply IH.
      * intros k Hk. apply Hacc.
        rewrite Hadd in Hk. rewrite Z2Nat.inj_add in Hk by lia. simpl in Hk. lia.
      * lia.
      * lia.
Qed.

(** Access agreement for a range of nat indices — from [valid_encoding]. *)
Lemma access63_agrees_range_ve : forall enc63 encZ k,
  valid_encoding enc63 encZ ->
  (k < ef_n encZ)%nat ->
  to_Z (access63 enc63 (of_Z (Z.of_nat k))) = access_ef encZ k.
Proof.
  intros enc63 encZ k Hve Hk.
  pose proof (ve_n _ _ Hve) as Hn.
  pose proof (to_Z_bounded (ef63_n enc63)) as Hn_bnd.
  assert (HkwB : (Z.of_nat k < wB)%Z).
  { unfold wB. change (2 ^ 63)%Z with Uint63.wB. lia. }
  rewrite (access63_agrees_ve enc63 encZ (of_Z (Z.of_nat k)) Hve).
  - rewrite to_Z_of_Z_small by lia. rewrite Nat2Z.id. reflexivity.
  - rewrite to_Z_of_Z_small by lia. lia.
  - rewrite to_Z_of_Z_small by lia. rewrite Nat2Z.id. exact Hk.
Qed.

(** Decode agreement from [valid_encoding]: [decode63] mirrors [decode] at the Z level. *)
Lemma decode63_aux_agrees_ve : forall enc63 encZ i n,
  valid_encoding enc63 encZ ->
  (0 <= to_Z i)%Z ->
  (to_Z i + Z.of_nat n < wB)%Z ->
  (Z.to_nat (to_Z i) + n <= ef_n encZ)%nat ->
  map to_Z (decode63_aux enc63 i n) = decode_aux encZ (Z.to_nat (to_Z i)) n.
Proof.
  intros enc63 encZ i n Hve Hi Hov Hn. revert i Hi Hov Hn.
  induction n as [|n' IH]; intros i Hi Hov Hn.
  - reflexivity.
  - simpl. f_equal.
    + (* access agrees *)
      assert (Hacc := access63_agrees_ve enc63 encZ i Hve Hi).
      rewrite Hacc by lia. reflexivity.
    + (* recursive case *)
      assert (Hadd : to_Z (add i 1) = (to_Z i + 1)%Z) by (apply add1_to_Z; lia).
      replace (S (Z.to_nat (to_Z i))) with (Z.to_nat (to_Z (add i 1)))
        by (rewrite Hadd; rewrite Z2Nat.inj_add by lia; simpl; lia).
      apply IH.
      * lia.
      * lia.
      * rewrite Hadd. rewrite Z2Nat.inj_add by lia. simpl. lia.
Qed.

Lemma decode63_to_Z_ve : forall enc63 encZ,
  valid_encoding enc63 encZ ->
  map to_Z (decode63 enc63) = decode encZ.
Proof.
  intros enc63 encZ Hve.
  unfold decode63, decode.
  pose proof (ve_n _ _ Hve) as Hn.
  pose proof (to_Z_bounded (ef63_n enc63)) as Hn_bnd.
  rewrite Hn.
  change (to_Z 0) with 0%Z.
  rewrite (decode63_aux_agrees_ve enc63 encZ 0%uint63 (ef_n encZ) Hve).
  - reflexivity.
  - change (to_Z 0) with 0%Z. lia.
  - change (to_Z 0) with 0%Z. unfold wB. change (2 ^ 63)%Z with Uint63.wB. lia.
  - change (to_Z 0) with 0%Z. simpl. lia.
Qed.

(** NextGEQ agreement from [valid_encoding]: [nextGEQ63] mirrors [nextGEQ] at the Z level. *)
Lemma nextGEQ63_to_Z_ve : forall enc63 encZ v,
  valid_encoding enc63 encZ ->
  option_map to_Z (nextGEQ63 enc63 v) = nextGEQ encZ (to_Z v).
Proof.
  intros enc63 encZ v Hve.
  unfold nextGEQ63, nextGEQ.
  pose proof (ve_n _ _ Hve) as Hn.
  pose proof (to_Z_bounded (ef63_n enc63)) as Hn_bnd.
  rewrite Hn.
  apply nextGEQ63_aux_agrees.
  - intros k Hk. simpl in Hk.
    apply access63_agrees_range_ve; [exact Hve | lia].
  - change (to_Z 0) with 0%Z. unfold wB. change (2 ^ 63)%Z with Uint63.wB. lia.
  - change (to_Z 0) with 0%Z. lia.
Qed.

(** Main access agreement — corollary of [encode63_valid_encoding] + [access63_agrees_ve]. *)
Theorem access63_agrees : forall U vals i,
  valid_input U vals ->
  0 <= to_Z i ->
  (Z.to_nat (to_Z i) < List.length vals)%nat ->
  to_Z (access63 (encode63 U vals) i) =
    access_ef (encode (to_Z U) (to_Z_list vals)) (Z.to_nat (to_Z i)).
Proof.
  intros U vals i Hvi Hi Hlen.
  apply access63_agrees_ve; [|exact Hi|].
  - exact (encode63_valid_encoding U vals Hvi).
  - simpl. unfold to_Z_list. rewrite length_map. exact Hlen.
Qed.

(** Access correctness — the payoff. *)
Corollary access63_correct : forall U vals i,
  valid_input U vals ->
  0 <= to_Z i ->
  (Z.to_nat (to_Z i) < List.length vals)%nat ->
  to_Z (access63 (encode63 U vals) i) = List.nth (Z.to_nat (to_Z i)) (to_Z_list vals) 0%Z.
Proof.
  intros U vals i Hvi Hi Hlen.
  rewrite access63_agrees; [| exact Hvi | exact Hi | exact Hlen].
  destruct Hvi as (? & Hs & Hnn & Hb).
  apply access_ef_correct; [exact Hs | exact Hnn | exact Hb |].
  unfold to_Z_list. rewrite length_map. exact Hlen.
Qed.

(* ================================================================= *)
(* Part 6a': Corollaries tying back to [valid_input] / [encode63]      *)
(* ================================================================= *)

Lemma access63_agrees_range : forall U vals k,
  valid_input U vals ->
  (k < List.length vals)%nat ->
  to_Z (access63 (encode63 U vals) (of_Z (Z.of_nat k))) =
    access_ef (encode (to_Z U) (to_Z_list vals)) k.
Proof.
  intros U vals k Hvi Hk.
  apply access63_agrees_range_ve; [exact (encode63_valid_encoding U vals Hvi) |].
  simpl. unfold to_Z_list. rewrite length_map. exact Hk.
Qed.

(* ================================================================= *)
(* Part 6c: Top-level theorems                                         *)
(* ================================================================= *)

(** Round-trip. *)
Theorem decode63_agrees : forall U vals,
  valid_input U vals ->
  map to_Z (decode63 (encode63 U vals)) = to_Z_list vals.
Proof.
  intros U vals Hvi.
  rewrite (decode63_to_Z_ve _ _ (encode63_valid_encoding U vals Hvi)).
  destruct Hvi as (_ & Hs & Hnn & Hb).
  exact (round_trip (to_Z U) (to_Z_list vals) Hs Hnn Hb).
Qed.

(** Shared setup: reduce nextGEQ63 to Z-level nextGEQ via agrees lemma. *)
Lemma nextGEQ63_to_Z : forall U vals v,
  valid_input U vals ->
  option_map to_Z (nextGEQ63 (encode63 U vals) v) =
    nextGEQ (encode (to_Z U) (to_Z_list vals)) (to_Z v).
Proof.
  intros U vals v Hvi.
  exact (nextGEQ63_to_Z_ve _ _ v (encode63_valid_encoding U vals Hvi)).
Qed.

(** nextGEQ found. *)
Theorem nextGEQ63_found : forall U vals v r,
  valid_input U vals ->
  nextGEQ63 (encode63 U vals) v = Some r ->
  In (to_Z r) (to_Z_list vals) /\ to_Z r >= to_Z v.
Proof.
  intros U vals v r Hvi Hfind.
  pose proof (nextGEQ63_to_Z U vals v Hvi) as Hagree.
  rewrite Hfind in Hagree. simpl in Hagree.
  destruct Hvi as (_ & Hs & Hnn & Hb).
  exact (nextGEQ_found_thm _ _ _ _ Hs Hnn Hb (eq_sym Hagree)).
Qed.

(** nextGEQ smallest. *)
Theorem nextGEQ63_smallest : forall U vals v r,
  valid_input U vals ->
  nextGEQ63 (encode63 U vals) v = Some r ->
  forall y, In y (to_Z_list vals) -> y >= to_Z v -> to_Z r <= y.
Proof.
  intros U vals v r Hvi Hfind y Hy Hyv.
  pose proof (nextGEQ63_to_Z U vals v Hvi) as Hagree.
  rewrite Hfind in Hagree. simpl in Hagree.
  destruct Hvi as (_ & Hs & Hnn & Hb).
  exact (nextGEQ_smallest_thm _ _ _ _ Hs Hnn Hb (eq_sym Hagree) y Hy Hyv).
Qed.

(** nextGEQ none. *)
Theorem nextGEQ63_none : forall U vals v,
  valid_input U vals ->
  nextGEQ63 (encode63 U vals) v = None ->
  forall y, In y (to_Z_list vals) -> y < to_Z v.
Proof.
  intros U vals v Hvi Hnone y Hy.
  pose proof (nextGEQ63_to_Z U vals v Hvi) as Hagree.
  rewrite Hnone in Hagree. simpl in Hagree.
  destruct Hvi as (_ & Hs & Hnn & Hb).
  exact (nextGEQ_none_thm _ _ _ Hs Hnn Hb (eq_sym Hagree) y Hy).
Qed.

(* ================================================================= *)
(* Part 7: Audit                                                       *)
(* ================================================================= *)

(* Audit: which axioms remain?
   Only popcount_spec (C-backed) plus Uint63/PArray primitives.
   bv_select_agrees is a proved lemma (not an axiom). *)
Print Assumptions access63_correct.
Print Assumptions decode63_agrees.
Print Assumptions nextGEQ63_found.
Print Assumptions nextGEQ63_smallest.
Print Assumptions nextGEQ63_none.
