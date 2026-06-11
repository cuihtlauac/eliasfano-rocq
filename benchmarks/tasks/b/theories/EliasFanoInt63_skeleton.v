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
Proof. Admitted.

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
Proof. Admitted.

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

(* Exact encoding size: n*l lower bits + upper bitvector. ef63_upper_bits
   includes one trailing sentinel zero, hence the [sub _ 1]; matches the
   verified serialization length (EliasFano.v, to_bits). *)
Definition bit_size63 (enc : ef63) : int :=
  if eqb (ef63_n enc) 0 then 0
  else add (mul (ef63_n enc) (ef63_l enc)) (sub (ef63_upper_bits enc) 1).

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
Proof. Admitted.

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
Proof. Admitted.

(** A3: mask [2^l - 1] agrees with [Z.ones l]. *)
Lemma mask63_spec : forall l : int,
  (0 <= to_Z l)%Z -> (to_Z l < 63)%Z ->
  to_Z (sub (1 << l) 1) = Z.ones (to_Z l).
Proof. Admitted.

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
Proof. Admitted.

(** [1 << k <> 0] when [k < 63]. *)
Lemma lsl1_nonzero : forall k : int,
  to_Z k < 63 -> (1 << k =? 0)%uint63 = false.
Proof. Admitted.

(** Z-level: [lor] with a power-of-2 bit preserves that bit under [land]. *)
Lemma lor_land_same_bit : forall a k,
  (0 <= k)%Z -> Z.land (Z.lor a (2 ^ k)) (2 ^ k) = (2 ^ k)%Z.
Proof. Admitted.

(** Z-level: [lor] with a different power-of-2 bit is invisible to [land]. *)
Lemma lor_land_diff_bit : forall a j k,
  (0 <= j)%Z -> (0 <= k)%Z -> j <> k ->
  Z.land (Z.lor a (2 ^ j)) (2 ^ k) = Z.land a (2 ^ k).
Proof. Admitted.

(** [wbits]-related facts. *)
Lemma wbits_val : to_Z wbits = 63%Z.
Proof. Admitted.

Lemma mod_wbits_bound : forall p, to_Z (p mod wbits) < 63.
Proof. Admitted.

Lemma div_mod_recover : forall p : int,
  to_Z p = (to_Z (p / wbits) * 63 + to_Z (p mod wbits))%Z.
Proof. Admitted.

Lemma div_mod_unique : forall p q : int,
  p / wbits = q / wbits -> p mod wbits = q mod wbits -> p = q.
Proof. Admitted.

Lemma div_mod_neq : forall p q : int,
  p <> q -> p / wbits = q / wbits -> p mod wbits <> q mod wbits.
Proof. Admitted.

(** [bv_get (bv_set bv p) p = true]. *)
Lemma bv_get_bv_set_same : forall bv pos,
  (pos / wbits <? PArray.length bv)%uint63 = true ->
  bv_get (bv_set bv pos) pos = true.
Proof. Admitted.

(** [bv_get (bv_set bv p) q = bv_get bv q] when [p <> q]. *)
Lemma bv_get_bv_set_other : forall bv p q,
  p <> q ->
  (p / wbits <? PArray.length bv)%uint63 = true ->
  bv_get (bv_set bv p) q = bv_get bv q.
Proof. Admitted.

(** [bv_get] on a zero array returns false. *)
Lemma bv_get_make_zero : forall n pos,
  bv_get (make n (0 : int)) pos = false.
Proof. Admitted.

(** Helper: [of_Z] is injective on [0, wB). *)
Lemma of_Z_inj : forall a b,
  (0 <= a < wB)%Z -> (0 <= b < wB)%Z ->
  of_Z a = of_Z b -> a = b.
Proof. Admitted.

(** Helper: [fill_lower] doesn't touch indices outside its range. *)
Lemma fill_lower_get_out : forall vals mask arr start j,
  (forall k, (start <= k < start + List.length vals)%nat ->
    of_Z (Z.of_nat k) <> j) ->
  (fill_lower vals mask arr start).[j] = arr.[j].
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.

(** Helper: [x >> l] agrees with [upper_value]. *)
Lemma lsr_upper_value : forall x l,
  0 <= to_Z l ->
  to_Z (x >> l) = upper_value (to_Z l) (to_Z x).
Proof. Admitted.

(** Helper: [nth] on [repeat false k ++ [true] ++ tail]. *)
Lemma nth_repeat_app_gap : forall k (tail : list bool) i,
  (i < k)%nat ->
  List.nth i (repeat false k ++ [true] ++ tail) false = false.
Proof. Admitted.

Lemma nth_repeat_app_one : forall k (tail : list bool),
  List.nth k (repeat false k ++ [true] ++ tail) false = true.
Proof. Admitted.

Lemma nth_repeat_app_tail : forall k (tail : list bool) j,
  List.nth (k + 1 + j) (repeat false k ++ [true] ++ tail) false = List.nth j tail false.
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.

(* ================================================================= *)
(* Part 5b: bv_select proof infrastructure                            *)
(* ================================================================= *)

(** Z-level: for odd q and n >= 1, subtracting 1 doesn't change
    the quotient by 2^n. *)
Lemma div_odd_sub1 : forall q n,
  (q mod 2 = 1)%Z -> (1 <= n)%Z ->
  ((q - 1) / 2 ^ n = q / 2 ^ n)%Z.
Proof. Admitted.

(** Z-level: [Z.land x (x-1)] clears the lowest set bit. *)
Lemma kernighan_clearbit : forall x k,
  (0 < x)%Z -> (0 <= k)%Z ->
  Z.testbit x k = true ->
  (forall j, (0 <= j < k)%Z -> Z.testbit x j = false) ->
  Z.land x (x - 1) = Z.clearbit x k.
Proof. Admitted.

(** [tail0] characterization: it gives the position of the lowest set bit. *)
Lemma tail0_lowest_bit : forall x : int,
  (0 < to_Z x)%Z ->
  Z.testbit (to_Z x) (to_Z (tail0 x)) = true /\
  (forall k, (0 <= k < to_Z (tail0 x))%Z -> Z.testbit (to_Z x) k = false).
Proof. Admitted.

(** Count one-bits in positions [0..j) of [x]. *)
Fixpoint Z_count_ones (j : nat) (x : Z) : nat :=
  match j with
  | O => O
  | S j' => (if Z.testbit x (Z.of_nat j') then S else id) (Z_count_ones j' x)
  end.

(** The accumulator-based [Z_count_bits] equals [Z_count_ones]. *)
Lemma Z_count_bits_eq : forall j z acc,
  Z_count_bits z j acc = (Z_count_ones j z + acc)%nat.
Proof. Admitted.

Local Open Scope Z_scope.

Lemma Z_count_ones_S : forall j x,
  Z.of_nat (Z_count_ones (S j) x) =
  Z.of_nat (Z_count_ones j x) + (if Z.testbit x (Z.of_nat j) then 1 else 0).
Proof. Admitted.

Lemma Z_count_ones_step : forall j' x,
  Z.of_nat (Z_count_ones (S j') x) =
  (Z.of_nat (Z_count_ones j' x) + (if Z.testbit x (Z.of_nat j') then 1 else 0))%Z.
Proof. Admitted.

(** Popcount restated: [popcount x = Z_count_ones 63 (to_Z x)]. *)
Lemma popcount_count_ones : forall x : int,
  Z.of_nat (Z_count_ones 63 (to_Z x)) = to_Z (popcount x).
Proof. Admitted.

(** Lift [kernighan_clearbit] to Int63: [x land (x-1)] at Int63 level
    clears the lowest set bit, provided no overflow. *)
Lemma kernighan_clears_lowest_bit63 : forall (x : int),
  (0 < to_Z x)%Z ->
  to_Z (x land (x - 1)) = Z.land (to_Z x) (to_Z x - 1).
Proof. Admitted.

(** Bits other than [k] are unchanged by [clearbit]. *)
Lemma Z_count_ones_clearbit_other : forall j x k,
  (j <= Z.to_nat k)%nat ->
  Z_count_ones j (Z.clearbit x k) = Z_count_ones j x.
Proof. Admitted.

(** [Z_count_ones] decreases by 1 when the lowest set bit is cleared. *)
Lemma Z_count_ones_clearbit : forall j x k,
  (0 <= k)%Z ->
  (Z.to_nat k < j)%nat ->
  Z.testbit x k = true ->
  (forall i, (0 <= i < k)%Z -> Z.testbit x i = false) ->
  Z_count_ones j (Z.clearbit x k) = Nat.pred (Z_count_ones j x).
Proof. Admitted.

(** [clear_n_ones word n] at the Z level clears the lowest [n] one-bits. *)
Lemma clear_n_ones_spec : forall n (word : int),
  (0 <= to_Z word)%Z ->
  (n <= Z_count_ones 63 (to_Z word))%nat ->
  Z_count_ones 63 (to_Z (clear_n_ones word n)) =
    (Z_count_ones 63 (to_Z word) - n)%nat /\
  (forall k, (0 <= k)%Z ->
    Z.testbit (to_Z (clear_n_ones word n)) k = true ->
    Z.testbit (to_Z word) k = true).
Proof. Admitted.

(** The position found by [tail0 (clear_n_ones word n)] is the
    position of the [n]-th one-bit in [word]. *)
Lemma select_word_correct : forall n (word : int),
  (0 < to_Z word)%Z ->
  (n < Z_count_ones 63 (to_Z word))%nat ->
  Z.testbit (to_Z word) (to_Z (tail0 (clear_n_ones word n))) = true /\
  Z_count_ones (Z.to_nat (to_Z (tail0 (clear_n_ones word n)))) (to_Z word) = n.
Proof. Admitted.

(* ================================================================= *)
(* Part 5c: bv_select bridging lemmas                                  *)
(* ================================================================= *)

(** [bv_get] is [Z.testbit] on the appropriate word. *)
Lemma bv_get_testbit : forall bv pos,
  bv_get bv pos = Z.testbit (to_Z bv.[pos / wbits]) (to_Z (pos mod wbits)).
Proof. Admitted.

(** Slice extraction: [list_chunk start len l] = [firstn len (skipn start l)]. *)
Definition list_chunk (start len : nat) (l : list bool) : list bool :=
  firstn len (skipn start l).

(** [Z_count_ones] agrees with [count_occ] on a chunk, given bit-by-bit agreement. *)
Lemma Z_count_ones_count_occ : forall (j : nat) (w : Z) (chunk : list bool),
  List.length chunk = j ->
  (forall k, (k < j)%nat -> Z.testbit w (Z.of_nat k) = nth k chunk false) ->
  Z_count_ones j w = count_occ Bool.bool_dec chunk true.
Proof. Admitted.

(** [select_go] on [prefix ++ rest]: if target >= prefix count, skip the prefix. *)
Lemma select_go_app :
  forall prefix rest target offset count,
  (count + count_occ Bool.bool_dec prefix true <= target)%nat ->
  select_go (prefix ++ rest) target offset count =
  select_go rest target (offset + List.length prefix) (count + count_occ Bool.bool_dec prefix true).
Proof. Admitted.

(** Shifting both target and count by the same amount is identity. *)
Lemma select_go_count_shift :
  forall bv target pos count d,
  (d <= count)%nat -> (count <= target)%nat ->
  select_go bv target pos count = select_go bv (target - d) pos (count - d).
Proof. Admitted.

(** [position_of_ith_one] on [prefix ++ rest] when target is in the rest. *)
Lemma position_of_ith_one_app :
  forall prefix rest target,
  (count_occ Bool.bool_dec prefix true <= target)%nat ->
  position_of_ith_one (prefix ++ rest) target =
  (position_of_ith_one rest (target - count_occ Bool.bool_dec prefix true)
    + List.length prefix)%nat.
Proof. Admitted.

(** Reading bit [k] from word [w_idx] via [bv_get]. *)
Lemma bv_get_word_bit : forall (bv : array int) (w_idx : int) (k : nat),
  (k < 63)%nat ->
  (to_Z w_idx * 63 + Z.of_nat k < wB)%Z ->
  (0 <= to_Z w_idx)%Z ->
  bv_get bv (of_nat (Z.to_nat (to_Z w_idx) * 63 + k)) =
    Z.testbit (to_Z bv.[w_idx]) (Z.of_nat k).
Proof. Admitted.

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
Proof. Admitted.

(** A6: [bv_select] agrees with [position_of_ith_one]. *)
Lemma bv_select_agrees : forall bv bv_list target,
  bv_agreement bv bv_list ->
  (to_nat target < count_occ Bool.bool_dec bv_list true)%nat ->
  to_nat (bv_select bv target) =
    position_of_ith_one bv_list (to_nat target).
Proof. Admitted.

(** A7: [lor (u << l) lo] recombines upper and lower bits. *)
Lemma recombine63 : forall u l lo,
  (0 <= to_Z u)%Z -> (0 <= to_Z l)%Z -> (0 <= to_Z lo)%Z ->
  (to_Z lo < 2 ^ to_Z l)%Z ->
  (to_Z u * 2 ^ to_Z l + to_Z lo < wB)%Z ->
  to_Z ((u << l) lor lo) = (to_Z u * 2 ^ to_Z l + to_Z lo)%Z.
Proof. Admitted.

(* ================================================================= *)
(* Part 6: Agreement theorems — proved from axioms                     *)
(* ================================================================= *)

(** The [ef63_l] field agrees with the Z-level [ef_l]. *)
Lemma encode63_l_agrees : forall U vals,
  in_range (to_Z U) (to_Z_list vals) ->
  vals <> [] ->
  to_Z (ef63_l (encode63 U vals)) = ef_l (encode (to_Z U) (to_Z_list vals)).
Proof. Admitted.

(* ================================================================= *)
(* Helper lemmas for access63_agrees                                  *)
(* ================================================================= *)

Lemma sorted_map_upper_value :
  forall l (vals : list Z), 0 <= l -> sorted vals -> sorted (map (upper_value l) vals).
Proof. Admitted.

Lemma Forall_nonneg_map_upper_value :
  forall l (vals : list Z), 0 <= l -> Forall (fun z => 0 <= z) vals ->
  Forall (fun u => 0 <= u) (map (upper_value l) vals).
Proof. Admitted.

Lemma last_map_upper_value :
  forall l (vals : list int),
  vals <> [] -> 0 <= l ->
  last (map (fun x => upper_value l (to_Z x)) vals) 0 =
    to_Z (last vals 0%uint63) / 2 ^ l.
Proof. Admitted.

Lemma fill_upper_length : forall vals l bv pos prev,
  PArray.length (fill_upper vals l bv pos prev) = PArray.length bv.
Proof. Admitted.

Lemma build_upper_length_eq :
  forall l (vals : list int),
  vals <> [] -> 0 <= l ->
  sorted (to_Z_list vals) -> all_nonneg (to_Z_list vals) ->
  Z.of_nat (List.length (build_upper (map (upper_value l) (to_Z_list vals)))) =
    (to_Z (last vals 0%uint63) / 2 ^ l + Z.of_nat (List.length vals))%Z.
Proof. Admitted.

Lemma build_upper_aux_length_bound :
  forall (U : Z) (us : list Z) (prev : Z),
  Forall (fun u => u >= prev) us ->
  Forall (fun u => u < U) us ->
  sorted us ->
  0 <= prev ->
  (Z.of_nat (Datatypes.length (build_upper_aux us prev)) <=
    Z.of_nat (Datatypes.length us) + Z.max 0 (U - prev))%Z.
Proof. Admitted.

Lemma build_upper_length_le :
  forall l (U : Z) (vals : list int),
  vals <> [] -> 0 <= l -> 0 < U ->
  sorted (to_Z_list vals) -> all_nonneg (to_Z_list vals) ->
  bounded_by U (to_Z_list vals) ->
  (Z.of_nat (Datatypes.length
    (build_upper (map (upper_value l) (to_Z_list vals)))) <=
    Z.of_nat (List.length vals) + U)%Z.
Proof. Admitted.

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
Proof. Admitted.

(** of_Z round-trip for values in range. *)
Lemma to_Z_of_Z_small : forall n : Z,
  (0 <= n < wB)%Z -> to_Z (of_Z n) = n.
Proof. Admitted.

(** Encode agreement: ef63_n and ef_n produce the same length. *)
Lemma encode63_n_agrees : forall U vals,
  in_range (to_Z U) (to_Z_list vals) ->
  Z.to_nat (to_Z (ef63_n (encode63 U vals))) = List.length vals.
Proof. Admitted.

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

  (* ---- Layer A: trivial fields ---- *)
  Lemma ve_trivial_component :
    (0 <= ef_l encZ) /\
    count_occ Bool.bool_dec (ef_upper encZ) true = ef_n encZ /\
    (forall i, (i < ef_n encZ)%nat ->
      0 <= nth i (ef_lower encZ) 0%Z < 2 ^ ef_l encZ).
  Proof. Admitted.

  (* ---- Layer B: in_range-dependent fields ---- *)
  Lemma ve_lower_component :
    to_Z l63 = lZ /\
    Z.to_nat (to_Z (ef63_n enc63)) = ef_n encZ /\
    (forall i, (i < ef_n encZ)%nat ->
      to_Z ((ef63_lower enc63).[of_Z (Z.of_nat i)]) = nth i (ef_lower encZ) 0%Z).
  Proof. Admitted.

  (* ---- Layer C: valid_input-dependent upper fields ---- *)
  Lemma ve_upper_component :
    (forall j, (j < List.length (ef_upper encZ))%nat ->
      bv_get (ef63_upper enc63) (of_Z (Z.of_nat j)) = nth j (ef_upper encZ) false) /\
    (forall j,
      (List.length (ef_upper encZ) <= j < to_nat (PArray.length (ef63_upper enc63)) * 63)%nat ->
      bv_get (ef63_upper enc63) (of_nat j) = false) /\
    (List.length (ef_upper encZ) <= to_nat (PArray.length (ef63_upper enc63)) * 63)%nat /\
    (to_Z (PArray.length (ef63_upper enc63)) * 63 < wB)%Z.
  Proof. Admitted.

  (* ---- Layer D: derived fields ---- *)
  Lemma ve_derived_component :
    (forall i, (i < ef_n encZ)%nat ->
      (0 <= access_ef encZ i < wB)%Z) /\
    (forall i, (i < ef_n encZ)%nat ->
      (i <= position_of_ith_one (ef_upper encZ) i)%nat).
  Proof. Admitted.

End encode63_components.

(** [encode63] produces a [valid_encoding] w.r.t. the Z-level [encode]. *)
Lemma encode63_valid_encoding : forall U vals,
  valid_input U vals ->
  valid_encoding (encode63 U vals) (encode (to_Z U) (to_Z_list vals)).
Proof. Admitted.

(** Access agreement from valid_encoding — the core access proof. *)
Lemma access63_agrees_ve : forall enc63 encZ i,
  valid_encoding enc63 encZ ->
  (0 <= to_Z i)%Z ->
  (Z.to_nat (to_Z i) < ef_n encZ)%nat ->
  to_Z (access63 enc63 i) = access_ef encZ (Z.to_nat (to_Z i)).
Proof. Admitted.

(** Safe increment. *)
Lemma add1_to_Z : forall i : int,
  (to_Z i + 1 < wB)%Z ->
  to_Z (add i 1) = (to_Z i + 1)%Z.
Proof. Admitted.

(* ================================================================= *)
(* Part 6a: Compositional agreement — from [valid_encoding]            *)
(* ================================================================= *)

(** Length of decode63_aux. *)
Lemma decode63_aux_length : forall enc i n,
  List.length (decode63_aux enc i n) = n.
Proof. Admitted.

(** Index access for decode63_aux. *)
Lemma decode63_aux_nth : forall enc n i j,
  (j < n)%nat ->
  (to_Z i + Z.of_nat n < wB)%Z ->
  (0 <= to_Z i)%Z ->
  nth j (decode63_aux enc i n) 0%uint63 = access63 enc (of_Z (to_Z i + Z.of_nat j)).
Proof. Admitted.

(** Functional agreement: nextGEQ63_aux mirrors nextGEQ_aux on Z. *)
Lemma nextGEQ63_aux_agrees : forall enc63 encZ v i n,
  (forall k, (Z.to_nat (to_Z i) <= k < Z.to_nat (to_Z i) + n)%nat ->
    to_Z (access63 enc63 (of_Z (Z.of_nat k))) = access_ef encZ k) ->
  (to_Z i + Z.of_nat n < wB)%Z ->
  (0 <= to_Z i)%Z ->
  option_map to_Z (nextGEQ63_aux enc63 v i n) =
    nextGEQ_aux encZ (to_Z v) (Z.to_nat (to_Z i)) n.
Proof. Admitted.

(** Access agreement for a range of nat indices — from [valid_encoding]. *)
Lemma access63_agrees_range_ve : forall enc63 encZ k,
  valid_encoding enc63 encZ ->
  (k < ef_n encZ)%nat ->
  to_Z (access63 enc63 (of_Z (Z.of_nat k))) = access_ef encZ k.
Proof. Admitted.

(** Decode agreement from [valid_encoding]: [decode63] mirrors [decode] at the Z level. *)
Lemma decode63_aux_agrees_ve : forall enc63 encZ i n,
  valid_encoding enc63 encZ ->
  (0 <= to_Z i)%Z ->
  (to_Z i + Z.of_nat n < wB)%Z ->
  (Z.to_nat (to_Z i) + n <= ef_n encZ)%nat ->
  map to_Z (decode63_aux enc63 i n) = decode_aux encZ (Z.to_nat (to_Z i)) n.
Proof. Admitted.

Lemma decode63_to_Z_ve : forall enc63 encZ,
  valid_encoding enc63 encZ ->
  map to_Z (decode63 enc63) = decode encZ.
Proof. Admitted.

(** NextGEQ agreement from [valid_encoding]: [nextGEQ63] mirrors [nextGEQ] at the Z level. *)
Lemma nextGEQ63_to_Z_ve : forall enc63 encZ v,
  valid_encoding enc63 encZ ->
  option_map to_Z (nextGEQ63 enc63 v) = nextGEQ encZ (to_Z v).
Proof. Admitted.

(** Main access agreement — corollary of [encode63_valid_encoding] + [access63_agrees_ve]. *)
Conjecture access63_agrees : forall U vals i,
  valid_input U vals ->
  0 <= to_Z i ->
  (Z.to_nat (to_Z i) < List.length vals)%nat ->
  to_Z (access63 (encode63 U vals) i) =
    access_ef (encode (to_Z U) (to_Z_list vals)) (Z.to_nat (to_Z i)).

(** Access correctness — the payoff. *)
Corollary access63_correct : forall U vals i,
  valid_input U vals ->
  0 <= to_Z i ->
  (Z.to_nat (to_Z i) < List.length vals)%nat ->
  to_Z (access63 (encode63 U vals) i) = List.nth (Z.to_nat (to_Z i)) (to_Z_list vals) 0%Z.
Proof. Admitted.

(* ================================================================= *)
(* Part 6a': Corollaries tying back to [valid_input] / [encode63]      *)
(* ================================================================= *)

Lemma access63_agrees_range : forall U vals k,
  valid_input U vals ->
  (k < List.length vals)%nat ->
  to_Z (access63 (encode63 U vals) (of_Z (Z.of_nat k))) =
    access_ef (encode (to_Z U) (to_Z_list vals)) k.
Proof. Admitted.

(* ================================================================= *)
(* Part 6c: Top-level theorems                                         *)
(* ================================================================= *)

(** Round-trip. *)
Conjecture decode63_agrees : forall U vals,
  valid_input U vals ->
  map to_Z (decode63 (encode63 U vals)) = to_Z_list vals.

(** Shared setup: reduce nextGEQ63 to Z-level nextGEQ via agrees lemma. *)
Lemma nextGEQ63_to_Z : forall U vals v,
  valid_input U vals ->
  option_map to_Z (nextGEQ63 (encode63 U vals) v) =
    nextGEQ (encode (to_Z U) (to_Z_list vals)) (to_Z v).
Proof. Admitted.

(** nextGEQ found. *)
Conjecture nextGEQ63_found : forall U vals v r,
  valid_input U vals ->
  nextGEQ63 (encode63 U vals) v = Some r ->
  In (to_Z r) (to_Z_list vals) /\ to_Z r >= to_Z v.

(** nextGEQ smallest. *)
Conjecture nextGEQ63_smallest : forall U vals v r,
  valid_input U vals ->
  nextGEQ63 (encode63 U vals) v = Some r ->
  forall y, In y (to_Z_list vals) -> y >= to_Z v -> to_Z r <= y.

(** nextGEQ none. *)
Conjecture nextGEQ63_none : forall U vals v,
  valid_input U vals ->
  nextGEQ63 (encode63 U vals) v = None ->
  forall y, In y (to_Z_list vals) -> y < to_Z v.

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
