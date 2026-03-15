(** Efficient Elias-Fano encoding with packed bitvectors.

    Same algorithm as the Rocq-verified implementation (EliasFano.v),
    but uses arrays and hardware popcount/ctz for performance.
    The Rocq proofs guarantee algorithmic correctness;
    this module provides an efficient realization. *)

external popcount : int -> int = "caml_ef_popcount" [@@noalloc]
external ctz : int -> int = "caml_ef_ctz" [@@noalloc]

(** Bits per word. OCaml int is 63 bits on 64-bit platforms;
    we use 62 to stay in non-negative range. *)
let word_bits = 62

let sampling_period = 512

type t = {
  lower : int array;
  upper : int array;      (* packed bitvector, 62 bits/word *)
  l : int;
  n : int;
  upper_bits : int;       (* total bit count in upper bitvector *)
  cum_popcnt : int array;  (* cum_popcnt.(w) = ones in words 0..w-1; length = nw+1 *)
  sel1 : int array;        (* sel1.(k) = word containing the (k*sampling_period)-th one-bit *)
  sel0 : int array;        (* sel0.(k) = word containing the (k*sampling_period)-th zero-bit *)
}

(** Floor of log2(x) for x >= 1, 0 for x <= 0.
    Matches Coq's [Z.log2]. *)
let ilog2 x =
  if x <= 1 then 0
  else
    let r = ref 0 in
    let v = ref x in
    while !v > 1 do incr r; v := !v lsr 1 done;
    !r

let set_bit bv pos =
  let w = pos / word_bits in
  let b = pos mod word_bits in
  bv.(w) <- bv.(w) lor (1 lsl b)

(** [select t i] returns the position of the [i]-th one bit
    (0-indexed) in the packed bitvector [t.upper].
    Uses sel1 sampling for O(1) lookup. *)
let select t i =
  let w = ref t.sel1.(i / sampling_period) in
  let remaining = ref (i - t.cum_popcnt.(!w)) in
  let pc = ref (popcount t.upper.(!w)) in
  while !pc <= !remaining do
    remaining := !remaining - !pc;
    incr w;
    pc := popcount t.upper.(!w)
  done;
  let bits = ref t.upper.(!w) in
  for _ = 1 to !remaining do
    bits := !bits land (!bits - 1)
  done;
  !w * word_bits + ctz !bits

(** [select_zero t i] returns the position of the [i]-th zero bit
    (0-indexed) in the packed bitvector [t.upper].
    Uses sel0 sampling for O(1) lookup. *)
let select_zero t i =
  let nw = Array.length t.upper in
  let w = ref t.sel0.(i / sampling_period) in
  (* cumulative zeros before word w = w*62 - cum_popcnt.(w) *)
  let remaining = ref (i - (!w * word_bits - t.cum_popcnt.(!w))) in
  (* For all words except the last, there are exactly word_bits bits.
     The last word may have fewer. *)
  let effective_bits w =
    if w < nw - 1 then word_bits
    else let r = t.upper_bits mod word_bits in if r = 0 then word_bits else r
  in
  let zeros_in w = effective_bits w - popcount t.upper.(w) in
  let zc = ref (zeros_in !w) in
  while !zc <= !remaining do
    remaining := !remaining - !zc;
    incr w;
    zc := zeros_in !w
  done;
  (* Invert the word (masking to effective bits) and find the remaining-th one *)
  let eb = effective_bits !w in
  let mask = if eb = word_bits then max_int else (1 lsl eb) - 1 in
  let bits = ref (lnot t.upper.(!w) land mask) in
  for _ = 1 to !remaining do
    bits := !bits land (!bits - 1)
  done;
  !w * word_bits + ctz !bits

let build_indices upper upper_bits =
  let nw = Array.length upper in
  (* cum_popcnt: prefix sum of popcount per word *)
  let cum_popcnt = Array.make (nw + 1) 0 in
  for w = 0 to nw - 1 do
    cum_popcnt.(w + 1) <- cum_popcnt.(w) + popcount upper.(w)
  done;
  let total_ones = cum_popcnt.(nw) in
  let total_zeros = upper_bits - total_ones in
  (* sel1: word containing the (k*K)-th one-bit *)
  let n1 = (total_ones + sampling_period - 1) / sampling_period in
  let sel1 = Array.make (max 1 n1) 0 in
  let next1 = ref 0 in
  for w = 0 to nw - 1 do
    while !next1 < n1 && cum_popcnt.(w + 1) > !next1 * sampling_period do
      sel1.(!next1) <- w;
      incr next1
    done
  done;
  (* sel0: word containing the (k*K)-th zero-bit *)
  let n0 = (total_zeros + sampling_period - 1) / sampling_period in
  let sel0 = Array.make (max 1 n0) 0 in
  let next0 = ref 0 in
  for w = 0 to nw - 1 do
    let cum_zeros = (w + 1) * word_bits - cum_popcnt.(w + 1) in
    (* last word may have fewer bits *)
    let cum_zeros =
      if w = nw - 1 then
        let r = upper_bits mod word_bits in
        let eb = if r = 0 then word_bits else r in
        w * word_bits + eb - cum_popcnt.(w + 1)
      else cum_zeros
    in
    while !next0 < n0 && cum_zeros > !next0 * sampling_period do
      sel0.(!next0) <- w;
      incr next0
    done
  done;
  (cum_popcnt, sel1, sel0)

let encode ~universe a =
  let n = Array.length a in
  if n = 0 then {
    lower = [||]; upper = [||]; l = 0; n = 0;
    upper_bits = 0; cum_popcnt = [||]; sel1 = [||]; sel0 = [||]
  }
  else begin
    let l = if universe > 0 then ilog2 (universe / n) else 0 in
    let mask = (1 lsl l) - 1 in
    let lower = Array.make n 0 in
    let max_upper = a.(n - 1) lsr l in
    let upper_bits = n + max_upper + 1 in
    let upper = Array.make ((upper_bits + word_bits - 1) / word_bits) 0 in
    let pos = ref 0 in
    let prev = ref 0 in
    for i = 0 to n - 1 do
      let x = a.(i) in
      lower.(i) <- x land mask;
      let u = x lsr l in
      pos := !pos + (u - !prev);
      set_bit upper !pos;
      incr pos;
      prev := u
    done;
    let (cum_popcnt, sel1, sel0) = build_indices upper upper_bits in
    { lower; upper; l; n; upper_bits; cum_popcnt; sel1; sel0 }
  end

let access t i =
  let s = select t i in
  let upper_val = s - i in
  (upper_val lsl t.l) lor t.lower.(i)

let decode t =
  if t.n = 0 then [||]
  else begin
    let result = Array.make t.n 0 in
    let nw = Array.length t.upper in
    let idx = ref 0 in
    let upper_val = ref 0 in
    for w = 0 to nw - 1 do
      let bits = ref t.upper.(w) in
      while !bits <> 0 && !idx < t.n do
        let bit_pos = ctz !bits in
        let pos = w * word_bits + bit_pos in
        upper_val := pos - !idx;
        result.(!idx) <- (!upper_val lsl t.l) lor t.lower.(!idx);
        incr idx;
        bits := !bits land (!bits - 1)
      done
    done;
    result
  end

let next_geq t v =
  if t.n = 0 then None
  else
    let uv = v lsr t.l in
    let max_upper_val = t.upper_bits - t.n in
    if uv > max_upper_val then None
    else
      (* The (uv-1)-th zero is the separator after elements with upper value uv-1.
         The first element with upper value >= uv starts right after it. *)
      let idx =
        if uv = 0 then 0
        else
          let pos = select_zero t (uv - 1) in
          pos + 1 - uv
      in
      let rec scan i =
        if i >= t.n then None
        else
          let x = access t i in
          if x >= v then Some x
          else scan (i + 1)
      in
      scan idx

let bit_size t =
  t.n * (t.l + 2)

let length t = t.n
