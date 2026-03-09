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

type t = {
  lower : int array;
  upper : int array;
  l : int;
  n : int;
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

(** [select upper i] returns the position of the [i]-th one bit
    (0-indexed) in the packed bitvector [upper]. *)
let select upper i =
  let remaining = ref i in
  let w = ref 0 in
  let pc = ref (popcount upper.(!w)) in
  while !pc <= !remaining do
    remaining := !remaining - !pc;
    incr w;
    pc := popcount upper.(!w)
  done;
  (* Clear the lowest !remaining one-bits to isolate the target *)
  let bits = ref upper.(!w) in
  for _ = 1 to !remaining do
    bits := !bits land (!bits - 1)
  done;
  !w * word_bits + ctz !bits

let encode ~universe xs =
  let n = List.length xs in
  if n = 0 then { lower = [||]; upper = [||]; l = 0; n = 0 }
  else begin
    let l = if universe > 0 then ilog2 (universe / n) else 0 in
    let mask = (1 lsl l) - 1 in
    let lower = Array.make n 0 in
    let a = Array.of_list xs in
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
    { lower; upper; l; n }
  end

let access t i =
  let s = select t.upper i in
  let upper_val = s - i in
  (upper_val lsl t.l) lor t.lower.(i)

let decode t =
  List.init t.n (fun i -> access t i)

let next_geq t v =
  let rec scan i =
    if i >= t.n then None
    else
      let x = access t i in
      if x >= v then Some x
      else scan (i + 1)
  in
  scan 0

let bit_size t =
  t.n * (t.l + 2)

let length t = t.n
