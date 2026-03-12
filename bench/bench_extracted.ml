(** Benchmark for Rocq-extracted Int63/PArray Elias-Fano.
    Same protocol as bench_ocaml.ml: reads data from stdin. *)

let time_us f =
  let t0 = Sys.time () in
  let r = f () in
  let t1 = Sys.time () in
  (r, (t1 -. t0) *. 1e6)

(* Uint63.t = int at runtime *)
let int_to_uint63 : int -> Uint63.t = Obj.magic
let uint63_to_int : Uint63.t -> int = Obj.magic

let () =
  let values = ref [] in
  (try while true do
    let line = input_line stdin in
    if line = "---" then raise Exit;
    values := int_of_string line :: !values
  done with Exit -> ());
  let values = List.rev !values in
  let n = List.length values in
  if n = 0 then (Printf.eprintf "empty input\n"; exit 1);
  let universe = List.fold_left max 0 values + 1 in
  let values63 = List.map int_to_uint63 values in
  let universe63 = int_to_uint63 universe in

  (* Encode *)
  let (ef, encode_us) = time_us (fun () ->
    EliasFanoInt63.encode63 universe63 values63
  ) in
  Printf.printf "extracted encode: %.1f us (%d elements)\n" encode_us n;

  (* Decode *)
  let (decoded, decode_us) = time_us (fun () ->
    EliasFanoInt63.decode63 ef
  ) in
  Printf.printf "extracted decode_all: %.1f us\n" decode_us;
  let decoded_ints = List.map uint63_to_int decoded in
  let sum = List.fold_left (+) 0 decoded_ints in
  Printf.printf "extracted decode_check: n=%d first=%d last=%d sum=%d\n"
    n (List.hd decoded_ints) (List.nth decoded_ints (n - 1)) sum;

  (* Queries *)
  (try while true do
    let line = input_line stdin in
    if String.length line > 7 && String.sub line 0 7 = "access " then begin
      let i = int_of_string (String.sub line 7 (String.length line - 7)) in
      let (r, us) = time_us (fun () ->
        EliasFanoInt63.access63 ef (int_to_uint63 i)) in
      Printf.printf "extracted access(%d) = %d [%.1f us]\n"
        i (uint63_to_int r) us
    end else if String.length line > 8 && String.sub line 0 8 = "nextGEQ " then begin
      let v = int_of_string (String.sub line 8 (String.length line - 8)) in
      let (r, us) = time_us (fun () ->
        EliasFanoInt63.nextGEQ63 ef (int_to_uint63 v)) in
      match r with
      | Some x ->
        Printf.printf "extracted nextGEQ(%d) = %d [%.1f us]\n"
          v (uint63_to_int x) us
      | None ->
        Printf.printf "extracted nextGEQ(%d) = None [%.1f us]\n" v us
    end
  done with End_of_file -> ());

  Printf.printf "extracted bitCount: %d bits\n"
    (uint63_to_int (EliasFanoInt63.bit_size63 ef))
