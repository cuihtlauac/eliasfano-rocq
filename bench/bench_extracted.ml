(** Benchmark for Rocq-extracted Int63/PArray Elias-Fano.
    Same protocol as bench_ocaml.ml: values, "---", indices, "---", values.
    Outputs TSV to stdout, oracle checks to stderr. *)

open Bench_common

let warmup = 3
let reps = 15
let impl = "extracted"

(* Uint63.t = int at runtime *)
let int_to_uint63 : int -> Uint63.t = Obj.magic
let uint63_to_int : Uint63.t -> int = Obj.magic

let () =
  (* Parse input *)
  let values = read_values () in
  let access_indices = read_values () in
  let nextgeq_values = read_queries () in
  let n = Array.length values in
  if n = 0 then (Printf.eprintf "empty input\n"; exit 1);
  let universe = values.(n - 1) + 1 in
  let nq = Array.length access_indices in
  let values63 = List.init n (fun i -> int_to_uint63 values.(i)) in
  let universe63 = int_to_uint63 universe in

  (* Encode *)
  let ef = ref (EliasFanoInt63.encode63 universe63 []) in
  let encode_stats = bench ~warmup ~reps (fun () ->
    ef := EliasFanoInt63.encode63 universe63 values63
  ) in
  let ef = !ef in
  let bits = uint63_to_int (EliasFanoInt63.bit_size63 ef) in
  let bits_per_elem = Float.of_int bits /. Float.of_int n in
  print_tsv ~impl ~n ~op:"encode" ~stats:encode_stats ~bits_per_elem ();

  (* Oracle: decode and verify *)
  let decoded_arr = EliasFanoInt63.decode63_fast ef in
  let ok = ref true in
  for i = 0 to n - 1 do
    let got = uint63_to_int (Ef_parray.get decoded_arr (int_to_uint63 i)) in
    if got <> values.(i) then ok := false
  done;
  if !ok then
    Printf.eprintf "%s n=%d ORACLE decode OK\n%!" impl n
  else
    Printf.eprintf "%s n=%d ORACLE decode FAIL\n%!" impl n;

  (* Oracle: spot-check access + nextGEQ *)
  let num_checks = min 100 nq in
  let access_ok = ref true in
  for i = 0 to num_checks - 1 do
    let idx = access_indices.(i) in
    let got = uint63_to_int (EliasFanoInt63.access63_fast ef (int_to_uint63 idx)) in
    if got <> values.(idx) then access_ok := false
  done;
  if !access_ok then
    Printf.eprintf "%s n=%d ORACLE access OK\n%!" impl n
  else
    Printf.eprintf "%s n=%d ORACLE access FAIL\n%!" impl n;

  let geq_ok = ref true in
  for i = 0 to num_checks - 1 do
    let v = nextgeq_values.(i) in
    let got = EliasFanoInt63.nextGEQ63_fast ef (int_to_uint63 v) in
    let expected = ref None in
    for j = 0 to n - 1 do
      if !expected = None && values.(j) >= v then
        expected := Some values.(j)
    done;
    let got_int = match got with
      | Some x -> Some (uint63_to_int x)
      | None -> None
    in
    if got_int <> !expected then geq_ok := false
  done;
  if !geq_ok then
    Printf.eprintf "%s n=%d ORACLE nextGEQ OK\n%!" impl n
  else
    Printf.eprintf "%s n=%d ORACLE nextGEQ FAIL\n%!" impl n;

  (* Decode benchmark *)
  let decode_stats = bench ~warmup ~reps (fun () ->
    ignore (Sys.opaque_identity (EliasFanoInt63.decode63_fast ef))
  ) in
  print_tsv ~impl ~n ~op:"decode" ~stats:decode_stats ();

  (* Batched access *)
  let access_stats = bench ~warmup ~reps (fun () ->
    let acc = ref 0 in
    for i = 0 to nq - 1 do
      let r = EliasFanoInt63.access63_fast ef (int_to_uint63 access_indices.(i)) in
      acc := !acc lxor (uint63_to_int r)
    done;
    ignore (Sys.opaque_identity !acc)
  ) in
  let per_query s = { median = s.median /. Float.of_int nq;
                      min = s.min /. Float.of_int nq;
                      p25 = s.p25 /. Float.of_int nq;
                      p75 = s.p75 /. Float.of_int nq } in
  print_tsv ~impl ~n ~op:"access" ~stats:(per_query access_stats) ();

  (* Batched nextGEQ *)
  let geq_stats = bench ~warmup ~reps (fun () ->
    let acc = ref 0 in
    for i = 0 to nq - 1 do
      (match EliasFanoInt63.nextGEQ63_fast ef (int_to_uint63 nextgeq_values.(i)) with
       | Some x -> acc := !acc lxor (uint63_to_int x)
       | None -> ())
    done;
    ignore (Sys.opaque_identity !acc)
  ) in
  print_tsv ~impl ~n ~op:"nextGEQ" ~stats:(per_query geq_stats) ()
