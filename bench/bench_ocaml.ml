(** OCaml Elias-Fano benchmark.
    Reads test data from stdin: values, "---", access indices, "---", nextGEQ values.
    Outputs TSV to stdout, oracle checks to stderr. *)

open Bench_common

let warmup = 3
let reps = 15
let impl = "ocaml"

let () =
  (* Parse input *)
  let values = read_values () in
  let access_indices = read_values () in
  let nextgeq_values = read_queries () in
  let n = Array.length values in
  if n = 0 then (Printf.eprintf "empty input\n"; exit 1);
  let universe = values.(n - 1) + 1 in
  let nq = Array.length access_indices in

  (* Encode *)
  let ef = ref (Elias_fano.encode ~universe [||]) in
  let encode_stats = bench ~warmup ~reps (fun () ->
    ef := Elias_fano.encode ~universe values
  ) in
  let ef = !ef in
  let bits = Elias_fano.bit_size ef in
  let bits_per_elem = Float.of_int bits /. Float.of_int n in
  print_tsv ~impl ~n ~op:"encode" ~stats:encode_stats ~bits_per_elem ();

  (* Oracle: decode all and verify *)
  let decoded = Elias_fano.decode ef in
  let ok = ref true in
  for i = 0 to n - 1 do
    if decoded.(i) <> values.(i) then ok := false
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
    let got = Elias_fano.access ef idx in
    if got <> values.(idx) then access_ok := false
  done;
  if !access_ok then
    Printf.eprintf "%s n=%d ORACLE access OK\n%!" impl n
  else
    Printf.eprintf "%s n=%d ORACLE access FAIL\n%!" impl n;

  let geq_ok = ref true in
  for i = 0 to num_checks - 1 do
    let v = nextgeq_values.(i) in
    let got = Elias_fano.next_geq ef v in
    (* Find expected by linear scan *)
    let expected = ref None in
    for j = 0 to n - 1 do
      if !expected = None && values.(j) >= v then
        expected := Some values.(j)
    done;
    if got <> !expected then geq_ok := false
  done;
  if !geq_ok then
    Printf.eprintf "%s n=%d ORACLE nextGEQ OK\n%!" impl n
  else
    Printf.eprintf "%s n=%d ORACLE nextGEQ FAIL\n%!" impl n;

  (* Decode benchmark *)
  let decode_stats = bench ~warmup ~reps (fun () ->
    ignore (Elias_fano.decode ef)
  ) in
  print_tsv ~impl ~n ~op:"decode" ~stats:decode_stats ();

  (* Batched access *)
  let access_stats = bench ~warmup ~reps (fun () ->
    let acc = ref 0 in
    for i = 0 to nq - 1 do
      acc := !acc lxor (Elias_fano.access ef access_indices.(i))
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
      (match Elias_fano.next_geq ef nextgeq_values.(i) with
       | Some r -> acc := !acc lxor r
       | None -> ())
    done;
    ignore (Sys.opaque_identity !acc)
  ) in
  print_tsv ~impl ~n ~op:"nextGEQ" ~stats:(per_query geq_stats) ()
