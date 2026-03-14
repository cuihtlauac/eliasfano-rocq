(** Shared benchmarking infrastructure: timer, batched measurement, statistics. *)

external monotonic_ns : unit -> int = "caml_bench_monotonic_ns" [@@noalloc]

let time_ns f =
  let t0 = monotonic_ns () in
  let r = f () in
  let t1 = monotonic_ns () in
  (r, t1 - t0)

type stats = {
  median : float;
  min : float;
  p25 : float;
  p75 : float;
}

let compute_stats (samples : float array) : stats =
  let a = Array.copy samples in
  Array.sort Float.compare a;
  let n = Array.length a in
  let percentile p =
    let k = Float.to_int (Float.of_int (n - 1) *. p) in
    a.(k)
  in
  { median = percentile 0.5;
    min = a.(0);
    p25 = percentile 0.25;
    p75 = percentile 0.75 }

let bench ~warmup ~reps f =
  (* Warm-up: untimed iterations *)
  for _ = 1 to warmup do
    f ()
  done;
  (* Measured iterations *)
  let samples = Array.init reps (fun _ ->
    Gc.compact ();
    let ((), ns) = time_ns f in
    Float.of_int ns
  ) in
  compute_stats samples

let gen_random_indices ~n ~count ~seed =
  let rng = Random.State.make [| seed |] in
  Array.init count (fun _ -> Random.State.int rng n)

let gen_random_values ~universe ~count ~seed =
  let rng = Random.State.make [| seed |] in
  Array.init count (fun _ -> Random.State.int rng universe)

(** Print a TSV row to stdout. *)
let print_tsv ~impl ~n ~op ~stats ?bits_per_elem () =
  let bpe = match bits_per_elem with
    | Some b -> Printf.sprintf "%.1f" b
    | None -> ""
  in
  Printf.printf "%s\t%d\t%s\t%.0f\t%.0f\t%.0f\t%.0f\t%s\n"
    impl n op stats.median stats.min stats.p25 stats.p75 bpe

(** Print TSV header. *)
let print_tsv_header () =
  Printf.printf "impl\tn\top\tmedian_ns\tmin_ns\tp25_ns\tp75_ns\tbits/elem\n"

(** Read values from stdin until "---". Returns array of ints. *)
let read_values () =
  let values = ref [] in
  (try while true do
    let line = input_line stdin in
    if line = "---" then raise Exit;
    values := int_of_string line :: !values
  done with Exit -> ());
  Array.of_list (List.rev !values)

(** Read remaining lines from stdin. Returns array of ints (queries). *)
let read_queries () =
  let queries = ref [] in
  (try while true do
    let line = input_line stdin in
    queries := int_of_string line :: !queries
  done with End_of_file -> ());
  Array.of_list (List.rev !queries)
