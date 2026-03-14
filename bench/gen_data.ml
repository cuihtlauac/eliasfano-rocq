(** Generate test data: sorted unique random integers + query arrays.
    Usage: gen_data <n> <universe> <seed> [--queries N]
    Outputs: one value per line, "---", then one query index per line,
    "---", then one query value per line. *)

let () =
  let n = int_of_string Sys.argv.(1) in
  let universe = int_of_string Sys.argv.(2) in
  let seed = int_of_string Sys.argv.(3) in
  let num_queries = ref 100000 in
  for i = 4 to Array.length Sys.argv - 1 do
    if Sys.argv.(i) = "--queries" && i + 1 < Array.length Sys.argv then
      num_queries := int_of_string Sys.argv.(i + 1)
  done;
  let nq = !num_queries in
  if n > universe then (
    Printf.eprintf "error: n=%d > universe=%d (need unique values)\n" n universe;
    exit 1
  );
  Random.init seed;
  (* Generate n unique random values in [0, universe) via rejection sampling.
     For n << universe this is fast. For n close to universe, use Fisher-Yates. *)
  let values =
    if n * 4 < universe then begin
      (* Rejection sampling *)
      let seen = Hashtbl.create n in
      let arr = Array.make n 0 in
      let i = ref 0 in
      while !i < n do
        let v = Random.int universe in
        if not (Hashtbl.mem seen v) then begin
          Hashtbl.add seen v ();
          arr.(!i) <- v;
          incr i
        end
      done;
      arr
    end else begin
      (* Reservoir: generate [0,universe), shuffle prefix *)
      let arr = Array.init universe (fun i -> i) in
      for i = 0 to n - 1 do
        let j = i + Random.int (universe - i) in
        let tmp = arr.(i) in
        arr.(i) <- arr.(j);
        arr.(j) <- tmp
      done;
      Array.sub arr 0 n
    end
  in
  Array.sort Int.compare values;
  (* Print values *)
  Array.iter (fun v -> Printf.printf "%d\n" v) values;
  print_endline "---";
  (* Print access query indices *)
  for _ = 1 to nq do
    Printf.printf "%d\n" (Random.int (max 1 n))
  done;
  print_endline "---";
  (* Print nextGEQ query values *)
  for _ = 1 to nq do
    Printf.printf "%d\n" (Random.int universe)
  done
