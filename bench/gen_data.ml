(** Generate test data: sorted random integers.
    Usage: gen_data <n> <universe> <seed>
    Outputs one integer per line, then "---", then query values. *)

let () =
  let n = int_of_string Sys.argv.(1) in
  let universe = int_of_string Sys.argv.(2) in
  let seed = int_of_string Sys.argv.(3) in
  Random.init seed;
  (* generate n random values in [0, universe) and sort *)
  let values = Array.init n (fun _ -> Random.int universe) in
  Array.sort Int.compare values;
  (* print values *)
  Array.iter (fun v -> Printf.printf "%d\n" v) values;
  print_endline "---";
  (* print access queries: indices 0, n/4, n/2, 3n/4, n-1 *)
  if n > 0 then begin
    List.iter (fun frac ->
      let i = min (n - 1) (n * frac / 4) in
      Printf.printf "access %d\n" i
    ) [0; 1; 2; 3; 4]
  end;
  (* print nextGEQ queries: random values *)
  for _ = 0 to 9 do
    Printf.printf "nextGEQ %d\n" (Random.int universe)
  done
