(** OCaml Elias-Fano benchmark.
    Reads test data from stdin (values, then queries).
    Outputs results and timing. *)

let time_us f =
  let t0 = Sys.time () in
  let r = f () in
  let t1 = Sys.time () in
  (r, (t1 -. t0) *. 1e6)

let () =
  (* Read values *)
  let values = ref [] in
  (try while true do
    let line = input_line stdin in
    if line = "---" then raise Exit;
    values := int_of_string line :: !values
  done with Exit -> ());
  let values = List.rev !values in
  let n = List.length values in
  if n = 0 then (
    Printf.eprintf "empty input\n";
    exit 1
  );
  let universe = List.fold_left max 0 values + 1 in

  (* Encode *)
  let (ef, encode_us) = time_us (fun () ->
    Elias_fano.encode ~universe values
  ) in
  Printf.printf "ocaml encode: %.1f us (%d elements)\n" encode_us n;

  (* Decode *)
  let (_decoded, decode_us) = time_us (fun () ->
    Elias_fano.decode ef
  ) in
  Printf.printf "ocaml decode_all: %.1f us\n" decode_us;

  (* Process queries *)
  (try while true do
    let line = input_line stdin in
    if String.length line > 7 && String.sub line 0 7 = "access " then begin
      let i = int_of_string (String.sub line 7 (String.length line - 7)) in
      let (result, us) = time_us (fun () -> Elias_fano.access ef i) in
      Printf.printf "ocaml access(%d) = %d [%.1f us]\n" i result us
    end else if String.length line > 8 && String.sub line 0 8 = "nextGEQ " then begin
      let v = int_of_string (String.sub line 8 (String.length line - 8)) in
      let (result, us) = time_us (fun () -> Elias_fano.next_geq ef v) in
      match result with
      | Some r -> Printf.printf "ocaml nextGEQ(%d) = %d [%.1f us]\n" v r us
      | None -> Printf.printf "ocaml nextGEQ(%d) = None [%.1f us]\n" v us
    end
  done with End_of_file -> ());

  Printf.printf "ocaml bitCount: %d bits\n" (Elias_fano.bit_size ef)
