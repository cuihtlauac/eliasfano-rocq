let () =
  let t = Elias_fano.encode ~universe:100 [|3; 7; 42|] in

  (* round-trip *)
  assert (Elias_fano.decode t = [|3; 7; 42|]);

  (* access *)
  assert (Elias_fano.access t 0 = 3);
  assert (Elias_fano.access t 1 = 7);
  assert (Elias_fano.access t 2 = 42);

  (* nextGEQ *)
  assert (Elias_fano.next_geq t 5 = Some 7);
  assert (Elias_fano.next_geq t 42 = Some 42);
  assert (Elias_fano.next_geq t 43 = None);
  assert (Elias_fano.next_geq t 0 = Some 3);

  (* larger example *)
  let t2 = Elias_fano.encode ~universe:1000 [|0; 1; 2; 3; 4; 5|] in
  assert (Elias_fano.decode t2 = [|0; 1; 2; 3; 4; 5|]);

  let t3 = Elias_fano.encode ~universe:256 [|10; 20; 30; 100; 200; 255|] in
  assert (Elias_fano.decode t3 = [|10; 20; 30; 100; 200; 255|]);

  (* edge cases *)
  assert (Elias_fano.decode (Elias_fano.encode ~universe:1 [||]) = [||]);
  assert (Elias_fano.decode (Elias_fano.encode ~universe:10 [|0|]) = [|0|]);
  assert (Elias_fano.decode (Elias_fano.encode ~universe:100 [|0; 0; 0|]) = [|0; 0; 0|]);

  (* bit_size: 3*5 lower bits + 4 upper bits *)
  assert (Elias_fano.bit_size t = 19);

  Printf.printf "All tests passed.\n"
