(* ------------------------------------------------------------------------- *)
(* Equivalent to 'needs', but skips checking all proofs using CHEAT_TAC.     *)
(* This must be used very carefully. Please call this function at the        *)
(* beginning of REPL (or a file) only when you are sure that all theorems in *)
(* the loaded file are proven to be correct in the past.                     *)
(* ------------------------------------------------------------------------- *)

let needs_skip_proofs s =
  let preamble_temp_ml = Filename.temp_file "" ".ml" in
  let oc = open_out preamble_temp_ml in
  Printf.fprintf oc "let prove_backup = prove;;\n";
  Printf.fprintf oc "let prove (t,ttac) = prove_backup (t, CHEAT_TAC);;\n";
  close_out oc;
  let postamble_temp_ml = Filename.temp_file "" ".ml" in
  let oc = open_out postamble_temp_ml in
  Printf.fprintf oc "let prove (t,ttac) = prove_backup (t,ttac);;\n";
  close_out oc;
  use_file preamble_temp_ml;
  (try
    needs s;
  with f ->
    use_file postamble_temp_ml;
    raise f);
  use_file postamble_temp_ml;;



