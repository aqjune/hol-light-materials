(* w must be `expr = x` where x is a meta variable *)
let UNIFY_REFL_TAC (asl,w:goal): goalstate =
  let w_lhs,w_rhs = dest_eq w in
  if not (is_var w_rhs) then
    failwith ("UNIFY_REFL_TAC: RHS isn't a variable: " ^ (string_of_term w_rhs))
  else if vfree_in w_rhs w_lhs then
    failwith (Printf.sprintf "UNIFY_REFL_TAC: failed: `%s`" (string_of_term w)) else

  let insts = term_unify [w_rhs] w_lhs w_rhs in
  ([],insts),[],
  let th_refl = REFL w_lhs in
  fun i [] -> INSTANTIATE i th_refl;;

let UNIFY_REFL_TAC_TEST = prove(`?x. 1 = x`, META_EXISTS_TAC THEN UNIFY_REFL_TAC);;
