(* An example that loads files using 'needs' *)
needs "L1.ml";;
needs "L2.ml";;
(* This 'needs' will not reload L1.ml because L1.ml hasn't been changed since
   the last load *)
needs "L1.ml";;

let my_lemma = prove(`!n m k. n * (((m + k) - k) + 1) = n * m + n`,
  REWRITE_TAC[ADD_SUB_LEMMA] THEN
  REWRITE_TAC[MUL_ADD_ONE_LEMMA]);;

