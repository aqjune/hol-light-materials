(* Strong induction for num. *)

let num_STRONG_INDUCTION = prove(
  `!(P:num->bool).
      ((P 0) /\ (!n. (!k. k < n ==> P k) ==> P n))
      ==> !n. P n`,
  REPEAT_N 3 STRIP_TAC THEN
  SUBGOAL_THEN `!p. p <= n ==> P p` MP_TAC THENL [
    SPEC_TAC (`n:num`,`n:num`) THEN
    INDUCT_TAC THENL [
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `p=0` SUBST_ALL_TAC THENL [
        ASM_ARITH_TAC; ALL_TAC
      ] THEN ASM_REWRITE_TAC[];

      REWRITE_TAC[LE_LT] THEN
      REWRITE_TAC[ARITH_RULE`!a b. (a<SUC b)<=>(a<=b)`] THEN
      REPEAT STRIP_TAC THENL [
        ASM_MESON_TAC[];

        SUBST_ALL_TAC (ASSUME `p=SUC n`) THEN
        ASM_MESON_TAC[
          ARITH_RULE`!a b. (a < SUC b) <=> (a <= b)`]
      ]
    ];
    ALL_TAC
  ] THEN
  MESON_TAC[ARITH_RULE`!k.k<=k`]);;

