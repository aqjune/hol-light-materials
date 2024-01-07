(* Exercises for proving theorems regarding natural numbers! *)

(* 1. PLUS_ONE *)

(* Sol A. *)
g `!n. n + 1 = 1 + n`;;
e(REPEAT STRIP_TAC);;
e(ARITH_TAC);;

(* Sol B. *)
g `!n. n + 1 = 1 + n`;;
e(REPEAT STRIP_TAC);;
e(REWRITE_TAC[ADD_SYM]);;

(* Sol C. *)
g `!n. n + 1 = 1 + n`;;
e(REPEAT STRIP_TAC);;
e(REWRITE_TAC[ARITH_RULE`n+m=m+n`]);;

(* Sol D (advanced; requires knowledge in more tactics). *)
g `!n. n + 1 = 1 + n`;;
e(INDUCT_TAC);;
  (* First goal: 0 + 1 = 1 + 0 *)
  e(CONV_TAC NUM_REDUCE_CONV);;

  (* Second goal: n + 1 = 1 + n ==> SUC n + 1 = 1 + SUC n *)
  e(ASM_REWRITE_TAC[ADD_SUC;ADD]);;


let PLUS_ONE = prove(`!n. n + 1 = 1 + n`,
  REPEAT STRIP_TAC THEN
  ARITH_TAC);;


(* 2. DISTRIBUTIVE *)
g `!n m k. n * (m + k) = n * m + n * k`;;
e(REPEAT STRIP_TAC);;
e(REWRITE_TAC[LEFT_ADD_DISTRIB]);;


(* 3. TRANSITIVE *)
g `!n m k. n < m /\ m <= k ==> n < k`;;
e(REWRITE_TAC[LTE_TRANS]);;


(* 4. FACTORIZE *)
g `!x y. (x + y) EXP 2 = x EXP 2 + 2 * x * y + y EXP 2`;;
e(ARITH_TAC);;


(* 5. SUBTRACT *)
g `2 - 3 = 0`;;
e(CONV_TAC NUM_REDUCE_CONV);;


(* 6. MOD_REFL *)
g `!x. x MOD x = 0`;;
e(REWRITE_TAC[MOD_REFL]);;


(* 7. MOD_ADD *)
g `!x. (x + 2 EXP 64) MOD 2 EXP 64 = x MOD 2 EXP 64`;;
e(ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD]);;
e(REWRITE_TAC[MOD_REFL;ADD_0;MOD_MOD_REFL]);;


(* 8. MOD_SUBIFGE *)
g `!x y.
  x < 2 EXP 64 /\ y < 2 EXP 64 ==>
  (x + y) MOD 2 EXP 64 =
  if x + y >= 2 EXP 64 then (x + y) - 2 EXP 64 else x + y`;;
e(REPEAT STRIP_TAC);;
e(IMP_REWRITE_TAC[MOD_ADD_CASES]);;
e(REWRITE_TAC[ARITH_RULE `!a b. (a >= b) <=> ~(a < b)`]);;
e(MESON_TAC[]);;


(* 9. CONJUNCTION *)
g `!n. 1 < n /\ n < 10 ==> 0 < n /\ n < 11`;;
e(GEN_TAC THEN STRIP_TAC);;
e(CONJ_TAC);;
  e(MATCH_MP_TAC LT_TRANS);;
  e(EXISTS_TAC `1`);;
  e(ASM_REWRITE_TAC[]);;
  e(CONV_TAC NUM_REDUCE_CONV);;

  e(MATCH_MP_TAC LT_TRANS);;
  e(EXISTS_TAC `10`);;
  e(ASM_REWRITE_TAC[]);;
  e(CONV_TAC NUM_REDUCE_CONV);;

let EXERCISE_CONJUNCTION = prove(`!n. 1 < n /\ n < 10 ==> 0 < n /\ n < 11`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;

    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `10` THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
  ]);;


(* 10. LT_SUBTRACT (Advanced) *)
g `!x y z. z <= x /\ x < y ==> x - z < y - z`;;
(* ARITH_TAC will solve this goal, but let's not rely on this. *)
e(REPEAT STRIP_TAC);;
e(UNDISCH_THEN `z <= x`
  (fun th -> CHOOSE_TAC (REWRITE_RULE[LE_EXISTS] th)));;
e(SUBGOAL_THEN `z <= y` ASSUME_TAC THENL [
    ASM_ARITH_TAC; ALL_TAC
  ]);;
e(UNDISCH_TAC `x < y`);;
e(UNDISCH_THEN `z <= y`
  (fun th -> CHOOSE_TAC (REWRITE_RULE[LE_EXISTS] th)));;
e(ASM_REWRITE_TAC[]);;
e(ASM_REWRITE_TAC[ADD_SUB2;LT_ADD_LCANCEL]);;


let LT_SUBTRACT = prove(`!x y z. x < y /\ z <= x ==> x - z < y - z`, ARITH_TAC);;


(* 11. SUBIFGE_LT (Advanced) *)
let subifge = new_definition `subifge x y = if x >= y then x - y else x`;;
let (subifge_evaluator:term->thm) =
    REWRITE_CONV[subifge] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[];;
subifge_evaluator `subifge 10 20`;;
subifge_evaluator `subifge 30 20`;;

g `!x. x < 2 * m ==> subifge x m < m`;;
e(REPEAT STRIP_TAC);;
e(REWRITE_TAC[subifge]);;
e(ASM_CASES_TAC `x >= m`);;
  (* The first case: `x >= m` is true *)
  e(ASM_REWRITE_TAC[]);;
  e(GEN_REWRITE_TAC RAND_CONV [ARITH_RULE`m=2*m-m`]);;
  e(IMP_REWRITE_TAC[LT_SUBTRACT]);;
  e(ASM_REWRITE_TAC[GSYM GE]);;

  (* The second case: `x >= m` is false *)
  e(ASM_REWRITE_TAC[]);;
  e(UNDISCH_TAC `~(x >= m)`);;
  e(REWRITE_TAC[GE;NOT_LE]);;



let SUBIFGE_LT = prove(`!x. x < 2 * m ==> subifge x m < m`,
  REWRITE_TAC[subifge] THEN ARITH_TAC);;
