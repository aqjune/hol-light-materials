(* Exercises for proving theorems regarding natural numbers! *)

(* 1. PLUS_ONE *)
(* Let's prove n + 1 = 1 + n for natural number n.
   HOL Light infers the type of n from operator '+'.
   '!' stands for 'for-all'.

   There are 4 ways to solve this problem!
   Sol A. Simply use ARITH_TAC. To understand what ARITH_TAC is,
          type 'help "ARITH_TAC";;' and enter.
          The HOL Light Search webpage also has this functioanlity!
   Sol B. Use REWRITE_TAC with 'commutativity of addition' lemma in HOL Light
          (which is ADD_SYM. Try "search [`x + y = y + x`];;"!)
   Sol C. Use REWRITE_TAC with an on-the-fly proven lemma (ARITH_RULE `n+m=m+n`)!
   Sol D (advanced). Use induction on n (INDUCT_TAC).
      Induction principle of natural number n states that we can prove
      P(n) holds for every n if
      1) P(0) holds, and
      2) given that P(n) holds, P(successor of n) holds! 'Successor of n' is
         just 1 + n with a fancy syntax.

   Sol A is the simplest solution, and Sol D. is the most fundamental solution. *)
g `!n. n + 1 = 1 + n`;;
e(REPEAT STRIP_TAC);;
e(CHEAT_TAC);;
(* If you want to undo the last tactic, use 'b();;'.
   If you want to print the current goal again, use 'p();;'.
*)

(* If you want to give a name to your proven lemma, pleas rewrite the previous proof
   of g-e() form into the THEN form.
   Actually, this is the only form that we accept as a complete proof.
   June has a script for this conversion (thenify.py), but this is really WIP
   at the moment; he will let you know when it is ready. *)
let PLUS_ONE = prove(`!n. n + 1 = 1 + n`,
  REPEAT STRIP_TAC THEN
  CHEAT_TAC);;


(* 2. DISTRIBUTIVE *)
g `!n m k. n * (m + k) = n * m + n * k`;;
(* hint: "search [`n * (m + k)`];;" *)
e(REPEAT STRIP_TAC);;
e(CHEAT_TAC);;


(* 3. TRANSITIVE *)
g `!n m k. n < m /\ m <= k ==> n < k`;;
(* /\ stands for 'and' (&&).
   Hint: you will want to use 'search' again :)
   If you want to use 'REPEAT STRIP_TAC', ARITH_TAC won't work because
   useful information is in assumptions. In this case, use ASM_ARITH_TAC! *)
e(CHEAT_TAC);;


(* 4. FACTORIZE *)
g `!x y. (x + y) EXP 2 = x EXP 2 + 2 * x * y + y EXP 2`;;
e(CHEAT_TAC);;


(* 5. SUBTRACT *)
(* Natural number subtraction is slightly different from integer subtraction:
   given 'x - y', if y is larger than x, the result is simply 0. *)
g `2 - 3 = 0`;;
(* You can use ARITH_TAC of course, but you can also use
   'CONV_TAC NUM_REDUCE_CONV' which is applying 'NUM_REDUCE_CONV' conversion
   (which simply calculates numbers in the expression) to prove the goal.*)
e(CHEAT_TAC);;


(* 6. MOD_REFL *)
g `!x. x MOD x = 0`;;
(* ARITH_TAC doesn't work anymore! You will want to search a necessary lemma
   and rewrite using it.
   Use the search command or HOL Light Search webpage online! *)
e(CHEAT_TAC);;


(* 7. MOD_ADD *)
g `!x. (x + 2 EXP 64) MOD 2 EXP 64 = x MOD 2 EXP 64`;;
(* You can use 6. MOD_ZERO to prove this problem. On top of this,
   (1) You will need to use 'GSYM <rewrite-rule>'. For example,
      # MOD_REFL;;
      val it : thm = |- !n. n MOD n = 0
      # GSYM MOD_REFL;;
      val it : thm = |- !n. 0 = n MOD n
   (2) You will need to use ONCE_REWRITE_TAC to avoid an infinite loop
       of REWRITE_TAC which happens when the rewrite rule can be
       applied infinite times.
   (3) You will need to find three more lemmas..! *)
e(CHEAT_TAC);;


(* 8. MOD_SUBIFGE *)
(* A famous expression for optimized modulo operation *)
g `!x y.
  x < 2 EXP 64 /\ y < 2 EXP 64 ==>
  (x + y) MOD 2 EXP 64 =
  if x + y >= 2 EXP 64 then (x + y) - 2 EXP 64 else x + y`;;
(* Hint: there is a lemma for this that is very similar to this.
   But, the lemma will require matching assumptions (x < .. /\ y < ..).
   You can use IMP_REWRITE_TAC which will automatically find the necessary
   assumptions.
   Then, you will want to rewrite the if condtion using ARITH_RULE, e.g.,
      ARITH_RULE `!a b. (a >= b) <=> ~(a < b)`.
   Finally, you will want to use MESON_TAC[] which is a powerful automated
   tactic for proving first-order logic problems. *)
e(REPEAT STRIP_TAC);;
e(CHEAT_TAC);;


(* 9. CONJUNCTION *)
g `!n. 1 < n /\ n < 10 ==> 0 < n /\ n < 11`;;
(* ARITH_TAC will solve this goal, but let's not rely on this. *)
e(GEN_TAC THEN STRIP_TAC);;
(* CONJ_TAC will split `0 < n /\ n < 11` into two goals:
   (1) 0 < n
   (2) n < 11 *)
e(CONJ_TAC);;
  (* Again, ASM_ARITH_TAC will prove this, but let's not use it.
     Let's use transitivity of '<' : x < y /\ y < z ==> x < z.
     Using 'MATCH_MP_TAC (transitivity lemma)' will make
     goal `?n'. 0 < n' /\ n' < n`, where `?n. ...` is `exists n. ....`.
     You can use `EXISTS_TAC ..` in this case.
     After EXISTS_TAC, there is one more tactic that you would like
     to use one of your assumptions. Hint: it starts with ASM_! *)
  e(CHEAT_TAC);;

  (* Second subgoal! *)
  e(CHEAT_TAC);;

(* The THEN form of the prove above will look like this.
   [.. ; ..] is a syntax for creating a list in OCaml *)
let EXERCISE_CONJUNCTION = prove(`!n. 1 < n /\ n < 10 ==> 0 < n /\ n < 11`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [
    CHEAT_TAC;
    CHEAT_TAC
  ]);;


(* 10. LT_SUBTRACT (Advanced)
       (This exercise is advanced not becaue the lemma is fancy, but
        this teaches several tactics at once) *)
g `!x y z. z <= x /\ x < y ==> x - z < y - z`;;
(* ARITH_TAC will solve this goal, but let's not rely on this. *)
e(REPEAT STRIP_TAC);;
(* Let's use LE_EXISTS to prove this, which is:
    # LE_EXISTS;;
    val it : thm = |- !m n. m <= n <=> (?d. n = m + d)
   To use this lemma, you need to pick up the `z <= x` assumption
   first. How do we do it? *)
e(UNDISCH_THEN `z <= x` (fun (th:thm) ->
  (* Use OCaml's printf function to print a theorem *)
  Printf.printf "Picked up an assumption '%s'\n" (string_of_thm th);
  (* Now put it as an assumption. *)
  ASSUME_TAC th));;

(* Now, let's pick up the lemma, then rewrite it using LE_EXISTS.
   Let's print it. *)
e(UNDISCH_THEN `z <= x` (fun (th:thm) ->
  let rewritten_thm = REWRITE_RULE[LE_EXISTS] th in
  Printf.printf "The rewritten assumption is: '%s'\n"
      (string_of_thm rewritten_thm);
  ASSUME_TAC th));;

(* Now, let's strip the '?d.' part, using CHOOSE_TAC, and assume it! *)
e(UNDISCH_THEN `z <= x`
  (fun th -> CHOOSE_TAC (REWRITE_RULE[LE_EXISTS] th)));;

(* Can we do the same thing for `y` in order to create `y = z + d'`?
   To do this, you will need `z <= y`. Let's do this using SUBGOAL_THEN. *)
e(SUBGOAL_THEN `z <= y` ASSUME_TAC THENL [
    (* SUBGOAL_THEN creates two subgoals: one for this sublemma's proof *)
    ASM_ARITH_TAC; (* Let's use the magic *)

    (* and what to do with the new lemma. Let's put ALL_TAC to proceed.*)
    ALL_TAC
  ]);;

(* Now we can do the same thing for `z`. Let's proceed. *)
e(CHEAT_TAC);;
(* Feel free to use UNDISCH_TAC which is similar to UNDISCH_THEN,
   except that it simply puts it at the LHS of the new implication goal. *)


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
(* ARITH_TAC will work right now, but let's not rely on the tool. *)
(* You will want to consider two cases: (1) x >= m, (2) x < m. *)
(* Command `help "ASM_CASES_TAC";;` will be helpful. *)
e(ASM_CASES_TAC `x >= m`);;
  (* The first case: `x >= m` is true *)
  e(ASM_REWRITE_TAC[]);;
  (* You can use LT_SUBTRACT because the goal is `x - m < m` and m is (2*m-m),
     but how do we change it to the form?
     There are multiple answers, but we can use 'GEN_REWRITE_TAC RAND_CONV [..]'
     to enforce rewriting to the right-hand side only.
  *)
  e(GEN_REWRITE_TAC RAND_CONV [ARITH_RULE`m=2*m-m`]);;
  e(CHEAT_TAC);;

  (* The second case: `x >= m` is false *)
  e(ASM_REWRITE_TAC[]);;
  e(CHEAT_TAC);;
