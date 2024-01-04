# HOL Light vs. Coq

## Tactics in HOL Light vs. Coq

| HOL Light                           | Coq                                                                                                                                                                | Doc |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|------|
| `` ABBREV_TAC `x=t` ``                    |  `remember t as x` and replace `t` with `x`. | [ABBREV_TAC](https://github.com/jrh13/hol-light/blob/master/Help/ABBREV_TAC.hlp) |
| `ABS_TAC`                             |  `extensionality` in Coq.Logic.FunctionalExtensionality                                                                                                          |
| `ACCEPT_TAC thm`                      |  `exact thm`                                                                                                                                                       |
| `ALL_TAC`                             |  `idtac` without a user message                                                                                                                                    |
| `ANTS_TAC`                            |  If the goal conclusion is `(p ==> q) ==> r`, this is equivalent to `assert (H: p). { (subgoal) } intros HIMPLY. apply HIMPLY in H. generalize H`           |
| `AP_TERM_TAC`                         |  `f_equal`                                                                                                                                                         |
| `AP_THM_TAC`                          |  `apply equal_f`                                                                                                                                                   |
| ``ARITH_TAC``                           |  Properly apply solvers in   Micromega (`lia`, `nia`, …). Sometimes `nia` can solve a goal that ARITH_TAC   cannot (e.g., `x*x-x = x*(x-1)`). Note that this tactic does not utilize assumptions; to use assumptions, use `ASM_ARITH_TAC`. | [ARITH_TAC](https://github.com/jrh13/hol-light/blob/master/Help/ARITH_TAC.hlp) |
| `ASM_CASES_TAC tm`                  |  Given `Axiom excluded_middle_axiom = forall P, P \/ ~P`, `assert (H_ANON := excluded_middle_axiom tm). destruct H_ANON as [H2 \| H2]; generalize H2.`         |
| `ASM_MESON_TAC[thm list]`             |  See `MESON_TAC`.                                                                                                                                                    |
| `ASM_REWRITE_TAC[thm list]`           |  See `REWRITE_TAC`.                                                                                                                                                  |
| `ASSUME_TAC thm`                    |  `assert (H_ANON := thm)`                                                                                                                                          |
| `ASSUM_LIST f` | Probably in Ltac only? | [ASSUM_LIST](https://github.com/jrh13/hol-light/blob/master/Help/ASSUM_LIST.hlp) |
| `BETA_TAC`                            |  `cbv beta`                                                                                                                                                        |
| `CHOOSE_TAC thm`                      |  If `thm` is `exists x. P x`, do `assert (HANON := thm). destruct HANON`. |
| `CONJ_TAC`                            |  `split` of a conjunction conclusion only                                                                                                                             |
| `CONS_11`                             |  `destruct` for list |
| `CONV_TAC NUM_REDUCE_CONV`            |  `simpl` for natural numbers |
| `CONV_TAC INT_REDUCE_CONV`            |  `simpl` for ints |
| `CHEAT_TAC`                           |  `admit` |
| `DESTRUCT_TAC`                            |  `destruct`, but with a slightly different syntax (see [the doc.](https://github.com/jrh13/hol-light/blob/master/Help/DESTRUCT_TAC.hlp))                                                                                                                             |
| `DISCH_TAC`                           |  `intro`, but moves an assumption only                                                                                                                           |
| `DISCH_THEN(LABEL_TAC "Hname")`       |  `intro Hname` |
| `DISCH_THEN(LABEL_TAC "Hname" o REWRITE_RULE[MOD_EQ_0]` | `intro Hname. rewrite MOD_EQ_0 in Hname` |
| `DISJ_CASES_TAC thm`                  |  `destruct` for disjunction |
| `DISJ1_TAC`                           |  `left`                                                                                                                                                            |
| `DISJ2_TAC`                           |  `right`                                                                                                                                                           |
| `EQ_TAC`                              |  `split` for an iff conclusion only                                                                                                                                      |
| `EVERY_ASSUM ttac` | For each assumption `thm`, run `ttac(thm)`. | [EVERY_ASSUM](https://github.com/jrh13/hol-light/blob/master/Help/EVERY_ASSUM.hlp) |
| `EXISTS_TAC`                          |  `exists`                                                                                                                                                          |
| `EXPAND_TAC s`                        |  `rewrite <- H` where `H` is `t = s` | [EXPAND_TAC](https://github.com/jrh13/hol-light/blob/master/Help/EXPAND_TAC.hlp) |
| `FIND_ASSUM ttac term` | If assumption `H:term` exists, apply tactic `ttac H`. | [FIND_ASSUM](https://github.com/jrh13/hol-light/blob/master/Help/FIND_ASSUM.hlp) |
| `FIRST_ASSUM ttac` | ? | [FIRST_ASSUM](https://github.com/jrh13/hol-light/blob/master/Help/FIRST_ASSUM.hlp) |
| `FIRST_ASSUM CONTR_TAC` | `exfalso` | [CONTR_TAC](https://github.com/jrh13/hol-light/blob/master/Help/CONTR_TAC.hlp) |
| `FIX_TAC s`                          | No matching tactic in Coq (correct me if I am wrong); `intros`, but specifies the variable to introduce | [FIX_TAC](https://github.com/jrh13/hol-light/blob/master/Help/FIX_TAC.hlp) |
| `GEN_TAC`                             |  `intro`, but targets   non-propositions only                                                                                                                      |
| `IMP_REWRITE_TAC[thm list]`           |  Given a list of theorems that look like `P ==> l = r`, do `rewrite` and add `P` to the goal as a conjunction. If the rewritten part is at `P'` of some other implication `P' ==> Q'`, `P` is added as `(P ==> P'[l/r]) ==> Q`. Thos also works for theorems that look like `P ==> l1 = r1 /\ l2 = r2 /\ ..` | [IMP_REWRITE_TAC](https://github.com/jrh13/hol-light/blob/master/Help/IMP_REWRITE_TAC.hlp) |
| `INDUCT_TAC`                          |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have 'num' type ('nat' in   Coq).                                         |
| `INTRO_TAC`                          |  `intros` + `destruct` of dis/conjunctions                                         |
| `LABEL_TAC s thm`                     |  `assert (s := thm)`                                                                                                                                               |
| `LABEL_TAC s (SPECL [t0;t1;…]   thm)` |  `specialize (thm t0 t1 …) as s`                                                                                                                                   |
| ``LABEL_TAC s (ISPECL [`x:(32)word`;…] thm) `` |  `specialize (thm t0 t1 …) as s` with type instantiations |
| `LIST_INDUCT_TAC`                     |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have '(ty)list' type   ('list ty' in Coq).                                |
| `MAP_EVERY f l` | ? | [MAP_EVERY](https://github.com/jrh13/hol-light/blob/master/Help/MAP_EVERY.hlp) |
| `MATCH_MP_TAC thm`                    |  `apply`, but the applying thm must be of the form `P ==> Q` |
| `MATCH_ACCEPT_TAC thm`                |  `apply` |
| `MESON_TAC[thm list]`                 |  `firstorder` with thms registered   to hint databases. Unlike ASM_MESON_TAC, this does not use assumptions.                                                       |
| `MP_TAC thm` | `assert (s := thm). generalize thm` | [MP_TAC](https://github.com/jrh13/hol-light/blob/master/Help/MP_TAC.hlp) |
| `NO_TAC`                              |  `fail`   |
| `ONCE_REWRITE_TAC[thm list]`          |  `rewrite` but rewrites only once.                                                                                                                                 |
| `tac ORELSE tac`                      |  `orelse` in Ltac2?                                                                                                                                                |
| `REAL_ARITH_TAC`                      |  `lra`?                                                                                                                                                            |
| `REFL_TAC`                            |  `reflexivity`, but REFL_TAC only   checks syntactic equivalence (e.g. x = 0 + x cannot be proved)                                                                 |
| `REMOVE_THEN s ttac` | Given an assumption whose name is s, equivalent to `USE_THEN s ttac`(in HOL Light) then `clear s` (in Coq). | [REMOVE_THEN](https://github.com/jrh13/hol-light/blob/master/Help/REMOVE_THEN.hlp) |
| `REPEAT`                              |  `repeat`                                                                                                                                                          |
| `REWRITE_TAC [thm list]`              |  `repeat (try rewrite thm[0]; try rewrite thm[1]; …)`, but unlike `rewrite` in Coq, if the conclusion matches exactly one of thm list, the goal is immediately proved. |
| `REWRITE_TAC [GSYM thm]`              |  `rewrite <- thm`, with the characteristics described in the generic REWRITE_TAC form above |
| `RULE_ASSUM_TAC (fn:thm->thm)`        |  Perform fn to every assumption. | [RULE_ASSUM_TAC](https://github.com/jrh13/hol-light/blob/master/Help/RULE_ASSUM_TAC.hlp) |
| `RULE_ASSUM_TAC (REWRITE_RULE[r])` | `rewrite r in * `<code>&#124;</code>`-` | |
| `SIMP_TAC [thm list]`                 |  `REWRITE_TAC`, but (1) applies intrinsic rewrite rules as well (basic_rewrites and basic_convs), and (2) accepts conditional rewrite rules of form `c ==> l = r`. The conditional rewrite rules are applied if `c` can be simplified into T. Different from `simpl` in Coq because it does not immediately look into the definitions. For example, SIMP_TAC cannot simplify `0 + x` into `x` without additional hints. | [SIMP_TAC](https://github.com/jrh13/hol-light/blob/master/Help/SIMP_TAC.hlp) |
| `` SPEC_TAC(`x:ty1`, `y:ty2`) ``   |  `generalize x as y`. If `x` is not used in any assumption and `x` is `y`, this is equal to `revert x`.                                                          |
| `STRIP_TAC`                           |  `split` (for conjunctions) + `intro` (GEN_TAC + CONJ_TAC + elaborated version of DISCH_TAC)                                                                     |
| `SUBGOAL_THEN tm ASSUME_TAC`          |  `cut tm. intros HASSUME`, or `assert (HASSUME: tm)` with a swapped subgoal order                                                                               |
| `SUBGOAL_THEN tm (LABEL_TAC "name")`  |  `cut tm. intros name`, or `assert (name: tm)` with a swapped subgoal order                                                                               |
| `TRY tac`                             |  `try tac`                                                                                                                                                         |
| `tac THEN tac`                        |  `tac; tac`                                                                                                                                                               |
| `tac THENL [tac list]`                |  `tac. { tac[0]. } { tac[1]. } …`                                                                                                                                     |
| `UNDISCH_TAC`                         |  `generalize` for a prop.                                                                                                                                          |
| `USE_THEN s ttac`   | Given an assumption whose name is s, apply ttac which should be analogous to `fun thm -> (*tactic*)`. | [USE_THEN](https://github.com/jrh13/hol-light/blob/master/Help/USE_THEN.hlp) |
| `X_GEN_TAC t`                         |  `intro t`, but targets non-propositions only                                                                                                                    |
| `` X_META_EXISTS_TAC `x:ty` ``            | `eexists`. Set the name of the meta variable to `x`.                                                                                                               |

- HOL Light tactics that appear in the [Quick Reference Guide](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.txt) but are not matched yet: COND_CASES_TAC, FIRST_X_ASSUM ttac, GEN_REWRITE_TAC cnvn [th], MP_TAC thm, POP_ASSUM ttac, POP_ASSUM_LIST ttac, SET_TAC [thm list]

- Frequently used Coq tactics that are not matched yet: `inversion`, `eapply`


## Inference Rules

| HOL Light                           | Coq                                                                                                                                                                | Doc |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|------|
| MP P Q  | `P Q` where `P` is `Prop -> Prop`, `Q` is Prop | [MP](https://github.com/jrh13/hol-light/blob/master/Help/MP.hlp) |
| MATCH_MP P Q | equivalent to MP P Q, but instantiates quantified variables | [MATCH_MP](https://github.com/jrh13/hol-light/blob/master/Help/MATCH_MP.hlp) |
| REWRITE_RULE [thms] thm | Given thm, return a new theorem that has thms rewritten in it | [REWRITE_RULE](https://github.com/jrh13/hol-light/blob/master/Help/REWRITE_RULE.hlp) |


## Commands

| HOL Light                           | Coq                                                                                                                                                                |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| help "<keyword>"      | ?                |
| loadt "path"          | `Load "path"`    |
| search [name "ASSOC"] | `Search "ASSOC"` |
| search [\`nat\`]      | `Search nat`     |
| search [\`x + y\`]    | `Search` with the pattern |
| type_of \`term\`      | `Check term`     |
| print_goalstack (!current_goalstack) | Prints the current goal stack. |
| r N                   | Similar to `focus` (it is a tactic in Coq), but `r` rotates the subgoals |


