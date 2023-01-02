# hol-light-materials
Online materials for HOL Light

## Tactics in HOL Light vs. Coq

| HOL Light                           | Coq                                                                                                                                                                |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| ABBREV_TAC \`x=t\`                    |  `remember t as x`                                                                                                                                                 |
| ABS_TAC                             |  `extensionality` in   Coq.Logic.FunctionalExtensionality                                                                                                          |
| ACCEPT_TAC thm                      |  `exact thm`                                                                                                                                                       |
| ALL_TAC                             |  `idtac` without a user message                                                                                                                                    |
| ANTS_TAC                            |  If the goal conclusion is `(p   ==> q) ==> r`, this is equivalent to `assert (H: p). { (subgoal) } intros HIMPLY. apply HIMPLY in H. generalize H`           |
| AP_TERM_TAC                         |  `f_equal`                                                                                                                                                         |
| AP_THM_TAC                          |  `apply equal_f`                                                                                                                                                   |
| ARITH_TAC                           |  Properly apply solvers in   Micromega (`lia`, `nia`, …). Sometimes `nia` can solve a goal that ARITH_TAC   cannot (e.g., x*x-x = x*(x-1)).                        |
| ASM_CASES_TAC   tm                  |  Given `Axiom excluded_middle_axiom = forall P, P \/ ~P`, `assert (H_ANON := excluded_middle_axiom tm). destruct H_ANON as [H2 \| H2]; generalize H2.`         |
| ASM_MESON_TAC[thm list]             |  See MESON_TAC.                                                                                                                                                    |
| ASM_REWRITE_TAC[thm list]           |  See REWRITE_TAC.                                                                                                                                                  |
| ASSUME_TAC   thm                    |  `assert (H_ANON := thm)`                                                                                                                                          |
| BETA_TAC                            |  `cbv beta`                                                                                                                                                        |
| CONJ_TAC                            |  `split` of a conjunction conclusion only                                                                                                                             |
| DISCH_TAC                           |  `intro`, but moves an assumption only                                                                                                                           |
| DISJ1_TAC                           |  `left`                                                                                                                                                            |
| DISJ2_TAC                           |  `right`                                                                                                                                                           |
| EQ_TAC                              |  `split` for an iff conclusion only                                                                                                                                      |
| EXISTS_TAC                          |  `exists`                                                                                                                                                          |
| GEN_TAC                             |  `intro`, but targets   non-propositions only                                                                                                                      |
| INDUCT_TAC                          |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have 'num' type ('nat' in   Coq).                                         |
| LABEL_TAC s thm                     |  `assert (s := thm)`                                                                                                                                               |
| LABEL_TAC s (SPECL [t0;t1;…]   thm) |  `specialize (thm t0 t1 …) as s`                                                                                                                                   |
| LIST_INDUCT_TAC                     |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have '(ty)list' type   ('list ty' in Coq).                                |
| MATCH_MP_TAC                        |  `apply`                                                                                                                                                           |
| MESON_TAC[thm list]                 |  `firstorder` with thms registered   to hint databases. Unlike ASM_MESON_TAC, this does not use assumptions.                                                       |
| ONCE_REWRITE_TAC[thm list]          |  `rewrite` but rewrites only once.                                                                                                                                 |
| tac ORELSE tac                      |  `orelse` in Ltac2?                                                                                                                                                |
| REAL_ARITH_TAC                      |  `lra`?                                                                                                                                                            |
| REFL_TAC                            |  `reflexivity`, but REFL_TAC only   checks syntactic equivalence (e.g. x = 0 + x cannot be proved)                                                                 |
| REPEAT                              |  `repeat`                                                                                                                                                          |
| REWRITE_TAC [thm list]              |  `repeat (try rewrite thm[0]; try rewrite thm[1]; …)`, but unlike `rewrite` in Coq, if the conclusion matches exactly one of thm list, the goal is immediately proved. |
| SIMP_TAC [thm list]                 |  Maybe `simpl` in Coq, but does not immediately look into definitions. Therefore, SIMP_TAC cannot simplify `0 + x` into `x` without additional hints.          |
| SPEC_TAC(\`x:ty1\`, \`y:ty2\`)          |  `generalize x as y`. If `x` is not used in any assumption and `x` is `y`, this is equal to `revert x`.                                                          |
| STRIP_TAC                           |  `split` (for conjunctions) + `intro` (GEN_TAC + CONJ_TAC + elaborated version of DISCH_TAC)                                                                     |
| SUBGOAL_THEN tm ASSUME_TAC          |  `cut tm. intros HASSUME`, or `assert (HASSUME: tm)` with a swapped subgoal order                                                                               |
| TRY tac                             |  `try tac`                                                                                                                                                         |
| tac THEN tac                        |  `;`                                                                                                                                                               |
| tac THENL [tac list]                |  `. { tac[0]. } { tac[1]. } …`                                                                                                                                     |
| UNDISCH_TAC                         |  `generalize` for a prop.                                                                                                                                          |
| X_GEN_TAC t                         |  `intro t`, but targets non-propositions only                                                                                                                    |
| X_META_EXISTS_TAC \`x:ty\`            | `eexists`. Set the name of the meta variable to `x`.                                                                                                               |

- HOL Light tactics that appear in the [Quick Reference Guide](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.txt) but are not matched yet: COND_CASES_TAC, DISCH_THEN ttac, EVERY_ASSUM ttac, EXPAND_TAC s, FIRST_ASSUM ttac, FIRST_X_ASSUM ttac, GEN_REWRITE_TAC cnvn [th], MAP_EVERY, MP_TAC thm, POP_ASSUM ttac, POP_ASSUM_LIST ttac, RULE_ASSUM_TAC, SET_TAC [thm list], USE_THEN s ttac
