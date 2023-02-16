# hol-light-materials
Online materials for HOL Light:
- [Tutorial](https://www.cl.cam.ac.uk/~jrh13/hol-light/tutorial.pdf)
- Reference Manual ([pdf](https://www.cl.cam.ac.uk/~jrh13/hol-light/reference.pdf), [html](https://www.cl.cam.ac.uk/~jrh13/hol-light/reference.html))
- Very Quick Reference ([pdf](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.pdf), [txt](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.txt))

## Fundamentals

```ocaml
(* Location: fusion.ml *)
(* type is a type *)
type hol_type = Tyvar of string
              | Tyapp of string *  hol_type list

(* term is a mathematical expression *)
type term = Var of string * hol_type
          | Const of string * hol_type
          | Comb of term * term
          | Abs of term * term

(* thm (theorem) is a proven fact *)
type thm = Sequent of (term list * term)
```

```ocaml
(* Location: equal.ml *)
(* conv (conversion) is simply an inference rule of type term -> thm that when given
   a term t, always returns (assuming it doesn’t fail) an equational theorem of the form
   `t = t′, that is, it proves that the term it was given is equal to some other term,
   possibly the same as the original. *)
type conv = term->thm;;
```

```ocaml
(* Location: tactics.ml *)
(* goal consists of named hypotheses ((string * thm) list) and yet unproven conclusion *)
type goal = (string * thm) list * term;;

(* a tactic for writing a backward proof. The definition of goalstate is kind of complicated. *)
type tactic = goal -> goalstate;;

type thm_tactic = thm -> tactic;;
```


## Tactics in HOL Light vs. Coq

| HOL Light                           | Coq                                                                                                                                                                |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| ABBREV_TAC \`x=t\`                    |  `remember t as x`                                                                                                                                                 |
| ABS_TAC                             |  `extensionality` in Coq.Logic.FunctionalExtensionality                                                                                                          |
| ACCEPT_TAC thm                      |  `exact thm`                                                                                                                                                       |
| ALL_TAC                             |  `idtac` without a user message                                                                                                                                    |
| ANTS_TAC                            |  If the goal conclusion is `(p ==> q) ==> r`, this is equivalent to `assert (H: p). { (subgoal) } intros HIMPLY. apply HIMPLY in H. generalize H`           |
| AP_TERM_TAC                         |  `f_equal`                                                                                                                                                         |
| AP_THM_TAC                          |  `apply equal_f`                                                                                                                                                   |
| ARITH_TAC                           |  Properly apply solvers in   Micromega (`lia`, `nia`, …). Sometimes `nia` can solve a goal that ARITH_TAC   cannot (e.g., `x*x-x = x*(x-1)`).                        |
| ASM_CASES_TAC   tm                  |  Given `Axiom excluded_middle_axiom = forall P, P \/ ~P`, `assert (H_ANON := excluded_middle_axiom tm). destruct H_ANON as [H2 \| H2]; generalize H2.`         |
| ASM_MESON_TAC[thm list]             |  See MESON_TAC.                                                                                                                                                    |
| ASM_REWRITE_TAC[thm list]           |  See REWRITE_TAC.                                                                                                                                                  |
| ASSUME_TAC   thm                    |  `assert (H_ANON := thm)`                                                                                                                                          |
| BETA_TAC                            |  `cbv beta`                                                                                                                                                        |
| CHOOSE_TAC thm                      |  If `thm` is `exists x. P x`, do `assert (HANON := thm). destruct HANON`. |
| CONJ_TAC                            |  `split` of a conjunction conclusion only                                                                                                                             |
| CONS_11                             |  `destruct` for list |
| CONV_TAC NUM_REDUCE_CONV            |  `simpl` for natural numbers |
| CONV_TAC INT_REDUCE_CONV            |  `simpl` for ints |
| CHEAT_TAC                           |  `admit` |
| DESTRUCT_TAC                            |  `destruct`, but with a slightly different syntax (see [the doc.](https://github.com/jrh13/hol-light/blob/master/Help/DESTRUCT_TAC.doc))                                                                                                                             |
| DISCH_TAC                           |  `intro`, but moves an assumption only                                                                                                                           |
| DISCH_THEN(LABEL_TAC "Hname")       |  `intro Hname` |
| DISCH_THEN(LABEL_TAC "Hname" o REWRITE_RULE\[MOD_EQ_0\] | `intro Hname. rewrite MOD_EQ_0 in Hname` |
| DISJ_CASES_TAC thm                  |  `destruct` for disjunction |
| DISJ1_TAC                           |  `left`                                                                                                                                                            |
| DISJ2_TAC                           |  `right`                                                                                                                                                           |
| EQ_TAC                              |  `split` for an iff conclusion only                                                                                                                                      |
| EXISTS_TAC                          |  `exists`                                                                                                                                                          |
| FIX_TAC                          | No matching tactic in Coq (correct me if I am wrong)                                                                                                                                                          |
| GEN_TAC                             |  `intro`, but targets   non-propositions only                                                                                                                      |
| IMP_REWRITE_TAC[thm list]           |  Given a list of theorems that look like `P ==> l = r`, do `rewrite` and add `P` to the goal as a conjunction. If the rewritten part is at `P'` of some other implication `P' ==> Q'`, `P` is added as `(P ==> P'[l/r]) ==> Q`. |
| INDUCT_TAC                          |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have 'num' type ('nat' in   Coq).                                         |
| INTRO_TAC                          |  `intros` + `destruct` of dis/conjunctions                                         |
| LABEL_TAC s thm                     |  `assert (s := thm)`                                                                                                                                               |
| LABEL_TAC s (SPECL [t0;t1;…]   thm) |  `specialize (thm t0 t1 …) as s`                                                                                                                                   |
| LIST_INDUCT_TAC                     |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have '(ty)list' type   ('list ty' in Coq).                                |
| MATCH_MP_TAC thm                    |  `apply`, but the applying thm must be of the form `P ==> Q` |
| MATCH_ACCEPT_TAC thm                |  `apply` |
| MESON_TAC[thm list]                 |  `firstorder` with thms registered   to hint databases. Unlike ASM_MESON_TAC, this does not use assumptions.                                                       |
| NO_TAC                              |  `fail`   |
| ONCE_REWRITE_TAC[thm list]          |  `rewrite` but rewrites only once.                                                                                                                                 |
| tac ORELSE tac                      |  `orelse` in Ltac2?                                                                                                                                                |
| REAL_ARITH_TAC                      |  `lra`?                                                                                                                                                            |
| REFL_TAC                            |  `reflexivity`, but REFL_TAC only   checks syntactic equivalence (e.g. x = 0 + x cannot be proved)                                                                 |
| REPEAT                              |  `repeat`                                                                                                                                                          |
| REWRITE_TAC [thm list]              |  `repeat (try rewrite thm[0]; try rewrite thm[1]; …)`, but unlike `rewrite` in Coq, if the conclusion matches exactly one of thm list, the goal is immediately proved. |
| REWRITE_TAC [GSYM thm]              |  `rewrite <- thm`, with the characteristics described in the generic REWRITE_TAC form above |
| SIMP_TAC [thm list]                 |  Maybe `simpl` in Coq, but does not immediately look into definitions. Therefore, SIMP_TAC cannot simplify `0 + x` into `x` without additional hints.          |
| SPEC_TAC(\`x:ty1\`, \`y:ty2\`)          |  `generalize x as y`. If `x` is not used in any assumption and `x` is `y`, this is equal to `revert x`.                                                          |
| STRIP_TAC                           |  `split` (for conjunctions) + `intro` (GEN_TAC + CONJ_TAC + elaborated version of DISCH_TAC)                                                                     |
| SUBGOAL_THEN tm ASSUME_TAC          |  `cut tm. intros HASSUME`, or `assert (HASSUME: tm)` with a swapped subgoal order                                                                               |
| SUBGOAL_THEN tm (LABEL_TAC "name")  |  `cut tm. intros name`, or `assert (name: tm)` with a swapped subgoal order                                                                               |
| TRY tac                             |  `try tac`                                                                                                                                                         |
| tac THEN tac                        |  `tac; tac`                                                                                                                                                               |
| tac THENL [tac list]                |  `tac. { tac[0]. } { tac[1]. } …`                                                                                                                                     |
| UNDISCH_TAC                         |  `generalize` for a prop.                                                                                                                                          |
| X_GEN_TAC t                         |  `intro t`, but targets non-propositions only                                                                                                                    |
| X_META_EXISTS_TAC \`x:ty\`            | `eexists`. Set the name of the meta variable to `x`.                                                                                                               |

- HOL Light tactics that appear in the [Quick Reference Guide](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.txt) but are not matched yet: COND_CASES_TAC, DISCH_THEN ttac, EVERY_ASSUM ttac, EXPAND_TAC s, FIRST_ASSUM ttac, FIRST_X_ASSUM ttac, GEN_REWRITE_TAC cnvn [th], MAP_EVERY, MP_TAC thm, POP_ASSUM ttac, POP_ASSUM_LIST ttac, RULE_ASSUM_TAC, SET_TAC [thm list], USE_THEN s ttac

- Frequently used Coq tactics that are not matched yet: `inversion`, `eapply`

### Examples

```ocaml
(* Given n:nat, do destruct n as [ | S n'] *)
DISJ_CASES_TAC(SPECL [`x:num`] num_CASES)
```

```ocaml
(* Calculate 1 + 2 - 3 *)
NUM_REDUCE_CONV `1 + 2 - 3` (* Note that this is 1 because it is 1 + (2 - 3)!! *)
```

## Commands in HOL Light vs. Coq

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
