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

| HOL Light                           | Coq                                                                                                                                                                | Doc |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|------|
| ABBREV_TAC \`x=t\`                    |  `remember t as x` and replace `t` with `x`. | [ABBREV_TAC](https://github.com/jrh13/hol-light/blob/master/Help/ABBREV_TAC.doc) |
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
| EXPAND_TAC s                        |  `rewrite <- H` where `H` is `t = s` | [EXPAND_TAC](https://github.com/jrh13/hol-light/blob/master/Help/EXPAND_TAC.doc) |
| FIX_TAC                          | No matching tactic in Coq (correct me if I am wrong)                                                                                                                                                          |
| GEN_TAC                             |  `intro`, but targets   non-propositions only                                                                                                                      |
| IMP_REWRITE_TAC[thm list]           |  Given a list of theorems that look like `P ==> l = r`, do `rewrite` and add `P` to the goal as a conjunction. If the rewritten part is at `P'` of some other implication `P' ==> Q'`, `P` is added as `(P ==> P'[l/r]) ==> Q`. Thos also works for theorems that look like `P ==> l1 = r1 /\ l2 = r2 /\ ..` | [IMP_REWRITE_TAC](https://github.com/jrh13/hol-light/blob/master/Help/IMP_REWRITE_TAC.doc) |
| INDUCT_TAC                          |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have 'num' type ('nat' in   Coq).                                         |
| INTRO_TAC                          |  `intros` + `destruct` of dis/conjunctions                                         |
| LABEL_TAC s thm                     |  `assert (s := thm)`                                                                                                                                               |
| LABEL_TAC s (SPECL [t0;t1;…]   thm) |  `specialize (thm t0 t1 …) as s`                                                                                                                                   |
| LABEL_TAC s (ISPECL [\`x:(32)word\`;…]   thm) |  `specialize (thm t0 t1 …) as s` with type instantiations |
| LIST_INDUCT_TAC                     |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have '(ty)list' type   ('list ty' in Coq).                                |
| MATCH_MP_TAC thm                    |  `apply`, but the applying thm must be of the form `P ==> Q` |
| MATCH_ACCEPT_TAC thm                |  `apply` |
| MESON_TAC[thm list]                 |  `firstorder` with thms registered   to hint databases. Unlike ASM_MESON_TAC, this does not use assumptions.                                                       |
| MP_TAC thm | `assert (s := thm). generalize thm` | [MP_TAC](https://github.com/jrh13/hol-light/blob/master/Help/MP_TAC.doc) |
| NO_TAC                              |  `fail`   |
| ONCE_REWRITE_TAC[thm list]          |  `rewrite` but rewrites only once.                                                                                                                                 |
| tac ORELSE tac                      |  `orelse` in Ltac2?                                                                                                                                                |
| REAL_ARITH_TAC                      |  `lra`?                                                                                                                                                            |
| REFL_TAC                            |  `reflexivity`, but REFL_TAC only   checks syntactic equivalence (e.g. x = 0 + x cannot be proved)                                                                 |
| REPEAT                              |  `repeat`                                                                                                                                                          |
| REWRITE_TAC [thm list]              |  `repeat (try rewrite thm[0]; try rewrite thm[1]; …)`, but unlike `rewrite` in Coq, if the conclusion matches exactly one of thm list, the goal is immediately proved. |
| REWRITE_TAC [GSYM thm]              |  `rewrite <- thm`, with the characteristics described in the generic REWRITE_TAC form above |
| RULE_ASSUM_TAC (fn:thm->thm)        |  Perform fn to every assumption. |
| SIMP_TAC [thm list]                 |  REWRITE_TAC, but (1) applies intrinsic rewrite rules as well (basic_rewrites and basic_convs), and (2) accepts conditional rewrite rules of form `c ==> l = r`. The conditional rewrite rules are applied if `c` can be simplified into T. Different from `simpl` in Coq because it does not immediately look into the definitions. For example, SIMP_TAC cannot simplify `0 + x` into `x` without additional hints. | [SIMP_TAC](https://github.com/jrh13/hol-light/blob/master/Help/SIMP_TAC.doc) |
| SPEC_TAC(\`x:ty1\`, \`y:ty2\`)          |  `generalize x as y`. If `x` is not used in any assumption and `x` is `y`, this is equal to `revert x`.                                                          |
| STRIP_TAC                           |  `split` (for conjunctions) + `intro` (GEN_TAC + CONJ_TAC + elaborated version of DISCH_TAC)                                                                     |
| SUBGOAL_THEN tm ASSUME_TAC          |  `cut tm. intros HASSUME`, or `assert (HASSUME: tm)` with a swapped subgoal order                                                                               |
| SUBGOAL_THEN tm (LABEL_TAC "name")  |  `cut tm. intros name`, or `assert (name: tm)` with a swapped subgoal order                                                                               |
| TRY tac                             |  `try tac`                                                                                                                                                         |
| tac THEN tac                        |  `tac; tac`                                                                                                                                                               |
| tac THENL [tac list]                |  `tac. { tac[0]. } { tac[1]. } …`                                                                                                                                     |
| UNDISCH_TAC                         |  `generalize` for a prop.                                                                                                                                          |
| USE_THEN s ttac   | Given an assumption whose name is s, apply ttac which should be analogous to `fun thm -> (*tactic*)`. | [USE_THEN](https://github.com/jrh13/hol-light/blob/master/Help/USE_THEN.doc) |
| X_GEN_TAC t                         |  `intro t`, but targets non-propositions only                                                                                                                    |
| X_META_EXISTS_TAC \`x:ty\`            | `eexists`. Set the name of the meta variable to `x`.                                                                                                               |

- HOL Light tactics that appear in the [Quick Reference Guide](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.txt) but are not matched yet: COND_CASES_TAC, DISCH_THEN ttac, EVERY_ASSUM ttac, FIRST_ASSUM ttac, FIRST_X_ASSUM ttac, GEN_REWRITE_TAC cnvn [th], MAP_EVERY, MP_TAC thm, POP_ASSUM ttac, POP_ASSUM_LIST ttac, RULE_ASSUM_TAC, SET_TAC [thm list]

- Frequently used Coq tactics that are not matched yet: `inversion`, `eapply`

### Examples

```ocaml
(* Given n:nat, do destruct n as [ | S n'] *)
DISJ_CASES_TAC(SPECL [`x:num`] num_CASES)
```

```ocaml
(* Apply the DIMINDEX_32 rewrite rule to every assumption. *)
RULE_ASSUM_TAC (REWRITE_RULE [DIMINDEX_32])
```

```ocaml
(* Pick an assumption "Hx0lt" (which becomes the 'thm' variable), and rewrite the goal using an equation
   'MATCH_MP add_64_32_mod_32_eq thm'. Note that add_64_32_mod_32_eq is some P -> Q, and thm is matched to P. *)
USE_THEN "Hx0lt" (fun thm -> REWRITE_TAC[MATCH_MP add_64_32_mod_32_eq thm])
```

```ocaml
(* Pick an assumption "H" and generalize it. *)
USE_THEN "H" MP_TAC
```

## Inference Rules

| HOL Light                           | Coq                                                                                                                                                                | Doc |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|------|
| MP P Q  | `P Q` where `P` is `Prop -> Prop`, `Q` is Prop | [MP](https://github.com/jrh13/hol-light/blob/master/Help/MP.doc) |
| MATCH_MP P Q | equivalent to MP P Q, but instantiates quantified variables | [MATCH_MP](https://github.com/jrh13/hol-light/blob/master/Help/MATCH_MP.doc) |
| REWRITE_RULE [thms] thm | Given thm, return a new theorem that has thms rewritten in it | [REWRITE_RULE](https://github.com/jrh13/hol-light/blob/master/Help/REWRITE_RULE.doc) |

#### Examples

```ocaml
(* Get the LHS of DIVISION_SIMP which is thm `|- (!m n. m DIV n * n + m MOD n = m) /\ (!m n. n * m DIV n + m MOD n = m)`,
   and specialize it. *)
SPECL [`x:num`; `2 EXP 32:num`] (CONJUNCT1 DIVISION_SIMP);;
```

```ocaml
(* Given a theorem VAL_MOD_REFL, (1) specialize it with the `y` variable, and (2) rewrite the theorem using
   the DIMINDEX_32 theorem. *)
REWRITE_RULE [DIMINDEX_32] (ISPECL [`y:(32)word`] VAL_MOD_REFL)
```

## Useful Conversions

- MOD_DOWN_CONV
- NUM_REDUCE_CONV

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

## Misc

### Thenify

`thenify.py` converts a properly formatted sequence of `e(..);;` commands into the `.. THEN ..` format.
If some tactic produces multiple subgoals, the beginning of each subgoal must be itemized with `- ` and the following
lines must have extra indentations. Currently, the indentation string is fixed to two spaces (`  `).
`thenify_test_input.txt` has an example and `thenify.py thenify_test_input.txt` shows the then-ified output. :)

### Others

```ocaml
(* Given an OCaml string 'name' and term 'tm', make a definition `name = tm` *)
new_definition (mk_eq (mk_var (name, `:(..type..)`), tm))
```
