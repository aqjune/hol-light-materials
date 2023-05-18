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

- Proposition is simply bool.
    - Truth has a bool type (`` type_of `T` `` is bool)
    - `TAUT` allows excluded middle. Double negation elimination (`~~P -> P`) is allowed
- Allows functional extensionality
- Unbound variables are considered as universally quantified variables
    - ex) Goal `x + 0 = x` is valid, and it means `!x. x + 0 = x`
- `!P` (which is `forall x, P x` in Coq) is equivalent to `(P = \x. true)`.
    - Therefore, `!` is `\P. (P = \x. true)`.
- Unlike Coq, you cannot define a type of an empty element (`False` in Coq)
    - See also: [new_type_definition](https://github.com/jrh13/hol-light/blob/master/Help/new_type_definition.doc)
- Uses a simply typed lambda calculus. (See [TYPE.md](TYPE.md))

## Basic Syntax

- A pair of `num`: `num#num`
- Optional `num`: `num option`
- A function definition with its type explicitly specified: `` new_definition `(f:num->num) x = x + 1` ``
- `match` does not have to be a total function; conversion will fail if there is no matching pattern instead.

## AST

Please read [AST.md](AST.md).

## Tactics in HOL Light vs. Coq

| HOL Light                           | Coq                                                                                                                                                                | Doc |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|------|
| `` ABBREV_TAC `x=t` ``                    |  `remember t as x` and replace `t` with `x`. | [ABBREV_TAC](https://github.com/jrh13/hol-light/blob/master/Help/ABBREV_TAC.doc) |
| `ABS_TAC`                             |  `extensionality` in Coq.Logic.FunctionalExtensionality                                                                                                          |
| `ACCEPT_TAC thm`                      |  `exact thm`                                                                                                                                                       |
| `ALL_TAC`                             |  `idtac` without a user message                                                                                                                                    |
| `ANTS_TAC`                            |  If the goal conclusion is `(p ==> q) ==> r`, this is equivalent to `assert (H: p). { (subgoal) } intros HIMPLY. apply HIMPLY in H. generalize H`           |
| `AP_TERM_TAC`                         |  `f_equal`                                                                                                                                                         |
| `AP_THM_TAC`                          |  `apply equal_f`                                                                                                                                                   |
| ``ARITH_TAC``                           |  Properly apply solvers in   Micromega (`lia`, `nia`, …). Sometimes `nia` can solve a goal that ARITH_TAC   cannot (e.g., `x*x-x = x*(x-1)`). Note that this tactic does not utilize assumptions; to use assumptions, use `ASM_ARITH_TAC`. | [ARITH_TAC](https://github.com/jrh13/hol-light/blob/master/Help/ARITH_TAC.doc) |
| `ASM_CASES_TAC tm`                  |  Given `Axiom excluded_middle_axiom = forall P, P \/ ~P`, `assert (H_ANON := excluded_middle_axiom tm). destruct H_ANON as [H2 \| H2]; generalize H2.`         |
| `ASM_MESON_TAC[thm list]`             |  See `MESON_TAC`.                                                                                                                                                    |
| `ASM_REWRITE_TAC[thm list]`           |  See `REWRITE_TAC`.                                                                                                                                                  |
| `ASSUME_TAC thm`                    |  `assert (H_ANON := thm)`                                                                                                                                          |
| `BETA_TAC`                            |  `cbv beta`                                                                                                                                                        |
| `CHOOSE_TAC thm`                      |  If `thm` is `exists x. P x`, do `assert (HANON := thm). destruct HANON`. |
| `CONJ_TAC`                            |  `split` of a conjunction conclusion only                                                                                                                             |
| `CONS_11`                             |  `destruct` for list |
| `CONV_TAC NUM_REDUCE_CONV`            |  `simpl` for natural numbers |
| `CONV_TAC INT_REDUCE_CONV`            |  `simpl` for ints |
| `CHEAT_TAC`                           |  `admit` |
| `DESTRUCT_TAC`                            |  `destruct`, but with a slightly different syntax (see [the doc.](https://github.com/jrh13/hol-light/blob/master/Help/DESTRUCT_TAC.doc))                                                                                                                             |
| `DISCH_TAC`                           |  `intro`, but moves an assumption only                                                                                                                           |
| `DISCH_THEN(LABEL_TAC "Hname")`       |  `intro Hname` |
| `DISCH_THEN(LABEL_TAC "Hname" o REWRITE_RULE[MOD_EQ_0]` | `intro Hname. rewrite MOD_EQ_0 in Hname` |
| `DISJ_CASES_TAC thm`                  |  `destruct` for disjunction |
| `DISJ1_TAC`                           |  `left`                                                                                                                                                            |
| `DISJ2_TAC`                           |  `right`                                                                                                                                                           |
| `EQ_TAC`                              |  `split` for an iff conclusion only                                                                                                                                      |
| `EVERY_ASSUM ttac` | For each assumption `thm`, run `ttac(thm)`. | [EVERY_ASSUM](https://github.com/jrh13/hol-light/blob/master/Help/EVERY_ASSUM.doc) |
| `EXISTS_TAC`                          |  `exists`                                                                                                                                                          |
| `EXPAND_TAC s`                        |  `rewrite <- H` where `H` is `t = s` | [EXPAND_TAC](https://github.com/jrh13/hol-light/blob/master/Help/EXPAND_TAC.doc) |
| `FIND_ASSUM ttac term` | If assumption `H:term` exists, apply tactic `ttac H`. | [FIND_ASSUM](https://github.com/jrh13/hol-light/blob/master/Help/FIND_ASSUM.doc) |
| `FIRST_ASSUM ttac` | ? | [FIRST_ASSUM](https://github.com/jrh13/hol-light/blob/master/Help/FIRST_ASSUM.doc) |
| `FIX_TAC s`                          | No matching tactic in Coq (correct me if I am wrong); `intros`, but specifies the variable to introduce | [FIX_TAC](https://github.com/jrh13/hol-light/blob/master/Help/FIX_TAC.doc) |
| `GEN_TAC`                             |  `intro`, but targets   non-propositions only                                                                                                                      |
| `IMP_REWRITE_TAC[thm list]`           |  Given a list of theorems that look like `P ==> l = r`, do `rewrite` and add `P` to the goal as a conjunction. If the rewritten part is at `P'` of some other implication `P' ==> Q'`, `P` is added as `(P ==> P'[l/r]) ==> Q`. Thos also works for theorems that look like `P ==> l1 = r1 /\ l2 = r2 /\ ..` | [IMP_REWRITE_TAC](https://github.com/jrh13/hol-light/blob/master/Help/IMP_REWRITE_TAC.doc) |
| `INDUCT_TAC`                          |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have 'num' type ('nat' in   Coq).                                         |
| `INTRO_TAC`                          |  `intros` + `destruct` of dis/conjunctions                                         |
| `LABEL_TAC s thm`                     |  `assert (s := thm)`                                                                                                                                               |
| `LABEL_TAC s (SPECL [t0;t1;…]   thm)` |  `specialize (thm t0 t1 …) as s`                                                                                                                                   |
| ``LABEL_TAC s (ISPECL [`x:(32)word`;…] thm) `` |  `specialize (thm t0 t1 …) as s` with type instantiations |
| `LIST_INDUCT_TAC`                     |  `induction` on the first universal   quantifier. (ex: x in `forall x x2 …, P`). It must have '(ty)list' type   ('list ty' in Coq).                                |
| `MATCH_MP_TAC thm`                    |  `apply`, but the applying thm must be of the form `P ==> Q` |
| `MATCH_ACCEPT_TAC thm`                |  `apply` |
| `MESON_TAC[thm list]`                 |  `firstorder` with thms registered   to hint databases. Unlike ASM_MESON_TAC, this does not use assumptions.                                                       |
| `MP_TAC thm` | `assert (s := thm). generalize thm` | [MP_TAC](https://github.com/jrh13/hol-light/blob/master/Help/MP_TAC.doc) |
| `NO_TAC`                              |  `fail`   |
| `ONCE_REWRITE_TAC[thm list]`          |  `rewrite` but rewrites only once.                                                                                                                                 |
| `tac ORELSE tac`                      |  `orelse` in Ltac2?                                                                                                                                                |
| `REAL_ARITH_TAC`                      |  `lra`?                                                                                                                                                            |
| `REFL_TAC`                            |  `reflexivity`, but REFL_TAC only   checks syntactic equivalence (e.g. x = 0 + x cannot be proved)                                                                 |
| `REMOVE_THEN s ttac` | Given an assumption whose name is s, equivalent to `USE_THEN s ttac`(in HOL Light) then `clear s` (in Coq). | [REMOVE_THEN](https://github.com/jrh13/hol-light/blob/master/Help/REMOVE_THEN.doc) |
| `REPEAT`                              |  `repeat`                                                                                                                                                          |
| `REWRITE_TAC [thm list]`              |  `repeat (try rewrite thm[0]; try rewrite thm[1]; …)`, but unlike `rewrite` in Coq, if the conclusion matches exactly one of thm list, the goal is immediately proved. |
| `REWRITE_TAC [GSYM thm]`              |  `rewrite <- thm`, with the characteristics described in the generic REWRITE_TAC form above |
| `RULE_ASSUM_TAC (fn:thm->thm)`        |  Perform fn to every assumption. |
| `SIMP_TAC [thm list]`                 |  `REWRITE_TAC`, but (1) applies intrinsic rewrite rules as well (basic_rewrites and basic_convs), and (2) accepts conditional rewrite rules of form `c ==> l = r`. The conditional rewrite rules are applied if `c` can be simplified into T. Different from `simpl` in Coq because it does not immediately look into the definitions. For example, SIMP_TAC cannot simplify `0 + x` into `x` without additional hints. | [SIMP_TAC](https://github.com/jrh13/hol-light/blob/master/Help/SIMP_TAC.doc) |
| `` SPEC_TAC(`x:ty1`, `y:ty2`) ``   |  `generalize x as y`. If `x` is not used in any assumption and `x` is `y`, this is equal to `revert x`.                                                          |
| `STRIP_TAC`                           |  `split` (for conjunctions) + `intro` (GEN_TAC + CONJ_TAC + elaborated version of DISCH_TAC)                                                                     |
| `SUBGOAL_THEN tm ASSUME_TAC`          |  `cut tm. intros HASSUME`, or `assert (HASSUME: tm)` with a swapped subgoal order                                                                               |
| `SUBGOAL_THEN tm (LABEL_TAC "name")`  |  `cut tm. intros name`, or `assert (name: tm)` with a swapped subgoal order                                                                               |
| `TRY tac`                             |  `try tac`                                                                                                                                                         |
| `tac THEN tac`                        |  `tac; tac`                                                                                                                                                               |
| `tac THENL [tac list]`                |  `tac. { tac[0]. } { tac[1]. } …`                                                                                                                                     |
| `UNDISCH_TAC`                         |  `generalize` for a prop.                                                                                                                                          |
| `USE_THEN s ttac`   | Given an assumption whose name is s, apply ttac which should be analogous to `fun thm -> (*tactic*)`. | [USE_THEN](https://github.com/jrh13/hol-light/blob/master/Help/USE_THEN.doc) |
| `X_GEN_TAC t`                         |  `intro t`, but targets non-propositions only                                                                                                                    |
| `` X_META_EXISTS_TAC `x:ty` ``            | `eexists`. Set the name of the meta variable to `x`.                                                                                                               |

- HOL Light tactics that appear in the [Quick Reference Guide](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.txt) but are not matched yet: COND_CASES_TAC, FIRST_X_ASSUM ttac, GEN_REWRITE_TAC cnvn [th], MAP_EVERY, MP_TAC thm, POP_ASSUM ttac, POP_ASSUM_LIST ttac, RULE_ASSUM_TAC, SET_TAC [thm list]

- Frequently used Coq tactics that are not matched yet: `inversion`, `eapply`

### Using Assumptions in HOL Light

Unlike Coq, assumptions in HOL Light do not have names by default.
This can be frustrating if you are already familiar with Coq-style proof because you cannot 'pick' an assumption and use it.
There are several ways to deal with this.

A direct solution is to explicitly name the assumption using `LABEL_TAC`.
If the goal is `.. |- P ==> Q`, you can `intro Hname` in Coq using `DISCH_THEN(LABEL_TAC "Hname")` in HOL Light.
This will make the goal look like this:

```
- : goalstack = 1 subgoal (1 total)

  0 [`P`] (Hname)

`Q`
```

While introducing `P`, you can apply some transformations on-the-fly.
For example, `DISCH_THEN(LABEL_TAC "Hname" o REWRITE_RULE[MOD_EQ_0])` introduces `P` and rewrites the assumption using a set of rewrite rules (`MOD_EQ_0` in this case).

To pick Hname, you can use `USE_THEN "Hname"` as follows:

```ocaml
(* Pick an assumption "Hx0lt" (which becomes the 'thm' variable), and rewrite the goal using an equation
   'MATCH_MP add_64_32_mod_32_eq thm'. Note that add_64_32_mod_32_eq is some P -> Q, and thm is matched to P. *)
USE_THEN "Hx0lt" (fun thm -> REWRITE_TAC[MATCH_MP add_64_32_mod_32_eq thm])
```

```ocaml
(* Pick an assumption "H" and generalize it. *)
USE_THEN "H" MP_TAC
```

If you want to use the assumption and remove it, you can use `REMOVE_THEN`. 

However, this solution may not work if you have a large codebase that already introduces a lot of unnamed assumptions.
Also, this does not explain how to pick one assumption and modify the assumption.
There are several solutions in these cases.

#### Using Assumption(s) to Update the Conclusion

The first kinds of tactics that you can try is the `ASM_*` tactics.
- To solve an arithmetic lemma, you might want to use `ARITH_TAC` (and its family tactics) which is analogous to the `lia` and `nia` tactics in Coq. 
However, `ARITH_TAC` does not consider the equalities/relational equations in the assumptions unlike the Coq tactics.
In this case, `ASM_ARITH_TAC` will resolve the issue.
- If you are aware that using the rewrite rules in the assumptions as well as the commutativity property of addition should solve the goal, you can use `ASM_REWRITE_TAC[ADD_SYM]`.
- If the rewrite rules contain conditional rules (`c ==> l = r`), you can use `ASM_SIMP_TAC[..]`.
`ASM_SIMP_TAC` first tries to prove `c` using the assumptions as well as the provided rewrite rules, and if it succeeds, it will rewrite `l` in the goal with `r`.
The table in Tactics in HOL Light vs. Coq describes the differences between `SIMP_TAC` and `REWRITE_TAC`.
- If the `c` assumption cannot be simply proved via rewritings, you can use `IMP_REWRITE_TAC[..]`.
- If the goal is a first-order logic problem, you can use `ASM_MESON_TAC[..]`.

If the `ASM_*` tactics are too coarse-grained to solve the goal, you can use tactics that picks an assumption matching some pre-defined pattern + does some behavior.
- `EXPAND_TAC "x"` finds the assumption of form `e = x` and rewrites all `x` in the conclusion with `e`.
However, this tactic does not rewrite `x` in the assumptions.

(TODO: more `apply H` in Coq)

If you could not find such tactic,
- You can use `FIRST_ASSUM ttac` where `ttac` is `thm -> tactic`.
`FIRST_X_ASSUM ttac` is equivalent to `FIRST_ASSUM ttac` except that the used assumption is removed.
- You can iterate over assumptions using `EVERY_ASSUM ttac`. For example, `EVERY_ASSUM (fun thm -> REWRITE_TAC[GSYM thm])` is equivalent to `ASM_REWRITE_TAC[]` modulo the rewrite direction (`<-` rather than `->`).
- Or, you can directly pick up an assumption using its definition using `ASSUME`.
For example, if the goal is `x = 0 |- 1 = x + 1`, you can rewrite `x` using ``REWRITE_TAC[ASSUME `x = 0`]``.


#### Using Assumption(s) to Update Other Assumptions

If you want to modify other assumptions using some assumption, you can use `RULE_ASSUM_TAC`.

```ocaml
(* Apply the DIMINDEX_32 rewrite rule to every assumption. *)
RULE_ASSUM_TAC (REWRITE_RULE [DIMINDEX_32])
```

Combined with the tactics picking a desired assumption that are explained above, this can be achieved.

#### Removing Unnecessary Assumptions

You can define a custom tactic that is analogous to the one in s2n-bignum ([link](https://github.com/awslabs/s2n-bignum/blob/b0aa5e4bc2b897cfa4b5d5d5e49c94f371afd0be/arm/proofs/arm.ml#L405-L410)):

```ocaml
let DISCARD_ASSUMPTIONS_TAC P =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check P));;

let DISCARD_MATCHING_ASSUMPTIONS pats =
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> exists (fun ptm -> can (term_match [] ptm) (concl th)) pats);;
   
(* Use case *)
e(DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]);;
```

### Others

```ocaml
(* Given n:nat, do destruct n as [ | S n'] *)
DISJ_CASES_TAC(SPECL [`x:num`] num_CASES)

(* Add the names to destruct *)
DISJ_CASES_THEN (LABEL_TAC "mcases") (SPECL [`m:num`] num_CASES)
```

### Useful Custom Tactics

#### Goal Printer

```ocaml
let PRINT_GOAL_TAC (desc: string): tactic =
  fun gl -> let _ = Printf.printf "<%s>\n" desc; print_goal gl in ALL_TAC gl;;
```

#### `note` Tactic

https://cr.yp.to/2023/holhull-20230406.sage has this `note` tactic that is very handy when you want to add an assumption that can be concluded from a set of rewrite rules 
```ocaml
let notetac t tac = SUBGOAL_THEN t MP_TAC THENL
[tac;
  ALL_TAC] THEN
DISCH_THEN(fun th -> ASSUME_TAC th);;

let note t why = notetac t(ASM_MESON_TAC why);;
  
(* usage *)
note `1 + 2 = 2 + 1` [ADD_SYM] THEN ...
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

```ocaml
(* Show the AST of a term *)
#remove_printer pp_print_qterm;;
`match x with | SOME y -> 10 | NONE -> 20`;;
#install_printer pp_print_qterm;;

(* Show the AST of a type *)
#remove_printer pp_print_qtype;;
loads "Library/words.ml":;
`word 10: (32)word`;;
#install_printer pp_print_qtype;;
```

## Misc

### Thenify

`thenify.py` converts a properly formatted sequence of `e(..);;` commands into the `.. THEN ..` format.
If some tactic produces multiple subgoals, the beginning of each subgoal must be itemized with `- ` and the following
lines must have extra indentations. Currently, the indentation string is fixed to two spaces (`  `).
`thenify_inputs/` has its inputs and `thenify.py <input.txt>` shows the then-ified output. :)

### Others

```ocaml
(* Given an OCaml string 'name' and term 'tm', make a definition `name = tm` *)
new_definition (mk_eq (mk_var (name, `:(..type..)`), tm))
```
