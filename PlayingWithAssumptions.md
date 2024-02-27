# Playing with Assumptions in HOL Light

## How to name assumptions and use them

Unlike Coq, assumptions in HOL Light do not have names by default.
This can be frustrating if you are already familiar with Coq-style proof because you cannot 'pick' an assumption and use it or update it.
This section describes several tips.

### Naming assumptions.

A simplest solution is to label all existing assumptions at once using `NAME_ASSUMS_TAC`.
This will simply assign names `H0`, `H1`, ... to all unnamed assumptions.

If the goal is `.. |- P ==> Q`, you can do `intro Hname` in Coq using `DISCH_THEN(LABEL_TAC "Hname")` in HOL Light.
This will make the goal look like this:

```
- : goalstack = 1 subgoal (1 total)

  0 [`P`] (Hname)

`Q`
```
While introducing `P`, you can apply some transformations on-the-fly.
For example, `DISCH_THEN(LABEL_TAC "Hname" o REWRITE_RULE[MOD_EQ_0])` introduces `P` and rewrites the assumption using a set of rewrite rules (`MOD_EQ_0` in this case).

### Picking and using named assumptions

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

```ocaml
(* Pick an assumption "Hmcases" that is `exists ...`, apply CHOOSE, name the resulting assumption as "Hmcases'" and remove the old "Hmcases". *)
REMOVE_THEN "Hmcases" (CHOOSE_THEN (LABEL_TAC "Hmcases'"))
```

## Using Unnamed Assumptions

Or, you can decide to adopt the proof style of HOL Light and use unnamed assumptions only.

### Using assumption(s) to update the conclusion

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

Or, you can explicitly pick the expression assumption and do something with it.
- You can directly pick up an assumption using its definition using `ASSUME`.
For example, if the goal is `x = 0 |- 1 = x + 1`, you can rewrite `x` using ``REWRITE_TAC[ASSUME `x = 0`]``.
- If you want a more general version, you can use `UNDISCH_THEN`, e.g., ``UNDISCH_THEN `k4 = 0` (fun thm -> REWRITE_TAC[thm])``.
Note that this will remove the assumption too.

Or, if you can avoid explicitly choosing, you can do follows:
- You can use `FIRST_ASSUM ttac` where `ttac` is `thm -> tactic`.
`FIRST_X_ASSUM ttac` is equivalent to `FIRST_ASSUM ttac` except that the used assumption is removed.
- You can iterate over assumptions using `EVERY_ASSUM ttac`. For example, `EVERY_ASSUM (fun thm -> REWRITE_TAC[GSYM thm])` is equivalent to `ASM_REWRITE_TAC[]` modulo the rewrite direction (`<-` rather than `->`).
- You can get a list of assumptions using `ASSUM_LIST` and do something with it.
- Or, you can write your own tactic because tactic can be written as `fun (assumption_list, goal_term) -> (* body *)`.


### Using assumption(s) to update other assumptions

If you want to modify other assumptions using some assumption, you can use `RULE_ASSUM_TAC`.

```ocaml
(* Apply the DIMINDEX_32 rewrite rule to every assumption. *)
RULE_ASSUM_TAC (REWRITE_RULE [DIMINDEX_32])
```

Combined with the tactics picking a desired assumption that are explained above, this can be achieved.

If you want to rewrite both conclusion and assumptions:
```ocaml
(* Rewrite k4 in every place into 0. *)
UNDISCH_THEN `k4 = 0` SUBST_ALL_TAC
```
Or, you can use the conclusion as a 'scratchpad', by converting `asm |- concl` into `|- asm ==> concl`
and using tactics that apply to the conclusion.
This is a pattern frequently appearing in HOL Light proofs:
```
  0 [`x = 0`]
  1 [`f x = 10`]

`f (f x) = 20`

# e (UNDISCH_TAC `f (x:num) = 10`);;

  0 [`x = 0`]

`f x = 10 ==> f (f x) = 20`
```

Now you can use tactics that applies to the conclusion, or pick up the assumption using `DISCH_THEN`.

### Removing a specific, unnamed assumption

You can use a pattern matcher.
Define a custom tactic that is analogous to the one in s2n-bignum ([link](https://github.com/awslabs/s2n-bignum/blob/b0aa5e4bc2b897cfa4b5d5d5e49c94f371afd0be/arm/proofs/arm.ml#L405-L410)):

```ocaml
let DISCARD_ASSUMPTIONS_TAC P =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check P));;

let DISCARD_MATCHING_ASSUMPTIONS pats =
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> exists (fun ptm -> can (term_match [] ptm) (concl th)) pats);;
   
(* Use case *)
e(DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]);;
```
