# Playing with Assumptions in HOL Light

Unlike Coq, assumptions in HOL Light do not have names by default.
You can name the assumptions using several existing tactics and use the named assumptions by picking them.
On the other hand, you can choose unnamed assumption style and write proofs because it can be more
convenient.
This document explains tactics that can be used in each proof style.

## 1. How to name assumptions and use them

### Naming assumptions.

A simplest solution is to label all existing assumptions at once using `NAME_ASSUMS_TAC`.
This will simply assign names `H0`, `H1`, ... to all unnamed assumptions.

If the goal is `.. |- P ==> Q`, you can do `intro Hname` in Coq using `INTRO_TAC "Hname"` in HOL Light.

```ocaml
# g `x = 0 ==> x + 1 = 1`;;
Warning: Free variables in goal: x
val it : goalstack = 1 subgoal (1 total)

`x = 0 ==> x + 1 = 1`

# e(INTRO_TAC "Hx");;
val it : goalstack = 1 subgoal (1 total)

  0 [`x = 0`] (Hx)

`x + 1 = 1`
```

The string argument of `INTRO_TAC` can actually be some pattern that can introduce
multiple assumptions (and universally quantified variables) at once.
Also, HOL Light has two more tactics `DESTRUCT_TAC` and `CLAIM_TAC` that are useful in
different cases and can be used to introduce named assumptions.
(doc:
[INTRO_TAC](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/INTRO_TAC.html),
[DESTRUCT_TAC](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/DESTRUCT_TAC.html) and
[CLAIM_TAC](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/CLAIM_TAC.html))

Or, in a slightly lower level, you can use `DISCH_THEN(LABEL_TAC "Hname")` in HOL Light.

`DISCH_THEN` picks the antecedent `P` of the conclusion, and pass it to `LABEL_TAC "Hname"`.
The first argument of `DISCH_THEN` is actually a lambda function that takes a theorem and returns a tactic.

Note that a lambda function in OCaml has a syntax `fun (arg:type) -> body`.
`DISCH_THEN(LABEL_TAC "Hname")` is therefore fully equivalent to `DISCH_THEN(fun (th:thm) -> LABEL_TAC "Hname" th)`.
In HOL Light, we use a term 'theorem-tactic' to indicate a lambda function that takes one `thm`-typed argument and returns a tactic.
Its OCaml type is `thm -> tactic`, but in many documents (including this doc) it is informally abbreviated as `ttac`.

While introducing `P`, you can apply some transformations to the assumption on-the-fly.
For example, `DISCH_THEN(LABEL_TAC "Hname" o REWRITE_RULE[MOD_EQ_0])` introduces `P` and rewrites the assumption using a set of rewrite rules (`MOD_EQ_0` in this case).
`o` is an operator that composes two functions.

### Picking and using named assumptions

To pick Hname, you can use `USE_THEN "Hname"` as follows:

```ocaml
(* Pick an assumption "H" and add it as an antecedent of the conclusion. *)
USE_THEN "H" MP_TAC
```

The second argument of `USE_THEN` is actually a lambda function that takes a theorem and returns a tactic.

```ocaml
(* Pick an assumption "Hx0lt" (which becomes the 'thm' variable), and rewrite the goal using an equation
   'MATCH_MP add_64_32_mod_32_eq thm'. Note that add_64_32_mod_32_eq is some P -> Q, and thm is matched to P. *)
USE_THEN "Hx0lt" (fun thm -> REWRITE_TAC[MATCH_MP add_64_32_mod_32_eq thm])
```

If you want to use the assumption and remove it, you can use `REMOVE_THEN`. 

```ocaml
(* Pick an assumption "Hmcases" that is `exists ...`, apply CHOOSE, name the resulting assumption as "Hmcases'" and remove the old "Hmcases". *)
REMOVE_THEN "Hmcases" (CHOOSE_THEN (LABEL_TAC "Hmcases'"))
```

### Using assumption(s) to update other assumptions

If you want to modify other assumptions using some assumption, you can use `RULE_ASSUM_TAC`.
Combined with the tactics picking a desired assumption that are explained above, this can be achieved.

```ocaml
(* Pick "my_hyp" assumption and apply the rewrite rule to every assumption. *)
USE_THEN "my_hyp" (fun my_hyp -> RULE_ASSUM_TAC (REWRITE_RULE [my_hyp]))
```

## 2. Using Unnamed Assumptions

### Using all assumption(s) to update the conclusion

The first kinds of tactics that you can try is the `ASM_*` tactics.
This simply uses all assumptions to update the conclusion.

- The probably most famous tactic in this area is `ASM_REWRITE_TAC[<rules>]`, which
rewrites the conclusion using whole assumptions as well as the additional rewrite rules `<rules>`.
- `ASM_ARITH_TAC` proves a goal that is an arithmetic expression such as `(x + y) * (x + y) = x * x + 2 * x * y + y * y`.
Note that the more basic tactic `ARITH_TAC` simply ignores all existing assumptions. Similarly, there are `ASM_REAL_ARITH_TAC` and `ASM_INT_ARITH_TAC`.
- If the rewrite rules contain conditional rules (`c ==> l = r`), you can use `ASM_SIMP_TAC[..]`.
`ASM_SIMP_TAC` first tries to prove `c` using the assumptions as well as the provided rewrite rules, and if it succeeds, it will rewrite `l` in the goal with `r`.
The table in Tactics in HOL Light vs. Coq describes the differences between `SIMP_TAC` and `REWRITE_TAC`. If the `c` assumption cannot be simply proved via rewritings, you can use `IMP_REWRITE_TAC[..]` which also uses assumptions.
To know more about how to use conditional rewrite rules, please refer to [RewriteTac.md](RewriteTac.md).
- If the goal is a first-order logic problem, you can use `ASM_MESON_TAC[..]` or `ASM_METIS_TAC[]`.

If you want to iterate over all assumptions and apply a tactic using each of those:

- You can use `EVERY_ASSUM ttac`. For example, `EVERY_ASSUM (fun thm -> REWRITE_TAC[GSYM thm])` is equivalent to `ASM_REWRITE_TAC[]` modulo the rewrite direction (`<-` rather than `->`).

### Using some assumption(s) to update the conclusion

You can pick an assumption by giving a pattern and use the assumption.
This can be done by either composing two tactics each of which does step by step, or using one tactic that has the combined behavior.

However, this tactic does not rewrite `x` in the assumptions.
- You can directly pick up an assumption using its definition using `ASSUME`.
For example, if the goal is `x = 0 |- 1 = x + 1`, you can rewrite `x` using ``REWRITE_TAC[ASSUME `x = 0`]``.
- If you want to immediately remove the assumption after picking and using it, you can use `UNDISCH_THEN`, e.g., ``UNDISCH_THEN `k4 = 0` (fun (t:thm) -> REWRITE_TAC[t])``.
Note that this will remove the assumption too.
- `EXPAND_TAC "x"` finds the assumption of form `e = x` and rewrites all `x` in the conclusion with `e`.

If what you want to do with an assumption is pretty complicated that it is obvious there will be only one assumption that will successfully finish the behavior, you can do is choosing `FIRST_{X_}ASSUM`:

- You can use `FIRST_ASSUM ttac`.
`FIRST_X_ASSUM ttac` is equivalent to `FIRST_ASSUM ttac` except that the used assumption is removed.

If you want to get the whole list assumption:

- You can use `ASSUM_LIST` and do something with it in a low level.


### Using assumption(s) to update other assumptions

If you want to rewrite other assumptions using some assumption, you can use `RULE_ASSUM_TAC`.
Combined with the tactics picking a desired assumption that are explained above, this can be achieved.

```ocaml
(* Pick existing assumption `x + y = 10` and apply the rewrite rule to every assumption including itself. *)
RULE_ASSUM_TAC (REWRITE_RULE [ASSUME `x + y = 10`])
```

You can also use `SUBST_ALL_TAC` as well as `SUBST1_TAC`.

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

Now you can use tactics that apply to the conclusion, or pick up the assumption using `DISCH_THEN`.

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
