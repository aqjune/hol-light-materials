# How to Prove Simple Goals

## 1. Proving simple equalities

### A. Proving `x = x`

You can use `REFL_TAC` ([doc](https://hol-light.github.io/references/HTML/REFL_TAC.html)).
This tactic will also accept alpha-equivalent terms, which is necessary when
the expression `x` contain lambdas with different bound variable names as well.

You can also use `REWRITE_TAC[]` (the `REWRITE_TAC` with empty rewrite rules to apply),
because `REWRITE_TAC` has an ability to discharge a simple goal.
However, unlike `REFL_TAC`, it does not fail even if the goal could not be discharged.

### B. Proving `x = x'` when `x` and `x'` are equivalent after unfolding definitions

`REFL_TAC` is a primitive tactic, and it does not automatically unfold definitions
in the goal.
This is unlike the `reflexivity` tactic in Rocq (Coq), which can prove `x = y` if both
terms are equal after 'simplification' (which will use definitional equality).
In fact, in HOL Light, there is no notion of definitional equality.

```ocaml
# g `APPEND [1;2] [3;4] = [1;2;3;4]`;;

- : goalstack = 1 subgoal (1 total)

`APPEND [1; 2] [3; 4] = [1; 2; 3; 4]`

# e REFL_TAC;;

Exception: Failure "REFL_TAC".
```

To unfold the definition and prove equality (which is simulating `reflexivity` of Rocq),
you can use `REWRITE_TAC[..(rewrite rules describing definitions)..] THEN NO_TAC`.
If it converges into the `x = x` form after rewriting, the goal will be automatically
discharged by `REWRITE_TAC`.
If it does not, `THEN NO_TAC` will raise `Failure` stating that it could not
be discharged. If you want to give a specific failure message, you can use
`THEN FAIL_TAC "your message"`.
In the above case, OCaml definition `APPEND` will have the definition of HOL
Light function `APPEND`.

```ocaml
# APPEND;;

- : thm =
|- (forall l. APPEND [] l = l) /\
   (forall h t l. APPEND (CONS h t) l = CONS h (APPEND t l))

# e (REWRITE_TAC[APPEND] THEN NO_TAC);;
(* Note that the APPEND theorem was a conjunction of two clauses;
   REWRITE_TAC tried each clause to the goal and proved it. *)

- : goalstack = No subgoals
```

A challenge is to find the rewrite rule that describes the definition of the
HOL Light constant or function, `APPEND` in this case.
Typically, it is using the same name: the `APPEND` OCaml variable in this case.
Sometimes it is using its lowercase name in OCaml.
If you are using VSCode, you can use 'Go to Definition' functionality and
pinpoint the rewrite rule.

### C. Proving `e = x` where `x` is the result of evaluating `e`

Sometimes `REWRITE_TAC[.. (definitions) ..]` is not a scalable approach because
the left-hand side (`e`) may contain too many constants to unfold
(like complex math expression), making it hard to list all necessary definitions.

In this case, you can try using existing conversions that are tailored to a specific domain.
For example, `NUM_REDUCE_CONV` will do it for natural numbers, and `WORD_REDUCE_CONV`
will do it for bit-vectors.
After choosing which conversion to use, running `CONV_TAC (LAND_CONV <the conversion>)`
will do the trick. `LAND_CONV` means that
it will look into the LHS of the binary operator (`=` in this case) and
apply the conversion to the LHS.

```ocaml
# g `1 + MIN 10 ((4 * 5) DIV 3) = 7`;;

- : goalstack = 1 subgoal (1 total)

`1 + MIN 10 ((4 * 5) DIV 3) = 7`

# e(CONV_TAC (LAND_CONV NUM_REDUCE_CONV));;

- : goalstack = 1 subgoal (1 total)

`7 = 7`

# e(REFL_TAC);;

- : goalstack = No subgoals
```

(In fact, `NUM_REDUCE_CONV` will recursively visit the expression and automatically
discharge `7 = 7`, so `CONV_TAC NUM_REDUCE_CONV` is enough. Actually, it can
be even shorter and be `NUM_REDUCE_TAC`. The example above is for explanation).

[How to Evaluate Expression in HOL Light](EvalExpression.md) will have more details about conversions.

### D. Proving `e = e'` after reductions.

**Beta reduction.** `REWRITE_TAC[]` has an ability to do beta reduction:

```ocaml
# g `(\x. x + 1) 1 = 2`;;

- : goalstack = 1 subgoal (1 total)

`(\x. x + 1) 1 = 2`

# e(REWRITE_TAC[]);;

- : goalstack = 1 subgoal (1 total)

`1 + 1 = 2`

# e(NUM_REDUCE_TAC);;

- : goalstack = No subgoals
```

If you want to exactly apply beta reduction, but not other simplifications that
`REWRITE_TAC[]` contain, please look into
[How to Evaluate Expression in HOL Light](EvalExpression.md).

**Generalized beta reduction, zeta reduction (let), reducing match expressions.**
[How to Evaluate Expression in HOL Light](EvalExpression.md)
will have relevant information. (TODO: introduce more rewrite-rule-based approach)


## 2. Proving the goal from existing lemmas

### A. By matching a previously proven lemma.

If the goal is exactly equivalent to a lemma, or equivalent after the universally quantified
variables are instantiated,
`MATCH_ACCEPT_TAC lemma` ([doc](https://hol-light.github.io/references/HTML/MATCH_ACCEPT_TAC.html)) will work.
If no instantiation of universally quantified variables is necessary from the
lemma, even more primitive `ACCEPT_TAC lemma` can be used.

Note that `REWRITE_TAC[lemma]` will also work.

### B. Using a lemma with precondition

If the goal is `Q` and the lemma is `P ==> Q`, you can use
`MATCH_MP_TAC lemma` ([doc](https://hol-light.github.io/references/HTML/MATCH_MP_TAC.html)).
If the goal is slightly different `Q`, say `Q'`, you can use the following strategy:

1. Do `MP_TAC lemma` ([doc](https://hol-light.github.io/references/HTML/MP_TAC.html)) which make the conclusion `(P ==> Q) ==> Q'`
2. Use `ANTS_TAC` ([doc](https://hol-light.github.io/references/HTML/ANTS_TAC.html)) to prove `P` in the first subgoal.
3. After proving `P`, the second subgoal will be set to `Q ==> Q'`.
You can move `Q` to an assumption using `DISCH_TAC` ([doc](https://hol-light.github.io/references/HTML/DISCH_TAC.html)),
or even do more interesting stuffs described in [PlayingWithAssumptions.md](PlayingWithAssumptions.md).

If the `Q` (or its LHS if `Q` is an equality) appears as a subterm of the `Q'`,
you will want to try `IMP_REWRITE_TAC`. [RewriteTac.md](RewriteTac.md) has more
explanation about this.

### C. Using a false assumption (principle of explosion, ex falso)

If the conclusion is `false ==> ...`, `REWRITE_TAC` will again do the trick.
`STRIP_TAC` also has an ability to discharge a simple goal like this.

If there is a `false` assumption, you can first undischarge the `false` assumption
and use `REWRITE_TAC[]`.

```ocaml
# UNDISCH_TAC `false` THEN REWRITE_TAC[]
```

Of course you can use the first order proof search tactics will will be described
below.
If you found a simpler solution, please let me know! :)


### D. Using automated tactics for first order logic

If you think that the goal can be naturally proven from a list of already proven
facts using basic logical reasoning, you can try using automated first-order
proof search tactics.
There are several known algorithms for first-order proof searching.
`METIS_TAC[]` ([doc](https://hol-light.github.io/references/HTML/METIS_TAC.html)),
`MESON_TAC[]` ([doc](https://hol-light.github.io/references/HTML/MESON_TAC.html)),
`LEANCOP_TAC[]` ([doc](https://hol-light.github.io/references/HTML/LEANCOP_TAC.html)),
`NANOCOP_TAC[]` ([doc](https://hol-light.github.io/references/HTML/NANOCOP_TAC.html))
all receives lemmas and discharges the goal if the goal can be solved using the
list of lemmas.

If the goal has to utilize assumptions, you can use `ASM_{METIS,MESON}_TAC[]` variant.
The default above tactics do not take assumptions into account.


## 3. Case splitting

### A. Breaking logical constructs

To break a conjunction `A /\ B` into two subgoals - `A` and `B`, you can use
`CONJ_TAC` ([doc](https://hol-light.github.io/references/HTML/CONJ_TAC.html)).
If the goal is `A1 /\ A2 /\ .. /\ An` and you want to break these at once,
you can use `REPEAT CONJ_TAC`.

From disjunction `A \/ B`, if you want to choose the left clause (`A`) and continue,
you can use `DISJ1_TAC` ([doc](https://hol-light.github.io/references/HTML/DISJ1_TAC.html)).
For the right one, you can use `DISJ2_TAC`
([doc](https://hol-light.github.io/references/HTML/DISJ2_TAC.html)).

If you want to break iff `P <=> Q` to two implications `P ==> Q /\ Q ==> P`,
`EQ_TAC` ([doc](https://hol-light.github.io/references/HTML/EQ_TAC.html)) will do the trick.

To case-split the condition `c` of `if c then e1 else e2` in the conclusion,
you can use `COND_CASES_TAC` ([doc](https://hol-light.github.io/references/HTML/COND_CASES_TAC.html)).

### B. Case-splitting `t \/ ~t` from boolean term `t` (excluded middle)

To case-split a boolean expression `t` into two cases when `t` is either true or
false, `ASM_CASES_TAC t` can be used ([doc](https://hol-light.github.io/references/HTML/ASM_CASES_TAC.html)).
This will create two subgoals, first of which adds `t` as an assumption,
and second of which adds `~t` as an assumption.

A similar tactic is `BOOL_CASES_TAC t` ([doc](https://hol-light.github.io/references/HTML/BOOL_CASES_TAC.html)).
This also creates two subgoals, but in each subgoal the occurrences of `t`
are replaced with constants `true` and `false`.

### C. Case analysis on a proven fact `P \/ Q`

From a lemma th `|- P \/ Q`, you can do case analysis using `DISJ_CASES_TAC th`
([doc](https://hol-light.github.io/references/HTML/DISJ_CASES_TAC.html)).
If the lemma has a universally quantified variable, it must be specialized
first.
The documentation linked above shows how to do it using `SPEC`.

### D. Case-splitting on constructors of inductive data type

If an inductive data type is defined using `new_inductive_definition`
([doc](https://hol-light.github.io/references/HTML/new_inductive_definition.html)),
it will have returned a triple of theorems:

1. Conjunction of equalities where each clause corresponds to one constructor
  (typically has `_RULES` suffix in its name)
2. The induction principle for the data type
  (typically has `_INDUCT` suffix in its name)
3. The case-analysis rule for the data type.
  (typically has `_CASES` suffix in its name)

For example:

```ocaml

# let steps_RULES,steps_INDUCT,steps_CASES = new_inductive_definition
  `(!s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (!s s'' n. (?s'. step s s' /\ steps step n s' s'') ==> steps step (n+1) s s'')`;;

val steps_RULES : thm =
  |- forall step.
         (forall s. steps step 0 s s) /\
         (forall s s'' n.
              (exists s'. step s s' /\ steps step n s' s'')
              ==> steps step (n + 1) s s'')
val steps_INDUCT : thm =
  |- forall step steps'.
         (forall s. steps' 0 s s) /\
         (forall s s'' n.
              (exists s'. step s s' /\ steps' n s' s'')
              ==> steps' (n + 1) s s'')
         ==> (forall a0 a1 a2. steps step a0 a1 a2 ==> steps' a0 a1 a2)
val steps_CASES : thm =
  |- forall step a0 a1 a2.
         steps step a0 a1 a2 <=>
         a0 = 0 /\ a2 = a1 \/
         (exists n.
              a0 = n + 1 /\ (exists s'. step a1 s' /\ steps step n s' a2))
```

When you want to case-split an expression `e` having an inductive data type,
you will want to use `STRUCT_CASES_TAC` ([doc](https://hol-light.github.io/references/HTML/STRUCT_CASES_TAC.html)).
This tactic receives the third (`*_CASES`) theorem, but with its quantified
variable instantiated with `e`.

### E. Case-splitting `forall i. i < n ==> P i`

To case split `forall i. i < n ==> P i` into
`P 0 /\ P 1 /\ P 2 /\ ... /\ P (n-1)`, you can use
`CONV_TAC EXPAND_CASES_CONV`([doc](https://hol-light.github.io/references/HTML/EXPAND_CASES_CONV.html)).

```ocaml
# g `forall i. i < 10 ==> P i`;;

- : goalstack = 1 subgoal (1 total)

`forall i. i < 10 ==> P i`

1 subgoal (1 total) # e (CONV_TAC EXPAND_CASES_CONV);;

- : goalstack = 1 subgoal (1 total)

`P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9`
```

## 4. Proof by induction

(TODO)

For natural numbers: `INDUCT_TAC` ([doc](https://hol-light.github.io/references/HTML/INDUCT_TAC.html))

For lists: `LIST_INDUCT_TAC` ([doc](https://hol-light.github.io/references/HTML/LIST_INDUCT_TAC.html))

For wellfounded induction: `WF_INDUCT_TAC` ([doc](https://hol-light.github.io/references/HTML/WF_INDUCT_TAC.html))

## 5. Arithmetic problems

(TODO)

For natural numbers: `ARITH_TAC`, `ASM_ARITH_TAC`,

For signed integers: `INT_ARITH_TAC`,

For real numbers: `REAL_ARITH_TAC`