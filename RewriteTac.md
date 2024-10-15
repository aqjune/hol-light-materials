# Using Rewrite Tactic in HOL Light

## 1. How to find the right rewrite rule

The first thing that you will want to do when using `REWRITE_TAC` or its family tactic is
to find out which rewrite rules to apply.

### A. Using `search`

If you think someone has already proven the rewrite rule as a lemma because it is a well
known property, you can search it using the `search` command.
The `search` command takes a list of patterns and prints the theorems containing
all of them.

```ocaml
# search [`x + y + z`; `(x + y) + z`];;

val it : (string * thm) list =
  [("ADD_AC",
    |- m + n = n + m /\ (m + n) + p = m + n + p /\ m + n + p = n + m + p);
   ("ADD_ASSOC", |- !m n p. m + n + p = (m + n) + p)]
```

You can also give `name "..."` as an argument to `search` to choose theorems that
have the string in their names. There are also `omit` and `exactly`. 
The [help](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/search.html)
document has more info.

### B. Building the rewrite rule on-the-fly

If you think the rewrite rule that you want to use is too specific to the case,
you can build the rewrite rule on-the-fly using various `*_RULE` functions.

For example, if you want to apply a rewrite rule `x * (y + z + w) = x * y + x * z + x * w` on
some natural number expression,
you can use `ARITH_RULE` as follows:

```ocaml
e(REWRITE_TAC[ARITH_RULE `x * (y + z + w) = x * y + x * z + x * w`]);;
```

Useful rules are:
- `ARITH_RULE`: for natural numbers
- `INT_ARITH`: for integers
- `REAL_ARITH`: for real numbers
- `TAUT`: for tautology (see [TAUT](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/TAUT.html))
- `MESON[]`, `METIS[]`: for first-order logic (see [MESON](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/MESON.html),
[METIS](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/METIS.html)) 
- `WORD_RULE`, `WORD_ARITH`, `WORD_BITWISE_RULE`, `WORD_BLAST`, `BITBLALST_RULE`: for bit-vectors (`N word` type)

#### Conversions.

Assuming that some equality `e = e'` is the rewrite rule that you want to create on-the-fly,
if `e'` is supposed to be a typical result of some known simplicification of `e`, you can use conversions.
For example, ``NUM_REDUCE_CONV `1 + 2` `` returns a new rewrite rule `` `1 + 2 = 3` ``, and you can use it
to rewrite any `1 + 2` in the conclusion with `3`.

```ocaml
# NUM_REDUCE_CONV `1 + 2`;;
val it : thm = |- 1 + 2 = 3
```

Note that `` ARITH_RULE `1 + 2 = 3` `` will create the same rewrite rule too.
However, unlike `NUM_REDUCE_CONV`, you need to explicitly give the result of addition at the right-hand side,
which can be cumbersome.

- `NUM_REDUCE_CONV`: takes a term `t` which is a numerical expression and creates `t = t'` where `t'` is the
calculated result of `t`.
- `REWRITE_CONV[]`: a conversion to create a rewrite rule using other rewrite rules on the fly! (see [REWRITE_CONV](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REWRITE_CONV.html))


### C. Deriving the rewrite rule from existing rules on-the-fly

If you could find rewrite rules that look relevant to what you wanted,
you can try to derive your wanted rule using them.

- `GSYM`: If you found `my_thm` saying `e1 = e2`, but you wanted `e2 = e1`, `GSYM my_thm` will return `e2 = e1`.
```ocaml
# ADD_ASSOC;;
val it : thm = |- !m n p. m + n + p = (m + n) + p
# GSYM ADD_ASSOC;;
val it : thm = |- !m n p. (m + n) + p = m + n + p
```
- `TRANS`: If you found `thm1` which is `e1 = e2` and `thm2` which is `e2 = e3`, `TRANS thm1 thm2` will return `e1 = e3`.
```ocaml
# TRANS (ARITH_RULE `1 + 1 = 2`) (ARITH_RULE `2 = 0 + 2`);;
val it : thm = |- 1 + 1 = 0 + 2
```
- `MATCH_MP`: If `thm1` is `P ==> e1 = e2` and `thm2` is `P`, `MATCH_MP thm1 thm2` will return `e1 = e2`.
  `MATCH_MP` can specialize universally quantified variables.
```ocaml
# MOD_LT;;
val it : thm = |- !m n. m < n ==> m MOD n = m
# MATCH_MP MOD_LT (ARITH_RULE `1 < 2`);;
val it : thm = |- 1 MOD 2 = 1
```
- `REWRITE_RULE`: `REWRITE_RULE[rewrite_rules] rule0` returns a new rewrite rule that is a result of rewriting
`rewrite_rules` at `rule0` (see [REWRITE_RULE](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REWRITE_RULE.html)).


### D. Choosing an assumption as a rewrite rule

If the rewrite rule you want to apply already exists as an assumption, you can use it using a proper tactic.

If you want to apply all available rewrite rules in assumption, `ASM_REWRITE_TAC[]` is the right tactic.

If you want to pick the assumption "H0" and use that, `USE_THEN "H0"` can be used.
(if you want to know how to name assumptions, please refer to [PlayingWithAssumptions.md](PlayingWithAssumptions.md))
```ocaml
# e(USE_THEN "H0" (fun th -> REWRITE_TAC[th]));;
```

Alternatively, if there is an assumption `x + y = z` and you want to pick that, you can use
``REWRITE_TAC[ASSUME `x + y + z`]``.
[PlayingWithAssumptions.md](PlayingWithAssumptions.md) has more info about how to utilize assumptions.



## 2. How to apply at a right place

`REWRITE_TAC[<rewrite_rules>]` will recursively traverse the conclusion from top to down (root to leafs) and rewrite
the subexpression whenever it matches one of the rewrite rules.
If you want to apply one of the rewrite rules only once, `ONCE_REWRITE_TAC[<rewrite_rules>]` will work.
The order of rules in `<rewrite_rules>` should not matter (see [ONCE_REWRITE_TAC](https://hol-light.github.io/references/HTML/ONCE_REWRITE_TAC.html)).

If you want to apply, e.g., `ADD_SYM` which is `|- !m n. m + n = n + m` only when `m` is 1,
the rewrite rule can be  specialized using `SPEC` as follows.
```
# SPEC `1` ADD_SYM;;
val it : thm = |- !n. 1 + n = n + 1
```

This can be used as ``REWRITE_TAC[SPEC `1` ADD_SYM]``, or like this using the `let` binding in OCaml:
```ocaml
e(let add_sym_1 = SPEC `1` ADD_SYM in
  REWRITE_TAC[add_sym_1]);;
```

If you want to specialize multiple quantifiers, you can use `SPECL [<list of exprs>] <theorem>`.

### Using `GEN_REWRITE_TAC`

To explicitly designate the locations to rewrite, `GEN_REWRITE_TAC <location> [<rewrite_rules>]`
can be used (see: [GEN_REWRITE_TAC](https://hol-light.github.io/references/HTML/GEN_REWRITE_TAC.html)).
Unlike `REWRITE_TAC`, this does not recursively traverse the expression by default.
Instead, it precisely rewrites at the given `<location>` (which is a function from `conv` to `conv`)
with respect to the root node.
Making it recursively traverse can be done by composing `<location>` with
a family of `DEPTH_CONV`, which will be explained later.

A few interesting `<location>` are:

- `LAND_CONV` ([LAND_CONV](https://hol-light.github.io/references/HTML/LAND_CONV.html)) applies the rewrites to the left-hand argument of binary operator. Note that, in the
following example, `y + x` in the left-hand side expression isn't rewritten to `x + y` because
`GEN_REWRITE_TAC` does not recursively traverse into the subexpression.

```
# ADD_SYM;;
val it : thm = |- !m n. m + n = n + m

# g `(y + x) + z = z + (x + y)`;;
Warning: Free variables in goal: x, y, z
val it : goalstack = 1 subgoal (1 total)

`(y + x) + z = z + x + y`

# e(GEN_REWRITE_TAC LAND_CONV [ADD_SYM]);;
val it : goalstack = 1 subgoal (1 total)

`z + y + x = z + x + y`
```

- Similarly, `RAND_CONV` ([RAND_CONV](https://hol-light.github.io/references/HTML/RAND_CONV.html)) applies
to the right-hand side of binary operator. Actually, this applies to any operand of an application because
`binop l r = (binop l) r`.
- `RATOR_CONV` ([RATOR_CONV](https://hol-light.github.io/references/HTML/RATOR_CONV.html)) applies to the
operator `f` of an application `f x`. If the expression is `f x y`, this applies to `f x` because `f x y`
is `(f x) y`.
- `PAT_CONV <pattern>` ([PAT_CONV](https://hol-light.github.io/references/HTML/PAT_CONV.html)) specifies
the subexpression to rewrite using `<pattern>` which is a lambda function.
  The parameter of lambda function works as a 'placeholder' to the pattern to match.
```
# g `(x - x) + (x - x) = (x - x)`;;
Warning: Free variables in goal: x
val it : goalstack = 1 subgoal (1 total)

`x - x + x - x = x - x`

# e(GEN_REWRITE_TAC (PAT_CONV `\x. x + a = b`) [ARITH_RULE `x - x = 0`]);;
val it : goalstack = 1 subgoal (1 total)

`0 + x - x = x - x`
```
- `PATH_CONV <path>` ([PATH_CONV](https://hol-light.github.io/references/HTML/PATH_CONV.html)) specifies
the subexpression to rewrite using a string `<path>`.
`PATH_CONV` starts from the root node and follows which child to take according to `<path>`.
`<path>` is a string of one of three characters `l` (for operator), `r` (for operand) and
`b` (for the body of an abstraction).
- And many more `_CONV` functions!

These locations can be composed together using the `o` operator.
For example, `LAND_CONV o RAND_CONV` points to the right-hand argument of the left-hand argument of
the binary operator.

#### Recursive traversal.

To make `GEN_REWRITE_TAC` recursively traverse the expression, the above `*_CONV` functions
can be composed with a family of `DEPTH_CONV` functions.

```
# g `!x (f:num->num). f ((x - x) + (x - x)) = f(x - x)`;;
val it : goalstack = 1 subgoal (1 total)

`!x f. f (x - x + x - x) = f (x - x)`

# e(REPEAT GEN_TAC);;
val it : goalstack = 1 subgoal (1 total)

`f (x - x + x - x) = f (x - x)`

# e(GEN_REWRITE_TAC (PAT_CONV `\x. x + a`) [ARITH_RULE `x - x = 0`]);;
  (* This fails because GEN_REWRITE_TAC does not recursively traverse the conclusion by default. *)
Exception: Failure "REWRITES_CONV".

# e(GEN_REWRITE_TAC (DEPTH_CONV o (PAT_CONV `\x. x + a`)) [ARITH_RULE `x - x = 0`]);;
val it : goalstack = 1 subgoal (1 total)

`f (0 + x - x) = f (x - x)`
```

`DEPTH_CONV` traverses in bottom-up order ([DEPTH_CONV](https://hol-light.github.io/references/HTML/DEPTH_CONV.html)).
It can be slow because it repeats traversal until there is no applicable rewrite.
To reduce its cost, cheaper functions (`ONCE_DEPTH_CONV`, `TOP_DEPTH_CONV`, `TOP_SWEEP_CONV`, ...)
can be considered.

`DEPTH_BINOP_CONV` conditionally traverses the expression only if its operator is exactly a given symbol:
```ocaml
(* Given a goal that is `w1:int64 = w2 /\ w3:int64 = w4`, convert this to
   `val w1 = val w2 /\ val w3 = val w4` using `GSYM VAL_EQ`.
   This works even if the goal has more than one conjunction. *)
GEN_REWRITE_TAC (DEPTH_BINOP_CONV `(/\):bool->bool->bool`) [GSYM VAL_EQ]
```


## 3. How to use conditional rewrite rules

Given a rewrite rule `P ==> e1 = e2`,
you might want to replace `e1` with `e2` using that.
Its simple solutions can be categorized into two classes.

1. Use tactics that always rewrite `e1` with `e2`, leaving the necessary
precondition `P` unproven, and prove it later to show that the rewrite(s) was okay.
2. Prove `P` first, making `e1 = e2` by modus ponens, and
then safely rewrite `e1` with `e2`.

If there are multiple subexpressions that match `e1`, and replacing all of them
with `e2` is safe,
the first solution is simpler in general because it provides specialized expressions of `P`
for each rewrite occurrence.
If the second solution was to be used in this case, you will have to manually specialize
`P` for each matching of `e1`, which will be laborsome.
However, the first solution may inadvertantly rewrite `e1` with `e2` even if the precondition
may not hold in that case.
In this case, the first solution must be avoided because this will make the goal not provable.

### A. Rewriting first and proving the necessary condition(s) later

`IMP_REWRITE_TAC[<the_rule>]` rewrites the expression and
leaves the condition `P` at the conclusion as a conjunction.

```
# MOD_ADD_CASES;;
val it : thm =
  |- !m n p.
         m < p /\ n < p
         ==> (m + n) MOD p = (if m + n < p then m + n else (m + n) - p)

# g `(x + y) MOD 10 = 0`;;
Warning: Free variables in goal: x, y
val it : goalstack = 1 subgoal (1 total)

`(x + y) MOD 10 = 0`

# e(IMP_REWRITE_TAC[MOD_ADD_CASES]);;
val it : goalstack = 1 subgoal (1 total)

`(if x + y < 10 then x + y else (x + y) - 10) = 0 /\ x < 10 /\ y < 10`
```

If the conclusion was implication `Q ==> R` and the rewritten part was in `Q`,
`P` is added as an assumption of `Q` like this.

```
# MOD_LT;;
val it : thm = |- !m n. m < n ==> m MOD n = m

# g `(1 + 2) MOD 5 = 3 ==> 1 + 3 = 4`;;
val it : goalstack = 1 subgoal (1 total)

`(1 + 2) MOD 5 = 3 ==> 1 + 3 = 4`

# e(IMP_REWRITE_TAC[MOD_LT]);;
val it : goalstack = 1 subgoal (1 total)

`(1 + 2 < 5 ==> 1 + 2 = 3) ==> 1 + 3 = 4`
```

`1 + 2 < 5` can be focused using `ANTS_TAC` and then be proven.
This will make the conclusion `1 + 2 = 3 ==> 1 + 3 = 4`.

Here are variants of `IMP_REWRITE_TAC`:
- If the order of rules to apply is important,
`SEQ_IMP_REWRITE_TAC` is the tactic to use (see [SEQ_IMP_REWRITE_TAC](https://hol-light.github.io/references/HTML/SEQ_IMP_REWRITE_TAC.html)).
- If you want to do a case analysis on its precondition `P`, you can use `CASE_REWRITE_TAC`. From a goal `Q`,
  it generates `(P ==> Q') /\ (~P ==> Q)` where `Q'` is derived from `Q` via the rewrites.
  See [CASE_REWRITE_TAC](https://hol-light.github.io/references/HTML/CASE_REWRITE_TAC.html).

**When is this approach good?**
As described before, a benefit of this solution is that it automatically generates
specialized preconditions.
For example, `MOD_LT`'s precondition `m < n` in the second example was automatically specialized
to `1 + 2 < 5` according to its matched expression.
Also, if there are more than one match, it generates multiple specialized preconditions:

```
# g `(x + y) MOD 10 = 0 /\ (x + y*2) MOD 20 = 0`;;
Warning: Free variables in goal: x, y
val it : goalstack = 1 subgoal (1 total)

`(x + y) MOD 10 = 0 /\ (x + y * 2) MOD 20 = 0`

# e(IMP_REWRITE_TAC[MOD_LT]);;
val it : goalstack = 1 subgoal (1 total)

`(x + y = 0 /\ 0 < 10) /\ x + y * 2 = 0 /\ 0 < 20`
```

### B. Proving the precondition first

`SIMP_TAC[<rules>]` tactic will try to prove the preconditions of conditional
rewrite rules and then rewrite the goal using them.
If assumptions in the goal can be used to prove the preconditions, or there
is a conditional rewrite rule in assumptions, you can use `ASM_SIMP_TAC`
(see [SIMP_TAC](https://hol-light.github.io/references/HTML/SIMP_TAC.html) and [ASM_SIMP_TAC](https://hol-light.github.io/references/HTML/ASM_SIMP_TAC.html)).
An example from [SIMP_CONV](https://hol-light.github.io/references/HTML/SIMP_CONV.html) will give some insight:

```
# SUB_ADD;;
val it : thm = |- !m n. n <= m ==> m - n + n = m

# SIMP_CONV[SUB_ADD; ARITH_RULE `0 < n ==> 1 <= n`]
        `0 < n ==> (n - 1) + 1 = n + f(k + 1)`;;
val it : thm =
|- 0 < n ==> n - 1 + 1 = n + f (k + 1) <=> 0 < n ==> n = n + f (k + 1)
```

If this automatic approach does not work, the precondition must be manually
proven and be applied to the conditional rewrite rule. You can use either

- `MATCH_MP <conditional rule> <proof to the precondition>`: it creates
a rewrite rule with its precondition relaxed.
You might want to refer to [this section as well](###C.-Deriving-the-rewrite-rule-from-existing-rules-on-the-fly).

- If the precondition needs a large proof that does not fit in few lines,
  `MP_TAC <conditional rule>` + `ANTS_TAC` + (proof of the precondition) +
  `DISCH_THEN(fun th -> REWRITE_TAC[th])` will work.
  If the conditional rule has universally quantified variables,
  `MP_TAC (SPECL [..(exprs)..] <conditional rule>)` will work.


---

TODO: `TARGET_REWRITE_TAC`
