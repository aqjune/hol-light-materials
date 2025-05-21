# How to Evaluate Expression in HOL Light

**Before reading:**
By default, `REWRITE_CONV` and `REWRITE_TAC` will do some simplifications even when its rewrite rule list is set to empty (`[]`).
This is because they have a list of built-in rewrite rules that
can be checked through `basic_rewrites()` ([doc](https://hol-light.github.io/references/HTML/basic_rewrites.html)) as well as built-in conversions `basic_convs()`
([doc](https://hol-light.github.io/references/HTML/basic_convs.html)).
Therefore, if you are in a hurry, you will want to simply try `REWRITE_TAC[]` and see
whether it makes any change.

```
# REWRITE_CONV[] `(\x y. x + y) 10 20`;;
val it : thm = |- (\x y. x + y) 10 20 = 10 + 20
```

If the result has a numerical expression, try adding `ARITH`:

```
# REWRITE_CONV[ARITH] `(\x y. x + y) 10 20`;;
val it : thm = |- (\x y. x + y) 10 20 = 30
```

If it did not help, please proceed and read the text below. :)

----

Given a term `t`, you might want to create a theorem `|- t = t'` where `t'`
is a result of computation/reduction/etc.
Creating the theorem is typically implemented as a conversion `term -> thm` (also called `conv`) returning an equality.
HOL Light has several handy conversions that can be used to evaluate expressions, and multiple conversions can be sequentially composed using `THENC` or `ORELSEC` (as `THEN` and `ORELSE` do for tactics).

If the term that needs to be simplified is embedded in a goal state, the conversion can be converted through `CONV_TAC` ([doc](https://hol-light.github.io/references/HTML/CONV_TAC.html)) or `CONV_RULE` ([doc](https://hol-light.github.io/references/HTML/CONV_RULE.html)) and used.
Simplifying a conclusion can be done by converting a conversion of interest to its tactic form using `CONV_TAC`.
Simplifying an assumption can be done by converting a conversion to its rule form using `CONV_RULE` and then feeding the result to `RULE_ASSUM` tactic to apply the rule to assumptions.
Unless there already exists a proven rewrite rule that can be used to simplify the goal, you will want to know the conversions that HOL Light supports.

In this chapter we will primarily focus on the first case which is building `|- t = t'` from `t`.
On top of it, we will also explain a few useful rewrite rules that
can also be directly applied to a goal state using the `REWRITE_TAC` family without needing the
complexity of using conversions.


## 1. Function application

`BETA_CONV` is a conversion that performs function application:

```
# BETA_CONV `(\x. x + 1) 2`;;
val it : thm = |- (\x. x + 1) 2 = 2 + 1
```

A `REWRITE_CONV` without any rewrite rule can be also used to do this:

```
# REWRITE_CONV [] `(\x. x + 1) 2`;;
val it : thm = |- (\x. x + 1) 2 = 2 + 1
```

This is because `REWRITE_CONV` internally adds a list of rewrite rules that
are registered in `basic_rewrites()` ([doc](https://hol-light.github.io/references/HTML/basic_rewrites.html)), and the list contains `BETA_THM`.
To avoid rewriting subexpressions and only applying this rule to the top-level
operator, you can use `GEN_REWRITE_CONV I [BETA_THM]`.
`GEN_REWRITE_CONV` does not (1) use `basic_rewrites()`, and
(2) does not visit subexpressions by default (`I`).

```
# GEN_REWRITE_CONV I [BETA_THM] `(\x. x + 1) 2`;;
val it : thm = |- (\x. x + 1) 2 = 2 + 1
```

The most basic form of beta reduction (`(\x. e) x -> e[x]`)
is implemented as an axiom called `BETA` in HOL Light, but it does not
implement the full algorithm of substitution.

**Generalized abstraction.**
For generalized abstractions (which is a jargon for a lambda function that has a structured argument), `GEN_BETA_CONV` can be used.

```
# GEN_BETA_CONV `(\(x,y,z). x + y + z) (1,2,3)`;;
val it : thm = |- (\(x,y,z). x + y + z) (1,2,3) = 1 + 2 + 3
# GEN_BETA_CONV `(\[a;b;c]. b) [1;2;3]`;;
val it : thm = |- (\([a; b; c]). b) [1; 2; 3] = 2
```

Since `GEN_BETA_CONV` is also in `basic_convs()`, you can simply use `REWRITE_CONV[]`
to reduce it.

```
# REWRITE_CONV [] `(\(x,y,z). x + y + z) (1,2,3)`;;
val it : thm = |- (\(x,y,z). x + y + z) (1,2,3) = 1 + 2 + 3
```

**Converting generalized abstraction into a plain abstraction (and vice versa).**
When a generalized abstraction appears in a goal state, you may want to
rely on rewrite rules that convert it into a plain abstraction.
This is especially useful because some tactics like `MATCH_MP_TAC` or `MESON`
cannot work well if generalized abstractions exist.
`LAMBDA_PAIR` and `LAMBDA_TRIPLE` are such rewrite rules that do the trick.

```
# LAMBDA_PAIR;;
val it : thm = |- forall f. (\(x,y). f x y) = (\p. f (FST p) (SND p))
# LAMBDA_TRIPLE;;
val it : thm =
  |- forall f.
         (\(x,y,z). f x y z) = (\t. f (FST t) (FST (SND t)) (SND (SND t)))
```

```
# g `(\x. (\(y1,y2). (P:A->B->C) y1 y2) x) = (\(y1,y2). P y1 y2)`;;
Warning: Free variables in goal: P
val it : goalstack = 1 subgoal (1 total)

`(\x. (\(y1,y2). P y1 y2) x) = (\(y1,y2). P y1 y2)`
# e(REWRITE_TAC[LAMBDA_PAIR]);;
val it : goalstack = No subgoals
```

In a specific case that cannot be covered with these rules, you will want to
prove your own theorem that does an analogous thing.
Writing and proving your own theorem isn't hard because the existing proofs
can be good templates for this.

**A few more useful inference rules.**

- `ETA_AX`: `|- forall t. (\x. t x) = t` (this is one of axioms in HOL Light)
- `FUN_EQ_THM`: `|- forall f g. f = g <=> (forall x. f x = g x)`
- `BETA_THM`: `|- forall f y. (\x. f x) y = f y)`;
- `FORALL_PAIR_THM`: `|- forall P. (forall p. P p) <=> (forall p1 p2. P (p1,p2))`
- `EXISTS_PAIR_THM`: `|- forall P. (exists p. P p) <=> (exists p1 p2. P (p1,p2))`


## 2. Numerical expression

To compute a numerical expression like `1 + 2 * 3`, you can use `NUM_REDUCE_CONV` ([doc](https://hol-light.github.io/references/HTML/NUM_REDUCE_CONV.html)) like this:

```
# NUM_REDUCE_CONV `1 + 2 * 3`;;
val it : thm = |- 1 + 2 * 3 = 7
```

HOL Light also has corresponding `*_REDUCE_CONV`s for signed integers,
real numbers, rational numbers and bit-vectors (`WORD_REDUCE_CONV`).

These `*_REDUCE_CONV` conversions simulate computation by
(1) recursively visiting its subexpressions and trying to reduce using a smaller reduction conversion, `*_RED_CONV`, and
(2) also applying rewrite rules that are registered in `basic_rewrites()`.
`*_RED_CONV` is implemented using smaller reduction conversions,
each of which is tailored to a specific operator (`NUM_ADD_CONV` for addition, `NUM_SUB_CONV` for subtraction, ...).
These smallest units succed only when the expression is has an operator with constant operands.

For natural numbers, there is also a rewrite rule `ARITH` that can 'evaluate' a numerical expression
for a few selected operators.
`ARITH` is useful if you want to keep your proof short by using only few `REWRITE_TAC`.

```
# g `(1 + 2) + x = x + 3`;;
Warning: Free variables in goal: x
val it : goalstack = 1 subgoal (1 total)

`(1 + 2) + x = x + 3`

# e(REWRITE_TAC[ARITH]);;
val it : goalstack = 1 subgoal (1 total)

`3 + x = x + 3`
```

When the input expression cannot be evaluated to a single constant, `*_REDUCE_CONV` tries to do its best and still computes its subexpressions whenever possible.
If the input `t` is something that can always be fully evaluated, `*_COMPUTE_CONV` can be used instead and it is usually faster than `*_REDUCE_CONV`.
For example, using `NUM_COMPUTE_CONV` is typically faster than `NUM_REDUCE_CONV` if the
expression can be reduced to a constant.
If the expression cannot be fully reduced, however, the result of `NUM_COMPUTE_CONV` may diverge
from that of `NUM_REDUCE_CONV`.

```
# NUM_COMPUTE_CONV `if x then (1 + 2) else (1 + 3)`;;
val it : thm = |- (if x then 1 + 2 else 1 + 3) = (if x then 1 + 2 else 1 + 3)
# NUM_REDUCE_CONV `if x then (1 + 2) else (1 + 3)`;;
val it : thm = |- (if x then 1 + 2 else 1 + 3) = (if x then 3 else 4)
```


## 3. Conditional/logical operations and `let`

For basic conditional/logical operations like `if-then-else` and `x /\ y`, `basic_rewrites()`
will already have a list of rewrite rules that can be used to reduce the expression.
Therefore, `REWRITE_CONV[]` can be used to reduce the expression.

```
# basic_rewrites();;
val it : thm list =
  [|- FST (x,y) = x; |- SND (x,y) = y; |- FST x,SND x = x;
   |- (if (x:?3094) = (x:?3094) then (y:?3087) else (z:?3087)) = (y:?3087);
   |- (if true then t1 else t2) = t1; |- (if false then t1 else t2) = t2;
   |- ~ ~t <=> t; |- (@y. y = x) = x; |- x = x <=> true;
   |- (true <=> t) <=> t; |- (t <=> true) <=> t; |- (false <=> t) <=> ~t;
   |- (t <=> false) <=> ~t; |- ~true <=> false; |- ~false <=> true;
   |- true /\ t <=> t; |- t /\ true <=> t; |- false /\ t <=> false;
   |- t /\ false <=> false; |- t /\ t <=> t; |- true \/ t <=> true;
   |- t \/ true <=> true; |- false \/ t <=> t; |- t \/ false <=> t;
   |- t \/ t <=> t; |- true ==> t <=> t; |- t ==> true <=> true;
   |- false ==> t <=> true; |- t ==> t <=> true; |- t ==> false <=> ~t;
   |- (forall x. t) <=> t; |- (exists x. t) <=> t; |- (\x. f x) y = f y;
   |- (x:?851) = (x:?851) ==> p <=> p]
```

**if-then-else**.
Reducing `if-then-else` can be done by applying the `COND_CLAUSES` rewrite rule which can
be found from `class.ml` of HOL Light.
Note that it is already included in `basic_rewrites()`.

**`let`**. Reducing `let x = e in e'` to `e'[e/x]` (zeta reduction) is done by `let_CONV` ([doc](https://hol-light.github.io/references/HTML/let_CONV.html)).


## 4. `match` operation

`MATCH_CONV` ([doc](https://hol-light.github.io/references/HTML/MATCH_CONV.html)) is a conversion
that looks into the first pattern clause of the match expression,
and matches the pattern if possible or eliminates it.

```
# MATCH_CONV `match [1;2;3;4;5] with CONS x (CONS y z) -> z`;;
val it : thm =
  |- (match [1; 2; 3; 4; 5] with CONS x (CONS y z) -> z) = [3; 4; 5]

# MATCH_CONV `match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z`;;
val it : thm =
  |- (match [1; 2; 3; 4; 5] with [] -> [] | CONS x (CONS y z) -> z) =
     (match [1; 2; 3; 4; 5] with CONS x (CONS y z) -> z)
```

This can be repeated using `REPEATC`.

```
# REPEATC MATCH_CONV `match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z`;;
val it : thm =
  |- (match [1; 2; 3; 4; 5] with [] -> [] | CONS x (CONS y z) -> z) =
     [3; 4; 5]
```

Since the match conversion is registered to `basic_convs()` by default, `REWRITE_CONV[]`
can reduce such expressions too.

```
# REWRITE_CONV [] `match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z`;;
val it : thm =
  |- (match [1; 2; 3; 4; 5] with [] -> [] | CONS x (CONS y z) -> z) =
     [3; 4; 5]
```

## 5. Lists

To simplify `EL i list` to `list[i]`, `EL_CONV` ([doc](https://hol-light.github.io/references/HTML/EL_CONV.html)) can be used:

```
# EL_CONV `EL 4 [1;2;3;4;5]`;;
val it : thm = |- EL 4 [1; 2; 3; 4; 5] = 5
```

`LENGTH_CONV` ([doc](https://hol-light.github.io/references/HTML/LENGTH_CONV.html)) reduces `LENGTH l` to its length:

```
# LENGTH_CONV `LENGTH [1;2;3;4;5]`;;
val it : thm = |- LENGTH [1; 2; 3; 4; 5] = 5
```

There are `LIST_OF_SEQ_CONV` ([doc](https://hol-light.github.io/references/HTML/LIST_OF_SEQ_CONV.html)) and `REVERSE_CONV` ([doc](https://hol-light.github.io/references/HTML/REVERSE_CONV.html)) as well.

`LIST_CONV f_conv t` is a generic conversion that receives a term `t` which is a type of `:(A)list` and a conversion `f_conv` and
applies `f_conv` to every element ([doc](https://hol-light.github.io/references/HTML/LIST_CONV.html)).

```
# LIST_CONV num_CONV `[1;2;3;4;5]`;;
val it : thm = |- [1; 2; 3; 4; 5] = [SUC 0; SUC 1; SUC 2; SUC 3; SUC 4]
```

## 6. Inductive data type

`distinctness` ([doc](https://hol-light.github.io/references/HTML/distinctness.html))
and `injectivity` ([doc](https://hol-light.github.io/references/HTML/injectivity.html))
creates useful (in)equality theorems that can be
used to simplify (1) an inequality between constructors, and (2) equality between
same constructor with different arguments.

```
# define_type "btree = LEAF A | NODE btree btree";;
...

# distinctness "btree";;
val it : thm = |- forall a a0' a1'. ~(LEAF a = NODE a0' a1')

# injectivity "btree";;
val it : thm =
  |- (forall a a'. LEAF a = LEAF a' <=> a = a') /\
     (forall a0 a1 a0' a1'.
          NODE a0 a1 = NODE a0' a1' <=> a0 = a0' /\ a1 = a1')
```

## 7. Composing multiple conversions

How can we compute an expression that has both function application and
numerical expression, e.g., `(\x. x + 1) 2` to `3`?
You can compose multiple conversions, say `BETA_CONV` and `NUM_REDUCE_CONV`, to
do a wanted computation.

```
# let my_eval_conv = BETA_CONV THENC NUM_REDUCE_CONV;;
# my_eval_conv `(\x. x + 1) 2`;;
val it : thm = |- (\x. x + 1) 2 = 3
```

If you want to repeatedly apply this conversion, you can use
`REPEATC (BETA_CONV THENC NUM_REDUCE_CONV)`:

```
# let my_eval_conv2 = REPEATC (BETA_CONV THENC NUM_REDUCE_CONV);;
# my_eval_conv2 `(\x. x + (\y. y + 3) (x+1)) 2`;;
val it : thm = |- (\x. x + (\y. y + 3) (x + 1)) 2 = 8
```

You can also use combinators like `CHANGED_CONV` ([doc](https://hol-light.github.io/references/HTML/CHANGED_CONV.html)) to repeat until there is no change,
or `DEPTH_CONV` ([doc](https://hol-light.github.io/references/HTML/DEPTH_CONV.html))
to make e.g., `BETA_CONV` visit subexpressions.


## 8. Building a call-by-value evaluator using the `Compute` module

Writing a custom evaluator by composing multiple conversions as previously described
has a limitation.
If it is necessary to write a fast evaluator that must run on a large expression
(e.g., a decoder of an assembly file, which can contain several thousands of instructions),
using `DEPTH_CONV`/`CHANGED_CONV` combinators can make it slow because the input/intermediate expressions will be large.
In fact, visiting every subexpression might not be necessary; we can choose only one subexpression to reduce and apply a proper conversion
(such a subexpression is often called a 'redex').

Another similar concern is that it is hard to selectively
unfold definitions of constants and/or functions.
Definitions can be unfolded by adding `REWRITE_CONV[my_definition]` between invocations
of other conversions,
but this can make the expression infinitely grow when the definition is recursive
and also unfold constants in unwanted subexpressions.

To deal with these issues, the `Compute` module can be used.
The OCaml module is defined in the `compute.ml` file and loaded from HOL Light by default.
It is possible to construct a custom evaluator (which again has the `conv` type)
that uses the call-by-value strategy with multiple conversions and constant-unfolding
rewrite rules registered.

If your definition is a combination of num expression and word expression, you can make your custom evaluator like this:
```
# needs "Library/words.ml";;
(..)

# let my_add = new_definition `my_add x y = word_add (word (x + y):int32) (word 10)`;;
val my_add : thm =
  |- forall x y. my_add2 x y = word_add (word (x + y)) (word 10)

# let rw = Compute.bool_compset();;
(* Let's make a Compset that already has default evaluation rules on bool ops. *)
val rw : Compute.compset = <abstr>

# word_compute_add_convs rw;;
- : unit = ()

# num_compute_add_convs rw;;
- : unit = ()

# Compute.add_thms [my_add] rw;;
val it : unit = ()

# let my_conv = Compute.WEAK_CBV_CONV rw;;
val my_conv : Hol_lib.term -> Hol_lib.thm = <fun>

# my_conv `my_add 20 30`;;
- : thm = |- my_add 20 30 = word 60
```

Instead of `Compute.bool_compset` you can also use `Compute.basic_compset` which has all `basic_convs` ([doc](https://hol-light.github.io/references/HTML/basic_convs.html)) and `basic_rewrites` ([doc](https://hol-light.github.io/references/HTML/basic_rewrites.html)) added.

`Compute.WEAK_CBV_CONV` receives a Compset and returns a conversion that
does call-by-value evaluation.
Note that there is `Compute.CBV_CONV` as well, which is in fact more aggressive than
the actual call-by-value stragey because it also tries to evaluate the body
of a lambda function even if it is not being applied.
`Compute.WEAK_CBV_CONV` implements the known call-by-value strategy.

`Compute.add_thms` receives a list of equalities, understands how to unfold relevant
constants from it, and applies the equality rule necessary.
If you want to apply a specific conversion to an expression starting with a constant,
`Compute.add_conv` can be used.
One useful case will be adding `GEN_BETA_CONV` to your rewrite rule because
`{WEAK_}CBV_CONV` cannot handle generalized abstractions by default.

```
# Compute.add_conv (`GABS`, (* A generalized abstraction starts from the `GABS` constant. *)
                    2,      (*GABS constant has two operands*)
                    GEN_BETA_CONV) rw;;

# let my_conv2 = Compute.WEAK_CBV_CONV rw;;

# my_conv2 `(\(x,y,z). word_add (my_add x y) z) (10,20,word 5)`;;
val it : Hol_lib.thm =
  |- (\(x,y,z). word_add (my_add x y) z) (10,20,word 5) = word 45
```

Another example Compute function that folds `EL n list`:

```ocaml
let my_conv =
  let rw = Compute.bool_compset () in
  (* avoid folding the branches of conditional expression before evaluating
     its condition *)
  set_skip rw `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs rw;
  Compute.add_thms [EL_CONS] rw;
  Compute.WEAK_CBV_CONV rw;;

my_conv `EL 1 [10;20;30;40]`;; (* - : Hol_lib.thm = |- EL 1 [10; 20; 30; 40] = 20 *)
```
The reason why the `EL` rewrite rule does not work was that it was relying on matching on the SUC constructor, which is not the default constructor that numerals in HOL Light use (they are rather in binary representation).


