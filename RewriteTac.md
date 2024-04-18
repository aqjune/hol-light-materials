# Using Rewrite Tactic in HOL Light

## How to find the right rewrite rule

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
have the string in their names. The [help](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/search.html)
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



## How to apply at a right place

TODO: ```GEN_REWRITE_TAC (PAT_CONV `\x. x + y`) [...]```

TODO: `TARGET_REWRITE_TAC`

```ocaml
(* Given a goal that is `w1:int64 = w2 /\ w3:int64 = w4`, convert this to
   `val w1 = val w2 /\ val w3 = val w4` using `GSYM VAL_EQ`.
   This works even if the goal has more than one conjunction. *)
GEN_REWRITE_TAC (DEPTH_BINOP_CONV `(/\):bool->bool->bool`) [GSYM VAL_EQ]
```
