# Using Rewrite Tactic in HOL Light

## How to find the right rewrite rule

The first thing that you will want to do when using `REWRITE_TAC` or its family tactic is
to find out which rewrite rules to apply.

### Using `search`

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

### Building the rewrite rule on-the-fly

If you think the rewrite rule that you want to use is too specific to the case,
you can build the rewrite rule on-the-fly using various conversions.

For example, if you want to apply a rewrite rule `x * (y + z + w) = x * y + x * z + x * w` on
some natural number expression,
you can use `ARITH_RULE` conversion as follows:

```ocaml
e(REWRITE_TAC[ARITH_RULE `x * (y + z + w) = x * y + x * z + x * w`]);;
```

Useful conversions are:
- `ARITH_RULE`: for natural numbers
- `INT_ARITH`: for integers
- `REAL_ARITH`: for real numbers
- `TAUT`: for tautology (see [TAUT](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/TAUT.html))
- `MESON[]`, `METIS[]`: for first-order logic (see [MESON](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/MESON.html),
[METIS](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/METIS.html)) 
- `REWRITE_CONV[]`: a conversion to create a rewrite rule using other rewrite rules on the fly! (see [REWRITE_CONV](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REWRITE_CONV.html))
- `WORD_RULE`, `WORD_ARITH`, `WORD_BITWISE_RULE`, `WORD_BLAST`, `BITBLALST_RULE`: for bit-vectors (`N word` type)

### Choosing an assumption as a rewrite rule

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
