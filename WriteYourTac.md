# Writing a custom tactic

Writing a custom tactic in HOL Light is not very hard.
It is as easy as writing an OCaml function because HOL Light tactics are just OCaml functions.

## 1. HOL Light tactic is an OCaml function

A tactic is an OCaml instance of type `tactic`, and `tactic` is a function type from `goal` to `goalstate`.
`goal` is a pair of named assumptions and conclusion, which is `(string * thm) list * term`.
The former `(string * thm) list` represents the named assumptions, and latter `term` represents the conclusion.
`goalstate` type has a slightly more complicated definition, but unless you are writing a low-level
tactic you can treat it as an opaque type in most cases.
[Fundamentals.md](Fundamentals.md) explains the mechanism of tactic in detail.

We will start with a very simple example, a tactic that does nothing.
There already is `ALL_TAC` that does nothing, and the first thing we will do is to simply reuse it.

```ocaml
let MY_ALL_TAC:tactic = ALL_TAC;;
```

This will work because `ALL_TAC` is also an OCaml object having the `tactic` type.
`MY_ALL_TAC` is equivalent to the following definition as well.

```ocaml
let MY_ALL_TAC:tactic = fun (assums,conclusion) -> ALL_TAC (assums,conclusion);;
```

`assums` is a list of assumptions (with their names), and `conclusion` is a term stating the conclusion
that we would like to eventually prove.
The type of a pair `(assums,conclusion)` is `goal`.

The next step is to extend the `MY_ALL_TAC` to erase assumptions whose name ends with "IGNORE".
We can use OCaml's `List.filter` and `String.ends_with` to filter such assumptions.

```ocaml
let MY_ALL_TAC:tactic =
  fun (assums,conclusion) ->
    let assums' = List.filter
      (fun (name,the_thm) -> not (String.ends_with ~suffix:"IGNORE" name))
      assums in
    ALL_TAC (assums',conclusion);;
```

Let's test this new `MY_ALL_TAC`:
```
# g `x + 1 = y ==> x + 2 = y + 1`;;
Warning: Free variables in goal: x, y
val it : goalstack = 1 subgoal (1 total)

`x + 1 = y ==> x + 2 = y + 1`

# e(DISCH_THEN (LABEL_TAC "H_IGNORE"));;
val it : goalstack = 1 subgoal (1 total)

  0 [`x + 1 = y`] (H_IGNORE)

`x + 2 = y + 1`

# e(MY_ALL_TAC);;
val it : goalstack = 1 subgoal (1 total)

`x + 2 = y + 1`
```

### Using tactic combinator

You can use tactic combinators such as `THEN`, `THENL` and `ORELSE` in your custom tactic
because they are in fact OCaml functions that take tactics and return the combined tactic.
For example, the following function is a valid tactic:

```ocaml
let MY_TAC2 = MY_ALL_TAC THEN ASM_ARITH_TAC;;
(* this is equal to the above version *)
let MY_TAC2' = fun (assums,conclusion) -> (MY_ALL_TAC THEN ASM_ARITH_TAC) (assums,conclusion);;
```

To avoid the repeated use of `(assums,conclusion)` at the end, the `W` combinator can be used.
`W f x` is simply `f x x`.

```ocaml
let MY_TAC2'' = W (fun (assums,conclusion) -> (MY_ALL_TAC THEN ASM_ARITH_TAC));;
```


## 2. Writing advanced tactics

### Asserting that the current goal state is in a good shape.
You can use `term_match` ([doc](https://hol-light.github.io/references/HTML/term_match.html)) to
assert that the conclusion is in a good shape.
`term_match` is an OCaml function that returns a matching (`instantiation`) if the term (last arg)
can be matched to a given pattern term (second arg), or raise `Failure` otherwise.
Note that this function isn't specialized for tactic implementation;
this can be used in generic cases, and we are using it here to check the conclusion.

```ocaml
let MY_CHECKER_TAC:tactic =
  fun (asl,g) ->
    (* Let's assert that the conclusion has the form 'x = y'. *)
    let _ = term_match [] `x = y` g in
    ALL_TAC (asl,g);;
```

```
# g `1 < 2`;;
val it : goalstack = 1 subgoal (1 total)

`1 < 2`

# e(MY_CHECKER_TAC);; (* This should fail *)
Warning: inventing type variables
Exception: Failure "term_pmatch".
```

To check that two terms are alpha-equivalent, `aconv` ([doc](https://hol-light.github.io/references/HTML/aconv.html))
can be used.
```
# aconv `?x. x <=> T` `?y. y <=> T`;;
val it : bool = true
```

<b>Getting free variables.</b>
To check a variable appears as a free variable inside an expression,
you can use `vfree_in` ([doc](https://hol-light.github.io/references/HTML/vfree_in.html)).
`frees` return a list of free variables ([doc](https://hol-light.github.io/references/HTML/frees.html)).

```
# vfree_in `x:num` `x + y + 1`;;
val it : bool = true
# frees `x = 1 /\ y = 2 /\ !z. z >= 0`;;
val it : term list = [`x`; `y`]
```

<b>Decomposing a term.</b>

- Numeral: You can use `is_numeral` to check whether the term is a constant numeral
([doc](https://hol-light.github.io/references/HTML/is_numeral.html)),
and use `dest_numeral` ([doc](https://hol-light.github.io/references/HTML/dest_numeral.html))
to get the actual constant.
The returned constant is a general-precision number datatype `num`.
If you know that the constant should fit in OCaml `int`,
use `dest_small_number`([doc](https://hol-light.github.io/references/HTML/dest_small_numeral.html`)).

- Function application: `strip_comb` will break `f x y z` into ``(`f`,[`x`;`y`;`z`])``
([doc](https://hol-light.github.io/references/HTML/strip_comb.html)).

- Others: there are `is_forall`, `strip_forall`, `is_conj`, `dest_conj`, `conjuncts`, etc.

### Checking that tactic actually did something

`CHANGED_TAC t` is a tactic that fails if tactic `t` did not change the goal state.


### Dealing with subgoals

To check that there only is one subgoal,
`tactic THENL [ ALL_TAC ] THEN next_tactic` can be used.
To check that there exactly are `n` subgoals,
`tactic THENL (map (fun _ -> ALL_TAC) (1--10)) THEN next_tactic`
will work.
