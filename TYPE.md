# Type System of HOL Light

HOL Light uses a simply typed lambda calculus.
Then, a natural question is how to represent e.g., a vector of N elements.
The solution is define vector of element type A as N -> A where N is a type variable ([link](https://www.cl.cam.ac.uk/~jrh13/papers/hol05.pdf)).
For example, an `8` type is a set containing `1..8` (or `0..7` if it is more convenient), and using this `8` type we can define `(8)word` which is a word of 8 bits.
Note that `N` does not need to be a numeric-like type; for example, you can use `(bool)word` type.

Note that `printer.ml` has the `typify_universal_set` flag that prints the universal set `UNIV:A->bool` as `"(:A)"`.

#### Q: But `` `let x:num = 1 in let y:(x)word = (word 0:(x)word) in y` `` seems to be a valid term!

A: Yes, but `x` at `:(x)word` isn't bound to `x=1` because it is defined as a type variable. Therefore, it cannot be reduced by zeta-reduction.

```ocaml
# let t = `let x:num = 1 in let y:(x)word = (word x:(x)word) in y`;;
(..)
# let s = let_CONV t;;
val s : thm = |- (let x = 1 in let y = word x in y) = (let y = word 1 in y)

# remove_printer pp_print_qterm;;
# rhs (concl s);;
- : term =
Comb
 (Comb (Const ("LET", `:((x)word->(x)word)->(x)word->(x)word`),
   Abs (Var ("y", `:(x)word`),
    Comb (Const ("LET_END", `:(x)word->(x)word`), Var ("y", `:(x)word`)))),
 Comb (Const ("word", `:num->(x)word`),
  Comb (Const ("NUMERAL", `:num->num`),
   Comb (Const ("BIT1", `:num->num`), Const ("_0", `:num`)))))
```
