# Type System of HOL Light

HOL Light uses a simply typed lambda calculus.
Then, a natural question is how to represent e.g., a vector of N elements.
The solution is define vector of element type A as N -> A where N is a type variable (link)

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
