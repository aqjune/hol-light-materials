# Syntax and AST

Sometimes, implementing conversions require understanding the internal representations, or ASTs, of specific terms of interest.
You can read the AST by turning of the printer via `#remove_printer pp_print_qterm;;` and simply typing e.g., `` `x+y` ``.
The printed trees can be lengthy and hard to read in some cases.
This document abbreviates the trees into shorter forms if necessary.

## Constants and variables

Constants and variables are represented as `Const(name:string, ty:hol_type)` and `Var(name:string, ty:hol_type)`
respectively.
Function applications are represented as `Comb(lhs:term, rhs:term)`.

```
# let my_add = define `my_add x = x + 1`;;
val my_add : thm = |- my_add x = x + 1
# #remove_printer pp_print_qterm;;
# `my_add n`;;
val it : term = Comb (Const ("my_add", `:num->num`), Var ("n", `:num`))
```

A natural number is represented in binary using `NUMERAL`,`BIT1`,`BIT0`,`_0` constructors.

```
# `6`;;
val it : term =
  Comb (Const ("NUMERAL", `:num->num`),
   Comb (Const ("BIT0", `:num->num`),
    Comb (Const ("BIT1", `:num->num`),
     Comb (Const ("BIT1", `:num->num`), Const ("_0", `:num`)))))
```

## `let .. in ..`

`` `let x = 3 in x + 1` `` is equivalent to:

```ocaml
Comb
  (Comb (Const ("LET", `:(num->num)->num->num`),
    Abs (Var ("x", `:num`),
    Comb (Const ("LET_END", `:num->num`),
      Comb (Comb (Const ("+", `:num->num->num`), Var ("x", `:num`)),
      Comb (Const ("NUMERAL", `:num->num`),
        Comb (Const ("BIT1", `:num->num`), Const ("_0", `:num`))))))),
  Comb (Const ("NUMERAL", `:num->num`),
    Comb (Const ("BIT1", `:num->num`),
      Comb (Const ("BIT1", `:num->num`), Const ("_0", `:num`)))))
```

## `match`

```ocaml
`match (x:num) with 1 -> T`;;
```
is equivalent to:

```ocaml
_MATCH x (\y out. _UNGUARDED_PATTERN (GEQ 1 y) (GEQ T out))
```

```ocaml
`match (x:num) with 1 -> SOME T | 2 -> NONE`;;
```

is equivalent to:
```ocaml
_MATCH x (_SEQPATTERN
    (\y1 out1. _UNGUARDED_PATTERN (GEQ 1 y1) (GEQ (SOME T) out1))
    (\y2 out2. _UNGUARDED_PATTERN (GEQ 2 y2) (GEQ NONE out2)))
```
