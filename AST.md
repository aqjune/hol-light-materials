# Syntax and AST

Sometimes, implementing conversions require understanding the internal representations, or ASTs, of specific terms of interest.
You can read the AST by turning of the printer via `#remove_printer pp_print_qterm;;` and simply typing e.g., `` `x+y` ``.
The printed trees can be lengthy and hard to read in some cases.
This document abbreviates the trees into shorter forms.

## `match`

```ocaml
`match (x:num) with 1 -> T`;;
```
is equivalent to:

```
_MATCH x (\y out. _UNGUARDED_PATTERN (GEQ 1 y) (GEQ T out))
```

```ocaml
`match (x:num) with 1 -> SOME T | 2 -> NONE`;;
```

is equivalent to:
```
_MATCH x (_SEQPATTERN
    (\y1 out1. _UNGUARDED_PATTERN (GEQ 1 y1) (GEQ (SOME T) out1))
    (\y2 out2. _UNGUARDED_PATTERN (GEQ 2 y2) (GEQ NONE out2)))
```
