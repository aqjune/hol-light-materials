# OCaml Data Structures of HOL Light

## 1. Types, terms and theorems

Types, terms and theorems:

```ocaml
(* Location: fusion.ml *)
(* type is a type *)
type hol_type = Tyvar of string
              | Tyapp of string *  hol_type list

(* term is a mathematical expression *)
type term = Var of string * hol_type
          | Const of string * hol_type
          | Comb of term * term         (* e1 e2 *)
          | Abs of term * term          (* \x. e *)

(* thm (theorem) is a proven fact *)
type thm = Sequent of (term list * term)
```

## 2. Definitions for interactive proof-writing:

```ocaml
(* Location: tactics.ml *)
(* A goal consists of named hypotheses ((string * thm) list) and yet unproven conclusion *)
type goal = (string * thm) list * term;;

(* A goalstate is ((meta variables list, instantiation), goals, justification).
   Justification is a function that reconstructs the original theorem from
   the theorems that correspond to the goals. *)
type goalstate = (term list * instantiation) * goal list * justification;;

(* a tactic for writing a backward proof. The definition of goalstate is kind of complicated. *)
type tactic = goal -> goalstate;;

type thm_tactic = thm -> tactic;;
```

Conversion from a term to a theorem:

```ocaml
(* Location: equal.ml *)
(* conv (conversion) is simply an inference rule of type term -> thm that when given
   a term t, always returns (assuming it doesn’t fail) an equational theorem of the form
   `t = t′, that is, it proves that the term it was given is equal to some other term,
   possibly the same as the original. *)
type conv = term->thm;;
```

## 3. Abstract Syntax Tree

Sometimes, implementing conversions require understanding the internal representations, or ASTs, of specific terms of interest.
You can read the AST by turning of the printer via `#remove_printer pp_print_qterm;;` and simply typing e.g., `` `x+y` ``.
The printed trees can be lengthy and hard to read in some cases.
This document abbreviates the trees into shorter forms if necessary.

### Constants and variables

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

### `let .. in ..`

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

### `match`

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
