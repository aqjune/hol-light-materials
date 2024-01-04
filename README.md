# hol-light-materials
Online materials for HOL Light:
- [Tutorial](https://www.cl.cam.ac.uk/~jrh13/hol-light/tutorial.pdf)
- Reference Manual ([pdf](https://www.cl.cam.ac.uk/~jrh13/hol-light/reference.pdf), [html](https://www.cl.cam.ac.uk/~jrh13/hol-light/reference.html))
- Very Quick Reference ([pdf](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.pdf), [txt](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.txt))

## Fundamentals

Please read [Fundamentals.md](Fundamentals.md)

## Basic Syntax

- A pair of `num`: `num#num`
- Optional `num`: `num option`
- A function definition with its type explicitly specified: `` new_definition `(f:num->num) x = x + 1` ``
- `match` does not have to be a total function; conversion will fail if there is no matching pattern instead.

## Useful & Easy Tricks

### Using or Updating Assumptions in HOL Light

See [PlayingWithAssumptions.md](PlayingWithAssumptions.md).


### How to Use Rewrite Tactic Well

See [RewriteTac.md](RewriteTac.md) (note: this is WIP)

### Useful Custom Tactics

#### Goal Printer

```ocaml
let PRINT_GOAL_TAC (desc: string): tactic =
  fun gl -> let _ = Printf.printf "<%s>\n" desc; print_goal gl in ALL_TAC gl;;
```

#### Rewrite assumptions

```ocaml
(* REWRITE_ASSUMES_TAC `x = 1` picks the `x = 1` assumption and rewrites all other assumptions using this rule. *)
let REWRITE_ASSUMES_TAC (t:term) =
    UNDISCH_THEN t (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm]) THEN ASSUME_TAC thm);;
```

#### `note` Tactic

https://cr.yp.to/2023/holhull-20230406.sage has this `note` tactic that is very handy when you want to add an assumption that can be concluded from a set of rewrite rules 
```ocaml
let notetac t tac = SUBGOAL_THEN t MP_TAC THENL
[tac;
  ALL_TAC] THEN
DISCH_THEN(fun th -> ASSUME_TAC th);;

let note t why = notetac t(ASM_MESON_TAC why);;
  
(* usage *)
note `1 + 2 = 2 + 1` [ADD_SYM] THEN ...
```

#### Examples

```ocaml
(* Get the LHS of DIVISION_SIMP which is thm `|- (!m n. m DIV n * n + m MOD n = m) /\ (!m n. n * m DIV n + m MOD n = m)`,
   and specialize it. *)
SPECL [`x:num`; `2 EXP 32:num`] (CONJUNCT1 DIVISION_SIMP);;
```

```ocaml
(* Given a theorem VAL_MOD_REFL, (1) specialize it with the `y` variable, and (2) rewrite the theorem using
   the DIMINDEX_32 theorem. *)
REWRITE_RULE [DIMINDEX_32] (ISPECL [`y:(32)word`] VAL_MOD_REFL)
```

```ocaml
(* Given n:nat, do destruct n as [ | S n'] *)
DISJ_CASES_TAC(SPECL [`x:num`] num_CASES)

(* Add the names to destruct *)
DISJ_CASES_THEN (LABEL_TAC "mcases") (SPECL [`m:num`] num_CASES)
```

### Useful Conversions

- NUM_REDUCE_CONV

```ocaml
(* Calculate 1 + 2 - 3 *)
NUM_REDUCE_CONV `1 + 2 - 3` (* Note that this is 1 because it is 1 + (2 - 3)!! *)
```

- MOD_DOWN_CONV

### Commands

```ocaml
(* Show the AST of a term *)
#remove_printer pp_print_qterm;;
`match x with | SOME y -> 10 | NONE -> 20`;;
#install_printer pp_print_qterm;;

(* Show the AST of a type *)
#remove_printer pp_print_qtype;;
loads "Library/words.ml":;
`word 10: (32)word`;;
#install_printer pp_print_qtype;;
```

## Internal Representation of Terms

Please read [AST.md](AST.md).

## HOL Light vs. Coq

Please read [HOL Light vs. Coq](HOLLightvsCoq.md).


## Misc

### Thenify

`thenify.py` converts a properly formatted sequence of `e(..);;` commands into the `.. THEN ..` format.
If some tactic produces multiple subgoals, the beginning of each subgoal must be itemized with `- ` and the following
lines must have extra indentations. Currently, the indentation string is fixed to two spaces (`  `).
`thenify_inputs/` has its inputs and `thenify.py <input.txt>` shows the then-ified output. :)

### Others

```ocaml
(* Given an OCaml string 'name' and term 'tm', make a definition `name = tm` *)
new_definition (mk_eq (mk_var (name, `:(..type..)`), tm))
```
