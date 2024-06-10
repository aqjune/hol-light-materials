# An overview of HOL Light

You might be interested in reading [this article](https://www.cl.cam.ac.uk/~jrh13/papers/hollight.pdf)
as well.

## HOL Light from a perspective of OCaml programmer

### The `thm` type

The goal of using HOL Light is to logically prove that a proposition is true.
A proposition is typically represented as a `term` data structure of OCaml, and
proving the proposition is equivalent to creating an instance of a `thm` OCaml type
describing the proposition.
The `thm` OCaml type is private, meaning that a programmer cannot freely create
an arbitrary instance of `thm`.
This prevents users from proving a false theorem (*consistency of the system of logic*).
To be concrete, let's dive into the definition of type `thm` in
`fusion.ml` ([link](https://github.com/jrh13/hol-light/blob/master/fusion.ml)):

```ocaml
module type Hol_kernel =
  sig
    ...
    type thm
    ...
end;;

module Hol : Hol_kernel = struct
  ...
  type thm = Sequent of (term list * term)
  ...
end;;
```

As shown above, `thm`'s constructor `Sequent` is not visible to the users outside `module Hol`.

The only way to create a valid `thm` instance is through the functions inside the `Hol` module
which have access to the `Sequent` constructor.
Among those, 10 are primitive inference rules that constitute the logical foundation of HOL Light
([link](https://github.com/jrh13/hol-light/blob/ae6f82198f85860f2fb648882bdc90f307e5f821/fusion.ml#L72-L81)).
A user can prove the interested theorem using these axioms in theory, but in practice this is
tough because a typical proof tree can grow very large.
There are two more functions: `new_axiom` and `new_basic_definition`.
`new_axiom` creates a new `thm` instance and it can indeed be used to create a false theorem.
To check whether any axiom has been introduced in the past, the return value of `axioms()` can be
checked.
Note that HOL Light introduces three axioms by default: `INFINITY_AX`, `ETA_AX`, and `SELECT_AX`.
`new_basic_definition` adds a new definition of form `x = e` and returns it as a `thm` instanace.
Using it does not introduce inconsistency in the logical system.


### Writing a proof in HOL Light

There are two generic styles of proofs in HOL Light. The first style is interactive proof-writing
style using subgoal packages.
A subgoal package contains several OCaml functions like `g` and `e` that allows users to
interactively set the goal term and prove step-by-step.
`g` is an OCaml function that takes a term and sets it as a goal.
`e` is an OCaml function that receives a `tactic` OCaml instance and applies it to the current goal,
refining it to a possibly smaller subgoal(s).
In this proof-writing style, OCaml REPL is often used to type commands and read the next goal state.
If writing proof is successfully finished, function `top_thm` will return the `thm` instance
that represents the proven theorem.

The second style is using a `prove` function.
It takes a pair of (1) goal term, and (2) one large tactic that is supposed to prove the goal
in one shot.
If the tactic proves the goal, `prove` returns a new `thm` instance.
Otherwise, it raises an exception.
The one large tactic is typically a series of tactics concatenated with `THEN`, or a tree-structure
of tactics concatenated with `THENL` if it creates multiple subgoals in the proof.

The first style is convenient for writing a proof, it is verbose because it has to repeat
`e(..)` and each `e` only applies to one of the subgoals.
Also, in some cases, it is slower than `prove` because `e` checks validity of a tactic
(`VAILD`, [link](https://hol-light.github.io/references/HTML/VALID.html)).
The second style is more succinct because (1) it omits `e(..)`, and (2) `t1 THEN t2` allows you to
apply `t2` to all subgoals of `t1`.
Also, it does not have to go through validity check.
However, it is fundamentally not interactive because it is a single OCaml expression rather than
multiple `;;`-separated OCaml statements.
Therefore, a natural flow would be to first write the proof in `g`-`e` style, then after it is
complete convert it into the `THEN` form and invoke `prove` with it.
However, this conversion is laborsome and unfortunately error-prone if done by hand.
For this reason, what I typically do is to just write a proof in the `THEN` style from the beginning,
then use an editor that supports automatic conversion of a selected text into the `e(..)`
form and running it. hol-light plugin of VSCode supports this.


## Interesting facts

- Proposition is simply bool.
    - Truth has a bool type (`` type_of `T` `` is bool)
    - `TAUT` allows excluded middle. Double negation elimination (`~~P -> P`) is allowed
- Allows functional extensionality.
- Unbound variables are considered as universally quantified variables
    - ex) Goal `x + 0 = x` is valid, and it means `!x. x + 0 = x`
- `!P` (which is `forall x, P x` in Coq) is equivalent to `(P = \x. true)`.
    - Therefore, `!` is `\P. (P = \x. true)`.
- Unlike Coq, you cannot define a type of an empty element (`False` in Coq)
    - See also: [new_type_definition](https://github.com/jrh13/hol-light/blob/master/Help/new_type_definition.hlp)
    - This allows you to prove `?x y. x = y`! (`?x` is exists x.)
- Uses a simply typed lambda calculus. (See [TYPE.md](TYPE.md))
- `match` does not have to be a total function; conversion will fail if there is no matching pattern instead.

## Basic Syntax

- `` `..` `` is a HOL Light term which is in fact `parse_term("..")`.
- `// ..` is an inline comment. This can be changed by manipulating some configuration.

### Typing.

- `:A`: type `A`
- A pair of `:num` type: `:num#num`
- Optional `num`: `:num option`
- List: `:num list`
- A function definition with its type explicitly specified: `` new_definition `(f:num->num) x = x + 1` ``
- Bit-vector: `:8 word`, `:N word`

### AST

- Let binding: `let x = e in y`
- If-then-else: `if c then e1 else e2`


## OCaml Definitions

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

Definitions for interactive proof-writing:

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


## Tactic of HOL Light

Tactic is a function from `goal` to `goalstate`.
`goal` is a pair of named assumptions and conclusion term.
`goalstate` is a complex data structure that has a list of subgoals, and
one `goalstate` is created after a `e()` function call.
Note that a tactic is only applied to the first goal of a goalstate.


### How does it eventually reconstruct a `thm` object?

Tactic allows writing a proof in a backward style by breaking a large goal into
smaller, more tractable goal.
However, since it is the `thm` type that represents a proven fact in HOL Light,
tactic must be able to reconstruct the `thm` instance in the end.

To understand how tactic reconstructs a `thm` instance, we need to look at
the `justification` type in `tactics.ml`.

```ocaml
(* tactics.ml *)
(* ------------------------------------------------------------------------- *)
(* A justification function for a goalstate [A1 ?- g1; ...; An ?- gn],       *)
(* starting from an initial goal A ?- g, is a function f such that for any   *)
(* instantiation @:                                                          *)
(*                                                                           *)
(*   f(@) [A1@ |- g1@; ...; An@ |- gn@] = A@ |- g@                           *)
(* ------------------------------------------------------------------------- *)

type justification = instantiation -> thm list -> thm;;
```

It takes

  1. `instantiation` which is a mapping from variables to their expressions.
     This is also a return type of a `term_match` function.
  2. `thm list` which is a list of proven theorems. Each item of this list
     will be the theorem created after each subgoal is finally proven.

Each goalstate carries its growing justification function object, as shown
from the previous OCaml definition of `goalstate`.
One `e()` function call will create a new `goalstate` with possibly 'smaller'
goals and grown justification.
Once the initial goal is fully proven, the goalstate will contain an empty
subgoal and fully grown justification.
The full theorem then can be reconstructed by invoking the justification
function with empty instantiation (`null_inst`) and empty theorems (`[]`).
The `top_thm` function as well as a part of `prove` function does this.
