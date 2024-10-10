# An overview of HOL Light

You might be interested in reading [this article](https://www.cl.cam.ac.uk/~jrh13/papers/hollight.pdf)
as well.

## HOL Light from a perspective of OCaml programmer

The goal of using HOL Light is to logically prove that a proposition is true.
A proposition is typically represented as a `term` data structure of OCaml, and
proving the proposition is equivalent to creating an instance of a `thm` OCaml type
describing the proposition.

### The `term` type

`term` is an OCaml data type that is used to represent any mathematical
formula such as `1 + 2` and `forall x. x - x = 0`.
A new `term` is created using the `parse_term` OCaml function by provinding
a string formula to it.
For example, `parse_term "x + y"` will construct the HOL Light term that will actually
look like the following:

```ocaml
Comb (Comb (Const ("+", `:num->num->num`), Var ("x", `:num`)), Var ("y", `:num`))
```

To avoid writing `parse_term` every time, back-ticks can be used.
These back-ticks are read by a Camlp5 preprocessor of HOL Light and automatically
converted to the `parse_term` form.
For example, `` `x + y` `` is translated to `parse_term "x + y"` after preprocessing.
Also, a pretty-printer for the `term` objects is set up on OCaml REPL for readability.
Therefore, running `parse_term "x + y"` on REPL will print:

```ocaml
val it : term = `x + y`
```

### The `thm` type

The `thm` OCaml type represents proven facts.
The type is private, meaning that a programmer cannot freely create
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
    - ex) Goal `x + 0 = x` is valid, and it means `forall x. x + 0 = x` (or more briefly, `!x. x + 0 = x`)
- `!x. P x` (which is `forall x, P x` in Coq and verbosely `forall x. P x` in HOL Light as well) is
    equivalent to `(P = \x. true)`.
- Unlike Coq, you cannot define a type of an empty element (`False` in Coq)
    - See also: [new_type_definition](https://github.com/jrh13/hol-light/blob/master/Help/new_type_definition.hlp)
    - This allows you to prove `exists x y. x = y`!
- Uses a simply typed lambda calculus. (See [TYPE.md](TYPE.md))
- `match` does not have to be a total function; conversion will fail if there is no matching pattern instead.

## Basic Syntax

- `` `..` `` is a HOL Light term which is in fact `parse_term("..")`.
- `` `:..` `` is a HOL Light type which is in fact `parse_type ("..")`.
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

Using tactic of HOL Light, a user can break a large goal into smaller, more tractable goals.
When the 'subgoals' become sufficiently small, they can be proven by simply applying existing
lemma or even by other tactics that can directly discharge the subgoal.
This 'backward-style' proof is different from a forward-style which is starting
from the given assumptions and constructing intermediate theorems using
inference rules.

In OCaml, a tactic (`tactic` type) is a function from `goal` to `goalstate`.
`goal` is a pair of named assumptions and conclusion term.
`goalstate` is a complex data structure that has a list of subgoals.


### How does it eventually reconstruct a `thm` instance?

Since it is the `thm` type that represents a proven fact in HOL Light,
tactic must be able to reconstruct the `thm` instance in the end.
To understand how tactic reconstructs a theorem, we need to look at
the definition of `justification` type in `tactics.ml`.

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

The type is a function taking two arguments and returning `thm`.

  1. `instantiation` is a mapping from metavariables to their expressions.
     This is also a return type of a `term_match` function, so looking at
     its documentation will be helpful in understanding it further.
  2. `thm list` is a list of proven theorems. Each item of this list
     will be the theorem created after each subgoal is finally proven.
     For example, if the tactic was applying an inference rule,
     the `thm list` must be the list of proven assumptions for the rule.

Each goalstate carries its growing justification function object, as shown
from the previous OCaml definition of `goalstate`.
Applying a tactic will create a new `goalstate` with possibly 'smaller'
goals and its justification.
Once the initial goal is fully proven, the goalstate will contain an empty
subgoal and fully grown justification.
The full theorem then can be reconstructed by invoking the justification
function with empty instantiation (`null_inst`) and empty theorems (`[]`).
The `top_thm` function as well as a part of `prove` function does this.

One good example showing how justification works is `CONJ_TAC` which splits the goal `A ?- P /\ Q`
into two subgoals `A ?- P` and `A ?- Q`.
Its inference rule version, `CONJ`, will take the proven facts `A |- P` and
`B |- Q` and return `A u B |- P /\ Q`.
The definition of `CONJ_TAC` clearly shows how `CONJ` is used to build its
justification:

```ocaml
let (CONJ_TAC: tactic) =
  fun (asl,w) -> (* asl: assumptions list, w: conclusion *)
    try let l,r = dest_conj w in
        null_meta,(* no metavariable instantiation *)
        [asl,l; asl,r], (* has two subgoals *)
        fun _ [th1;th2] -> CONJ th1 th2 (* this is the justification *)
    with Failure _ -> failwith "CONJ_TAC";;
```

After a user writes a full proof using tactics,
HOL Light checks whether the proof is correct by composing the justification functions
of the used tactics and checking whether the justification function returns a wanted `thm` instance.
If the returned `thm` instance is syntactically correct, it indeed represents a correct proof
because any created `thm` instance is logically correct by construction (unless axiomatized). :)


### `e(tac)` modularly checks the validity of `tac`

We can check whether a full proof consisting of multiple tactics is correct or not by
inspecting the output of composed justification function.
Another important question would be how to check whether individual tactic is correct,
or at least 'makes sense'.
For example, let's assume that you are writing your own `CONJ_TAC` implementation.
How can one check that the tactic provides the right next subgoals and justification function?

This is called the validity of a tactic.
`e(tac)` checks the validity of `tac` using `VALID` ([doc](https://hol-light.github.io/references/HTML/VALID.html))
internally.
It is easy to write an example that makes the validity check fail.
For example, consider a tactic that adds `x = 0` without any context:

```ocaml
let BOGUS_TAC:tactic =
  fun (assums,goal) -> ALL_TAC (("I_am_bogus",ASSUME `x = 0`)::assums,goal);;
```

Running this tactic should fail in general because it is adding `x = 0` as
an assumption without any condition.
Indeed, using this tactic will raise `Failure "VALID: Invalid tactic"` exception.

```
# g `x + 1 = 1`;;
Warning: Free variables in goal: x
val it : goalstack = 1 subgoal (1 total)

`x + 1 = 1`

# e(BOGUS_TAC);;
Exception: Failure "VALID: Invalid tactic".
```

The mechanism of validity check is simple. We will use the previous `CONJ_TAC` as an example.
Let's assume that, from a goal `(assums,concl)`, applying `CONJ_TAC` returned
(1) two subgoals `(assums1,concl1)` and `(assums2,concl2)`
(2) a justification `f` which will take the two sub-theorems for inference rule `CONJ`
    (we will omit the metavariable instantiation for simplicty).

Also, let's assume that we could somehow construct a theorem `thm1` that exactly
corresponds to `(assums1,concl1)` and `thm2` that is exactly `(assums2,concl2)`.
If the output theorem of `f (thm1,thm2)` is equivalent to `(assums,concl)`, meaning that
its assumptions are `assums` and its conclusion is `concl`, `f` successfully justified that
the tactic worked well fine.

One important question is: can we construct a theorem `thm1` for
`(assums1,concl1)` and `thm2` for `(assums2,concl2)` without axiomatizing these?
It is `mk_fthm` that does a trick.
Instead of axiomatization, `mk_fthm(assums,concl)` returns a new theorem
that is `assums,_FALSITY_ |- concl` where `_FALSITY_ = false`.
This is correct because false implies anything.
Then, the theorems generated by this function are fed to `f` and the output theorem is checked.
This is under an assumption that the justification function is oblivious of `_FALSITY_`
and does not do something smart using it.