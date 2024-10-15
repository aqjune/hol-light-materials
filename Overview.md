# An overview of HOL Light

## 1. HOL Light from a perspective of OCaml programmer

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

Given a goal which is a `term` type, writing its proof is simply writing an OCaml expression that
constructs the `thm` instance whose conclusion is the goal and assumption is an empty list.

HOL Light proofs are often written in a 'backward' style, which is, breaking a large goal into
smaller, more tractable subgoals and attacking these.
When the subgoals become sufficiently small, they can be proven by simply applying existing
lemma or even by other tactics that can directly discharge the subgoal.
This 'backward-style' proof is different from a forward-style which is starting
from the given assumptions and constructing intermediate theorems using
inference rules.

There are two generic styles of backward-stype proofs in HOL Light. The first style is to
interactively write proofs on OCaml REPL.
This uses a subgoal package which contains several OCaml functions like `g` and `e`.
Running these functions on OCaml REPL allows users to interactively set the goal term and
prove step-by-step.
`g` is an OCaml function that takes a term and sets it as a goal.
`e` is an OCaml function that receives a `tactic` OCaml instance and applies it to the current goal,
refining it to a possibly smaller subgoal(s).
In this proof-writing style, OCaml REPL is often used to type commands and read the next goal state.
If writing proof is successfully finished, there must be no remaining subgoal.
Then, function `top_thm` will return the `thm` instance that represents the proven theorem.

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


## 2. Interesting facts

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

## 3. Basic syntax and commands

- `` `..` `` is a HOL Light term which is in fact `parse_term("..")` without the camlp5 preprocessor.
- `` `:..` `` is a HOL Light type which is in fact `parse_type ("..")` without the camlp5 preprocessor.
- `// ..` is an inline comment. This notation can be changed by a user by updating `comment_token`([doc](https://hol-light.github.io/references/HTML/comment_token.html)).

### Expressions

- Let binding: `let x = e in y`
- If-then-else: `if c then e1 else e2`
- Match expression: `match x with .. -> .. | .. -> ..`
- True: `true`, (or succinctly) `T` / False: `false`, (or succinctly) `F`
- Optional value: `NONE`, `SOME x`
- List: `[]`, `[1;2;3]`, `CONS 1 (CONS 2 NIL)`
- Universal quantification: `forall x. ..(x)..`, (or succinctly) `!x. ..(x)..`
- Existential quantification: `exists x. ..(x)..`, (or succinctly) `?x. ..(x)..`
- Uniqueness quantification: `existsunique x. ..(x)..`, (or succinctly) `?!x. ..(x)..`

### Types

- A symbolic type `A`: `` `:A` ``
- An expression `e` which has type `A`: `` `e:A` ``
- A natural number type: `` `:num` ``
- A pair of `:num` type: `` `:num#num` ``
- Optional `num`: `` `:num option` ``
- Number list type: `` `:num list` ``
- Bit-vector: `` `:8 word` `` (8-bit word), `` `:N word` ``

### Commands (which are OCaml functions)

- Define a function `f`: `` new_definition `(f:num->num) x = x + 1` ``
- Define an inductive data type: `` define_type `new_typename = .. | .. | ..` `` ([doc](https://hol-light.github.io/references/HTML/define_type.html))


## 4. Q&As

Q: What are the benefits of using HOL Light?
- Its underlying language, OCaml, is a well-known generic-purpose language.
  If you are already familiar with OCaml, you can quickly understand many parts of existing HOL Light proofs.
- Its small core provides a transparent view about how things are working in OCaml.
  This is especially important when you are dealing with large proofs and understanding why
  the proof checking is slow is necessary.
  Also, you can use optimized OCaml library/compilers as well.
- Writing a tactic is really writing a simple OCaml function. You can quickly learn how to learn very
  advanced tactics.
- Has automated tactics that proves low-level theorems such as an equality between two bit-vector expressions.

Q: Can I prove a property of OCaml function in HOL Light without embedding it in HOL Light?
- No.

Q: How can I make loading `hol.sh` faster?
- To avoid repeating initialization, you can use a checkpointing program.
  I recommend DMTCP, but there are CRIU and selfie as well (the README of HOL Light has instructions).
