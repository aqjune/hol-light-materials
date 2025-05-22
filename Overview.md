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
The constructor takes a pair of `term list` and `term`, where `term list` is a list of
assumptions and `term` is a conclusion.

The only way to create a valid `thm` instance is through the functions inside the `Hol` module
which have access to the `Sequent` constructor.
Among those, 10 are primitive inference rules that constitute the logical foundation of HOL Light
([link](https://github.com/jrh13/hol-light/blob/ae6f82198f85860f2fb648882bdc90f307e5f821/fusion.ml#L72-L81)).
A user can prove the interested theorem using these axioms in theory, but in practice this is
tough because a typical proof tree can grow very large.

Other than using the existing axioms, there are two more functions to make a `thm` instance:
`new_axiom` and `new_basic_definition`.
`new_axiom` creates a new `thm` instance and it can indeed be used to create a false theorem.
To check whether any axiom has been introduced in the past, the return value of `axioms()` can be
checked.
Note that HOL Light introduces three axioms by default: `INFINITY_AX`, `ETA_AX`, and `SELECT_AX`.
`new_basic_definition` adds a new definition of form `x = e` and returns it as a `thm` instanace.
Using it does not introduce inconsistency in the logical system.


### Writing a proof in HOL Light

Given a goal which is a `term` type, writing its proof is simply writing an OCaml expression that
constructs the `thm` instance whose conclusion is the goal and assumption is an empty list.

For example, if we want to prove that `forall x. x + 1 = 1 + x` is true, we must write a proof
that will help creation of a theorem instance which should be
`` Sequent ([], `forall x. x + 1 = 1 + x`) ``.
Of course, we can directly make this theorem object using `new_axiom`, but this might not be
what we want.

#### How does a typical HOL Light proof look like?

HOL Light proofs are often written in a 'backward' style, which is, breaking a large goal into
smaller, more tractable subgoals and attacking these.
This is analogous to "To show that the goal is true, it is sufficient to prove this slightly
simpler goal" in mathematics.
When the subgoals become sufficiently small, they can be proven by simply applying existing
lemma or even by other tactics that can directly discharge the subgoal.

This 'backward-style' proof is different from a forward-style which is starting
from the given assumptions and constructing intermediate theorems using
inference rules.
Note that, however, the backward style is not the only available option in HOL Light and
one can also write it in a forward style.
This document will introduce the backward style for brevity.

#### Two proof-writing styles

There are two widely used methods for writing backward-style proofs in HOL Light.
The first style is to use a subgoal package which contains several OCaml functions like `g` and `e`.
To help users to interactively see the 'current' proof state and write the next part of their
proof, this method is supposed to be used on OCaml REPL.
The second style is using a `prove` function.
It takes a pair of (1) goal term, and (2) one large tactic that is supposed to prove the goal
in one shot.


<b>Using a subgoal package.</b>
To start with, a function `g` is an OCaml function that takes a term and sets it as a goal.
For example, on OCaml REPL (you can use `hol.sh` provided by HOL Light to launch OCaml REPL with
the right configuration):

```
# g `forall x. x + 1 = 1 + x`;;
val it : goalstack = 1 subgoal (1 total)

`forall x. x + 1 = 1 + x`

#
```

`e` is an OCaml function that receives a `tactic` OCaml instance and applies it to the current goal,
refining it to a possibly smaller subgoal(s).
If writing proof is successfully finished, there must be no remaining subgoal.
For the above example, we can simply use a `ARITH_TAC` tactic ([doc](https://hol-light.github.io/references/HTML/ARITH_TAC.html)) to immediately prove the goal.

```
# ARITH_TAC;;
val it : tactic = <fun>

# e ARITH_TAC;;
val it : goalstack = No subgoals
```

Then, function `top_thm` will return the `thm` instance that represents the proven theorem.

```
# top_thm();;
val it : thm = |- forall x. x + 1 = 1 + x
```

The automatically installed pretty printer of `thm` will use `|-` and show the list of assumptions
on the left and its conclusion on the right, which are actually the two components of `Sequent`.

<b>Using `prove`.</b>
The second style is using a `prove` function.
It takes a pair of (1) goal term, and (2) one large tactic that is supposed to prove the goal
in one shot.
If the tactic proves the goal, `prove` returns a new `thm` instance.
Otherwise, it raises an exception.

```
# let my_theorem = prove(`forall x. x + 1 = 1 + x`, ARITH_TAC);;
val my_theorem : thm = |- forall x. x + 1 = 1 + x
```

The one large tactic is typically a series of tactics concatenated with `THEN`, or a tree-structure
of tactics concatenated with `THENL` if it creates multiple subgoals in the proof.

<b>Which style should I use?</b>
The first style is convenient when you are actually writing a proof, because its style is
interactive.
However, you have to repeat `e(..)` and each `e` only applies to one of the subgoals.
Also, in some cases, its running time is slower than `prove` because `e` checks validity of a tactic
(`VAILD`, [link](https://hol-light.github.io/references/HTML/VALID.html)).
A validity of a tactic will be explained in detail in [TacticDetails.md](TacticDetails.md).
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


## 2. Basic syntax and commands

- `` `..` `` is a HOL Light term which is in fact `parse_term("..")` without the camlp5 preprocessor.
- `` `:..` `` is a HOL Light type which is in fact `parse_type ("..")` without the camlp5 preprocessor.
- `// ..` is an inline comment. This notation can be changed by a user by updating `comment_token`([doc](https://hol-light.github.io/references/HTML/comment_token.html)).

### Expressions in HOL Light

- Let binding: `` `let x = e in y` ``
- If-then-else: `` `if c then e1 else e2` ``
- Match expression: `` `match x with .. -> .. | .. -> ..` ``
- True: `` `true` ``, (or succinctly) `` `T` `` / False: `` `false` ``, (or succinctly) `` `F` ``
- Optional value: `` `NONE` ``, `` `SOME x` ``
- List: `` `[]` ``, `` `[1;2;3]` ``, `` `CONS 1 (CONS 2 NIL)` ``
- Universal quantification: `` `forall x. ..(x)..` ``, (or succinctly) `` `!x. ..(x)..` ``
- Existential quantification: `` `exists x. ..(x)..` ``, (or succinctly) `` `?x. ..(x)..` ``
- Uniqueness quantification: `` `existsunique x. ..(x)..` ``, (or succinctly) `` `?!x. ..(x)..` ``

### Types in HOL Light

- A natural number: `:num`
- A symbolic type `A`: `` `:A` ``
- An expression `e` which has type `A`: `` `e:A` ``
- A natural number type: `` `:num` ``
- A pair of `:num` type: `` `:num#num` ``
- Optional `num`: `` `:num option` ``
- Number list type: `` `:num list` ``
- Bit-vector: `` `:8 word` `` (8-bit word), `` `:N word` ``

### Commands (which are OCaml functions)

- Define a function `f`: `` new_definition `(f:num->num) x = x + 1` `` ([doc](https://hol-light.github.io/references/HTML/new_definition.html))
- Define an inductive data type: `` define_type `new_typename = .. | .. | ..` `` ([doc](https://hol-light.github.io/references/HTML/define_type.html))


## 3. Interesting facts

- Proposition is simply bool.
    - Truth has a bool type (`` type_of `T` `` is bool)
    - `TAUT` allows excluded middle. Double negation elimination (`~~P -> P`) is allowed
- Then what is type `bool`?
    - It isn't an inductive data type having `` `T` `` (`` `true` `` in the modern syntax) and `` `F` `` (`` `false` `` in the modern syntax) as constructors.
    - It is just a primitive type that exists from the very foundation of HOL Light; it does not explicitly have its 'elements'.
    - It is (1) the definition of equality `` `(=):A->A->bool` `` and (2) axioms around `` `=` `` that eventually gives a meaning to type `bool`.
    - Truth `T` is defined as: `` `T = ((\p:bool. p) = (\p:bool. p))` `` (`T_DEF`)
    - Universal quantifier `` `!` `` is defined as: `` `\P:A->bool. P = \x. T` `` (`FORALL_DEF`)
    - False `F` is defined as: `` `!p:bool. p` `` (`F_DEF`)
    - It is interesting to see that `F` is defined upon `!` which is defined upon `T` :)
- Allows functional extensionality.
- Unbound variables are considered as universally quantified variables
    - ex) Goal `x + 0 = x` is valid, and it means `forall x. x + 0 = x` (or more briefly, `!x. x + 0 = x`)
- `!x. P x` (which is `forall x, P x` in Coq and verbosely `forall x. P x` in HOL Light as well) is
    equivalent to `(P = \x. true)`.
- Unlike Coq, you cannot define a type of an empty element (`False` in Coq)
    - See also: [new_type_definition](https://github.com/jrh13/hol-light/blob/master/Help/new_type_definition.hlp)
    - This allows you to prove `exists x y. x = y`!
- Uses a simply typed lambda calculus. (See [TYPE.md](TYPE.md))
- There is no definitional equality because definition is simply an equality. :) Every equality is born equal.
- `match` does not have to be a total function; conversion will fail if there is no matching pattern instead.
- Using `new_specification`, you can define a constant whose definition is not explicitly given but satisfies some constraint.
- Generalized abstraction is defined using Axiom of Choice (the `@` operator). See `GABS`.


## 4. Q&As

Q: What are the benefits of using HOL Light?
- Its underlying language, OCaml, is a well-known generic-purpose language.
  If you are already familiar with OCaml, you can quickly understand many parts of existing HOL Light proofs.
- Its small core provides a transparent view about how things are working in OCaml.
  This is especially important when you are dealing with large proofs and understanding why
  the proof checking is slow is necessary.
- For speed, you can use optimized OCaml library/compilers. Also, you can use the debugging facilities of OCaml.
- Writing a tactic is really writing a simple OCaml function. You can quickly learn how to write very
  advanced tactics.
- Has automated tactics that proves low-level theorems such as an equality between two bit-vector expressions.

Q: Can I prove a property of an OCaml function in HOL Light without embedding it in HOL Light?
- No.

Q: It is cool that we can do theorem proving in OCaml, but I am not convinced whether there
   can be a synergic effect between HOL Light and existing OCaml projects.
- There can be a few examples, such as:
- Using HOL Light to benefit OCaml projects: you can write a 'validator' in HOL Light
  checking whether your calculation in OCaml is indeed correct. For example, the output
  of a polynomial factorization function written in OCaml can be translated into
  HOL Light terms and checked whether the original and factorized equations are logically same.
  This is just a rough idea.
- Improving OCaml that will benefit HOL Light: Any improvement in OCaml toolchain - compiler,
  debugging tools, profiler, REPL updates, etc - will eventually improve HOL Light.

Q: How can I make loading `hol.sh` faster?
- To avoid repeating initialization, you can use a checkpointing program.
  I recommend DMTCP, but there are CRIU and selfie as well (the README of HOL Light has instructions).
