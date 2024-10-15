# How Tactic of HOL Light Works

In OCaml, a tactic (`tactic` type) is a function from `goal` to `goalstate`.
`goal` is a pair of named assumptions and conclusion term.
`goalstate` is a complex data structure that has a list of subgoals.


## 1. How does it eventually reconstruct a `thm` instance?

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


## 2. `e(tac)` modularly checks the validity of `tac`

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