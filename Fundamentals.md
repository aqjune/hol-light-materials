# Fundamentals of HOL Light

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

```ocaml
(* Location: equal.ml *)
(* conv (conversion) is simply an inference rule of type term -> thm that when given
   a term t, always returns (assuming it doesn’t fail) an equational theorem of the form
   `t = t′, that is, it proves that the term it was given is equal to some other term,
   possibly the same as the original. *)
type conv = term->thm;;
```

```ocaml
(* Location: tactics.ml *)
(* goal consists of named hypotheses ((string * thm) list) and yet unproven conclusion *)
type goal = (string * thm) list * term;;

(* a tactic for writing a backward proof. The definition of goalstate is kind of complicated. *)
type tactic = goal -> goalstate;;

type thm_tactic = thm -> tactic;;
```

- Proposition is simply bool.
    - Truth has a bool type (`` type_of `T` `` is bool)
    - `TAUT` allows excluded middle. Double negation elimination (`~~P -> P`) is allowed
- Allows functional extensionality
- Unbound variables are considered as universally quantified variables
    - ex) Goal `x + 0 = x` is valid, and it means `!x. x + 0 = x`
- `!P` (which is `forall x, P x` in Coq) is equivalent to `(P = \x. true)`.
    - Therefore, `!` is `\P. (P = \x. true)`.
- Unlike Coq, you cannot define a type of an empty element (`False` in Coq)
    - See also: [new_type_definition](https://github.com/jrh13/hol-light/blob/master/Help/new_type_definition.hlp)
    - This allows you to prove `?x y. x = y`! (`?x` is exists x.)
- Uses a simply typed lambda calculus. (See [TYPE.md](TYPE.md))
