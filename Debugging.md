# Debugging a tactic and proof in HOL Light

This document introduces methods to debug a tactic and proof in HOL Light.

## 1. Useful debugging tools of OCaml

In toplevel, you can use `Printexc.record_backtrace true;;` to print a call stack
when an exception happened.
Note note that the printed call stack may omit
some invocations due to the optimizations performed by OCaml.
Also, enabling this option will make the speed of tactic significantly slow.

`#trace <function name>;;` tells the values of arguments passed to the function
and its return values.
This may give some hints about how the tactic works.
You can disable the trace using `#untrace <function name>;;` or simply `#untrace_all`.
[This document](https://ocaml.org/docs/debugging#tracing-functions-calls-in-the-toplevel)
has more details.

OCaml also has a C-style printer function `Printf.printf "..(format).." ..(args)..`
([API](https://ocaml.org/manual/5.2/api/Printf.html)), which will be familiar if
C was one of your languages.
Sometimes `Printf.printf` may not immediately print the string, and this can be
resolved by adding `%!` to the format string
([example](https://discuss.ocaml.org/t/when-does-printf-printf-flush/12057)).
This document also describes how to print terms, types and theorems.


## 2. Debugging a proof

After Q.E.D, a proof is typically rewritten to the `prove(the_goal, ... (tactics) ...)`
form because it is much more compact than the `g`-`e` form.
However, debugging a failing proof in `prove` is not easy because it is not interactive.
This section describes a few tips to do this.


### Converting a proof into the `g`-`e` form

As the first step, you can convert the proof into `g`-`e` form.
This will implicitly happen even if you are using the VSCode HOL Light plugin
to go through each tactic step by step because it will wrap it with `e(..)` on REPL.
Therefore, the proof does not have to be manually converted if the VSCode plugin is used.

However, `t1 THEN t2` is not equivalent to `e(t1);; e(t2);;` and this may make a supposed-to-be-correct
proof going wrong.
There are two reasons why they are not equivalent.

1. If `t1` generates multiple subgoals, `t2` is applied to every subgoal whereas `e(t2);;`
   will only be applied to the first subgoal.
2. `e(..)` does validity check of the tactic which can fail (this case is rare).

To check that a proof in `prove(..)` does not have the first issue,
run `unset_then_multiple_subgoals;;` first and rerun the `prove(..)` again.
If it passes, translating the proof into `g`-`e` form will not suffer from the first problem.

Personally, I recommend turning on `unset_then_multiple_subgoals` and writing your proof
from the beginning because this will reduce the burden of later maintenance.
For any tactic that can generate multiple subgoals, one can use `.. THENL (replicate t2 n)` where
`n` is the number of subgoals.

### Printing the intermediate goal states

There is `PRINT_GOAL_TAC` ([doc](https://hol-light.github.io/references/HTML/PRINT_GOAL_TAC.html))
which is a tactic that simply prints the goal state.
You can combine this with `ORELSE` so that the goal state is printed and a failure is returned
if the tactic fails:

```
(... (a tactic that can fail) ...) ORELSE (PRINT_GOAL_TAC THEN FAIL_TAC "my message")
```

If you want to print more or less information, you can write your own tactic that looks like this:

```ocaml
let MY_PRINT_CONCLUSION_TAC:tactic =
  fun (asl,g) ->
    let _ = Printf.printf "The conclusion was: `%s`\n" (string_of_term g) in
    ALL_TAC (asl,g);;
```

If the goal is too large to print in a reasonable terminal buffer size,
you can set `print_goal_hyp_max_boxes := Some <small number>;;`
([doc](https://hol-light.github.io/references/HTML/print_goal_hyp_max_boxes.html)).
This will make the goal printer omit subexpressions with dots if they use more
'boxes' than the parameter.

If you already converted the proof to `g()` and `e()` and are deubgigng it,
other than using `e(PRINT_GOAL_TAC)` you can also use:
```
# print_goal (top_realgoal());;
```

<b>Timing of printing.</b> Let's assume that you want to use `Printf.printf` to figure out which tactic is failing.
It will be tempting to write
```ocaml
let my_proof = prove(`...`,
	SOME_TACTIC1 THEN
	let _ = Printf.printf "SOME_TACTIC1 was fine\n" in
	SOME_TACTIC2 THEN
	let _ = Printf.printf "SOME_TACTIC2 was fine\n" in
	...);;
```
but this won't work because it will always print the whole messages successfully.
This is because function arguments are always eagerly evaluated in OCaml.
So, messages will have been already printed before the `prove` function is invoked.


## 3. Printing terms, types and theorems

There are `string_of_*` functions that convert a HOL Light object into OCaml string:
`string_of_term`, `string_of_type` and `string_of_thm`.
You can use `Printf.printf "..(format).." ..(args)..` to print them.
There are also shorter versions `print_term`, `print_type` and `print_thm`.
You can also use `pp_print_*` and `Format.asprintf`:

```ocaml
Format.asprintf "test: %a %a" pp_print_qterm `1` pp_print_qterm `1+2`;;
```

<b>Printing types of subterms.</b>
By default, HOL Light will not print the types of subterms unless they are invented type
variables like `:?123`.
To force HOL Light to print every subtype, set `print_types_of_subterms := 2;;`.
Its help [doc](https://hol-light.github.io/references/HTML/print_types_of_subterms.html) has nice examples
about this.

<b>Printing the actual OCaml data structure.</b>
Sometimes it is necessary to understand the actual OCaml data structure that represents
a term when e.g., writing a function matching a term.
In this case, removing the printer will give the information.
```
#remove_printer pp_print_qterm;;
# `1 + x`;;
val it : term =
  Comb
   (Comb (Const ("+", `:num->num->num`),
     Comb (Const ("NUMERAL", `:num->num`),
      Comb (Const ("BIT1", `:num->num`), Const ("_0", `:num`)))),
   Var ("x", `:num`))
# #install_printer pp_print_qterm;;
# `1 + x`;;
val it : term = `1 + x`
```

## 4. Exceptions in HOL Light

The `Failure` exception type is commonly used in HOL Light to stop execution if
an unexpected situation happened.
This can be conveniently raised using the `failwith "msg"` function of OCaml, which is
equivalent to `raise (Failure "msg")`.
However, there are several predefined types of exceptions in OCaml, and
`Failure` is only one of them.
For example, `assert` will raise `Assert_failure` which is slightly different from
`Failure`.
My suggestion is to stick to `Failure` in HOL Light unless it is very necessary to
use the other types.
For example, `t1 ORELSE t2` will execute `t2` if `t1` raised Failure, or immediately
stop otherwise.
[This link](https://ocaml.org/docs/error-handling) has more info for generic
situations.

## 5. Other useful tricks

### Tips for understanding a complex tactic.

If a tactic starts with `fun (asl,g) -> ...`,
one easy start is to initiate `asl` and `g` using the following command:
```ocaml
let asl,g = top_realgoal();;
```
and follow the statements step by step.
Note that this overwrites the global definition of `g` which is used to
set the goal (e.g., ``"g `1 + 1 = 2`;;"``). The original definition can be recovered by
```ocaml
let g t = set_goal([],t);;
```

If it contains a complicated expression, a subexpression can be explored
by typing it at toplevel and using the returned `it` variable to explore
an expression that subsumes it.


### Flags for immediately stopping at failures or warnings.

<b>Nested file load failure.</b>
HOL Light does not stop by default when a failure happend during loading nested files.
To control this behavior, setting `use_file_raise_failure := true;;` will work
([doc](https://hol-light.github.io/references/HTML/use_file_raise_failure.html)).
With this flag on, loading a file will immediately stop whenever there is a failure
even in its nested load.

<b>Avoiding invented types.</b>
Invented types can be problematic in some tactics like `SUBGOAL_THEN` which will
a bogus, unprovable goal.
To immediately stop when types are invented, `type_invention_error := true;;`
will work ([doc](https://hol-light.github.io/references/HTML/type_invention_error.html))


### Understanding why a tactic is slow.

In general, a tactic can be slow for various reasons.

- Nested `DEPTH_CONV` and `REWRITE_CONV`: `REWRITE_CONV` recursively visits the subterms.
If it is used inside `DEPTH_CONV`, this can cause a significant slowdown because the
subterms are recursively visited twice.

- Use of `prove()`: If the tactic proves a custom lemma using `prove()` on the fly, the `prove()`
invocation can be a bottleneck because it is slow. One possible solution is to cache
the lemmas that are proven by `prove()` and reuse it.

- Validity check of `e()`: Sometimes the speed of `e()` can significantly slow down
due to its validity check. This can be temporarily avoided by redefining `e` as:

```ocaml
(*let e tac = refine(by(VALID tac));;*)
let e tac = refine(by(tac));;
```

TODO: use of `CLARIFY_TAC` in s2n-bignum


### Omitting proof checks of needed `.ml` files for speed

It is often not necessary to check the proofs of the proof files that is being loaded.
[needs_skip_proofs](needs_skip_proofs.ml) is a tactic that can replace `needs` to omit the
`prove()` calls inside the file.