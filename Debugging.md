# Debugging a tactic in HOL Light

This document introduces methods to debug a tactic in HOL Light.

## Debugging tools of OCaml

In toplevel, you can use `Printexc.record_backtrace true;;` to print a call stack
when an exception happened.
Note note that the printed call stack may omit
some invocations due to the optimizations performed by OCaml.
Also, enabling this option will make the speed of tactic significantly slow.

`#trace <function name>;;` tells the values of arguments passed to the function
and its return values.
This may give some hints about how the tactic works.
You can disable the trace using `#untrace <function name>;;`
[This document](https://ocaml.org/docs/debugging#tracing-functions-calls-in-the-toplevel)
has more details.

OCaml also has a C-style printer function `Printf.printf "..(format).." ..(args)..`
([API](https://ocaml.org/manual/5.2/api/Printf.html)), which will be familiar if
C was one of your languages.
Sometimes `Printf.printf` may not immediately print the string, and this can be
resolved by adding `%!` to the format string
([example](https://discuss.ocaml.org/t/when-does-printf-printf-flush/12057)).

<b>Timing of printing.</b>
Let's assume that you want to use `Printf.printf` to figure out which tactic is failing.
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

In this case, `Printf.printf` must be wrapped inside a function which will run when `prove`
is eventually started.
Or, `... ORELSE FAIL_TAC "message"` can be used instead.
This will be explained in the later section of this document.


## Printing terms, types and theorems.

There are `string_of_*` functions that convert a HOL Light object into OCaml string:
`string_of_term`, `string_of_type` and `string_of_thm`.
You can use `Printf.printf "..(format).." ..(args)..` to print them.
There are also shorter versions `print_term`, `print_type` and `print_thm`.

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

## Printing the goal state.

There is `PRINT_GOAL_TAC` ([doc](https://hol-light.github.io/references/HTML/PRINT_GOAL_TAC.html))
which is a tactic that simply prints the goal state.
You can combine this with `ORELSE` so that the goal state is printed and a failure is returned
if the tactic fails:

```
(... (a tactic that can fail) ...) ORELSE (PRINT_GOAL_TAC THEN FAIL_TAC "my message")
```

If you want to print more messages, you can write your own tactic that looks like this:

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

If you are editing your proof using `g()` and `e()` (the subgoal package),
other than using `e(PRINT_GOAL_TAC)` you can also use:
```
# print_goal (top_realgoal());;
```

## Asserting that the current goal state is in a good shape.

You can use `term_match` ([doc](https://hol-light.github.io/references/HTML/term_match.html)) to
assert that the conclusion is in a good shape.

```ocaml
let MY_CHECKER_TAC:tactic =
  fun (asl,g) ->
    (* Let's assert that the conclusion has the form 'x = y'. *)
    let _ = term_match [] `x = y` g in
    ALL_TAC (asl,g);;
```

```
# g `1 < 2`;;
val it : goalstack = 1 subgoal (1 total)

`1 < 2`

# e(MY_CHECKER_TAC);; (* This should fail *)
Warning: inventing type variables
Exception: Failure "term_pmatch".
```

<b>Checking the number of subgoals.</b>
To check that there only is one subgoal,
`tactic THENL [ ALL_TAC ] THEN next_tactic` can be used.
To check that there exactly are `n` subgoals,
`tactic THENL (map (fun _ -> ALL_TAC) (1--10)) THEN next_tactic`
will work.

## Other useful tricks

### Tips for understanding a complex tactic.
Understanding how a complex tactic works is a hard thing.
If a tactic typically starts with `fun (asl,g) -> ...`,
one easy start is to initiate `asl` and `g` using the following command:
```ocaml
let asl,g = top_realgoal();;
```
and follow the statements step by step.

If it contains a complicated expression, a subexpression can be explored
by typing it at toplevel and using the returned `it` variable to explore
an expression that subsumes it.

### Flags for immediately stopping at failures or warnings.

<b>Nested file load failure.</b>
HOL Light does not stop by default when a failure happend during loading nested files.
To control this behavior, setting `use_file_raise_failure := true;;` will work
([doc](https://hol-light.github.io/references/HTML/use_file_raise_failure.html)).

<b>Avoiding invented types.</b>
Invented types can be problematic in some tactics like `SUBGOAL_THEN` which will
a bogus, unprovable goal.
To immediately stop when types are invented, `type_invention_error := true;;`
will work ([doc](https://hol-light.github.io/references/HTML/type_invention_error.html))