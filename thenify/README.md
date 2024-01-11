### Thenify

[thenify/thenify.py](thenify) converts a properly formatted sequence of `e(..);;` commands into the `.. THEN ..` format.
If some tactic produces multiple subgoals, each subgoal must have extra indentation
of two spaces and start with `(** SUBGOAL(..your description..) **)`.
`tests/` has its inputs and `thenify.py <input.txt>` shows the then-ified output.

This tool provides a subset of features of Tactician (http://www.proof-technologies.com/tactician/).
The tool supports only up to OCaml 4.01 however.


