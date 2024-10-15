# hol-light-materials

## Building & Running HOL Light

Assuming that [OPAM](https://opam.ocaml.org/doc/Install.html) is installed in your machine,
you can easily build HOL Light using the following instructions which are also described in [README](https://github.com/jrh13/hol-light/blob/master/README):

```
make switch # use 'make switch-5' if you want to use OCaml 5
eval $(opam env)
make
# Now you have 'hol.sh' .
```

### 1. Checkpointing

DMTCP is recommended (README of HOL Light has more instructions).
Once `dmtcp_restart_script.sh` is created, you can create multiple instances of HOL Light by
starting the script with distinct ports `-p <port number>`.

### 2. Compiling HOL Light

Set the `HOLLIGHT_USE_MODULE` environment variable to 1 and recompile HOL Light using `make`.
This will create `hol_lib.cmo`.
Please refer to the 'COMPILING HOL LIGHT' section of [README](https://github.com/jrh13/hol-light/blob/master/README).

### 3. Editors

- VSCode: [vscode-hol-light](https://github.com/monadius/vscode-hol-light) is available at VSCode Marketplace.
- Emacs: [hol-light-emacs](https://github.com/gilith/hol-light-emacs)

## Contents

- [An overview of HOL Light](Overview.md)

### 1. How-to

- [Use or update assumptions in HOL Light](PlayingWithAssumptions.md)
- [Use rewrite tactics well](RewriteTac.md)
- [Write your own tactic](WriteYourTac.md)
- [Debug a proof and tactic](Debugging.md)
- [Prove 'trivial' goals](ProvingTrivialGoals.md)

### 2. More Details

- [OCaml data structure of HOL Light](OCamlDataStructure.md)
- [How does tactic work?](TacticDetails.md)
- [HOL Light vs. Coq comparison](HOLLightvsCoq.md)

### 3. Examples and Exercises

- [exercises](exercises): exercises for HOL Light
- [s2n-bignum-examples](s2n-bignum-examples): examples for proving assembly programs in s2n-bignum

### 4. Other Online Materials

- [Tutorial](https://hol-light.github.io/tutorial.pdf)
- [HOL Light: an overview](https://www.cl.cam.ac.uk/~jrh13/papers/hollight.pdf)
- Reference Manual ([pdf](https://hol-light.github.io/references/reference.pdf), [html](https://hol-light.github.io/references/HTML/reference.html))
- Very Quick Reference ([pdf](https://hol-light.github.io/holchart/holchart.pdf), [txt](https://hol-light.github.io/holchart/holchart.txt))


## [Misc](Misc.md)
