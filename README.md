# hol-light-materials
Online materials for HOL Light:
- [Tutorial](https://www.cl.cam.ac.uk/~jrh13/hol-light/tutorial.pdf)
- Reference Manual ([pdf](https://www.cl.cam.ac.uk/~jrh13/hol-light/reference.pdf), [html](https://www.cl.cam.ac.uk/~jrh13/hol-light/reference.html))
- Very Quick Reference ([pdf](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.pdf), [txt](https://www.cl.cam.ac.uk/~jrh13/hol-light/holchart.txt))

## Building & Running HOL Light

```
cd build-script
./clone-and-build-hollight.sh
cd hol-light
eval $(opam env)
./hol.sh
```

The OCaml REPL does not accept arrow keys by default. To resolve this. you can use ledit (https://opam.ocaml.org/packages/ledit/) and use ledit ocaml instead. ledit can be installed using either apt install ledit or opam install ledit, then do `export LINE_EDITOR=ledit` before calling `hol.sh`.

## Editors

- VSCode: [vscode-hol-light](https://github.com/monadius/vscode-hol-light) is available at VSCode Marketplace.
- Emacs: [hol-light-emacs](https://github.com/gilith/hol-light-emacs)

## How-to

- [Use or update assumptions in HOL Light](PlayingWithAssumptions.md).
- [Use rewrite tactics well](RewriteTac.md)
- [Prove 'trivial' goals](ProvingTrivialGoals.md)

## [HOL Light vs. Coq](HOLLightvsCoq.md)

## Fundamentals and Internal Representation of Terms

- [Fundamentals](Fundamentals.md)
- [AST](AST.md).

## Examples and Exercises

- [exercises](exercises): exercises for HOL Light
- [s2n-bignum-examples](s2n-bignum-examples): examples for proving assembly programs in s2n-bignum


## [Misc](Misc.md)
