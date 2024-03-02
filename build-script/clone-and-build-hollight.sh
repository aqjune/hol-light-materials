set -e

git clone https://github.com/jrh13/hol-light.git
cd hol-light
opam switch create `pwd` 4.14.0
eval $(opam env)

opam pin add -y camlp5 8.00.03
opam install -y num ledit

eval $(opam env)
make
ocamlmktop -o ocaml-full

cd hol-light
cp ../run-hol-light-template ./run-hol-light
sed -i "s|__DIR|$(pwd)|g" run-hol-light
sed -i "s|__OCAML|./ocaml-full|g" run-hol-light
chmod +x run-hol-light
