set -e
git clone https://github.com/jrh13/hol-light.git
cd hol-light
opam switch create `pwd` 4.05.0
eval $(opam env)

opam pin add -y camlp5 7.10
opam install -y num

eval $(opam env)
make
cp ../run-hol-light-template ./run-hol-light
sed -i "s|__DIR|$(pwd)|g" run-hol-light
sed -i "s|__OCAML|ocaml|g" run-hol-light
chmod +x run-hol-light
