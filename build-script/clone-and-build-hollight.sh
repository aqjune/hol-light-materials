set -e

git clone https://github.com/jrh13/hol-light.git
cd hol-light
opam switch create `pwd` 4.14.0
eval $(opam env)

opam pin add -y camlp5 8.00.03
opam install -y zarith ledit # If installing zarith fails, please install its dependency gmp using e.g., apt-get install -y libgmp-dev .

eval $(opam env)
make

# Now you can use `hol.sh`.
# When you are invoking `hol.sh` from a directory other than hol-light,
# Please run `eval $(opam env --switch (the hol-light directory path) --set-switch)` first.
# If you want to use ledit, please do `export LINE_EDITOR=ledit` before calling `hol.sh`.
