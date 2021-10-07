#!/bin/bash
set -ex

# Install ocaml-z3
if [ ! -d "ocaml-z3" ]; then
  git clone --branch use-successes https://github.com/eichholz/ocaml-z3.git
  cd ocaml-z3
else 
  cd ocaml-z3
  git fetch --all
  git checkout use-successes
  git reset --hard use-successes
fi
opam pin add z3 . --working-dir -y
