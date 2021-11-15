#!/bin/bash
set -ex

# Initialize opam
opam init -a -y

# Install ocaml
opam switch create ocaml-base-compiler.4.11.1 -y
eval $(opam config env)

opam update
