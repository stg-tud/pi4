#!/bin/bash
set -ex

# Initialize opam
opam init -a -y

# Install ocaml
opam switch create 4.11.1 -y
eval $(opam config env)
