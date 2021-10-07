#!/bin/sh
set -ex

# Install petr4
if [ ! -d "petr4" ]; then
  git clone --branch 0.1.2 https://github.com/verified-network-toolchain/petr4.git
  cd petr4
else
  cd petr4
  git fetch --all
  git checkout 0.1.2
  git reset --hard 0.1.2
fi
opam pin add petr4 . --working-dir -y
