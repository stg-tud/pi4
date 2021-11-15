#!/bin/bash
set -ex

wget https://github.com/cornell-netlab/p4pp/archive/refs/tags/v0.1.6.tar.gz
tar -xzf v0.1.6.tar.gz
mv ./p4pp-0.1.6/ ./p4pp
cd ./p4pp
opam pin add p4pp . --working-dir -y
cd ..
