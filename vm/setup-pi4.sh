#!/bin/bash
set -ex

# TODO: Clone git repository

cd pi4/
# Install dependencies
opam install . --deps-only -y
