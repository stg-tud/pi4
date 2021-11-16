#!/bin/bash
set -ex

# Clone git repository
git clone --branch popl-22 https://github.com/stg-tud/pi4

cd pi4/
# Install dependencies
opam install . --deps-only -y
