#!/bin/bash

./setup-aiger.sh
./setup-cadical.sh

echo "Compiling Lingeling with AIGER support"
cd ..
./configure.sh --aiger=./deps/aiger/
make
