#!/bin/bash

./setup-aiger.sh
./setup-cadical.sh

echo "Compiling Lingeling"
cd ..
./configure.sh
make
