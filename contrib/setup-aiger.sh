#!/bin/bash

./setup-picosat.sh

cd ..
mkdir ./deps
cd ./deps

wget http://fmv.jku.at/aiger/aiger-1.9.4.tar.gz
tar -xvzf aiger-1.9.4.tar.gz
mv aiger-1.9.4 aiger
cd aiger
./configure
make
rm aiger-1.9.4.tar.gz
