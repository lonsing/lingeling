#!/bin/bash

# Must use old version 951 (not latest 965) of picosat because later
# versions come with different API, which is incompatible with version
# of AIGER.
# NOTE: picosat is only required to build model checker 'aigbmc'. We
# build it for reference.
PICOSATVERSION="951"

cd ..
mkdir ./deps
cd ./deps

wget http://fmv.jku.at/picosat/picosat-${PICOSATVERSION}.tar.gz
tar -xvzf picosat-${PICOSATVERSION}.tar.gz
mv picosat-${PICOSATVERSION} picosat
cd picosat
./configure
make
rm picosat-${PICOSATVERSION}.tar.gz
