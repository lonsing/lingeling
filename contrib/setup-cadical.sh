#!/bin/bash

# Version from 18 June 2020
CADICALVERSION=c622a490ec3d9a1a1e998b08120c9b8d0b67a123

cd ..
mkdir ./deps
cd ./deps

git clone https://github.com/arminbiere/cadical.git
cd cadical
git checkout ${CADICALVERSION}
./configure
make
