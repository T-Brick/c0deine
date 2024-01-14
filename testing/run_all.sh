#!/bin/bash
sh ./clean.sh
sh ./run.sh tests/l4/
sh ./run.sh tests/c0/
sh ./run.sh tests/bugs/
# sh ./run.sh tests/stdlib/conio
sh ./run.sh tests/stdlib/parse
sh ./run.sh tests/stdlib/string
sh ./run.sh tests/infloop
