#!/bin/bash
TEST=$1
shift

../.lake/build/bin/c0deine -e wasm -o $TEST.wasm $TEST
# wat2wasm --output=$TEST.wasm $TEST.wat
