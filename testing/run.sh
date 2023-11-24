#!/bin/bash
NODE=${NODE:=$(which node)}

../build/bin/c0deine $1 > $1.wat
wat2wasm --output=$1.wasm $1.wat
exec $NODE run.js "$1.wasm"
