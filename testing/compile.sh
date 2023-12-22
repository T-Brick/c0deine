#!/bin/bash
TEST=$1
MODE="wasm"
shift

../.lake/build/bin/c0deine -e $MODE -o $TEST.$MODE $@ $TEST && (
  if test "$MODE" = "wat"
  then
    wat2wasm --output=$TEST.wasm $TEST.wat
  fi
)
