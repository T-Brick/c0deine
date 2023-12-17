# C0deine
C0deine is a reference compiler for c0. It is written in Lean 4, which allows us
to express the formal semantics in the same language as the compiler itself.

Currently, we are working to target Web Assembly. We plan to also target C, and
x86-64 assembly. No phases of the compiler are currently proven correct, but we
are hoping to do so in the future.

Information about the source and target languages can be found in
[langs](langs.md).

## Install

This project requires [Lean4](https://lean-lang.org/lean4/doc/setup.html). The
example programs that evaluate the compiled code requires
[node](https://nodejs.org).

To compile C0deine run:
```sh
lake exe cache get
lake build
```

If you'd like to compile C0deine itself to WebAssembly this requires
[emscripten](https://emscripten.org/docs/getting_started/downloads.html). Once
installed run the following commands:

```sh
lake build wasm_builder
lake exe wasm_builder
```

This can take some time. Once finished, the compiler can then be invoked
via `lake run js <args>` or `node ./.lake/build/wasm/main.js <args>`.

## Usage

Run `bin/c0c -h` to verify everything compiled correct and to see the help
message. By default, C0deine targets the WebAssembly Text Format (WAT). It also
can target the WebAssembly Binary Format (WASM).

The file [example.js](testing/example.js) provides a small example how to
evaluate a program (it also compiles it using [compile.sh](testing/compile.sh)).
To run the example driver, `cd testing` and run `node example.js <test>`. To
compile, execute (if applicable), and verify the result
`./run.sh <test/test_dir>` can be used.

## The Name
"c0deine" is a reference to the major component of a street drug sometimes
called "lean" (see, e.g.,
[here](https://americanaddictioncenters.org/codeine-addiction/cough-syrup)). The
pun was hard to resist.

That said, opioid addiction is not a joke, and codeine is still one of the most
commonly abused opioids. please reach out if the name makes you uncomfortable
(we can change it).
