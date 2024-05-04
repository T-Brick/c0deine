# C0deine
C0deine is a reference compiler for c0. It is written in Lean 4, which allows us
to express the formal semantics in the same language as the compiler itself. You
can try it out in your browser at
[theabrick.com/c0](https://www.theabrick.com/c0/)!

Currently, we only support targeting WebAssembly. In the future, we hope to also
target C, x86-64 assembly, and potentially C0 bytecode. No phases of the
compiler are currently proven correct, but we are hoping to do so in the future.

Information about the source languages and standard libraries can be found in
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
via `lake run js <args>` or `node ./.lake/build/wasm/main.js <args>`. To compile
to WASM that can be used without node, run `lake exe wasm_builder web`.

## Usage

Run `bin/c0c -h` to verify everything compiled correct and to see the help
message. By default, C0deine targets the WebAssembly Text Format (WAT). It also
can target the WebAssembly Binary Format (WASM).

The file [example.js](testing/example.js) provides a small example how to
evaluate a program (it also compiles it using [compile.sh](testing/compile.sh)).
To run the example driver, `cd testing` and run `node example.js <test>`. To
compile, execute (if applicable), and verify the result
`./run.sh <test/test_dir>` can be used.

## Related Projects

The C0deine compiler depends on a number of other packages that are also being
maintained. Here is a list of them:

- [Numbers](https://github.com/T-Brick/Numbers) -- Arbitrary bit-length signed
  integers in Lean (following the WebAssembly specification).
- [Lean-Wasm](https://github.com/T-Brick/lean-wasm) -- Formalisation of the
  WebAssembly specification as well as other related utilities.
- [Control Flow](https://github.com/T-Brick/ControlFlow) -- Theorems about
  control flow graphs as well as implementations of various utilities.
- [Lean2Wasm](https://github.com/T-Brick/lean2wasm) -- A tool for compiling
  Lean source code into WebAssembly.
- [c0_web_driver](https://github.com/T-Brick/c0_web_driver) -- A web-based UI
  for both compiling c0 code and executing it in the browser.

## Contributions

Issues and PR are always welcome! This is a very large project and although
I've already done a lot, there's much more I'd love to do! Even if you don't
have much (if any) experience with writing Lean you can still help. If you are
interested or have any questions feel free to DM me (Thea Brick) on the
[Lean Community Zulip](https://leanprover.zulipchat.com).

Special thanks to @JamesGallicchio for their initial implementation of the
parser and other core utilities used by the compiler.

## The Name
"c0deine" is a reference to the major component of a street drug sometimes
called "lean" (see, e.g.,
[here](https://americanaddictioncenters.org/codeine-addiction/cough-syrup)). The
pun was hard to resist.

That said, opioid addiction is not a joke, and codeine is still one of the most
commonly abused opioids. please reach out if the name makes you uncomfortable
(we can change it).
