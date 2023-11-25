const fs = require("fs");

var args = process.argv.slice(2);
const filename = process.argv[2];
const bytes = fs.readFileSync(filename);
const wasm = new WebAssembly.Module(bytes);

const imports = {c0deine: {
    result: v => process.stdout.write("" + (v | 0) + "\n"),
}};

const instance = new WebAssembly.Instance(wasm, imports);
