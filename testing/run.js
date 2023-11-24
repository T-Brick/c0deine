const fs = require("fs");

var args = process.argv.slice(3);
const filename = process.argv[2];
const bytes = fs.readFileSync(filename);
const wasm = new WebAssembly.Module(bytes);

const imports = {console: {
    log: v => process.stdout.write("" + (v | 0) + "\n"),
}};

const instance = new WebAssembly.Instance(wasm, imports);
