/* Functional-Programming-pilled woman tries to write javascript
    Viewer discretion is advised xd :')
 */
const fs = require("fs");
const util = require("util");
const exec = util.promisify(require("child_process").exec);
const path = require("path");

let args = process.argv.slice(2);

const quiet = 0;
const freshMemory = false;
const checkTimeouts = true;
const maxEnterLabel = 100000000; // maximum number of times a label is entered

let failed = 0;
let success = 0;

const c0_parse_str = (memory) => async (address) => {
  const bytes = new Uint8Array(memory.buffer.slice(address | 0));
  let i = 0;
  let msg = "";
  while (i < bytes.length && bytes[i] !== undefined && bytes[i] !== 0) {
    msg += String.fromCharCode(bytes[i]);
    i += 1;
  }
  return msg;
};

const log_c0_error = (memory) => async (str) => {
  let msg = await c0_parse_str(memory)(str);
  msg = "error:  " + msg;
  console.log(msg);
};

const c0_debug = (labelMap) => (lbl) => {
  if (checkTimeouts) {
    if (labelMap[lbl + ""] === undefined) {
      labelMap[lbl + ""] = 1;
    } else {
      labelMap[lbl + ""] = labelMap[lbl + ""] + 1;
    }
    if (labelMap[lbl + ""] > maxEnterLabel) {
      console.log("Exceeded maximum label entry on " + lbl);
      return 1;
    }
  }
  return 0;
};

const passTest = async (filename) => {
  success++;
  if (quiet <= 0) {
    console.log("\x1b[32m%s\x1b[0m", "Test '" + filename + "' Passed!");
  }
  return true;
};

const failTest = async (filename, expect, got) => {
  failed++;
  if (quiet <= 2) {
    console.log("\x1b[31m%s\x1b[0m", "Test '" + filename + "' Failed :(");
    if (quiet <= 1) {
      console.log("\x1b[31m%s\x1b[0m", "  Expected: " + expect);
      console.log("\x1b[31m%s\x1b[0m", "  Received: " + got);
    }
  }
  return false;
};

const resultToString = (result) => {
  if (result["return"] !== undefined) {
    return result["return"] | 0;
  } else if (result["div-by-zero"] !== undefined) {
    return "div-by-zero";
  } else if (result["abort"] !== undefined) {
    return "abort";
  } else if (result["memerror"] !== undefined) {
    return "memerror";
  } else if (result["error"] !== undefined) {
    return "error";
  } else if (result["typecheck"] !== undefined) {
    return "typecheck";
  } else if (result["compile"] !== undefined) {
    return "compile";
  }
  return "unknown test result";
};

const result = (filename, expect) => {
  return async (got) => {
    if (expect["return"] === undefined) {
      return failTest(filename, resultToString(expect), got);
    } else {
      if (expect["return"] === (got | 0)) {
        return passTest(filename, resultToString(expect), got | 0);
      } else {
        return failTest(filename, resultToString(expect), got | 0);
      }
    }
  };
};

const abort = (filename, expect) => {
  return async (got) => {
    if (expect["abort"] !== undefined && (got | 0) === 6) {
      return passTest(filename, "abort", got | 0);
    } else if (expect["memerror"] !== undefined && (got | 0) === 12) {
      return passTest(filename, "memerror", got | 0);
    } else if (expect["div-by-zero"] !== undefined && (got | 0) === 8) {
      return true;
    }
    return failTest(filename, resultToString(expect), "abort" + (got | 0));
  };
};

const error = (memory) => (filename, expect) => {
  return async (got) => {
    const str = await c0_parse_str(memory)(got);
    if (expect["abort"] !== undefined) {
      return passTest(filename, "abort", str);
    }
    return failTest(filename, resultToString(expect), "error:  " + str);
  };
};

async function parseExpectedResult(filename) {
  const data = await fs.promises.readFile(filename);
  let str = (data + "").split("\n", 2)[0].trim();
  if (str.startsWith("//test")) {
    str = str.substring(7);

    if (str.startsWith("return")) {
      return {
        return: str.substring(7).trim().replace("~", "-").replace(";", "") | 0,
      };
    } else if (str.startsWith("div-by-zero")) {
      return { "div-by-zero": true };
    } else if (str.startsWith("abort")) {
      return { abort: true };
    } else if (str.startsWith("memerror")) {
      return { memerror: true };
    } else if (str.startsWith("error")) {
      return { error: true };
    } else if (str.startsWith("typecheck")) {
      return { typecheck: true };
    } else if (str.startsWith("compile")) {
      return { compile: true };
    }
  }

  console.log("Couldn't parse testcase result for '" + filename + "' :(");
  return undefined;
}

/**
 * @returns a boolean indicating whether to execute the compiled output.
 */
async function compile(filename, header, result) {
  let cmd = `sh compile.sh "${filename}"`;
  if (result["typecheck"] || result["compile"]) {
    cmd = cmd + " -t";
  }
  if (header !== undefined) {
    cmd = cmd + ' -l"' + header + '"';
  }
  if (checkTimeouts) {
    cmd = cmd + " --wasm-debugger";
  }

  try {
    const { stdout, stderr } = await exec(cmd);
  } catch (error) {
    if (result === undefined) {
      console.log(stdout);
      console.log(stderr);
      return false;
    }

    if (result["error"] !== undefined) {
      await passTest(filename, "Compile error", "Compile error");
      return false;
    }
    await failTest(
      filename,
      resultToString(result),
      "\n" + stdout + "\n" + stderr
    );
    return false;
  }
  return true;
}

async function run(filename, imports, expect) {
  const bytes = await fs.promises.readFile(filename + ".wasm");
  const wasm = new WebAssembly.Module(bytes);

  if (expect !== undefined && expect["compile"]) {
    return passTest(filename, "Compile and link", "Compile and link");
  }

  try {
    const instance = new WebAssembly.Instance(wasm, imports);
  } catch (e) {
    if (expect === undefined) {
      console.log(e + "");
      return false;
    }

    if (e instanceof WebAssembly.RuntimeError && expect["div-by-zero"]) {
      return passTest(filename, "div-by-zero", "div-by-zero");
    } else if (
      e instanceof WebAssembly.RuntimeError &&
      (expect["memerror"] || expect["abort"])
    ) {
    } else {
      throw e;
      // return failTest(filename, resultToString(expect), "\n" + e + "\n")
    }
  }
}

async function evalTest(filename, header) {
  const expectRes = await parseExpectedResult(filename);
  const shldExe = await compile(filename, header, expectRes);

  if (!shldExe) return;

  if (expectRes["typecheck"]) {
    await passTest(filename, "Typechecked", "Typechecked");
    return;
  }

  const memory = new WebAssembly.Memory({ initial: 1 });
  if (!freshMemory) {
    // todo dirty the memory
  }
  let labelMap = {};

  const check_imports = {
    c0deine: {
      memory: memory,
      result: result(filename, expectRes),
      abort: abort(filename, expectRes),
      error: async (got) => await error(memory)(filename, expectRes)(got),
      debug: c0_debug(labelMap),
    },
    conio: {
      print: async (str) => {
        process.stdout.write(await c0_parse_str(memory)(str));
      },
      println: async (str) => {
        process.stdout.write((await c0_parse_str(memory)(str)) + "\n");
      },
      flush: () => {
        process.stdout.flush();
      },
      eof: () => {
        console.log("TODO: eof unimplemented!");
      },
      readline: () => {
        console.log("TODO: readline unimplemented!");
      },
    },
  };
  return run(filename, check_imports, expectRes);
}

async function main() {
  if (!fs.existsSync(args[0])) {
    process.stdout.write("Couldn't find file/directory: " + args[0] + "\n");
    console.log(args);
    return;
  }

  if (fs.lstatSync(args[0]).isFile()) {
    const filename = args[0];
    let header = filename.slice(0, -2) + "h0";
    if (!fs.existsSync(header) || !fs.lstatSync(header).isFile()) {
      header = undefined;
    }
    await evalTest(filename, header);
    return;
  }

  if (fs.lstatSync(args[0]).isDirectory()) {
    const dir = args[0];
    const files = await fs.promises.readdir(dir);

    const evalFile = async (file) => {
      if (
        file.endsWith(".l4") ||
        file.endsWith(".l3") ||
        file.endsWith(".l2") ||
        file.endsWith(".l1") ||
        file.endsWith(".c0")
      ) {
        let header = file.slice(0, -2) + "h0";
        header = path.join(dir, header);

        if (!fs.existsSync(header) || !fs.lstatSync(header).isFile()) {
          header = undefined;
        }

        await evalTest(path.join(dir, file), header);
      }
    };

    await Promise.allSettled(files.map((file, _i, _a) => evalFile(file)));
    console.log(`Passed ${success}  Failed ${failed}`);

    return;
  }
}

main();

let labelMap = {}; // tracking number of times we've reached a label
let memory = new WebAssembly.Memory({ initial: 1 });

const conio = {
  print: async (str) => {
    process.stdout.write(await c0_parse_str(memory)(str));
  },
  println: async (str) => {
    process.stdout.write((await c0_parse_str(memory)(str)) + "\n");
  },
  flush: () => {
    process.stdout.flush();
    setTimeout(() => {}, 0);
  },
  eof: () => {
    console.log("TODO: eof unimplemented!");
  },
  readline: () => {
    console.log("TODO: readline unimplemented!");
  },
};

const print_imports = {
  c0deine: {
    memory: memory,
    result: (res) => {
      console.log(res | 0);
    },
    abort: (sig) => {
      console.log("abort: " + (sig | 0));
    },
    error: log_c0_error,
    debug: (lbl) => {
      console.log("debug:  entered label " + lbl);
      setTimeout(() => {
        return 0;
      }, 0);
    },
  },
  conio: conio,
};

/* Uncomment if you'd rather run one specific test without passing through
    the testing framework. Useful for debugging specific WAT files that you
    can manually modify.
*/
// run("tests/c0/reference", print_imports, undefined, () => {});
