const fs = require("fs");
const { exec } = require('child_process');
const path = require('path');

var args = process.argv.slice(2);

var quiet = 0;

var failed = 0;
var success = 0;

const print_imports = {c0deine: {
  result: res => { console.log((res | 0))},
  abort: sig => { console.log("abort: " + (sig | 0))},
}};

const buildLazyList = function(list) {
  if(list === undefined || list === null || list.length === 0) {
    return {nil: true}
  }
  return {hd: list[0], tl: () => {
    return buildLazyList(list.slice(1));
  }};
}

const passTest = function(filename) {
  success++;
  if(quiet <= 0) {
    console.log("\x1b[32m%s\x1b[0m", "Test '" + filename + "' Passed!");
  }
}

const failTest = function(filename, expect, got) {
  failed++;
  if(quiet <= 2) {
    console.log("\x1b[31m%s\x1b[0m", "Test '" + filename + "' Failed :(");
    if(quiet <= 1) {
      console.log("\x1b[31m%s\x1b[0m", "  Expected: " + expect);
      console.log("\x1b[31m%s\x1b[0m", "  Received: " + got);
    }
  }
}

const resultToString = function(result) {
  if(result["return"] !== undefined) {
    return "return " + (result["return"] | 0);
  } else if(result["div-by-zero"] !== undefined) {
    return "div-by-zero"
  } else if(result["abort"] !== undefined) {
    return "abort"
  } else if(result["memerror"] !== undefined) {
    return "memerror"
  } else if(result["error"] !== undefined) {
    return "error"
  } else if(result["typecheck"] !== undefined) {
    return "typecheck"
  } else if(result["compile"] !== undefined) {
    return "compile"
  }
  return "unknown test result"
}

const result = function(filename, expect) {
  return got => {
    if(expect["return"] === undefined) {
      failTest(filename, resultToString(expect), got);
    } else {
      if(expect["return"] === (got | 0)) {
        passTest(filename, resultToString(expect["return"]), (got | 0));
      } else {
        failTest(filename, resultToString(expect["return"]), (got | 0));
      }
    }
    return;
  };
}

const abort = function(filename, expect) {
  return got => {
    if(expect["abort"] !== undefined && (got | 0) === 6) {
      passTest(filename, "abort", (got | 0));
      return;
    } else if(expect["memerror"] !== undefined && (got | 0) === 12) {
      passTest(filename, "memerror", (got | 0));
      return;
    } else if(expect["div-by-zero"] !== undefined && (got | 0) === 8) {
      return; // checked by the runtime exception
    }
    failTest(filename, resultToString(expect), "abort" + (got | 0));
    return;
  };
}

const parseExpectedResult = function(filename, k, next) {
  fs.readFile(filename, (err, data) => {
    var str = (data + "").split("\n", 2)[0].trim();
    if(str.startsWith("//test")) {
      str = str.substring(7);

      if(str.startsWith("return")) {
        return k({"return":
          (str.substring(7).trim().replace("~","-").replace(";", "") | 0)
        });
      } else if(str.startsWith("div-by-zero")) {
        return k({"div-by-zero": true})
      } else if(str.startsWith("abort")) {
        return k({"abort": true})
      } else if(str.startsWith("memerror")) {
        return k({"memerror": true})
      } else if(str.startsWith("error")) {
        return k({"error": true})
      } else if(str.startsWith("typecheck")) {
        return k({"typecheck": true})
      } else if(str.startsWith("compile")) {
        return k({"compile": true})
      }
    }

    console.log("Couldn't parse testcase result for '" + filename + "' :(")
    return next();
  });
}

const compile = function(filename, result, exe, next) {
  exec('sh compile.sh ' + filename,
    (error, stdout, stderr) => {
      if(result === undefined) {
        if(error !== null) {
          console.log(stdout);
          console.log(stderr);
          return next();
        }
        return exe();
      }

      if (error !== null && result["error"]) {
        passTest(filename, "Compile error", "Compile error")
        return next();
      }
      if (error !== null) {
        failTest(filename, resultToString(result), "\n" + stdout + "\n" + stderr);
        return next();
      }
      return exe();
    }
  );
}

const run = function(filename, imports, expect, k) {
  const bytes = fs.readFileSync(filename + ".wasm");
  const wasm = new WebAssembly.Module(bytes);

  if(expect !== undefined && expect["compile"]) {
    return passTest(filename, "Compile and link", "Compile and link");
  }

  try {
    const instance = new WebAssembly.Instance(wasm, imports);
  } catch(e) {
    if(expect === undefined) {
      console.log(e + "");
    }

    if(e instanceof WebAssembly.RuntimeError && expect["div-by-zero"]) {
      passTest(filename, "div-by-zero", "div-by-zero");
    } else if(e instanceof WebAssembly.RuntimeError
              && (expect["memerror"] || expect["abort"])) {
    } else {
      failTest(filename, resultToString(expect), "\n" + e + "\n")
    }
  }
  k();
}

const evalTest = function(filename, k) {
  parseExpectedResult(filename, res => {
    compile(filename, res, () => {
      if(res["typecheck"]) {
        return passTest(filename, "Typechecked", "Typechecked")
      }
      const check_imports = {c0deine: {
        result: result(filename, res),
        abort: abort(filename, res),
      }};
      run(filename, check_imports, res, k);
    }, k);
  }, k);
}

const main = function() {
  if(!fs.existsSync(args[0])) {
    process.stdout.write("Couldn't find file/directory: " + args[0] + "\n");
    console.log(args);
    return;
  }

  if(fs.lstatSync(args[0]).isFile()) {
    const filename = args[0]
    evalTest(filename, () => {});
    return;
  }

  if(fs.lstatSync(args[0]).isDirectory()) {
    const dir = args[0]
    fs.readdir(dir, (err, files) => {
      if(err !== null) {
        console.log("Something went wrong reading directory!");
        return;
      }

      const iter = function(llist) {
        if(llist === undefined || llist === null || llist.nil) {
          console.log("Passed: " + success + "  Failed: "+ failed);
          return;
        }
        const file = llist.hd
        if(file.endsWith(".l4")
            || file.endsWith(".l3")
            || file.endsWith(".l2")
            || file.endsWith(".l1")
            || file.endsWith(".c0")) {
          evalTest(path.join(dir, file), () => {
            iter(llist.tl())
          });
        } else {
          iter(llist.tl())
        }
      };
    iter(buildLazyList(files));
    });
    return;
  }
}

main();
// run("../test", print_imports, undefined, () => {});

