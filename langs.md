# Information about Source Languages + Emitted Code

## Source Languages

C0deine has a variety of source languages that build upon each other by adding
new features. Here is a list of currently supported languages (as well as links
to their definition/information about them):

- [L1](https://www.cs.cmu.edu/~janh/courses/411/23/labs/lab1.pdf) is a simple
  language that only allows for integer variables and straight-line code.
- [L2](https://www.cs.cmu.edu/~janh/courses/411/23/labs/lab2.pdf) expands on L1
  by allowing for control-flow constructs (if statements, while-loops, etc.) as
  well as boolean variables and operations.
- [L3](https://www.cs.cmu.edu/~janh/courses/411/23/labs/lab3.pdf) adds the
  ability to declare and define other functions besides `main`. It also adds
  `typedef`s.
- [L4](https://www.cs.cmu.edu/~janh/courses/411/23/labs/lab4.pdf) finally
  reaches a usable programming language with pointers, structs, arrays.
- [C0](https://c0.cs.cmu.edu/docs/c0-reference.pdf) is the primary source
  language. It adds `char`, `string` types as well as contracts to reason about
  code. The original definition of C0 can be found
  [here](http://reports-archive.adm.cs.cmu.edu/anon/2010/CMU-CS-10-145.pdf)

For a general summary, here is a reprint of differences between C0 and C
from [2.10.1](http://reports-archive.adm.cs.cmu.edu/anon/2010/CMU-CS-10-145.pdf)
> - No unions
> - No casting
> - No pointer arithmetic
> - No sizeof operator
> - No address-of operator (&)
> - No storage modifiers (static, volatile, register, extern)
> - No labels, goto, switch statements or do ... while loops
> - No assignment in expressions
> - No floating point datatypes or literals
> - No complex types
> - No unsigned or other integral types besides int
> - Structure types may not be declared as local variables or used as return types for functions
> - No comma separated expressions
> - No explicit memory deallocation
> - Allocation is done using types not a size in bytes.
> - No fixed size arrays
> - No stack allocated arrays

Eventually, we intend to extend C0deine to support C1 (and potentially beyond)
which addresses some of the limitations of C0.

### Deviations

This implementation makes a few (known) deviations from the source languages
defined above as well as some behaviour clarifications:

- The keyword `error` from C0 is now reserved in all languages (not just C0).
- The compiler `#use` directive from C0 can be used in L3/L4.
- A bug in the `cc0` reference compiler means some operations occur out of order
  when using assign-ops:
  ```c
  int main() {
    int[] x = alloc_array(int, 0);
    x[0] += 1 / 0;
    return 0;
  }
  ```
  The reference semantics indicate this should be a memory error but the `cc0`
  compiler produces a FPE. C0deine correctly raises a memory error.

- The `error` statement is specified to "immediately terminate the program".
  Likewise, the reference semantics state that "Along each control-flow path in
  the body of each block in each func- tion, each locally declared variable is
  initialized before its use." (C0.24). Thus, it follows that we should accept
  the following program (since `error` ends the control flow path):
  ```c
  int main() {
    int y;
    if(false) {
      error("this terminates the program");
      return y;
    } else {
      return 0;
    }
  }
  ```
  The `cc0` compiler incorrectly rejects this program (stating that `y` is
  uninitialised). C0deine correctly accepts this program.

- In the C0 grammar, the definition for `<spec>` implies that new lines `\n`
  could be placed after the contract keyword or even within the expression. This
  causes issues when using the line annotations:
  ```c
  int exp(int k, int n)
  //@requires n
        >= 0;
  // rest of program omitted...
  ```
  The grammar indicates that this is a valid program. Currently, C0deine accepts
  such programs (but this may be changed later).

- In the semantics for annotations an "`@assert` cannot annotate functions"
  (C0.25). This is the only comment made about `@assert`, implying that they
  could procede loop bodies:
  ```c
  int main(){
    int i = 0;
    while(i < 10)
    //@assert i <= 10;
    {
      i++;
    }
    return i;
  }
  ```
  It is unclear what the intended semantics of this would be, so C0deine rejects
  this program (as does `cc0`).

- The grammar allows for `'''` to be parsed as a valid `char`. Since C0 is
  intended to roughly be a subset of C, C0deine rejects this (as does `cc0`).


## Target Languages
### WASM

By default C0deine requires importing two functions `result` and `abort`:

```wat
(import "c0deine" "result" (func $result (param i32) ))
(import "c0deine" "abort" (func $abort (param i32) ))
```

The result function is called with the result of the `main` function defined
by the user.

If the program executes a divide by zero, this error will be handled through
WASM error handling. For all other errors the abort function is called with the
signal of the error that occured:
- Arithmetic errors: SIGFPE (8)
  - Importantly this is called for bitshifts that are out of bounds as well
    as `INT_MIN % -1` which is not considered an error in WASM.
- Assertion failure: SIGABRT (6)
- Memory error: SIGUSR2 (12)
