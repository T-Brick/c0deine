/* c0deine.h

  This is a representation of built-in functions and imports that the runtime
  should provide to WASM. Each declaration includes a brief summary of what it
  is as well as the corresponding import that appears in the compiled output.

  The current WASM spec has a 32-bit memory. While there are proposals to extend
  this to 64-bits, C0deine uses the 32-bit spec. Due to this, all pointers, when
  compiling to WASM, are represented by a `u32` address. That being said, when
  using anything represented as a pointer in `struct`'s or `array`'s will be
  allocated 8-bytes and struct alignment will take account of this.

  - Thea Brick
*/


/* `c0_memory` is a representation of how c0deine expects memory to be laid out
   for the executable program. The data segment of the outputted code will
   initiate the `free_ptr` and `text` fields. The `text` portion should never be
   modifed after being initiated.

  `(import "c0deine" "memory" (memory  1))`
*/
typedef struct {
  int *free_ptr;   // pointer to next free segment in `data`
  char text[0];    // segment corresponding to static text in the program
  char data[0];    // data that c0 uses
} c0_memory;


/* `result` function is called with the result of the c0 `main` function defined
   by the source program.

   `(import "c0deine" "result" (func $result (param i32)) )`
*/
void result(int i);


/* If the program executes a divide by zero, this error will be handled through
   WASM error handling. For all other errors the `abort` function is called with
   the signal of the error that occured:
   - Arithmetic errors: SIGFPE (8)
     - Importantly this is called for bitshifts that are out of bounds as well
       as `INT_MIN % -1` which is not considered an error in WASM.
   - Assertion failure: SIGABRT (6)
   - Memory error: SIGUSR2 (12)

   An unreachable statement will be executed if the `abort` function returns.

  `(import "c0deine" "abort"  (func $abort  (param i32)) )`
*/
void abort(int sig);


/* The `error` function is called with index of a NULL (\0) terminated string in
   WASML's memory. An unreachable statement will be executed if this function
   returns.

   `(import "c0deine" "error"  (func $error  (param i32)) )`
*/
void error(char *str);


/* `calloc` allocates a free block of memory of the inputted size with all of
   the memory set to 0. All allocated pointers are adjusted so that the
   `free_ptr` in `c0_memory` is at the NULL address.

  By default, c0deine provides an implementation of `calloc`. A custom one must
  be provided when the `--wasm-import-calloc` flag is used. A imported
  implementation is expected to preserve the following invariants:
  - Only return a pointer to `NULL` (`0`) upon some sort of memory failure.
  - Only return pointers to free memory that are zero'd out.
  - The text section should never be altered.
  - Any live memory should never be altered.

  `(import "c0deine" "calloc" (func $calloc (param i32) (result i32)) )`
*/
void *calloc(unsigned int size);


/* `free` allows for the deallocation of memory. Importantly, `free` should
   never deallocate live memory and will only be called when C0deine has
   identified that the memory is dead.

  By default, c0deine provides an implementation of `free`. A custom one must be
  provided when the `--wasm-import-calloc` flag is used.

   `(import "c0deine" "free" (func $free (param i32)) )`
*/
void free(void *ptr);
