# Proofs about C0 Code

[Pauline](https://github.com/T-Brick/pauline) provided a nice proof-of-concept
for reasoning about programs in other languages within Lean. The goal is to
scale up these efforts so that proofs can be written about C0. There are various
challenges to this, chief among them being: C0 is an imperative language as
opposed to the strictly functional nature of SML and I am far less familiar with
writing proofs about C0 code than SML.

## Observations/Ideas

We need to know how various C0 statements in C0 affect the proof state. Luckily
many of these things generally correspond to various tactics in Lean (because
tactics are, in essence, imperative):
- A contract introduces one or more new goals
- An assignment introduces a new hypothesis about what a variable equals
- An if-statement splits our proof into cases
- etc.

For example, consider the following C0 and Lean code which should functionally
have near identical behaviour on the proof-state:

```c
int i = 5;
//@assert i == 5;
```

```lean
-- in tactics mode
let i := 5
have : i = 5
```

Ideally, we should be able to close the newly opened goals for both proofs by
using `rfl`.

Similarly, for writing proofs about loop-invariants we introduce goals for
entry, an arbitrary iteration (along with a hypothesis that the loop-invariant
initially holds). An open question right now is how to deal with variable
shadowing (I suspect the Lean approach of being able to rename shadowed
variables may be the best, but not 100% confident).

### Architecture

We first want to parse and typecheck some C0 code. The TST should be stored as a
variable representing the program in Lean. Then, using that variable, we
indicate we'd like to prove that program correct. Here is some pseudo-code to
illustrate what we are doing:

```lean
def prog : Tst.Prog := C0.parse_typecheck "
  int example() {
    int i = 0;

    while(i < 10)
    //@loop-invariant i <= 10;
    {
      i = i + 1;
    }
    //@assert i == 10;
    return 150;
  }
"


example : C0.verify prog "example" := by
  /- There should be 3 goals (assuming we don't try to close easy goals) -/
  sorry   -- loop init | hypo: i = 0                          wts: i <= 10
  sorry   -- loop pres | hypo: i <= 10; i < 10; i' = i + 1    wts: i' <= 10
  sorry   -- assert    | hypo: ¬(i < 10); i <= 10             wts: i == 10
```

Importantly, the description of the proof states, specifically the hypotheses,
are somewhat deceiving. Expressions like `i + 1` are not "Lean" expressions but
rather Tst expressions. The dynamic semantics enable use to evaluate these C0
expressions into components that can then be discharged into Lean expressions.


## What Needs to be Done

While there is still a lot to be done, in my opinion, we are actually quite
close to being able to implement something like this. The current plan is to do
all the reasoning/proofs on the TST IR of C0deine. This has the benefit of
knowing, structurally, that the program typechecks, as well as removing a lot of
redundant syntax.

That being said, ideally the reasoning about programs is similar/identical to
the written C0 code, so marking/metadata needs to be added to both the AST and
the TST so that we can delaborate the TST back to something closed to what was
parsed.

Having lists of things are nice, so here is the top priority items (not
necessarily ordered):
- [x] Fix lingering issues in TST
- [x] Finish the dynamic semantics for TSTs
- [ ] Further investigate and identify what C0 proofs are expected to look like
- [ ] Create list of sample programs that we'd like to be able to prove
- [ ] Identify and create list of possible tactics/theorems that would be useful
- [ ] Implement tactics/theorems for evaluating C0 code in proof-mode
- [ ] Document everything

Lower priority items that are technically not required are as follows:
- [ ] Add marking/metadata in the AST and TST
- [ ] Implement delaborator
- [ ] Implement purity checker
- [ ] Clean-up typechecker more


## Future Work

Once this project is complete and assuming it works well enough there are serval
avenues that could be explored:
- Integrating into existing curricula (e.g. 122)
- Developing something similar to the Natural Numbers Game but for C0
- Adding and supporting language extensions (e.g. C1, new contracts, etc.)
- Explore requiring/having proofs of termination (rather than just assuming it)
- Verifying correctness of more complex C0 programs
- Embedding C0 as a DSL directly into Lean via metaprogramming
