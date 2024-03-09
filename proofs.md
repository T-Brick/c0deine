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
- An if-statement is splits our proof into cases
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
initially holds), and exit. An open question right now is how to deal with
variable shadowing (I suspect the Lean approach of being able to rename shadowed
variables may be the best, but not 100% confident).


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

Having lists of things are nice, so here is the top priority items:
- [ ] Fix lingering issues in TST and clean-up typechecker more
- [ ] Finish the dynamic semantics for TSTs
- [ ] Further investigate and identify what C0 proofs are expected to look like
- [ ] Create list of sample programs that we'd like to be able to prove
- [ ] Identify and create list of possible tactics that would be useful
- [ ] Implement tactics/theorems for evaluating C0 code in a proof-mode
- [ ] Document everything

Lower priority items are as follows
- [ ] Add marking/metadata in the AST and TST
- [ ] Implement delaborator
- [ ] Implement purity checker
- [ ] Embed C0 as a DSL directly into Lean via metaprogramming


## Future Work

Once this project is complete and assuming it works well enough there are serval
avenues that could be explored:
- Integrating into existing curricula (e.g. 122)
- Developing something similar to the Natural Numbers Game but for C0
- Add and support language extensions (e.g. C1, new contracts, etc.)
- Explore requiring/having proofs of termination (rather than just assuming it)
- Verifying correctness of more complex C0 programs
