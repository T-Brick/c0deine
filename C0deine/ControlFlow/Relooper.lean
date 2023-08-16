/-
  We use the "Relooper Algorithm" to reconstruct more structured control-flow
  from our less structured basic blocks. While it might be simpler to go from
  a language that represent's C0 control-flow better (like the TST), this would
  make it hard to do many optimisations and run other checks that C0 requires.

  In theory, the code generated via this algorithm shouldn't be too inefficient
  since C0 doesn't have strange control-flow (like goto).

  https://github.com/emscripten-core/emscripten/blob/main/docs/paper.pdf
-/

import C0deine.Context.Label
import C0deine.ControlFlow.Digraph

namespace C0deine.ControlFlow.Relooper

/- `simple` represents block with only one exit
 - `loop` represents a block body and the block after the loop
 - `multi` represents branching and then the block after they merge -/
inductive Block where
| simple : Label → Option Block → Block
| loop   : (inner next : Option Block) → Block
| multi  : (handled : List Block) → (next : Option Block) → Block
