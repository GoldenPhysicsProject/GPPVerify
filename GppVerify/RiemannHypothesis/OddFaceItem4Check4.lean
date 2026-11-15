import GppVerify.RiemannHypothesis.OddFaceItem4Core

/-!
# OddFace(0.5), item 4: kernel check, rows 37..45

`decide +kernel` evaluates `rowOk i` (the exact integer residual bound `|resInt i j| ≤ EE` for all
`j < 73`) for these rows. See `OddFaceItem4Core.lean`. Sharded so each file's kernel run stays short.
-/

namespace GppOddFaceItem4

theorem rows_4 : (List.range' 37 9).all rowOk = true := by decide +kernel

end GppOddFaceItem4

#print axioms GppOddFaceItem4.rows_4
