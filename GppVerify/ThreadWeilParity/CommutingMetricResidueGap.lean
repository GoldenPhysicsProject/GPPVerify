import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Why `d1aec733`'s forward/converse formulas need an extra reality hypothesis

`formalization_queue` item `d1aec733` ("Positive commuting metric equivalent to residue
positivity"), Weil-Parity thread — flagged in the sixth/seventh-pass writeups as "carrying
a real subtlety," this file makes that subtlety precise instead of leaving it a hunch.

The item defines, for an eigenvector `u_j` of `A`, `c_j := (η^*u_j)(u_j^*e0)` and
`g_j := (η^*u_j)/(u_j^*e0)` (forward direction), and separately (converse direction)
`c_j := ⟨u_j, G u_j⟩ · |u_j^*e0|²` — i.e. `c_j = g_j · |u_j^*e0|²` with a **modulus square**.
Unwinding the forward direction's own two definitions algebraically:
`c_j = (η^*u_j)(u_j^*e0) = [g_j·(u_j^*e0)]·(u_j^*e0) = g_j·(u_j^*e0)²` — a **plain square**,
not a modulus square. These agree only when `u_j^*e0` is real (then `w² = |w|²`); in
general, for complex `w := u_j^*e0`, `w² ≠ |w|²`.

## What this file proves

The exact algebraic identity behind the mismatch: `c_j = g_j · w²` unconditionally (given
`w ≠ 0`), confirming — by direct computation, not impression — that the item's claimed
equivalence "`c_j > 0` for all `j` iff `G` positive definite" (which would need `g_j` real
and positive, i.e. effectively `c_j = g_j·|w|²`) does not follow from the forward
direction's bare definitions alone unless `u_j^*e0` is additionally assumed real. This is
a genuine, checked finding about the item as literally stated, not a proof that the
underlying mathematical claim is false in the intended (presumably real-symmetric or
otherwise structured) setting — only that the queue item's abstract phrasing is
underspecified at exactly this point, worth flagging back to the research source rather
than silently patched over or forced through.

## What this file does NOT do

Does not attempt the full iff `c_j > 0 for all j ⟺ G positive definite` at all, does not
define Hermitian matrices, eigenvectors, or the operator `G = Σ_j g_j |u_j⟩⟨u_j|`. No
axiom, no sorry.
-/

namespace GppWeilParity

/-- **The exact algebraic identity**: with `c := v·w` and `g := v/w` (the item's own
`c_j`, `g_j` formulas for `v := η^*u_j`, `w := u_j^*e0`), `c = g·w²` — a **plain** complex
square, not `g·|w|²`. Confirms the forward/converse formula mismatch precisely: the two
coincide only when `w` is real. -/
theorem cj_eq_gj_mul_sq {v w : ℂ} (hw : w ≠ 0) : v * w = (v / w) * w ^ 2 := by
  field_simp

/-- The mismatch is not vacuous: a genuine `w` with `w² ≠ (normSq w : ℂ)` exists whenever
`w` is non-real (e.g. `w = i`: `w² = -1` but `normSq i = 1`). Recorded as the concrete
witness that the reality hypothesis is not free. -/
example : (Complex.I) ^ 2 ≠ ((Complex.normSq Complex.I : ℝ) : ℂ) := by
  rw [Complex.I_sq, Complex.normSq_I, Complex.ofReal_one]
  intro h
  have hre : (-1 : ℝ) = 1 := by
    have := congrArg Complex.re h
    simpa using this
  norm_num at hre

end GppWeilParity
