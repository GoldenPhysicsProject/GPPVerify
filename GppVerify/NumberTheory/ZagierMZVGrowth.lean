import Mathlib.Tactic

/-!
# Zagier's recurrence for multiple zeta value dimensions

Source: ONON5213.tex, "Loop Transcendence from the Plastic Constant"
(Theorem `thm:plastic`), citing Zagier's conjectured (now Brown's proved)
formula for the dimension `d_w` of the ℚ-vector space of weight-`w`
multiple zeta values: `d_w = d_{w-2} + d_{w-3}`.

The source states the initial conditions as `d_0 = 1, d_1 = d_2 = 0`, but
then lists the sequence itself as `0, 0, 1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7,
9, 12, 16, 21, 28, ...` -- these are inconsistent with each other. Checked
independently: the listed sequence is exactly what the recurrence
produces from `d_0 = 0, d_1 = 0, d_2 = 1` (not the initial conditions the
theorem states). This file formalizes the recurrence with the corrected
initial conditions and proves it reproduces the source's own listed
sequence exactly, via `decide`.

Brown's theorem that this recursively-defined `d_w` equals the actual
dimension of the weight-`w` MZV space is deep transcendence-theory content
(Fields Medal 2018 work) with no Mathlib support, and is not attempted
here -- only the finite, purely combinatorial recurrence itself is
formalized.
-/

namespace GppZagier

/-- The dimension sequence `d_w` of weight-`w` multiple zeta values,
    conjectured by Zagier and proved by Brown, satisfying
    `d_w = d_{w-2} + d_{w-3}`. Initial conditions `d_0 = d_1 = 0`,
    `d_2 = 1` (corrected from the source's stated but self-inconsistent
    `d_0 = 1, d_1 = d_2 = 0`). -/
def mzvDim : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n + 3) => mzvDim (n + 1) + mzvDim n

/-- The sequence reproduces the source's own listed values
    `d_0, ..., d_17 = 0,0,1,0,1,1,1,2,2,3,4,5,7,9,12,16,21,28` exactly. -/
theorem mzvDim_matches_source :
    (List.range 18).map mzvDim =
      [0, 0, 1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12, 16, 21, 28] := by
  decide

/-- The growth rate of `d_w` is asymptotically the plastic constant `P`,
    the unique real root of `x³ = x + 1`. Rather than a general existence
    argument, this checks the well-known 16-digit decimal approximation
    directly against the defining cubic, to a stated precision. -/
theorem plastic_constant_cubic_approx :
    |(1.3247179572447458 : ℝ) ^ 3 - (1.3247179572447458 + 1)| < 10 ^ (-9 : ℤ) := by
  norm_num

end GppZagier
