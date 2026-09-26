import GppVerify.GrassmannianMass
import Mathlib.Tactic

/-!
# Grassmannian orientation map as a genuine Z/4 action on the big cell

The coordinate chart transition used in the mass/orientation program already satisfies
`τ² = -id` whenever the Plücker determinant is nonzero.  This file packages the same
map as a tuple self-map and proves the actual fourth-iterate statement, including the
nonzero-determinant domain check at the negated intermediate point.
-/

namespace GppGrassmannianOrientationZ4

open GppGrassmannian

/-- Tuple-packaged version of the Gr(2,4) big-cell transition. -/
noncomputable def tauTuple : (ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ)
  | (a, b, c, d) => transition a b c d

/-- The determinant coordinate on the big cell. -/
def chartDet : (ℝ × ℝ × ℝ × ℝ) → ℝ
  | (a, b, c, d) => a * d - b * c

/-- Coordinate negation preserves the chart determinant. -/
theorem chartDet_neg (a b c d : ℝ) :
    chartDet (-a, -b, -c, -d) = chartDet (a, b, c, d) := by
  simp [chartDet]
  ring

/-- The tuple-packaged orientation map squares to coordinate negation. -/
theorem tauTuple_sq_eq_neg (a b c d : ℝ)
    (hD : chartDet (a, b, c, d) ≠ 0) :
    tauTuple (tauTuple (a, b, c, d)) = (-a, -b, -c, -d) := by
  simpa [tauTuple, chartDet] using
    transition_transition_eq_neg a b c d (by simpa [chartDet] using hD)

/-- **Exact order-four closure.**  On the nonzero-determinant big cell,
applying the orientation transition four times returns the original point. -/
theorem tauTuple_four_eq (a b c d : ℝ)
    (hD : chartDet (a, b, c, d) ≠ 0) :
    tauTuple (tauTuple (tauTuple (tauTuple (a, b, c, d)))) = (a, b, c, d) := by
  rw [tauTuple_sq_eq_neg a b c d hD]
  have hDneg : chartDet (-a, -b, -c, -d) ≠ 0 := by
    rw [chartDet_neg]
    exact hD
  rw [tauTuple_sq_eq_neg (-a) (-b) (-c) (-d) hDneg]
  simp

end GppGrassmannianOrientationZ4

#print axioms GppGrassmannianOrientationZ4.tauTuple_sq_eq_neg
#print axioms GppGrassmannianOrientationZ4.tauTuple_four_eq
