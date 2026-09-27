import Mathlib.Tactic

/-!
# Tetrad invertibility is the geometric order parameter for a genuinely premetric boundary

`m=0` does not make a Lorentz metric degenerate.  A more appropriate geometric variable is
the soldering/tetrad determinant.  This file gives the exact two-dimensional prototype of
the general identity

    det(g) = det(eta) det(e)^2

for `g = e^T eta e`.

Write

    e = [[a,b],[c,d]],      det(e)=ad-bc,
    eta = diag(-1,+1).

Then direct calculation gives

    det(g) = -(ad-bc)^2.

Hence `g` is degenerate exactly when the tetrad is.  This is the correct algebraic model for
"metric undefined/degenerate before the Lorentzian phase": the order parameter is
invertibility of the soldering form, not ordinary particle masslessness.

A Dirac mass term in tetrad form is multiplied in the action density by the tetrad volume.
The final elementary lemmas record only the corresponding scalar fact that an effective
volume-weighted coupling `m * det(e)` vanishes at the degenerate boundary and is nonzero
when both factors are nonzero.  They do NOT identify physical mass with `det(e)`.
-/

namespace GppTetradMetricOrderParameter

/-- Determinant of the 2x2 tetrad prototype. -/
def tetradDet (a b c d : ℝ) : ℝ := a*d - b*c

/-- Entries of `g=e^T eta e`, eta=diag(-1,+1). -/
def g00 (a c : ℝ) : ℝ := -a^2 + c^2
def g01 (a b c d : ℝ) : ℝ := -a*b + c*d
def g11 (b d : ℝ) : ℝ := -b^2 + d^2

/-- Determinant of the induced metric prototype. -/
def metricDet (a b c d : ℝ) : ℝ :=
  g00 a c * g11 b d - (g01 a b c d)^2

/-- Exact tetrad/metric determinant identity. -/
theorem metricDet_eq_neg_tetradDet_sq (a b c d : ℝ) :
    metricDet a b c d = -(tetradDet a b c d)^2 := by
  simp [metricDet, g00, g01, g11, tetradDet]
  ring

/-- Degenerate tetrad implies degenerate induced metric. -/
theorem tetrad_degenerate_implies_metric_degenerate
    (a b c d : ℝ) (h : tetradDet a b c d = 0) :
    metricDet a b c d = 0 := by
  rw [metricDet_eq_neg_tetradDet_sq, h]
  norm_num

/-- Over the reals the converse holds as well. -/
theorem metric_degenerate_implies_tetrad_degenerate
    (a b c d : ℝ) (h : metricDet a b c d = 0) :
    tetradDet a b c d = 0 := by
  rw [metricDet_eq_neg_tetradDet_sq] at h
  have hs : (tetradDet a b c d)^2 = 0 := by linarith
  exact sq_eq_zero_iff.mp hs

/-- Premetric/degenerate boundary is exactly the zero-tetrad-determinant locus in this
    prototype. -/
theorem metric_degenerate_iff_tetrad_degenerate (a b c d : ℝ) :
    metricDet a b c d = 0 ↔ tetradDet a b c d = 0 := by
  constructor
  · exact metric_degenerate_implies_tetrad_degenerate a b c d
  · exact tetrad_degenerate_implies_metric_degenerate a b c d

/-- Scalar prototype of a volume-weighted fermion mass coupling in the action density. -/
def volumeWeightedMass (m a b c d : ℝ) : ℝ := m * tetradDet a b c d

/-- At a degenerate tetrad boundary the volume-weighted mass term vanishes identically. -/
theorem volume_weighted_mass_vanishes_at_premetric_boundary
    (m a b c d : ℝ) (h : tetradDet a b c d = 0) :
    volumeWeightedMass m a b c d = 0 := by
  simp [volumeWeightedMass, h]

/-- Away from the boundary, a nonzero mass parameter gives a nonzero volume-weighted
    coupling. -/
theorem volume_weighted_mass_nonzero_of_invertible_tetrad
    (m a b c d : ℝ) (hm : m ≠ 0) (he : tetradDet a b c d ≠ 0) :
    volumeWeightedMass m a b c d ≠ 0 := by
  exact mul_ne_zero hm he

end GppTetradMetricOrderParameter
