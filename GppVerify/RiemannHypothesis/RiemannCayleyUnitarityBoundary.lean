import Mathlib.Tactic

/-!
# Cayley unitarity boundary for the Riemann critical line

Use the Cayley coordinate

  beta(s) = 1 - 1/s = (s - 1)/s.

For `s = sigma + i t`, its squared modulus is

  |beta(s)|^2 = ((sigma - 1)^2 + t^2) / (sigma^2 + t^2).

The finite real algebra below proves:

* `|beta| < 1` exactly on `sigma > 1/2`;
* `|beta| = 1` exactly on `sigma = 1/2`;
* `|beta| > 1` exactly on `sigma < 1/2`;
* functional-equation reflection `sigma -> 1-sigma` reciprocates the squared modulus;
* the exact contraction defect of `sigma = 1/2 + delta` is
  `2 delta / ((1/2+delta)^2+t^2)`.

Thus the critical line is literally the unitary boundary of this Cayley chart, while an
off-line functional-equation pair is a contraction/expansion reciprocal pair.  This file is
pure finite algebra; it contains no claim about the location of zeta zeros.
-/

namespace GppRiemannCayleyUnitarityBoundary

/-- Squared modulus of `(s-1)/s` for `s = sigma + i t`. -/
def cayleyNormSq (sigma t : ℝ) : ℝ :=
  (((sigma - 1)^2 + t^2) / (sigma^2 + t^2))

/-- Right of the critical line is exactly the contractive disk side. -/
theorem cayley_lt_one_iff
    (sigma t : ℝ) (hden : 0 < sigma^2 + t^2) :
    cayleyNormSq sigma t < 1 ↔ (1 / 2 : ℝ) < sigma := by
  unfold cayleyNormSq
  rw [div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith [sq_nonneg (sigma - 1), sq_nonneg sigma, sq_nonneg t]

/-- The critical line is exactly the unit-circle locus in the Cayley chart. -/
theorem cayley_eq_one_iff
    (sigma t : ℝ) (hden : 0 < sigma^2 + t^2) :
    cayleyNormSq sigma t = 1 ↔ sigma = (1 / 2 : ℝ) := by
  unfold cayleyNormSq
  constructor
  · intro h
    have hcross := (div_eq_iff hden.ne').mp h
    nlinarith [sq_nonneg (sigma - 1), sq_nonneg sigma, sq_nonneg t]
  · intro hs
    apply (div_eq_iff hden.ne').2
    nlinarith [sq_nonneg (sigma - 1), sq_nonneg sigma, sq_nonneg t]

/-- Left of the critical line is exactly the expansive side. -/
theorem one_lt_cayley_iff
    (sigma t : ℝ) (hden : 0 < sigma^2 + t^2) :
    1 < cayleyNormSq sigma t ↔ sigma < (1 / 2 : ℝ) := by
  unfold cayleyNormSq
  rw [lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith [sq_nonneg (sigma - 1), sq_nonneg sigma, sq_nonneg t]

/-- The critical-line comparison is controlled by the single numerator `1 - 2 sigma`. -/
theorem cayley_norm_sq_sub_one
    (sigma t : ℝ) (hden : sigma^2 + t^2 ≠ 0) :
    cayleyNormSq sigma t - 1 =
      (1 - 2 * sigma) / (sigma^2 + t^2) := by
  unfold cayleyNormSq
  field_simp [hden]
  ring

/-- The exact positive contraction defect for a right-shift `delta` from the critical line. -/
theorem cayley_right_shift_defect
    (delta t : ℝ)
    (hden : 0 < ((1 / 2 : ℝ) + delta)^2 + t^2) :
    1 - cayleyNormSq ((1 / 2 : ℝ) + delta) t =
      (2 * delta) / (((1 / 2 : ℝ) + delta)^2 + t^2) := by
  have hsub := cayley_norm_sq_sub_one ((1 / 2 : ℝ) + delta) t hden.ne'
  linarith

/-- A positive displacement from the critical line gives a strictly positive defect. -/
theorem cayley_right_shift_defect_pos
    (delta t : ℝ)
    (hdelta : 0 < delta)
    (hden : 0 < ((1 / 2 : ℝ) + delta)^2 + t^2) :
    0 < 1 - cayleyNormSq ((1 / 2 : ℝ) + delta) t := by
  rw [cayley_right_shift_defect delta t hden]
  positivity

/--
Functional-equation reflection across `sigma = 1/2` exchanges contraction and expansion:
the squared Cayley modulus is inverted.
-/
theorem reflected_cayley_norm_sq_reciprocal
    (sigma t : ℝ)
    (hden : 0 < sigma^2 + t^2)
    (hnum : 0 < (sigma - 1)^2 + t^2) :
    cayleyNormSq (1 - sigma) t = 1 / cayleyNormSq sigma t := by
  unfold cayleyNormSq
  field_simp [hden.ne', hnum.ne']
  ring

/-- A reflected off-line pair cannot have both members contractive. -/
theorem reflected_right_half_becomes_expansive
    (sigma t : ℝ)
    (hden : 0 < sigma^2 + t^2)
    (hrefden : 0 < (1 - sigma)^2 + t^2)
    (hsigma : (1 / 2 : ℝ) < sigma) :
    1 < cayleyNormSq (1 - sigma) t := by
  exact (one_lt_cayley_iff (1 - sigma) t hrefden).2 (by linarith)

end GppRiemannCayleyUnitarityBoundary
