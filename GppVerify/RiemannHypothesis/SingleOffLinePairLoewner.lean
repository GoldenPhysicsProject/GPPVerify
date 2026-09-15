import Mathlib.Tactic

/-!
# Single off-line folded pair: exact order-two Loewner obstruction

For a conjugate pair of safe folded spectral parameters `t = a ± i b`, the real
Pick/Löwner contribution is

    phi(u) = 2*u*(u+a) / ((u+a)^2 + b^2).

This file formalizes the elementary rational algebra behind the observation that one
nonreal conjugate pair already makes every nontrivial 2-by-2 Löwner determinant
negative.  It contains no zeta-zero input and makes no claim of RH; other spectral
modes can alter the determinant of the full kernel.
-/

namespace GppSingleOffLinePairLoewner

/-- Positive-real-axis denominator for one conjugate folded pole pair. -/
def pairDenom (a b u : ℝ) : ℝ := (u + a)^2 + b^2

/-- Real contribution `u*t/(u+t) + u*conj(t)/(u+conj(t))`. -/
def pairPhi (a b u : ℝ) : ℝ :=
  2 * u * (u + a) / pairDenom a b u

/-- Closed rational formula for `pairPhi'`. -/
def pairPhiPrime (a b u : ℝ) : ℝ :=
  2 * (a^3 + 2*a^2*u + a*b^2 + a*u^2 + 2*b^2*u) /
    (pairDenom a b u)^2

/-- Closed rational formula for the divided difference of `pairPhi`. -/
def pairPhiDivDiff (a b u v : ℝ) : ℝ :=
  2 * (a^3 + a^2*u + a^2*v + a*b^2 + a*u*v + b^2*u + b^2*v) /
    (pairDenom a b u * pairDenom a b v)

/-- The displayed prime formula is the actual derivative of `pairPhi`. -/
theorem hasDerivAt_pairPhi {a b u : ℝ}
    (hD : pairDenom a b u ≠ 0) :
    HasDerivAt (pairPhi a b) (pairPhiPrime a b u) u := by
  unfold pairPhi pairPhiPrime pairDenom
  convert
    (((hasDerivAt_id u).mul ((hasDerivAt_id u).add_const a)).const_mul 2).div
      ((((hasDerivAt_id u).add_const a).pow 2).add_const (b^2)) hD using 1 <;>
    field_simp <;> ring

/-- For distinct sample points, the displayed off-diagonal entry really is the
Löwner divided difference. -/
theorem pairPhi_dividedDifference {a b u v : ℝ}
    (huv : u ≠ v)
    (hDu : pairDenom a b u ≠ 0)
    (hDv : pairDenom a b v ≠ 0) :
    (pairPhi a b u - pairPhi a b v) / (u - v) = pairPhiDivDiff a b u v := by
  unfold pairPhi pairPhiDivDiff pairDenom at *
  field_simp
  ring

/-- Exact determinant identity for the 2-by-2 Löwner matrix of one conjugate pair. -/
theorem pairLoewner_det_identity {a b u v : ℝ}
    (hDu : pairDenom a b u ≠ 0)
    (hDv : pairDenom a b v ≠ 0) :
    pairPhiPrime a b u * pairPhiPrime a b v - (pairPhiDivDiff a b u v)^2 =
      -4 * b^2 * (a^2 + b^2) * (u-v)^2 /
        ((pairDenom a b u)^2 * (pairDenom a b v)^2) := by
  unfold pairPhiPrime pairPhiDivDiff pairDenom at *
  field_simp
  ring

/-- A genuinely nonreal folded pair (`b ≠ 0`) has a strictly negative 2-by-2
Löwner determinant at every pair of distinct positive sample points. -/
theorem pairLoewner_det_neg {a b u v : ℝ}
    (ha : 0 < a) (hb : b ≠ 0) (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) :
    pairPhiPrime a b u * pairPhiPrime a b v - (pairPhiDivDiff a b u v)^2 < 0 := by
  have hDuPos : 0 < pairDenom a b u := by
    unfold pairDenom
    positivity
  have hDvPos : 0 < pairDenom a b v := by
    unfold pairDenom
    positivity
  rw [pairLoewner_det_identity hDuPos.ne' hDvPos.ne']
  have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
  have hab : 0 < a^2 + b^2 := by positivity
  have huv2 : 0 < (u-v)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr huv)
  have hden : 0 < (pairDenom a b u)^2 * (pairDenom a b v)^2 := by positivity
  exact div_neg_of_neg_of_pos (by positivity) hden

/-- In the folded zeta parametrization `b = -2*delta*gamma`, nonzero horizontal
displacement and nonzero ordinate force a nonreal folded pair. -/
theorem folded_imag_ne_zero {δ γ : ℝ} (hδ : δ ≠ 0) (hγ : γ ≠ 0) :
    (-2 * δ * γ : ℝ) ≠ 0 := by
  positivity

end GppSingleOffLinePairLoewner

#check @GppSingleOffLinePairLoewner.pairPhi_dividedDifference
#check @GppSingleOffLinePairLoewner.pairLoewner_det_identity
#check @GppSingleOffLinePairLoewner.pairLoewner_det_neg
#check @GppSingleOffLinePairLoewner.folded_imag_ne_zero
