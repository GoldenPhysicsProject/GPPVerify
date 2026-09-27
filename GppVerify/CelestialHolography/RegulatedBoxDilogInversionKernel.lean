import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Branch-free real dilogarithm inversion kernel

For a real function `L` on the negative axis satisfying

  L'(y) = -log(1-y)/y,

the reciprocal combination

  L(-x) + L(-1/x) + (1/2) log(x)^2

has derivative zero for every `x > 0`.  This is the calculus core of the real
inversion formula needed by the regulated scalar box.  No complex logarithm or
branch convention occurs here.
-/

namespace GppRegulatedBoxDilogInversionKernel

/-- The reciprocal dilogarithm combination, without its eventual additive constant. -/
noncomputable def inversionCombination (L : ℝ → ℝ) (x : ℝ) : ℝ :=
  L (-x) + L (-1 / x) + (Real.log x) ^ 2 / 2

/-- **Derivative-cancellation kernel for real dilogarithm inversion.** -/
theorem inversionCombination_hasDerivAt_zero
    (L : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hL : ∀ y : ℝ, y < 0 →
      HasDerivAt L (-Real.log (1 - y) / y) y) :
    HasDerivAt (inversionCombination L) 0 x := by
  have hxne : x ≠ 0 := ne_of_gt hx

  have hneg_inner : HasDerivAt (fun t : ℝ => -t) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hLneg := hL (-x) (neg_neg_of_pos hx)
  have hneg_comp := hLneg.comp x hneg_inner
  have hneg : HasDerivAt (fun t : ℝ => L (-t))
      (-Real.log (1 + x) / x) x := by
    convert hneg_comp using 1 <;> field_simp [hxne] <;> ring

  have hinv_inner : HasDerivAt (fun t : ℝ => -1 / t) (1 / x ^ 2) x := by
    have h := (hasDerivAt_const x (-1 : ℝ)).div (hasDerivAt_id x) hxne
    convert h using 1 <;> field_simp [hxne] <;> ring
  have hinvpos : 0 < 1 / x := one_div_pos.mpr hx
  have hargneg : -1 / x < 0 := by
    rw [show (-1 : ℝ) / x = -(1 / x) by ring]
    exact neg_neg_of_pos hinvpos
  have hLinv := hL (-1 / x) hargneg
  have hinv_comp := hLinv.comp x hinv_inner
  have hinv : HasDerivAt (fun t : ℝ => L (-1 / t))
      (Real.log (1 + 1 / x) / x) x := by
    convert hinv_comp using 1 <;> field_simp [hxne] <;> ring

  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hxne
  have hlogsq : HasDerivAt (fun t : ℝ => (Real.log t) ^ 2 / 2)
      (Real.log x / x) x := by
    convert (hlog.pow 2).div_const 2 using 1 <;> ring

  have hsum := (hneg.add hinv).add hlogsq
  have hlog_identity :
      Real.log (1 + 1 / x) + Real.log x = Real.log (1 + x) := by
    have hleft : 1 + 1 / x ≠ 0 := by positivity
    rw [← Real.log_mul hleft hxne]
    congr 1
    field_simp [hxne]
    ring
  have hnum :
      -Real.log (1 + x) + Real.log (1 + 1 / x) + Real.log x = 0 := by
    linarith [hlog_identity]
  have hcoef :
      -Real.log (1 + x) / x + Real.log (1 + 1 / x) / x + Real.log x / x = 0 := by
    calc
      -Real.log (1 + x) / x + Real.log (1 + 1 / x) / x + Real.log x / x =
          (-Real.log (1 + x) + Real.log (1 + 1 / x) + Real.log x) / x := by ring
      _ = 0 := by rw [hnum, zero_div]

  unfold inversionCombination
  convert hsum using 1
  exact hcoef.symm

end GppRegulatedBoxDilogInversionKernel

#print axioms GppRegulatedBoxDilogInversionKernel.inversionCombination_hasDerivAt_zero
