import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Branch-free real Landen derivative kernel

For a real function `L` satisfying the classical dilogarithm derivative at the
two arguments used below, the Landen combination

  L(x/(1+x)) + L(-x) + (1/2) log(1+x)^2

has derivative zero for `x > 0`.  This is deliberately an abstract calculus
kernel: the project's real dilogarithm series supplies the required derivative
hypotheses on `0 < x < 1` via the punctured-unit-disk theorem.
-/

namespace GppRegulatedBoxLandenKernel

/-- The real Landen combination before endpoint normalization. -/
noncomputable def landenCombination (L : ℝ → ℝ) (x : ℝ) : ℝ :=
  L (x / (1 + x)) + L (-x) + (Real.log (1 + x)) ^ 2 / 2

/-- Derivative cancellation for the branch-free real Landen combination. -/
theorem landenCombination_hasDerivAt_zero
    (L : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hpos : HasDerivAt L
      (-Real.log (1 - x / (1 + x)) / (x / (1 + x)))
      (x / (1 + x)))
    (hneg : HasDerivAt L
      (-Real.log (1 - (-x)) / (-x)) (-x)) :
    HasDerivAt (landenCombination L) 0 x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h1x : 1 + x ≠ 0 := by positivity

  have hfrac_inner :
      HasDerivAt (fun t : ℝ => t / (1 + t)) (1 / (1 + x) ^ 2) x := by
    have hnum := hasDerivAt_id x
    have hden := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
    have h := hnum.div hden h1x
    convert h using 1 <;> field_simp [h1x] <;> ring
  have hfrac_comp := hpos.comp x hfrac_inner
  have hfrac :
      HasDerivAt (fun t : ℝ => L (t / (1 + t)))
        (Real.log (1 + x) / (x * (1 + x))) x := by
    have hlogfrac :
        Real.log (1 - x / (1 + x)) = -Real.log (1 + x) := by
      have hpos1x : 0 < 1 + x := by positivity
      have hcalc : 1 - x / (1 + x) = 1 / (1 + x) := by
        field_simp [h1x]
        ring
      rw [hcalc, Real.log_one_div hpos1x.ne']
    convert hfrac_comp using 1
    · field_simp [hx0, h1x]
      ring
    · rw [hlogfrac]
      field_simp [hx0, h1x]
      ring

  have hneg_inner : HasDerivAt (fun t : ℝ => -t) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hneg_comp := hneg.comp x hneg_inner
  have hneg_final :
      HasDerivAt (fun t : ℝ => L (-t))
        (-Real.log (1 + x) / x) x := by
    convert hneg_comp using 1 <;> field_simp [hx0] <;> ring

  have hlog_inner : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
    simpa [h1x] using (Real.hasDerivAt_log h1x).comp x hlog_inner
  have hlogsq :
      HasDerivAt (fun t : ℝ => (Real.log (1 + t)) ^ 2 / 2)
        (Real.log (1 + x) / (1 + x)) x := by
    convert (hlog.pow 2).div_const 2 using 1 <;> ring

  have hsum := (hfrac.add hneg_final).add hlogsq
  have hcancel :
      Real.log (1 + x) / (x * (1 + x)) -
          Real.log (1 + x) / x +
          Real.log (1 + x) / (1 + x) = 0 := by
    field_simp [hx0, h1x]
    ring
  unfold landenCombination
  convert hsum using 1
  exact hcancel.symm

end GppRegulatedBoxLandenKernel

#print axioms GppRegulatedBoxLandenKernel.landenCombination_hasDerivAt_zero
