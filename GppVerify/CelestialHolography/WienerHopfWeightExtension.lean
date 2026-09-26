import GppVerify.CelestialHolography.MehlerFockSpectralWeight
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Continuous extension of the Wiener--Hopf spectral weight

The raw project weight `pi*lambda/sinh(pi*lambda)` is represented in Lean using
totalized division, so its literal value at `lambda = 0` is `0`. Analytically the
singularity is removable and the continuous value is `1`. This file separates the
mathematically intended spectral weight from that totalized-division artifact and
proves that the assigned value is the genuine continuous extension at the origin.
-/

namespace GppWienerHopfWeightExtension

open GppMehlerFockSpectral

/-- Wiener--Hopf weight with the removable origin assigned its analytic value `1`. -/
noncomputable def extendedWienerHopfWeight (lam : ℝ) : ℝ :=
  if lam = 0 then 1 else wienerHopfWeight lam

@[simp] theorem extendedWienerHopfWeight_zero :
    extendedWienerHopfWeight 0 = 1 := by
  simp [extendedWienerHopfWeight]

/-- Away from the removable point, the extended and raw weights agree exactly. -/
theorem extendedWienerHopfWeight_eq {lam : ℝ} (hlam : lam ≠ 0) :
    extendedWienerHopfWeight lam = wienerHopfWeight lam := by
  simp [extendedWienerHopfWeight, hlam]

/-- The extended Wiener--Hopf spectral weight is strictly positive for every real
spectral parameter, including the removable origin. -/
theorem extendedWienerHopfWeight_pos (lam : ℝ) :
    0 < extendedWienerHopfWeight lam := by
  by_cases hlam : lam = 0
  · subst lam
    simp
  · rw [extendedWienerHopfWeight_eq hlam]
    unfold wienerHopfWeight
    rcases lt_or_gt_of_ne hlam with hneg | hpos
    · exact div_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg Real.pi_pos hneg)
        (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos hneg))
    · exact div_pos
        (mul_pos Real.pi_pos hpos)
        (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hpos))

/-- Hence the extended weight never vanishes. -/
theorem extendedWienerHopfWeight_ne_zero (lam : ℝ) :
    extendedWienerHopfWeight lam ≠ 0 :=
  ne_of_gt (extendedWienerHopfWeight_pos lam)

/-- The quotient `sinh x / x` with its derivative value inserted at the origin. -/
noncomputable def sinhQuotientExtension (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / x

@[simp] theorem sinhQuotientExtension_zero : sinhQuotientExtension 0 = 1 := by
  simp [sinhQuotientExtension]

/-- The derivative of `sinh` at zero proves that its divided difference has the
continuous value `1` there. -/
theorem continuousAt_sinhQuotientExtension :
    ContinuousAt sinhQuotientExtension 0 := by
  have h := (Real.hasDerivAt_sinh 0).continuousAt_div
  have hupdate :
      sinhQuotientExtension =
        Function.update (fun x : ℝ => (Real.sinh x - Real.sinh 0) / (x - 0)) 0 1 := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [sinhQuotientExtension]
    · simp [sinhQuotientExtension, hx]
  rw [hupdate]
  simpa using h

/-- The reciprocal of the extended `sinh x / x` quotient is continuous at zero. -/
theorem continuousAt_inv_sinhQuotientExtension :
    ContinuousAt (fun x : ℝ => (sinhQuotientExtension x)⁻¹) 0 := by
  exact continuousAt_sinhQuotientExtension.inv₀ (by simp)

/-- The extended Wiener--Hopf weight is exactly the reciprocal extended hyperbolic
sinc evaluated at `pi*lambda`. -/
theorem extendedWienerHopfWeight_eq_inv_sinhQuotient (lam : ℝ) :
    extendedWienerHopfWeight lam =
      (sinhQuotientExtension (Real.pi * lam))⁻¹ := by
  by_cases hlam : lam = 0
  · subst lam
    simp
  · have hpi : Real.pi * lam ≠ 0 := mul_ne_zero Real.pi_ne_zero hlam
    have hs : Real.sinh (Real.pi * lam) ≠ 0 := by
      rcases lt_or_gt_of_ne hlam with hneg | hpos
      · exact (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos hneg)).ne
      · exact (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hpos)).ne'
    rw [extendedWienerHopfWeight_eq hlam]
    simp only [sinhQuotientExtension, if_neg hpi]
    unfold wienerHopfWeight
    field_simp [hpi, hs]

/-- **Removable-singularity closure.** The Wiener--Hopf weight with value `1` at
`lambda=0` is genuinely continuous at the origin. -/
theorem continuousAt_extendedWienerHopfWeight :
    ContinuousAt extendedWienerHopfWeight 0 := by
  rw [show extendedWienerHopfWeight =
      fun lam : ℝ => (sinhQuotientExtension (Real.pi * lam))⁻¹ by
    funext lam
    exact extendedWienerHopfWeight_eq_inv_sinhQuotient lam]
  have hmul : ContinuousAt (fun lam : ℝ => Real.pi * lam) 0 := by
    fun_prop
  exact continuousAt_inv_sinhQuotientExtension.comp_of_eq hmul (by simp)

end GppWienerHopfWeightExtension

#print axioms GppWienerHopfWeightExtension.extendedWienerHopfWeight_zero
#print axioms GppWienerHopfWeightExtension.extendedWienerHopfWeight_eq
#print axioms GppWienerHopfWeightExtension.extendedWienerHopfWeight_pos
#print axioms GppWienerHopfWeightExtension.extendedWienerHopfWeight_ne_zero
#print axioms GppWienerHopfWeightExtension.continuousAt_sinhQuotientExtension
#print axioms GppWienerHopfWeightExtension.extendedWienerHopfWeight_eq_inv_sinhQuotient
#print axioms GppWienerHopfWeightExtension.continuousAt_extendedWienerHopfWeight
