import GppVerify.CelestialHolography.WienerHopfWeightExtension
import Mathlib.Tactic

/-!
# Reflection symmetry of the extended Wiener--Hopf weight

The analytic spectral density

  P(lambda) = pi lambda / sinh(pi lambda),   P(0)=1,

is even.  This file records that symmetry for the globally positive continuous extension,
so the principal-series spectral measure can be treated on either the full real line or the
nonnegative half-line without a hidden origin exception.
-/

namespace GppWienerHopfWeightSymmetry

open GppMehlerFockSpectral
open GppWienerHopfWeightExtension

/-- The raw Wiener--Hopf weight is even away from the removable singularity. -/
theorem wienerHopfWeight_neg {lam : ℝ} (hlam : lam ≠ 0) :
    wienerHopfWeight (-lam) = wienerHopfWeight lam := by
  unfold wienerHopfWeight
  rw [show Real.pi * (-lam) = -(Real.pi * lam) by ring, Real.sinh_neg]
  ring

/-- **Global reflection symmetry.**  The continuously extended Wiener--Hopf spectral
weight is an even, strictly positive function on the whole real principal series. -/
theorem extendedWienerHopfWeight_neg (lam : ℝ) :
    extendedWienerHopfWeight (-lam) = extendedWienerHopfWeight lam := by
  by_cases hlam : lam = 0
  · subst lam
    simp
  · have hneg : -lam ≠ 0 := neg_ne_zero.mpr hlam
    rw [extendedWienerHopfWeight_eq hneg, extendedWienerHopfWeight_eq hlam]
    exact wienerHopfWeight_neg hlam

/-- Equivalent absolute-value reduction of the spectral density. -/
theorem extendedWienerHopfWeight_abs (lam : ℝ) :
    extendedWienerHopfWeight |lam| = extendedWienerHopfWeight lam := by
  rcases le_total 0 lam with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    exact extendedWienerHopfWeight_neg lam

end GppWienerHopfWeightSymmetry

#print axioms GppWienerHopfWeightSymmetry.extendedWienerHopfWeight_neg
#print axioms GppWienerHopfWeightSymmetry.extendedWienerHopfWeight_abs
