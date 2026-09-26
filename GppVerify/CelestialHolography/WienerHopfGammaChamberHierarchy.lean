import GppVerify.CelestialHolography.WienerHopfGammaBridge
import GppVerify.QuantumGravity.SpectralRhoRecurrence
import Mathlib.Tactic

/-!
# Wiener--Hopf bridge through the full Gamma chamber hierarchy

The base bridge identifies the continuously extended Wiener--Hopf weight with the
normalized `k=0` Gamma/Mehler--Fock chamber.  The exact chamber recurrence then
propagates that identification to every `k` by a finite product of positive step
factors.

No convolution theorem is assumed here: this is the exact algebraic closure of
base normalization plus the already-proved Gamma recurrence.
-/

namespace GppWienerHopfGammaChamberHierarchy

open GppWienerHopfWeightExtension
open GppWienerHopfGammaBridge
open GppSpectralRho

/-- Every normalized Gamma chamber is the base chamber multiplied by the finite
product of recurrence factors encountered on the way from `0` to `k`. -/
theorem rhoGamma_eq_prod_stepFactor_mul_base (k : ℕ) (x : ℝ) :
    rhoGamma k x =
      (((∏ j in Finset.range k, rhoStepFactor j x : ℝ) : ℝ) : ℂ) * rhoGamma 0 x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [rhoGamma_succ, ih, Finset.prod_range_succ]
      unfold rhoStepFactor
      push_cast
      ring

/-- Taking real parts and inserting the global Wiener--Hopf/base-chamber bridge
gives an exact formula for the real spectral density in every chamber. -/
theorem rhoGamma_re_eq_prod_stepFactor_mul_wienerHopf (k : ℕ) (x : ℝ) :
    (rhoGamma k x).re =
      (∏ j in Finset.range k, rhoStepFactor j x) *
        ((2 / Real.pi) * extendedWienerHopfWeight x) := by
  rw [rhoGamma_eq_prod_stepFactor_mul_base]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [rhoGamma_zero_re_eq_two_over_pi_mul_extendedWienerHopfWeight]

/-- The full chamber multiplier relative to the Wiener--Hopf base is strictly
positive. -/
theorem prod_rhoStepFactor_pos (k : ℕ) (x : ℝ) :
    0 < ∏ j in Finset.range k, rhoStepFactor j x := by
  exact Finset.prod_pos fun j _ => rhoStepFactor_pos j x

/-- **Strict positivity in every Gamma chamber.**  The continuously extended
Wiener--Hopf base weight is positive on the whole real axis, and every recurrence
step contributes a positive factor.  Hence the real part of every normalized
Gamma/Mehler--Fock chamber is strictly positive, including at the removable
origin. -/
theorem rhoGamma_re_pos (k : ℕ) (x : ℝ) :
    0 < (rhoGamma k x).re := by
  rw [rhoGamma_re_eq_prod_stepFactor_mul_wienerHopf]
  have hprod : 0 < ∏ j in Finset.range k, rhoStepFactor j x :=
    prod_rhoStepFactor_pos k x
  have hpi : 0 < (2 : ℝ) / Real.pi := div_pos (by norm_num) Real.pi_pos
  have hwh : 0 < extendedWienerHopfWeight x := extendedWienerHopfWeight_pos x
  positivity

end GppWienerHopfGammaChamberHierarchy

#print axioms GppWienerHopfGammaChamberHierarchy.rhoGamma_eq_prod_stepFactor_mul_base
#print axioms GppWienerHopfGammaChamberHierarchy.rhoGamma_re_eq_prod_stepFactor_mul_wienerHopf
#print axioms GppWienerHopfGammaChamberHierarchy.prod_rhoStepFactor_pos
#print axioms GppWienerHopfGammaChamberHierarchy.rhoGamma_re_pos
