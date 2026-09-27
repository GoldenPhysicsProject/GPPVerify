import GppVerify.CelestialHolography.WienerHopfWeightExtension
import GppVerify.QuantumGravity.GammaModulusIdentity
import Mathlib.Tactic

/-!
# Gamma-one realization of the extended Wiener--Hopf weight

The raw quotient `pi*lambda/sinh(pi*lambda)` is totalized to zero at `lambda = 0`
in Lean, while its analytic continuation takes the removable value `1`.  The
project's `extendedWienerHopfWeight` already installs and proves continuity of
that value.  This file closes the corresponding Gamma-function identity on the
entire real spectral axis:

  P_ext(lambda) = Gamma(1+i lambda) Gamma(1-i lambda).

Away from zero this is the existing Euler-reflection/Gamma-shift identity.  At
zero both Gamma factors are `Gamma(1)=1`, so the extension matches exactly.
This theorem is about the Wiener--Hopf/Gamma weight; it does not identify that
weight with an `SL(2,C)` Plancherel density.
-/

namespace GppWienerHopfGammaOneExtension

open Complex
open GppWienerHopfWeightExtension

/-- **All-real Gamma-one bridge.** The continuously extended Wiener--Hopf weight
is exactly the principal-series Gamma modulus product for every real spectral
parameter, including the removable point `lambda = 0`. -/
theorem extendedWienerHopfWeight_eq_gamma_one_product (lam : ℝ) :
    ((extendedWienerHopfWeight lam : ℝ) : ℂ) =
      Complex.Gamma (1 + (lam : ℂ) * I) *
        Complex.Gamma (1 - (lam : ℂ) * I) := by
  by_cases hlam : lam = 0
  · subst lam
    simp [extendedWienerHopfWeight]
  · rw [extendedWienerHopfWeight_eq hlam]
    symm
    exact GppGammaModulus.gamma_one_add_mul_gamma_one_sub lam hlam

end GppWienerHopfGammaOneExtension

#print axioms GppWienerHopfGammaOneExtension.extendedWienerHopfWeight_eq_gamma_one_product
