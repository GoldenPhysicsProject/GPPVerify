import GppVerify.QuantumGravity.CausalDiamondFisherCancellation
import GppVerify.QuantumGravity.GammaModulusIdentity
import Mathlib.Tactic

/-!
# Causal-diamond Fisher kernel = principal-series Gamma modulus

At the Bisognano--Wichmann temperature the Kubo--Mori kernel is not merely
similar to the Gamma-family weight: away from its removable zero it is exactly

  Gamma(1+i lam) Gamma(1-i lam) = pi lam / sinh(pi lam).

Consequently the exact flattening of the Kontorovich--Lebedev density can be
read equivalently as multiplication by the principal-series Gamma modulus.
-/

namespace GppCausalDiamondGammaBridge

open Complex
open GppCausalDiamondFisher
open GppGammaModulus

/-- The Bisognano--Wichmann Fisher kernel is exactly the principal-series Gamma
modulus squared, viewed as a real scalar inside `C`. -/
theorem gamma_modulus_eq_bwFisherKernel (lam : ℝ) (hlam : lam ≠ 0) :
    Complex.Gamma (1 + (lam : ℂ) * I) *
      Complex.Gamma (1 - (lam : ℂ) * I)
      = ((bwFisherKernel lam : ℝ) : ℂ) := by
  simpa [bwFisherKernel] using
    gamma_one_add_mul_gamma_one_sub lam hlam

/-- The KL Plancherel density times the Gamma modulus is exactly the flat
quadratic Fisher weight. -/
theorem klDensity_mul_gamma_modulus
    (lam : ℝ) (hlam : lam ≠ 0) :
    ((klDensity lam : ℝ) : ℂ) *
        (Complex.Gamma (1 + (lam : ℂ) * I) *
          Complex.Gamma (1 - (lam : ℂ) * I))
      = (((2 / Real.pi) * lam^2 : ℝ) : ℂ) := by
  have hsinh : Real.sinh (Real.pi * lam) ≠ 0 := by
    exact Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hlam)
  rw [gamma_modulus_eq_bwFisherKernel lam hlam]
  have hreal := klDensity_mul_bwFisherKernel lam hsinh
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hreal
  simpa only [Complex.ofReal_mul] using hcast

end GppCausalDiamondGammaBridge

#print axioms GppCausalDiamondGammaBridge.gamma_modulus_eq_bwFisherKernel
#print axioms GppCausalDiamondGammaBridge.klDensity_mul_gamma_modulus
