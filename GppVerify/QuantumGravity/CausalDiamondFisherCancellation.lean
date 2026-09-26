import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Exact Fisher/Plancherel cancellation for the causal diamond

The Kontorovich--Lebedev density of the radial boost is

  rho(lam) = (2/pi^2) lam sinh(pi lam),

while the KMS-symmetric Kubo--Mori kernel at the Bisognano--Wichmann inverse
temperature beta=2*pi is

  kappa(lam) = pi lam / sinh(pi lam).

Away from the removable point lam=0 their product is exactly

  (2/pi) lam^2.
-/

namespace GppCausalDiamondFisher

noncomputable def klDensity (lam : ℝ) : ℝ :=
  (2 / Real.pi^2) * lam * Real.sinh (Real.pi * lam)

noncomputable def bwFisherKernel (lam : ℝ) : ℝ :=
  (Real.pi * lam) / Real.sinh (Real.pi * lam)

/-- Exact cancellation of the hyperbolic thermal factors. -/
theorem klDensity_mul_bwFisherKernel
    (lam : ℝ) (hsinh : Real.sinh (Real.pi * lam) ≠ 0) :
    klDensity lam * bwFisherKernel lam = (2 / Real.pi) * lam^2 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold klDensity bwFisherKernel
  field_simp [hsinh, hpi]
  ring

/-- The polynomialized Fisher weight has an exact double zero at the trivial spectral point. -/
theorem flatFisherWeight_zero :
    (2 / Real.pi) * (0 : ℝ)^2 = 0 := by
  ring

/-- Its coefficient is strictly positive. -/
theorem flatFisherWeight_coeff_pos : 0 < (2 / Real.pi : ℝ) := by
  positivity

end GppCausalDiamondFisher

#print axioms GppCausalDiamondFisher.klDensity_mul_bwFisherKernel
#print axioms GppCausalDiamondFisher.flatFisherWeight_zero
#print axioms GppCausalDiamondFisher.flatFisherWeight_coeff_pos
