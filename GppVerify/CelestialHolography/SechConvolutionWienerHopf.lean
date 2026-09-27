import GppVerify.CelestialHolography.SechConvolutionClosedForm
import GppVerify.CelestialHolography.MehlerFockSpectralWeight
import Mathlib.Tactic

/-!
# Shifted-sech convolution as the Wiener--Hopf spectral weight

The exact whole-line shifted-sech self-convolution obtained from the log-cosh
primitive is the project Wiener--Hopf weight with the fixed normalization `2/pi`.
The statement is made away from the removable origin because
`wienerHopfWeight` is currently defined using Lean's totalized division and hence
has value zero at `lam = 0`; a continuous extension should be defined separately.
-/

namespace GppSechConvolutionWienerHopf

open MeasureTheory
open GppSechConvolutionClosedForm
open GppMehlerFockSpectral

/-- For nonzero spectral parameter, the shifted-sech convolution is exactly
`(2/pi)` times the existing Wiener--Hopf spectral weight. -/
theorem integral_sech_convolution_eq_wienerHopfWeight
    {lam : ℝ} (hlam : lam ≠ 0) :
    (∫ x : ℝ,
      1 / (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) =
      (2 / Real.pi) * wienerHopfWeight lam := by
  rw [integral_sech_convolution_eq hlam]
  unfold wienerHopfWeight
  have hsinh : Real.sinh (Real.pi * lam) ≠ 0 := sinh_pi_mul_ne_zero hlam
  field_simp [Real.pi_ne_zero, hsinh]
  ring

end GppSechConvolutionWienerHopf

#print axioms GppSechConvolutionWienerHopf.integral_sech_convolution_eq_wienerHopfWeight
