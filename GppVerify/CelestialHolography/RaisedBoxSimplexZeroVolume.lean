import GppVerify.CelestialHolography.RaisedBoxSimplexGammaClosure
import Mathlib.Tactic

/-!
# Raised-box simplex volume at zero regulator

The exact Gamma-ratio majorant family also fixes the zero-regulator normalization.
At `delta = 0` it is the standard affine three-simplex volume:

  Gamma(1)^2 / Gamma(4) = 1/6.
-/

namespace GppRaisedBoxSimplexZeroVolume

open Complex
open GppRaisedBoxSimplexNestedReduction
open GppRaisedBoxSimplexGammaClosure

/-- The nested affine simplex integral at zero singular exponent is exactly `1/6`. -/
theorem nestedSimplexIntegral_zero :
    nestedSimplexIntegral 0 = (1 / 6 : ℂ) := by
  rw [nestedSimplexIntegral_eq_gamma_ratio (by norm_num : (0 : ℝ) < 1)]
  have h1raw := Complex.Gamma_nat_eq_factorial 0
  have h4raw := Complex.Gamma_nat_eq_factorial 3
  have h1 : Gamma (1 : ℂ) = 1 := by
    convert h1raw using 1 <;> norm_num
  have h4 : Gamma (4 : ℂ) = 6 := by
    convert h4raw using 1 <;> norm_num
  norm_num [h1, h4]

end GppRaisedBoxSimplexZeroVolume

#print axioms GppRaisedBoxSimplexZeroVolume.nestedSimplexIntegral_zero
