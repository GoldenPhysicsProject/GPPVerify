import GppVerify.CelestialHolography.RaisedBoxSimplexGammaClosure
import Mathlib.Tactic

/-!
# Raised-box simplex: zero-regulator normalization

The exact Gamma closure of the nested affine-simplex majorant gives a sharp endpoint check.
At `delta = 0` the singular factors disappear and the integral reduces to the ordinary
three-simplex volume.  The Gamma ratio evaluates exactly to

  Gamma(1)^2 / Gamma(4) = 1 / 6.

This normalization is the endpoint required by the dimensional-regulator dominated-
convergence route; the remaining work is the actual simplex domination/limit theorem.
-/

namespace GppRaisedBoxSimplexZeroRegulator

open Complex
open GppRaisedBoxSimplexNestedReduction
open GppRaisedBoxSimplexGammaClosure

/-- The nested raised-box simplex majorant at zero regulator is exactly `1/6`. -/
theorem nestedSimplexIntegral_zero :
    nestedSimplexIntegral 0 = (1 : ℂ) / 6 := by
  rw [nestedSimplexIntegral_eq_gamma_ratio (δ := 0) (by norm_num)]
  norm_num [Complex.Gamma_ofNat_eq_factorial]

end GppRaisedBoxSimplexZeroRegulator

#print axioms GppRaisedBoxSimplexZeroRegulator.nestedSimplexIntegral_zero
