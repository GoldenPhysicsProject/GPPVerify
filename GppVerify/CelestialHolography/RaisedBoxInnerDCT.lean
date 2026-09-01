import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import GppVerify.CelestialHolography.RaisedBoxRealMajorantSlice
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Raised-box inner dominated-convergence layer

This file isolates the exact Mathlib 4.33 interval-DCT interface needed for the
innermost `x3` slice of the concrete raised-box moment.  It deliberately does
not claim the full simplex limit: measurability, almost-everywhere domination,
and almost-everywhere pointwise convergence on the affine slice remain explicit
hypotheses until they are discharged from the concrete Symanzik geometry.
-/

namespace GppRaisedBoxInnerDCT

open MeasureTheory Filter Real
open scoped Interval Topology
open GppRaisedBoxConcreteMoment

/-- The certified one-channel singular majorant is interval-integrable on every
nonnegative inner affine slice once `δ < 1`.  This removes the bound-integrability
hypothesis from the eventual concrete DCT application. -/
theorem inner_majorant_intervalIntegrable
    {δ S x1 L : ℝ}
    (hδ : δ < 1) (hS : 0 ≤ S) (hx1 : 0 ≤ x1) (hL : 0 ≤ L) :
    IntervalIntegrable
      (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ)) volume 0 L := by
  exact intervalIntegral.intervalIntegrable_const.add
    (GppRaisedBoxRealMajorantSlice.channel_inner_intervalIntegrable hδ hS hx1 hL)

/-- The Mathlib 4.33 interval dominated-convergence theorem specialized to one
raised-box `x3` slice and the certified one-channel majorant.

This is the analytic interface used by the final nested proof.  The conclusion
is genuinely the convergence of the inner physical integral; the remaining
hypotheses are precisely the three a.e. obligations that must be proved on the
simplex slice. -/
theorem inner_integral_tendsto_of_ae_data
    {δ S T x1 x2 L : ℝ}
    (hbound : IntervalIntegrable
      (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ)) volume 0 L)
    (hmeas : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable
        (fun x3 : ℝ => integrand ε S T x1 x2 x3)
        (volume.restrict (Ι (0 : ℝ) L)))
    (hdom : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ᵐ x3 : ℝ ∂volume, x3 ∈ Ι (0 : ℝ) L →
        ‖integrand ε S T x1 x2 x3‖ ≤
          1 + (S * x1 * x3) ^ (-δ : ℝ))
    (hlim : ∀ᵐ x3 : ℝ ∂volume, x3 ∈ Ι (0 : ℝ) L →
      Tendsto (fun ε : ℝ => integrand ε S T x1 x2 x3)
        (𝓝[>] 0) (𝓝 (1 : ℝ))) :
    Tendsto
      (fun ε : ℝ => ∫ x3 in (0 : ℝ)..L, integrand ε S T x1 x2 x3)
      (𝓝[>] 0)
      (𝓝 (∫ _x3 in (0 : ℝ)..L, (1 : ℝ))) := by
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ))
    hmeas hdom hbound hlim

end GppRaisedBoxInnerDCT

#print axioms GppRaisedBoxInnerDCT.inner_majorant_intervalIntegrable
#print axioms GppRaisedBoxInnerDCT.inner_integral_tendsto_of_ae_data
