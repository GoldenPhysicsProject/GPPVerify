import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import GppVerify.CelestialHolography.RaisedBoxRealMajorantSlice
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Raised-box inner dominated-convergence layer

This file isolates the exact Mathlib 4.33 interval-DCT interface needed for the
innermost `x3` slice of the concrete raised-box moment.  It deliberately does
not claim the full simplex limit: the eventual domination on the affine slice
remains explicit until it is discharged from the concrete Symanzik geometry.
-/

namespace GppRaisedBoxInnerDCT

open MeasureTheory Filter Real
open scoped Interval Topology
open GppRaisedBoxConcreteMoment

/-- The certified one-channel singular majorant is interval-integrable on every
nonnegative inner affine slice once `δ < 1`. -/
theorem inner_majorant_intervalIntegrable
    {δ S x1 L : ℝ}
    (hδ : δ < 1) (hS : 0 ≤ S) (hx1 : 0 ≤ x1) (hL : 0 ≤ L) :
    IntervalIntegrable
      (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ)) volume 0 L := by
  exact intervalIntegral.intervalIntegrable_const.add
    (GppRaisedBoxRealMajorantSlice.channel_inner_intervalIntegrable hδ hS hx1 hL)

/-- For every fixed regulator, the concrete inner raised-box integrand is
strongly measurable on every interval restriction.  The Symanzik polynomial is
a continuous affine function of `x3`, and real `rpow` is a measurable power. -/
theorem inner_integrand_aestronglyMeasurable
    (ε S T x1 x2 L : ℝ) :
    AEStronglyMeasurable
      (fun x3 : ℝ => integrand ε S T x1 x2 x3)
      (volume.restrict (Ι (0 : ℝ) L)) := by
  have hQ : Continuous (fun x3 : ℝ => Q S T x1 x2 x3) := by
    unfold Q x4
    fun_prop
  have hm : Measurable (fun x3 : ℝ => integrand ε S T x1 x2 x3) := by
    unfold integrand
    exact hQ.measurable.pow_const (-ε)
  exact hm.aestronglyMeasurable

/-- Consequently the measurability hypothesis required by filter-DCT holds
uniformly in the regulator filter. -/
theorem eventually_inner_integrand_aestronglyMeasurable
    (S T x1 x2 L : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable
        (fun x3 : ℝ => integrand ε S T x1 x2 x3)
        (volume.restrict (Ι (0 : ℝ) L)) := by
  filter_upwards with ε
  exact inner_integrand_aestronglyMeasurable ε S T x1 x2 L

/-- On a genuine affine simplex slice `L = 1 - x1 - x2`, every point of the
oriented interval `Ι 0 L` is strictly away from the singular endpoint `x3 = 0`.
The positive `S x1 x3` channel therefore gives pointwise regulator removal even
when the second channel vanishes on the opposite boundary. -/
theorem inner_integrand_tendsto_one_on_interval
    {S T x1 x2 L x3 : ℝ}
    (hS : 0 < S) (hT : 0 ≤ T) (hx1 : 0 < x1) (hx2 : 0 ≤ x2)
    (hLdef : L = 1 - x1 - x2) (hL : 0 ≤ L)
    (hx3mem : x3 ∈ Ι (0 : ℝ) L) :
    Tendsto (fun ε : ℝ => integrand ε S T x1 x2 x3)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
  rw [Set.uIoc_of_le hL] at hx3mem
  have hx3 : 0 < x3 := hx3mem.1
  have hx4 : 0 ≤ x4 x1 x2 x3 := by
    unfold x4
    linarith [hx3mem.2, hLdef]
  unfold integrand Q
  exact
    (GppRaisedBoxPointwiseLimit.symanzik_neg_regulator_tendsto_one
      hS hT hx1 hx2 hx3 hx4).mono_left inf_le_left

/-- Almost-everywhere form of the preceding pointwise statement, in exactly the
shape consumed by interval filter-DCT. -/
theorem ae_inner_integrand_tendsto_one
    {S T x1 x2 L : ℝ}
    (hS : 0 < S) (hT : 0 ≤ T) (hx1 : 0 < x1) (hx2 : 0 ≤ x2)
    (hLdef : L = 1 - x1 - x2) (hL : 0 ≤ L) :
    ∀ᵐ x3 : ℝ ∂volume, x3 ∈ Ι (0 : ℝ) L →
      Tendsto (fun ε : ℝ => integrand ε S T x1 x2 x3)
        (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
  filter_upwards with x3
  intro hx3mem
  exact inner_integrand_tendsto_one_on_interval
    hS hT hx1 hx2 hLdef hL hx3mem

/-- The Mathlib 4.33 interval dominated-convergence theorem specialized to one
raised-box `x3` slice and the certified one-channel majorant.

The conclusion is genuinely the convergence of the inner physical integral;
only the eventual domination obligation remains explicit. -/
theorem inner_integral_tendsto_of_domination
    {δ S T x1 x2 L : ℝ}
    (hbound : IntervalIntegrable
      (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ)) volume 0 L)
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
    (eventually_inner_integrand_aestronglyMeasurable S T x1 x2 L)
    hdom hbound hlim

end GppRaisedBoxInnerDCT

#print axioms GppRaisedBoxInnerDCT.inner_majorant_intervalIntegrable
#print axioms GppRaisedBoxInnerDCT.inner_integrand_aestronglyMeasurable
#print axioms GppRaisedBoxInnerDCT.eventually_inner_integrand_aestronglyMeasurable
#print axioms GppRaisedBoxInnerDCT.inner_integrand_tendsto_one_on_interval
#print axioms GppRaisedBoxInnerDCT.ae_inner_integrand_tendsto_one
#print axioms GppRaisedBoxInnerDCT.inner_integral_tendsto_of_domination
