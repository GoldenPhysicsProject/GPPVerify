import GppVerify.CelestialHolography.Mu4DimensionShiftAlgebra
import GppVerify.CelestialHolography.GammaResidueAtZero
import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import GppVerify.CelestialHolography.RaisedBoxSimplexZeroVolume
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Raised-box residue assembly

For the dimension-shifted four-dimensional scalar box, the only remaining analytic input
needed for the finite `mu^4` rational term is the simplex moment

  simplexMoment(eps) -> 1/6.

A Feynman-parameter derivation factors the raised-dimensional integral as

  I8(eps) = Gamma(eps) * simplexMoment(eps).

`GammaResidueAtZero.lean` proves the Gamma-pole input

  eps * Gamma(eps) -> 1.

The concrete Feynman-parametric moment is now defined in
`RaisedBoxConcreteMoment.lean`, with

  Q = S x1 x3 + T x2 x4,
  x4 = 1 - x1 - x2 - x3,

on the standard affine three-simplex.  `RaisedBoxSimplexZeroVolume.lean`
independently certifies the reduced zero-regulator simplex normalization `1/6`.
Thus the remaining physics-side analytic target is precisely dominated convergence
for that concrete moment.  The positive-regulator specializations below align this
assembly with the one-sided DCT domain `eps -> 0+` used by the majorant.
-/

namespace GppRaisedBoxResidueAssembly

open Filter Set
open scoped Topology
open GppMu4DimensionShift
open GppGammaResidueAtZero
open GppRaisedBoxConcreteMoment

/-- Product assembly for the scaled raised-box residue. -/
theorem tendsto_scaledRaisedBox_of_gamma_simplex
    {gammaFactor simplexMoment : ℝ → ℝ} {l : Filter ℝ}
    (hgamma : Tendsto (fun ε : ℝ => ε * gammaFactor ε) l (nhds 1))
    (hsimplex : Tendsto simplexMoment l (nhds (1 / 6 : ℝ))) :
    Tendsto
      (fun ε : ℝ => ε * (gammaFactor ε * simplexMoment ε))
      l (nhds (1 / 6 : ℝ)) := by
  have hmul := hgamma.mul hsimplex
  convert hmul using 1
  · funext ε
    ring
  · ring

/-- If the raised-dimensional box is pointwise represented by a Gamma factor times
its simplex moment, the same two analytic limits imply the exact scaled residue. -/
theorem tendsto_scaledRaisedBox_of_factorization
    {I gammaFactor simplexMoment : ℝ → ℝ} {l : Filter ℝ}
    (hI : ∀ ε, I ε = gammaFactor ε * simplexMoment ε)
    (hgamma : Tendsto (fun ε : ℝ => ε * gammaFactor ε) l (nhds 1))
    (hsimplex : Tendsto simplexMoment l (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => ε * I ε) l (nhds (1 / 6 : ℝ)) := by
  have h := tendsto_scaledRaisedBox_of_gamma_simplex hgamma hsimplex
  convert h using 1
  funext ε
  rw [hI ε]

/-- **Real-Gamma specialization.** Once the actual raised box is represented as
`Gamma(eps) * simplexMoment(eps)`, the Gamma-pole part is no longer a hypothesis:
only the simplex-volume limit remains. -/
theorem tendsto_scaledRaisedBox_realGamma_of_simplex
    {I simplexMoment : ℝ → ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε)
    (hsimplex : Tendsto simplexMoment
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => ε * I ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ)) := by
  exact tendsto_scaledRaisedBox_of_factorization hI
    tendsto_mul_realGamma_zero hsimplex

/-- **Positive-regulator Real-Gamma specialization.**  On `eps -> 0+`, the Gamma
residue is already certified, so only the one-sided simplex DCT remains. -/
theorem tendsto_scaledRaisedBox_realGamma_pos_of_simplex
    {I simplexMoment : ℝ → ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε)
    (hsimplex : Tendsto simplexMoment (𝓝[>] 0) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => ε * I ε) (𝓝[>] 0) (nhds (1 / 6 : ℝ)) := by
  exact tendsto_scaledRaisedBox_of_factorization hI
    tendsto_mul_realGamma_zero_pos hsimplex

/-- **Concrete Feynman-parametric specialization.** For fixed Euclidean chamber
parameters `S,T`, once the concrete moment from `RaisedBoxConcreteMoment` is shown
to tend to the simplex volume `1/6`, the scaled raised box has residue `1/6`.
This theorem makes the sole remaining analytic obligation explicit. -/
theorem tendsto_scaledRaisedBox_realGamma_of_concreteMoment
    {I : ℝ → ℝ} {S T : ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε S T)
    (hsimplex : Tendsto (fun ε => simplexMoment ε S T)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => ε * I ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ)) := by
  exact tendsto_scaledRaisedBox_realGamma_of_simplex hI hsimplex

/-- Concrete positive-regulator specialization matching the one-channel majorant domain. -/
theorem tendsto_scaledRaisedBox_realGamma_pos_of_concreteMoment
    {I : ℝ → ℝ} {S T : ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε S T)
    (hsimplex : Tendsto (fun ε => simplexMoment ε S T)
      (𝓝[>] 0) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => ε * I ε) (𝓝[>] 0) (nhds (1 / 6 : ℝ)) := by
  exact tendsto_scaledRaisedBox_realGamma_pos_of_simplex hI hsimplex

/-- **Complete algebraic route to the finite `mu^4` rational term.** Once the
Feynman-parameter factorization, Gamma residue, and simplex-volume limit are
available, the dimension-shifted product tends to `-1/6`. -/
theorem tendsto_mu4_rational_of_gamma_simplex
    {I gammaFactor simplexMoment : ℝ → ℝ} {l : Filter ℝ}
    (hε : Tendsto (fun ε : ℝ => ε) l (nhds 0))
    (hI : ∀ ε, I ε = gammaFactor ε * simplexMoment ε)
    (hgamma : Tendsto (fun ε : ℝ => ε * gammaFactor ε) l (nhds 1))
    (hsimplex : Tendsto simplexMoment l (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => shiftFactor ε * I ε) l (nhds (-(1 / 6 : ℝ))) := by
  apply tendsto_shiftFactor_mul_of_scaledResidue hε
  exact tendsto_scaledRaisedBox_of_factorization hI hgamma hsimplex

/-- **Real-Gamma `mu^4` closure.** On the punctured real regulator neighborhood,
the sole remaining analytic hypothesis is the simplex moment tending to `1/6`. -/
theorem tendsto_mu4_rational_realGamma_of_simplex
    {I simplexMoment : ℝ → ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε)
    (hsimplex : Tendsto simplexMoment
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => shiftFactor ε * I ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-(1 / 6 : ℝ))) := by
  apply tendsto_shiftFactor_mul_of_scaledResidue
    (tendsto_id.mono_left inf_le_left)
  exact tendsto_scaledRaisedBox_realGamma_of_simplex hI hsimplex

/-- **Positive-regulator `mu^4` closure.**  Once the actual simplex DCT is proved on
`eps -> 0+`, the existing dimension-shift algebra gives the finite rational residue
without strengthening the DCT to an unnecessary two-sided regulator limit. -/
theorem tendsto_mu4_rational_realGamma_pos_of_simplex
    {I simplexMoment : ℝ → ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε)
    (hsimplex : Tendsto simplexMoment (𝓝[>] 0) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => shiftFactor ε * I ε)
      (𝓝[>] 0) (nhds (-(1 / 6 : ℝ))) := by
  exact tendsto_mu4_rational_of_gamma_simplex
    (tendsto_id.mono_left inf_le_left) hI
    tendsto_mul_realGamma_zero_pos hsimplex

/-- Concrete `mu^4` specialization: the only remaining hypothesis is the DCT
limit for the actual Symanzik simplex moment. -/
theorem tendsto_mu4_rational_realGamma_of_concreteMoment
    {I : ℝ → ℝ} {S T : ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε S T)
    (hsimplex : Tendsto (fun ε => simplexMoment ε S T)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => shiftFactor ε * I ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-(1 / 6 : ℝ))) := by
  exact tendsto_mu4_rational_realGamma_of_simplex hI hsimplex

/-- Concrete positive-regulator closure: after the one-sided simplex DCT, the physical
`mu^4` rational term is exactly `-1/6`. -/
theorem tendsto_mu4_rational_realGamma_pos_of_concreteMoment
    {I : ℝ → ℝ} {S T : ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε S T)
    (hsimplex : Tendsto (fun ε => simplexMoment ε S T)
      (𝓝[>] 0) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => shiftFactor ε * I ε)
      (𝓝[>] 0) (nhds (-(1 / 6 : ℝ))) := by
  exact tendsto_mu4_rational_realGamma_pos_of_simplex hI hsimplex

end GppRaisedBoxResidueAssembly

#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_of_gamma_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_of_factorization
#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_realGamma_of_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_realGamma_pos_of_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_realGamma_of_concreteMoment
#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_realGamma_pos_of_concreteMoment
#print axioms GppRaisedBoxResidueAssembly.tendsto_mu4_rational_of_gamma_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_mu4_rational_realGamma_of_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_mu4_rational_realGamma_pos_of_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_mu4_rational_realGamma_of_concreteMoment
#print axioms GppRaisedBoxResidueAssembly.tendsto_mu4_rational_realGamma_pos_of_concreteMoment
