import GppVerify.RiemannHypothesis.CesaroMeanDivergence
import GppVerify.RiemannHypothesis.RHProofStructure
import Mathlib.Tactic

/-!
# Cesaro boundedness selects the arithmetic principal series

For the symmetric Haar/Cesaro mean of the squared half-density character,

  M_sigma(R) = (1/(2 log R)) int_[1/R,R] r^(2 sigma - 2) dr,

the existing divergence theorem proves `M_sigma(R) -> +infinity` whenever
`sigma != 1/2`, while `born_rule_cesaro` proves `M_{1/2}(R) = 1` for every `R > 1`.

This file packages those two results into an exact admissibility criterion:
`M_sigma` is eventually bounded above if and only if `sigma = 1/2`.

This is a genuine principal-series selection theorem for the scale-invariant Cesaro norm.
It does not identify zeta zeros with admissible characters and therefore does not prove RH.
-/

namespace GppCesaroPrincipalSeriesSelector

open Filter Real

/-- Symmetric Haar/Cesaro mean of the squared half-density character. -/
noncomputable def cesaroMean (sigma R : ℝ) : ℝ :=
  (∫ r in (1 / R)..R, r ^ (2 * sigma - 2)) / (2 * Real.log R)

/-- On the principal series the Cesaro mean is exactly one at every sufficiently large scale. -/
theorem eventually_cesaroMean_eq_one :
    ∀ᶠ R : ℝ in atTop, cesaroMean ((1 : ℝ) / 2) R = 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  unfold cesaroMean
  have hborn := GppRHProofStructure.born_rule_cesaro R hR
  have hpow :
      (fun r : ℝ => r ^ (2 * ((1 : ℝ) / 2) - 2)) = (fun r : ℝ => r⁻¹) := by
    funext r
    norm_num
    exact Real.rpow_neg_one r
  rw [hpow]
  exact hborn

/-- Any eventual finite upper bound forces the principal-series line. -/
theorem critical_of_eventually_bounded
    {sigma M : ℝ}
    (hbound : ∀ᶠ R : ℝ in atTop, cesaroMean sigma R ≤ M) :
    sigma = (1 : ℝ) / 2 := by
  by_contra hsigma
  have hinf : Tendsto (cesaroMean sigma) atTop atTop := by
    unfold cesaroMean
    simpa only [one_div] using GppCesaroMean.tendsto_cesaro_mean_atTop_of_ne hsigma
  have hlower : ∀ᶠ R : ℝ in atTop, M + 1 ≤ cesaroMean sigma R :=
    (tendsto_atTop.1 hinf) (M + 1)
  have hboth : ∀ᶠ R : ℝ in atTop, cesaroMean sigma R ≤ M ∧ M + 1 ≤ cesaroMean sigma R :=
    hbound.and hlower
  rcases hboth.exists with ⟨R, hupper, hlowerR⟩
  linarith

/-- **Principal-series selector.** The symmetric Haar/Cesaro norm is eventually bounded
above exactly on the half-density line `sigma = 1/2`. -/
theorem eventually_bounded_iff_critical (sigma : ℝ) :
    (∃ M : ℝ, ∀ᶠ R : ℝ in atTop, cesaroMean sigma R ≤ M) ↔
      sigma = (1 : ℝ) / 2 := by
  constructor
  · rintro ⟨M, hM⟩
    exact critical_of_eventually_bounded hM
  · intro hsigma
    subst sigma
    refine ⟨1, ?_⟩
    filter_upwards [eventually_cesaroMean_eq_one] with R hR
    rw [hR]

end GppCesaroPrincipalSeriesSelector

#print axioms GppCesaroPrincipalSeriesSelector.eventually_cesaroMean_eq_one
#print axioms GppCesaroPrincipalSeriesSelector.critical_of_eventually_bounded
#print axioms GppCesaroPrincipalSeriesSelector.eventually_bounded_iff_critical
