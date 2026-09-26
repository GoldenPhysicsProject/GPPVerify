import GppVerify.RiemannHypothesis.ZetaGibbsThermodynamicDerivatives
import GppVerify.RiemannHypothesis.ZetaGibbsStrictThermodynamics
import GppVerify.RiemannHypothesis.ZetaGibbsCumulantDerivative
import Mathlib.Tactic

/-!
# Differential entropy law for the zeta Gibbs family

The project already identifies the real-axis Massieu potential and mean log-energy by

  A'(β) = -U(β),    U'(β) = -g(β),

where `g` is the genuine Gibbs variance of `log(n+1)`.  This file packages the corresponding
entropy potential

  S(β) = A(β) + β U(β)

and proves the actual differential identity

  S'(β) = -β g(β).

The cumulant flow `g'(β) = -κ₃(β)` then gives the exact entropy-response curvature

  (S')'(β) = -g(β) + β κ₃(β).

Thus the previously formalized `entropyBetaDerivative` is not merely a response ansatz: it
is the derivative of an explicit entropy potential on the honest Gibbs half-line `β > 1`.
No analytic continuation of this thermodynamic interpretation is asserted.
-/

namespace GppZetaGibbsEntropyDerivative

open GppZetaGibbsFisher
open GppZetaGibbsSummability
open GppZetaGibbsStrictThermodynamics
open GppZetaGibbsThermodynamicDerivatives
open GppZetaGibbsCumulantDerivative

/-- Entropy potential written directly in terms of the real zeta log-partition and mean
log-energy response. -/
noncomputable def zetaEntropy (β : ℝ) : ℝ :=
  zetaLogPartition β + β * zetaMeanEnergy β

/-- The zeta Gibbs partition is at least its `n=0` Gibbs term, which is exactly one. -/
theorem one_le_Z {β : ℝ} (hβ : 1 < β) :
    1 ≤ Z β := by
  have hs : Summable (gibbsWeight β) := summable_gibbsWeight hβ
  have hnonneg : ∀ n : ℕ, 0 ≤ gibbsWeight β n := by
    intro n
    unfold gibbsWeight
    positivity
  have hle := sum_le_tsum ({0} : Finset ℕ)
    (fun n _ => hnonneg n) hs
  simpa [Z, gibbsWeight] using hle

/-- The real zeta log-partition is nonnegative on the honest Gibbs half-line. -/
theorem zetaLogPartition_nonneg {β : ℝ} (hβ : 1 < β) :
    0 ≤ zetaLogPartition β := by
  unfold zetaLogPartition
  rw [zetaPartition_eq_Z hβ]
  exact Real.log_nonneg (one_le_Z hβ)

/-- Every logarithmic energy `log(n+1)` is nonnegative. -/
theorem logEnergy_nonneg (n : ℕ) :
    0 ≤ logEnergy n := by
  unfold logEnergy
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- The unnormalized first logarithmic moment is nonnegative. -/
theorem M1_nonneg (β : ℝ) :
    0 ≤ M1 β := by
  unfold M1
  apply tsum_nonneg
  intro n
  exact mul_nonneg (by unfold gibbsWeight; positivity) (logEnergy_nonneg n)

/-- The zeta Gibbs mean log-energy is nonnegative on `β > 1`. -/
theorem zetaMeanEnergy_nonneg {β : ℝ} (hβ : 1 < β) :
    0 ≤ zetaMeanEnergy β := by
  rw [zetaMeanEnergy_eq_M1_div_Z hβ]
  have hZ : 0 ≤ Z β := by
    simpa [Z] using (gibbsWeight_tsum_pos hβ).le
  exact div_nonneg (M1_nonneg β) hZ

/-- **Entropy positivity.**  The honest zeta Gibbs entropy is nonnegative for every
`β > 1`.  This follows directly from `Z ≥ 1`, nonnegative logarithmic energy, and
`S = log Z + β U`; no thermodynamic sign convention is assumed. -/
theorem zetaEntropy_nonneg {β : ℝ} (hβ : 1 < β) :
    0 ≤ zetaEntropy β := by
  unfold zetaEntropy
  have hβ0 : 0 ≤ β := by linarith
  exact add_nonneg (zetaLogPartition_nonneg hβ)
    (mul_nonneg hβ0 (zetaMeanEnergy_nonneg hβ))

/-- The entropy potential has derivative `-β` times the Gibbs Fisher variance. -/
theorem hasDerivAt_zetaEntropy
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt zetaEntropy (entropyBetaDerivative β) β := by
  have hA := hasDerivAt_zetaLogPartition hβ
  have hU := hasDerivAt_zetaMeanEnergy hβ
  have hS := hA.add ((hasDerivAt_id β).mul hU)
  have hcoef :
      -zetaMeanEnergy β +
          (1 * zetaMeanEnergy β + β * (-logEnergyVariance β)) =
        entropyBetaDerivative β := by
    unfold entropyBetaDerivative
    ring
  rw [← hcoef]
  simpa only [zetaEntropy] using hS

/-- Consequently the zeta Gibbs entropy is strictly decreasing with inverse temperature
throughout the honest Gibbs domain. -/
theorem deriv_zetaEntropy_neg
    {β : ℝ} (hβ : 1 < β) :
    deriv zetaEntropy β < 0 := by
  rw [(hasDerivAt_zetaEntropy hβ).deriv]
  exact entropyBetaDerivative_neg hβ

/-- The derivative of entropy is exactly minus heat capacity divided by inverse
temperature. -/
theorem deriv_zetaEntropy_eq_neg_heatCapacity_div_beta
    {β : ℝ} (hβ : 1 < β) :
    deriv zetaEntropy β = -heatCapacity β / β := by
  rw [(hasDerivAt_zetaEntropy hβ).deriv]
  exact entropyBetaDerivative_eq_neg_heatCapacity_div_beta (by linarith)

/-- The positive entropy-loss rate recovers heat capacity after multiplication by `β`. -/
theorem heatCapacity_eq_neg_beta_mul_deriv_zetaEntropy
    {β : ℝ} (hβ : 1 < β) :
    heatCapacity β = -β * deriv zetaEntropy β := by
  rw [(hasDerivAt_zetaEntropy hβ).deriv]
  exact heatCapacity_eq_neg_beta_mul_entropyBetaDerivative β

/-- **Exact entropy-response curvature law.**  Differentiating
`S'(β) = -β κ₂(β)` and using `κ₂'(β) = -κ₃(β)` gives

`(S')'(β) = -κ₂(β) + β κ₃(β)`.

No sign is asserted: variance and skewness compete. -/
theorem hasDerivAt_entropyBetaDerivative
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt entropyBetaDerivative
      (-logEnergyVariance β + β * logEnergyThirdCumulant β) β := by
  have hvar := hasDerivAt_logEnergyVariance hβ
  have hprod :
      HasDerivAt
        (fun y : ℝ => y * logEnergyVariance y)
        (logEnergyVariance β + β * (-logEnergyThirdCumulant β)) β := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id β).mul hvar
  have hneg := hprod.neg
  unfold entropyBetaDerivative
  convert hneg using 1 <;> ring

/-- Derivative form of the entropy-response curvature identity. -/
theorem deriv_entropyBetaDerivative
    {β : ℝ} (hβ : 1 < β) :
    deriv entropyBetaDerivative β =
      -logEnergyVariance β + β * logEnergyThirdCumulant β := by
  exact (hasDerivAt_entropyBetaDerivative hβ).deriv

end GppZetaGibbsEntropyDerivative

#print axioms GppZetaGibbsEntropyDerivative.one_le_Z
#print axioms GppZetaGibbsEntropyDerivative.zetaLogPartition_nonneg
#print axioms GppZetaGibbsEntropyDerivative.logEnergy_nonneg
#print axioms GppZetaGibbsEntropyDerivative.M1_nonneg
#print axioms GppZetaGibbsEntropyDerivative.zetaMeanEnergy_nonneg
#print axioms GppZetaGibbsEntropyDerivative.zetaEntropy_nonneg
#print axioms GppZetaGibbsEntropyDerivative.hasDerivAt_zetaEntropy
#print axioms GppZetaGibbsEntropyDerivative.deriv_zetaEntropy_neg
#print axioms GppZetaGibbsEntropyDerivative.deriv_zetaEntropy_eq_neg_heatCapacity_div_beta
#print axioms GppZetaGibbsEntropyDerivative.heatCapacity_eq_neg_beta_mul_deriv_zetaEntropy
#print axioms GppZetaGibbsEntropyDerivative.hasDerivAt_entropyBetaDerivative
#print axioms GppZetaGibbsEntropyDerivative.deriv_entropyBetaDerivative
