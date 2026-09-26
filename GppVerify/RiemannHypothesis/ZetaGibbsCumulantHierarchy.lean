import GppVerify.RiemannHypothesis.GibbsCumulantDifferentialAlgebra
import GppVerify.RiemannHypothesis.ZetaGibbsFourthCumulant
import GppVerify.RiemannHypothesis.ZetaGibbsThirdCumulantDerivative
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Raw-moment derivative ladder and the exact third-to-fourth cumulant law

On the honest Gibbs half-line `beta > 1`, the unnormalized zeta Gibbs moments form
the canonical exponential-family ladder

  Z'  = -M1,
  M1' = -M2,
  M2' = -M3,
  M3' = -M4.

The abstract quotient-rule algebra in `GibbsCumulantDifferentialAlgebra` therefore
specializes to the genuine zeta Gibbs cumulants:

  kappa_3'(beta) = -kappa_4(beta).

Combined with the independently proved strict decrease of `kappa_3`, this also
proves `kappa_4(beta) > 0` throughout the honest Gibbs half-line.

The same hierarchy gives an exact two-observable fluctuation invariant.  For the
observables `X = log(n+1)` and `X^2`, their covariance determinant is

  kappa_2*kappa_4 + 2*kappa_2^3 - kappa_3^2,

where `kappa_2` is the log-energy variance.  All dependence on the mean cancels.

No analytic continuation of these identities or signs outside `beta > 1` is asserted.
-/

namespace GppZetaGibbsCumulantHierarchy

open Complex LSeries Set Filter
open GppZetaGibbsSummability
open GppZetaGibbsMoments
open GppZetaGibbsMomentBridge
open GppZetaGibbsFisher
open GppZetaGibbsFourthCumulant
open GppGibbsCumulantDifferentialAlgebra
open scoped Topology

private theorem abscissa_one_lt_beta {β : ℝ} (hβ : 1 < β) :
    LSeries.abscissaOfAbsConv (fun _ : ℕ => (1 : ℂ)) < (((β : ℂ).re : ℝ) : EReal) := by
  have hβE : (1 : EReal) < (((β : ℂ).re : ℝ) : EReal) := by
    exact_mod_cast hβ
  exact constant_abscissa_le_one.trans_lt hβE

/-- Partition derivative: `Z' = -M1`. -/
theorem hasDerivAt_Z {β : ℝ} (hβ : 1 < β) :
    HasDerivAt Z (-M1 β) β := by
  have habs := abscissa_one_lt_beta hβ
  have hc := LSeries_hasDerivAt habs
  have hr : HasDerivAt
      (fun x : ℝ => (LSeries (fun _ : ℕ => (1 : ℂ)) (x : ℂ)).re)
      (-(LSeries (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ))).re β :=
    hc.real_of_complex
  have hcoef :
      (-(LSeries (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ))).re = -M1 β := by
    rw [LSeries_logMul_one_eq_ofReal_firstMoment hβ]
    simp [M1]
  rw [hcoef] at hr
  have heq :
      (fun x : ℝ => Z x) =ᶠ[𝓝 β]
        (fun x : ℝ => (LSeries (fun _ : ℕ => (1 : ℂ)) (x : ℂ)).re) := by
    filter_upwards [Ioi_mem_nhds hβ] with x hx
    rw [LSeries_one_eq_ofReal_gibbsWeight_tsum hx]
    simp [Z]
  exact hr.congr_of_eventuallyEq heq

/-- First raw moment derivative: `M1' = -M2`. -/
theorem hasDerivAt_M1 {β : ℝ} (hβ : 1 < β) :
    HasDerivAt M1 (-M2 β) β := by
  have habs0 := abscissa_one_lt_beta hβ
  have habs :
      LSeries.abscissaOfAbsConv (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) <
        (((β : ℂ).re : ℝ) : EReal) := by
    simpa using habs0
  have hc := LSeries_hasDerivAt habs
  have hr : HasDerivAt
      (fun x : ℝ =>
        (LSeries (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (x : ℂ)).re)
      (-(LSeries
        (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))
        (β : ℂ))).re β := hc.real_of_complex
  have hcoef :
      (-(LSeries
        (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))
        (β : ℂ))).re = -M2 β := by
    rw [LSeries_logMul_logMul_one_eq_ofReal_secondMoment hβ]
    simp [M2]
  rw [hcoef] at hr
  have heq :
      (fun x : ℝ => M1 x) =ᶠ[𝓝 β]
        (fun x : ℝ =>
          (LSeries (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (x : ℂ)).re) := by
    filter_upwards [Ioi_mem_nhds hβ] with x hx
    rw [LSeries_logMul_one_eq_ofReal_firstMoment hx]
    simp [M1]
  exact hr.congr_of_eventuallyEq heq

/-- Second raw moment derivative: `M2' = -M3`. -/
theorem hasDerivAt_M2 {β : ℝ} (hβ : 1 < β) :
    HasDerivAt M2 (-M3 β) β := by
  have habs0 := abscissa_one_lt_beta hβ
  have habs :
      LSeries.abscissaOfAbsConv
          (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) <
        (((β : ℂ).re : ℝ) : EReal) := by
    simpa using habs0
  have hc := LSeries_hasDerivAt habs
  have hr : HasDerivAt
      (fun x : ℝ =>
        (LSeries
          (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))
          (x : ℂ)).re)
      (-(LSeries
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))
        (β : ℂ))).re β := hc.real_of_complex
  have hcoef :
      (-(LSeries
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))
        (β : ℂ))).re = -M3 β := by
    rw [LSeries_logMul_logMul_logMul_one_eq_ofReal_thirdMoment hβ]
    simp [M3]
  rw [hcoef] at hr
  have heq :
      (fun x : ℝ => M2 x) =ᶠ[𝓝 β]
        (fun x : ℝ =>
          (LSeries
            (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))
            (x : ℂ)).re) := by
    filter_upwards [Ioi_mem_nhds hβ] with x hx
    rw [LSeries_logMul_logMul_one_eq_ofReal_secondMoment hx]
    simp [M2]
  exact hr.congr_of_eventuallyEq heq

/-- Third raw moment derivative: `M3' = -M4`. -/
theorem hasDerivAt_M3 {β : ℝ} (hβ : 1 < β) :
    HasDerivAt M3 (-M4 β) β := by
  have habs0 := abscissa_one_lt_beta hβ
  have habs :
      LSeries.abscissaOfAbsConv
          (LSeries.logMul
            (LSeries.logMul
              (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))) <
        (((β : ℂ).re : ℝ) : EReal) := by
    simpa using habs0
  have hc := LSeries_hasDerivAt habs
  have hr : HasDerivAt
      (fun x : ℝ =>
        (LSeries
          (LSeries.logMul
            (LSeries.logMul
              (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))
          (x : ℂ)).re)
      (-(LSeries
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul
              (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))))
        (β : ℂ))).re β := hc.real_of_complex
  have hcoef :
      (-(LSeries
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul
              (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))))
        (β : ℂ))).re = -M4 β := by
    rw [LSeries_logMul_four_one_eq_ofReal_fourthMoment hβ]
    simp [M4]
  rw [hcoef] at hr
  have heq :
      (fun x : ℝ => M3 x) =ᶠ[𝓝 β]
        (fun x : ℝ =>
          (LSeries
            (LSeries.logMul
              (LSeries.logMul
                (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))
            (x : ℂ)).re) := by
    filter_upwards [Ioi_mem_nhds hβ] with x hx
    rw [LSeries_logMul_logMul_logMul_one_eq_ofReal_thirdMoment hx]
    simp [M3]
  exact hr.congr_of_eventuallyEq heq

/-- **Exact zeta Gibbs cumulant hierarchy at fourth order**:
`d kappa_3 / d beta = -kappa_4` for every `beta > 1`. -/
theorem hasDerivAt_logEnergyThirdCumulant_eq_neg_fourth
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt logEnergyThirdCumulant (-logEnergyFourthCumulant β) β := by
  have hZne : Z β ≠ 0 := (gibbsWeight_tsum_pos hβ).ne'
  have h := hasDerivAt_kappa3Expr
    (hasDerivAt_Z hβ) (hasDerivAt_M1 hβ) (hasDerivAt_M2 hβ) (hasDerivAt_M3 hβ) hZne
  simpa [kappa3Expr, kappa4Expr, logEnergyThirdCumulant,
    logEnergyFourthCumulant] using h

/-- Derivative-level form of the same identity. -/
theorem deriv_logEnergyThirdCumulant_eq_neg_fourth
    {β : ℝ} (hβ : 1 < β) :
    deriv logEnergyThirdCumulant β = -logEnergyFourthCumulant β :=
  (hasDerivAt_logEnergyThirdCumulant_eq_neg_fourth hβ).deriv

/-- **Strict fourth-cumulant positivity** on the honest zeta Gibbs domain. -/
theorem logEnergyFourthCumulant_pos
    {β : ℝ} (hβ : 1 < β) :
    0 < logEnergyFourthCumulant β := by
  have hneg :=
    GppZetaGibbsThirdCumulantDerivative.deriv_logEnergyThirdCumulant_neg hβ
  rw [deriv_logEnergyThirdCumulant_eq_neg_fourth hβ] at hneg
  linarith

/-- Covariance of the Gibbs observables `X` and `X^2` in normalized raw moments. -/
noncomputable def logEnergySquareCovariance (β : ℝ) : ℝ :=
  M3 β / Z β - (M1 β / Z β) * (M2 β / Z β)

/-- Variance of the squared Gibbs observable `X^2`. -/
noncomputable def logEnergySquareVariance (β : ℝ) : ℝ :=
  M4 β / Z β - (M2 β / Z β) ^ 2

/-- Determinant of the covariance matrix of `X` and `X^2`. -/
noncomputable def logEnergyTwoObservableDet (β : ℝ) : ℝ :=
  logEnergyVariance β * logEnergySquareVariance β -
    (logEnergySquareCovariance β) ^ 2

/-- The mixed covariance is `kappa_3 + 2 mu kappa_2`. -/
theorem logEnergySquareCovariance_eq_cumulants (β : ℝ) :
    logEnergySquareCovariance β =
      logEnergyThirdCumulant β +
        2 * (M1 β / Z β) * logEnergyVariance β := by
  unfold logEnergySquareCovariance logEnergyThirdCumulant logEnergyVariance
  ring

/-- The squared-observable variance in cumulant coordinates. -/
theorem logEnergySquareVariance_eq_cumulants (β : ℝ) :
    logEnergySquareVariance β =
      logEnergyFourthCumulant β +
        4 * (M1 β / Z β) * logEnergyThirdCumulant β +
        4 * (M1 β / Z β) ^ 2 * logEnergyVariance β +
        2 * (logEnergyVariance β) ^ 2 := by
  unfold logEnergySquareVariance logEnergyFourthCumulant
  unfold logEnergyThirdCumulant logEnergyVariance
  ring

/-- **Exact two-observable zeta Gibbs fluctuation invariant.**  The determinant
of the covariance matrix of `X` and `X^2` is independent of the mean and equals
`kappa_2*kappa_4 + 2*kappa_2^3 - kappa_3^2`. -/
theorem logEnergyTwoObservableDet_eq_cumulants (β : ℝ) :
    logEnergyTwoObservableDet β =
      logEnergyVariance β * logEnergyFourthCumulant β +
        2 * (logEnergyVariance β) ^ 3 -
        (logEnergyThirdCumulant β) ^ 2 := by
  unfold logEnergyTwoObservableDet
  rw [logEnergySquareVariance_eq_cumulants,
    logEnergySquareCovariance_eq_cumulants]
  exact covarianceDetFromCumulants_eq
    (M1 β / Z β) (logEnergyVariance β)
      (logEnergyThirdCumulant β) (logEnergyFourthCumulant β)

end GppZetaGibbsCumulantHierarchy

#print axioms GppZetaGibbsCumulantHierarchy.hasDerivAt_Z
#print axioms GppZetaGibbsCumulantHierarchy.hasDerivAt_M1
#print axioms GppZetaGibbsCumulantHierarchy.hasDerivAt_M2
#print axioms GppZetaGibbsCumulantHierarchy.hasDerivAt_M3
#print axioms GppZetaGibbsCumulantHierarchy.hasDerivAt_logEnergyThirdCumulant_eq_neg_fourth
#print axioms GppZetaGibbsCumulantHierarchy.deriv_logEnergyThirdCumulant_eq_neg_fourth
#print axioms GppZetaGibbsCumulantHierarchy.logEnergyFourthCumulant_pos
#print axioms GppZetaGibbsCumulantHierarchy.logEnergySquareCovariance_eq_cumulants
#print axioms GppZetaGibbsCumulantHierarchy.logEnergySquareVariance_eq_cumulants
#print axioms GppZetaGibbsCumulantHierarchy.logEnergyTwoObservableDet_eq_cumulants
