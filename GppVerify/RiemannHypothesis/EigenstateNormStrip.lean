import GppVerify.RiemannHypothesis.SechFourthIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The eigenstate norms `N_σ` are finite and positive across the strip

Thread A1 of `docs/FORMALIZATION_PLAN.md`: for every `σ > 0` (in particular throughout the
critical strip `0 < σ < 1`), the Yakaboylu eigenstate norm

  `N_σ = (1/16) ∫₀^∞ t^{2σ}/cosh⁴(t/2) dt`

is given by a **genuinely convergent** integral with a **strictly positive** value — the
fact on which Theorem 3.5's square-integrability claim (arXiv:2408.15135v14) and the
norm formula of rh_cesaro_v2 Proposition 5.1 rest.

* Integrability (`integrableOn_eigenstateNorm_integrand`): the squared decay bound
  `1/cosh⁴(t/2) ≤ 16·e^{−2t}` (squaring Thread A2's `1/cosh² ≤ 4e^{−2·}` at `t/2`)
  dominates the integrand by `16·e^{−t}·t^{(2σ+1)−1}`, the Euler Gamma integrand at
  `s = 2σ+1` (`Real.GammaIntegral_convergent`).
* Positivity (`eigenstateNorm_pos`): the integrand is strictly positive on `(0,∞)`, so its
  support meets `(0,∞)` in a set of infinite Lebesgue measure
  (`setIntegral_pos_iff_support_of_nonneg_ae` + `Real.volume_Ioi`).
* Consistency (`eigenstateNorm_at_half`): at `σ = 1/2` the abstract norm reduces to
  Thread A2's exact value `log 2/6 − 1/24` — the two threads agree on the nose.
-/

namespace GppSechIntegral

open Filter MeasureTheory Set Function

/-- Squared decay bound in the `t`-variable: `1/cosh⁴(t/2) ≤ 16·e^{−2t}`. -/
theorem one_div_cosh_fourth_le (t : ℝ) :
    1 / Real.cosh (t/2) ^ 4 ≤ 16 * Real.exp (-(2 * t)) := by
  have h := one_div_cosh_sq_le (t/2)
  rw [show 2 * (t/2) = t by ring] at h
  have h0 : (0 : ℝ) ≤ 1 / Real.cosh (t/2) ^ 2 := by positivity
  calc 1 / Real.cosh (t/2) ^ 4 = (1 / Real.cosh (t/2) ^ 2) ^ 2 := by ring
    _ ≤ (4 * Real.exp (-t)) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 16 * (Real.exp (-t) * Real.exp (-t)) := by ring
    _ = 16 * Real.exp (-(2 * t)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **Convergence across the strip**: for `σ > 0` the norm integrand is integrable on
    `(0,∞)`, dominated by `16` times the Euler Gamma integrand at `s = 2σ+1`. -/
theorem integrableOn_eigenstateNorm_integrand {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (2*σ) / Real.cosh (t/2) ^ 4) (Ioi (0:ℝ)) := by
  have hg : IntegrableOn (fun t : ℝ => 16 * (Real.exp (-t) * t ^ (2*σ + 1 - 1)))
      (Ioi (0:ℝ)) :=
    (Real.GammaIntegral_convergent (by linarith : (0:ℝ) < 2*σ + 1)).const_mul 16
  refine hg.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.div
    · exact continuous_id.rpow_const fun x => Or.inr (by positivity)
    · exact (Real.continuous_cosh.comp (continuous_id.div_const 2)).pow 4
    · intro x
      positivity
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply Filter.Eventually.of_forall
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have hnum : (0:ℝ) ≤ t ^ (2*σ) := Real.rpow_nonneg ht'.le _
    have hf_nonneg : (0:ℝ) ≤ t ^ (2*σ) / Real.cosh (t/2) ^ 4 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hf_nonneg]
    calc t ^ (2*σ) / Real.cosh (t/2) ^ 4
        = t ^ (2*σ) * (1 / Real.cosh (t/2) ^ 4) := by ring
      _ ≤ t ^ (2*σ) * (16 * Real.exp (-(2*t))) :=
          mul_le_mul_of_nonneg_left (one_div_cosh_fourth_le t) hnum
      _ ≤ t ^ (2*σ) * (16 * Real.exp (-t)) := by
          apply mul_le_mul_of_nonneg_left _ hnum
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 16)
          exact Real.exp_le_exp.mpr (by linarith)
      _ = 16 * (Real.exp (-t) * t ^ (2*σ + 1 - 1)) := by
          rw [show 2*σ + 1 - 1 = 2*σ by ring]
          ring

/-- **The eigenstate norm `N_σ`**, as in rh_cesaro_v2 Proposition 5.1. -/
noncomputable def eigenstateNorm (σ : ℝ) : ℝ :=
  1/16 * ∫ t in Ioi (0:ℝ), t ^ (2*σ) / Real.cosh (t/2) ^ 4

/-- The norm integral is strictly positive for `σ > 0`: the integrand is positive on all
    of `(0,∞)`, which has infinite measure. -/
theorem eigenstateNorm_integral_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < ∫ t in Ioi (0:ℝ), t ^ (2*σ) / Real.cosh (t/2) ^ 4 := by
  have hfi := integrableOn_eigenstateNorm_integrand hσ
  have hae : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun t : ℝ => t ^ (2*σ) / Real.cosh (t/2) ^ 4 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : (0:ℝ) < t := ht
    simp only [Pi.zero_apply]
    positivity
  rw [setIntegral_pos_iff_support_of_nonneg_ae hae hfi]
  have hsub : Ioi (0:ℝ) ⊆ support fun t : ℝ => t ^ (2*σ) / Real.cosh (t/2) ^ 4 := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    rw [Function.mem_support]
    have hpos : (0:ℝ) < t ^ (2*σ) / Real.cosh (t/2) ^ 4 := by positivity
    exact hpos.ne'
  rw [Set.inter_eq_self_of_subset_right hsub, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- **`N_σ > 0` for every `σ > 0`** — the eigenstate norms are genuine, finite, strictly
    positive quantities throughout the critical strip. -/
theorem eigenstateNorm_pos {σ : ℝ} (hσ : 0 < σ) : 0 < eigenstateNorm σ :=
  mul_pos (by norm_num) (eigenstateNorm_integral_pos hσ)

/-- **Consistency with Thread A2**: at the critical point the abstract norm reduces to
    the exact closed form, `N_{1/2} = log 2/6 − 1/24`. -/
theorem eigenstateNorm_at_half : eigenstateNorm (1/2) = Real.log 2 / 6 - 1/24 := by
  have hpt : ∀ t : ℝ, t ^ (2*(1/2:ℝ)) = t := by
    intro t
    rw [show 2*(1/2:ℝ) = 1 by norm_num, Real.rpow_one]
  show 1/16 * ∫ t in Ioi (0:ℝ), t ^ (2*(1/2:ℝ)) / Real.cosh (t/2) ^ 4 = _
  simp_rw [hpt]
  exact eigenstate_norm_half

end GppSechIntegral
