import GppVerify.RiemannHypothesis.ZetaGibbsCumulantHierarchy
import Mathlib.Tactic

/-!
# Strict centered geometry of the zeta Gibbs family

For every real `β > 1`, normalize the genuine Gibbs weights

  p_β(n) = (n+1)^(-β) / Z(β),

and consider the centered observables `X = log(n+1)` and `X^2`.
This file proves that every nonzero linear combination of the two centered
observables has strictly positive normalized mean square.

The analytic input is only absolute summability of the logarithmic moments
through order four.  Strictness is witnessed already by the three support points
`n = 0,1,3`, whose energies are `0, log 2, 2 log 2`.
No analytic continuation outside `β > 1` is used.
-/

namespace GppZetaGibbsCenteredGeometry

open GppZetaGibbsSummability
open GppZetaGibbsFisher

/-- Normalized zeta Gibbs probability on the positive integer `n+1`. -/
noncomputable def gibbsProbability (β : ℝ) (n : ℕ) : ℝ :=
  gibbsWeight β n / Z β

/-- First normalized log-energy moment. -/
noncomputable def meanLog (β : ℝ) : ℝ := M1 β / Z β

/-- Second normalized log-energy moment. -/
noncomputable def meanLogSq (β : ℝ) : ℝ := M2 β / Z β

/-- Centered logarithmic observable. -/
noncomputable def centeredLog (β : ℝ) (n : ℕ) : ℝ :=
  logEnergy n - meanLog β

/-- Centered squared-logarithmic observable. -/
noncomputable def centeredLogSq (β : ℝ) (n : ℕ) : ℝ :=
  (logEnergy n) ^ 2 - meanLogSq β

/-- Every unnormalized Gibbs weight is strictly positive. -/
theorem gibbsWeight_pos (β : ℝ) (n : ℕ) : 0 < gibbsWeight β n := by
  unfold gibbsWeight
  positivity

/-- Every normalized Gibbs probability is strictly positive on the honest Gibbs domain. -/
theorem gibbsProbability_pos {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    0 < gibbsProbability β n := by
  unfold gibbsProbability Z
  exact div_pos (gibbsWeight_pos β n) (gibbsWeight_tsum_pos hβ)

private theorem summable_gibbsWeight_centered_score_sq
    {β a b : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ =>
      gibbsWeight β n *
        (a * centeredLog β n + b * centeredLogSq β n) ^ 2) := by
  let μ1 : ℝ := meanLog β
  let μ2 : ℝ := meanLogSq β
  let c : ℝ := a * μ1 + b * μ2
  have h0 := (summable_gibbsWeight hβ).mul_left (c ^ 2)
  have h1 := (summable_gibbsWeight_mul_logEnergy hβ).mul_left (-2 * a * c)
  have h2 := (summable_gibbsWeight_mul_logEnergy_sq hβ).mul_left (a ^ 2 - 2 * b * c)
  have h3 := (summable_gibbsWeight_mul_logEnergy_cube hβ).mul_left (2 * a * b)
  have h4 := (summable_gibbsWeight_mul_logEnergy_fourth hβ).mul_left (b ^ 2)
  have hs := (((h0.add h1).add h2).add h3).add h4
  refine hs.congr ?_
  intro n
  dsimp [μ1, μ2, c]
  unfold centeredLog centeredLogSq
  ring

/-- The normalized centered quadratic score is summable. -/
theorem summable_gibbsProbability_centered_score_sq
    {β a b : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ =>
      gibbsProbability β n *
        (a * centeredLog β n + b * centeredLogSq β n) ^ 2) := by
  have h := (summable_gibbsWeight_centered_score_sq (β := β) (a := a) (b := b) hβ).div_const (Z β)
  refine h.congr ?_
  intro n
  unfold gibbsProbability
  ring

private theorem logEnergy_zero : logEnergy 0 = 0 := by
  simp [logEnergy]

private theorem logEnergy_one : logEnergy 1 = Real.log (2 : ℝ) := by
  norm_num [logEnergy]

private theorem logEnergy_three : logEnergy 3 = 2 * Real.log (2 : ℝ) := by
  unfold logEnergy
  norm_num
  simpa using (Real.log_pow (2 : ℝ) 2)

/-- A nonzero coefficient pair cannot make the centered quadratic score vanish
simultaneously at the three Gibbs support points `0,1,3`. -/
theorem exists_three_point_score_ne_zero
    {β a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ n : ℕ, n ∈ ({0, 1, 3} : Finset ℕ) ∧
      a * centeredLog β n + b * centeredLogSq β n ≠ 0 := by
  by_contra h
  push_neg at h
  have h0 := h 0 (by simp)
  have h1 := h 1 (by simp)
  have h3 := h 3 (by simp)
  rw [centeredLog, centeredLogSq, logEnergy_zero] at h0
  rw [centeredLog, centeredLogSq, logEnergy_one] at h1
  rw [centeredLog, centeredLogSq, logEnergy_three] at h3
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have e1 :
      a * Real.log (2 : ℝ) + b * (Real.log (2 : ℝ)) ^ 2 = 0 := by
    nlinarith [h0, h1]
  have e3 :
      2 * a * Real.log (2 : ℝ) +
        4 * b * (Real.log (2 : ℝ)) ^ 2 = 0 := by
    nlinarith [h0, h3]
  have eb : b * (Real.log (2 : ℝ)) ^ 2 = 0 := by
    nlinarith [e1, e3]
  have hlog2ne : (Real.log (2 : ℝ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hlog.ne'
  have hb : b = 0 := (mul_eq_zero.mp eb).resolve_right hlog2ne
  have ea : a * Real.log (2 : ℝ) = 0 := by
    simpa [hb] using e1
  have ha : a = 0 := (mul_eq_zero.mp ea).resolve_right hlog.ne'
  exact hab.elim (fun hane => hane ha) (fun hbne => hbne hb)

/-- **Strict centered two-observable zeta Gibbs geometry.**  On every `β > 1`,
every nonzero linear combination of centered `log(n+1)` and `log(n+1)^2` has
strictly positive normalized mean square. -/
theorem normalized_centered_quadratic_pos
    {β a b : ℝ} (hβ : 1 < β) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < ∑' n : ℕ, gibbsProbability β n *
      (a * centeredLog β n + b * centeredLogSq β n) ^ 2 := by
  have hsum :=
    summable_gibbsProbability_centered_score_sq (β := β) (a := a) (b := b) hβ
  rcases exists_three_point_score_ne_zero (β := β) hab with ⟨n, hn, hscore⟩
  apply hsum.tsum_pos
  · intro i
    exact mul_nonneg (gibbsProbability_pos hβ i).le (sq_nonneg _)
  · exact n
  · exact mul_pos (gibbsProbability_pos hβ n) (sq_pos_of_ne_zero hscore)

end GppZetaGibbsCenteredGeometry

#print axioms GppZetaGibbsCenteredGeometry.gibbsProbability_pos
#print axioms GppZetaGibbsCenteredGeometry.summable_gibbsProbability_centered_score_sq
#print axioms GppZetaGibbsCenteredGeometry.exists_three_point_score_ne_zero
#print axioms GppZetaGibbsCenteredGeometry.normalized_centered_quadratic_pos
