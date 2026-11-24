import GppVerify.RiemannHypothesis.BNBounded

/-!
# `t_N(0) − θ(N) = o(θ(N))`: the weighted-Cesàro little-o (Turbo's build-order step (4))

`t_N(0) − θ(N) = Σ_{p≤N} (log p) · 2q_p/(1 − q_p)` exactly (`tN0_sub_theta`), `q_p = p^{−1/2}`. The weights
`2q_p/(1 − q_p) → 0`, and `θ(N) → ∞` (`theta_unbounded`), so the Cesàro-type average tends to `0`
(`tN0_sub_theta_le`): for every `ε > 0` there is `N₀` with `t_N(0) − θ(N) ≤ ε θ(N)` for `N ≥ N₀`.
Elementary: split at a prime bound `P` beyond which the weight is `≤ ε/2`; the head is a fixed constant,
absorbed once `θ(N) ≥ 2 S_P/ε`. No prime number theorem; only `θ(N) → ∞`.

No `sorry`, no axiom.
-/

open MeasureTheory
open GppArithmeticReflection

noncomputable section

namespace GppShiftPresentation

/-- The weight `c_p = 2 q_p / (1 − q_p)`. -/
def cWeight (p : ℕ) : ℝ := 2 * qOf p / (1 - qOf p)

theorem cWeight_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ cWeight p := by
  have := qOf_pos hp; have := qOf_lt_one hp
  unfold cWeight
  exact div_nonneg (by linarith) (by linarith)

/-- `t_N(0) − θ(N) = Σ_{p≤N} (log p) · 2q_p/(1 − q_p)`. -/
theorem tN0_sub_theta (N : ℕ) :
    tN0 N - thetaN N = ∑ p ∈ primesUpTo N, Real.log p * cWeight p := by
  rw [tN0_eq]
  unfold thetaN cWeight
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
  have hq1 := qOf_lt_one hp2
  have hne : (1 - qOf p) ≠ 0 := by linarith
  field_simp
  ring

/-- The weights are eventually `≤ ε`. -/
theorem cWeight_small {ε : ℝ} (hε : 0 < ε) : ∃ P : ℕ, ∀ p : ℕ, P ≤ p → 2 ≤ p → cWeight p ≤ ε := by
  set δ : ℝ := min (1 / 2) (ε / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε / 4 := min_le_right _ _
  refine ⟨⌈1 / δ ^ 2⌉₊, fun p hP hp2 => ?_⟩
  have hq0 := qOf_pos hp2
  have hq1 := qOf_lt_one hp2
  have hpge : 1 / δ ^ 2 ≤ (p : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hP)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq2 : qOf p ^ 2 ≤ δ ^ 2 := by
    rw [qOf_sq hp2, div_le_iff₀ hp0]
    rw [div_le_iff₀ (by positivity)] at hpge
    nlinarith
  have hqδ : qOf p ≤ δ := (sq_le_sq₀ hq0.le hδ0.le).mp hq2
  have hq12 : qOf p ≤ 1 / 2 := hqδ.trans hδ1
  unfold cWeight
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The weighted-Cesàro little-o:** `t_N(0) − θ(N) ≤ ε θ(N)` for large `N`. -/
theorem tN0_sub_theta_le {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, tN0 N - thetaN N ≤ ε * thetaN N := by
  obtain ⟨P, hP⟩ := cWeight_small (ε := ε / 2) (by linarith)
  set f : ℕ → ℝ := fun p => if 2 ≤ p ∧ p < P then Real.log p * cWeight p else 0 with hf
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    simp only [hf]
    split_ifs with h
    · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))
        (cWeight_nonneg h.1)
    · exact le_rfl
  set S : ℝ := ∑ p ∈ Finset.range P, f p with hS
  obtain ⟨N₁, hN₁⟩ := theta_unbounded (2 * S / ε)
  refine ⟨max N₁ P, fun N hN => ?_⟩
  have hNP : P ≤ N := le_of_max_le_right hN
  have hθ : 2 * S / ε ≤ thetaN N := hN₁ N (le_of_max_le_left hN)
  have hpt : ∀ p ∈ primesUpTo N, Real.log p * cWeight p ≤ f p + ε / 2 * Real.log p := by
    intro p hp
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    by_cases hlt : p < P
    · have : f p = Real.log p * cWeight p := by simp [hf, hp2, hlt]
      rw [this]; nlinarith
    · have : f p = 0 := by simp [hf, hlt]
      rw [this, zero_add]
      exact mul_le_mul_of_nonneg_left (hP p (not_lt.mp hlt) hp2) hlog |>.trans_eq (by ring)
  have hsum : tN0 N - thetaN N ≤ (∑ p ∈ primesUpTo N, f p) + ε / 2 * thetaN N := by
    rw [tN0_sub_theta]
    calc ∑ p ∈ primesUpTo N, Real.log p * cWeight p
        ≤ ∑ p ∈ primesUpTo N, (f p + ε / 2 * Real.log p) := Finset.sum_le_sum hpt
      _ = (∑ p ∈ primesUpTo N, f p) + ε / 2 * thetaN N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
  have hsub : ∑ p ∈ primesUpTo N, f p ≤ S := by
    have h1 : ∑ p ∈ primesUpTo N, f p = ∑ p ∈ (primesUpTo N).filter (· < P), f p := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hlt : p < P
      · simp [hlt]
      · have : f p = 0 := by simp [hf, hlt]
        simp [hlt, this]
    rw [h1]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hf0 p)
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  have hS' : S ≤ ε / 2 * thetaN N := by
    rw [div_le_iff₀ hε] at hθ
    nlinarith
  nlinarith

end GppShiftPresentation

#print axioms GppShiftPresentation.tN0_sub_theta_le
