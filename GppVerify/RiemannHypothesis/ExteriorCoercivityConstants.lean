import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The finite arithmetic of Astra's all-`L` exterior coercivity choice

From `work/2026-10-17_astra_explicit_exterior_and_coupling_tail.md`, sections 3 and 5. With
`H = L²([-L, L])`, Fourier nodes `e_j = exp(i j π x / L)/√(2L)`, projector `P_N` onto `|j| ≤ N`, the
note bounds the completed Weil form on the exterior by `Q(f) ≥ α‖f‖²` with
`α = b - (b - a₀) r - s - d_N`, where `r = 4LT/(π³(N - LT/π))` and `d_N = 8L sinh²(L/2)/(π²N)`.
Section 5 then picks `b = s + 2`, `T = 2π exp(s + 3)` and `N` large, and concludes `α ≥ 1/2`.

This file proves exactly the elementary inequalities that choice uses:

* `tail_inv_sq_le`: `Σ_{N < j ≤ M} 1/(j - a)² ≤ 1/(N - a) - 1/(M - a) ≤ 1/(N - a)` for `a < N`
  (the tail bound behind the low-band leakage constant `r` and behind `d_N`);
* `leakage_ratio_le`: `r ≤ 1/(b - a₀)` once `N ≥ LT/π + 4LT(b - a₀)/π³`;
* `exteriorTail_le_half`: `d_N ≤ 1/2` once `N ≥ 16 L sinh²(L/2)/π²`;
* `alpha_ge_half`: with `b = s + 2`, `r (b - a₀) ≤ 1` and `d ≤ 1/2`, `α ≥ 1/2`.

**Scope.** Real-number inequalities only. The Fourier estimates that produce `r` and `d_N`, the digamma
lower bound `a(t) ≥ log(|t|/2π) - 2/|t|`, the coupling-tail bound and the identification of `Q` with the
Weil form are not formalized. Nothing here is a statement about positivity of the Weil form beyond the
exterior of a finite Fourier block, and there is no RH claim.
-/

namespace GppExteriorConstants

open Finset

/-- Telescoping tail bound `Σ_{N < j ≤ M} 1/(j - a)² ≤ 1/(N - a) - 1/(M - a)` for `a < N ≤ M`. -/
theorem tail_inv_sq_le (a : ℝ) (N M : ℕ) (ha : a < N) (hNM : N ≤ M) :
    ∑ j ∈ Ioc N M, 1 / ((j : ℝ) - a) ^ 2 ≤ 1 / ((N : ℝ) - a) - 1 / ((M : ℝ) - a) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hM : (0 : ℝ) < (M : ℝ) - a := by
      have : (N : ℝ) ≤ M := by exact_mod_cast hNM
      linarith
    have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) - a := by push_cast; linarith
    have key : 1 / (((M + 1 : ℕ) : ℝ) - a) ^ 2 ≤ 1 / ((M : ℝ) - a) - 1 / (((M + 1 : ℕ) : ℝ) - a) := by
      have hx : ((M + 1 : ℕ) : ℝ) - a = ((M : ℝ) - a) + 1 := by push_cast; ring
      rw [hx]
      set x : ℝ := (M : ℝ) - a with hxdef
      have e : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by field_simp; ring
      rw [e]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    linarith

/-- The tail is at most `1/(N - a)`. -/
theorem tail_inv_sq_le_inv (a : ℝ) (N M : ℕ) (ha : a < N) (hNM : N ≤ M) :
    ∑ j ∈ Ioc N M, 1 / ((j : ℝ) - a) ^ 2 ≤ 1 / ((N : ℝ) - a) := by
  have h := tail_inv_sq_le a N M ha hNM
  have hM : (0 : ℝ) < (M : ℝ) - a := by
    have : (N : ℝ) ≤ M := by exact_mod_cast hNM
    linarith
  have : 0 < 1 / ((M : ℝ) - a) := by positivity
  linarith

/-- With `N ≥ LT/π + 4LT(b - a₀)/π³`, the leakage constant satisfies `r ≤ 1/(b - a₀)`. -/
theorem leakage_ratio_le (L T N b a₀ : ℝ) (hL : 0 < L) (hT : 0 < T) (hb : a₀ < b)
    (hN : L * T / Real.pi + 4 * L * T * (b - a₀) / Real.pi ^ 3 ≤ N) :
    4 * L * T / (Real.pi ^ 3 * (N - L * T / Real.pi)) ≤ 1 / (b - a₀) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hba : 0 < b - a₀ := by linarith
  have hpos : 0 < 4 * L * T * (b - a₀) / Real.pi ^ 3 := by positivity
  have hD : 0 < Real.pi ^ 3 * (N - L * T / Real.pi) := by
    have : 0 < N - L * T / Real.pi := by linarith
    positivity
  rw [div_le_div_iff₀ hD hba]
  have h1 : 4 * L * T * (b - a₀) / Real.pi ^ 3 ≤ N - L * T / Real.pi := by linarith
  have h2 : 4 * L * T * (b - a₀) ≤ Real.pi ^ 3 * (N - L * T / Real.pi) := by
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt (pow_pos hpi 3))
    rwa [mul_div_cancel₀ _ (pow_pos hpi 3).ne'] at this
  linarith

/-- With `N ≥ 16 L sinh²(L/2)/π²` and `N ≥ 1`, `d_N = 8 L sinh²(L/2)/(π² N) ≤ 1/2`. -/
theorem exteriorTail_le_half (L N : ℝ) (hN1 : 1 ≤ N)
    (hN : 16 * L * Real.sinh (L / 2) ^ 2 / Real.pi ^ 2 ≤ N) :
    8 * L * Real.sinh (L / 2) ^ 2 / (Real.pi ^ 2 * N) ≤ 1 / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hN0 : 0 < N := by linarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : 16 * L * Real.sinh (L / 2) ^ 2 ≤ N * Real.pi ^ 2 := by
    have := (div_le_iff₀ (pow_pos hpi 2)).mp hN
    linarith
  nlinarith [this]

/-- The combination step: `α = b - (b - a₀) r - s - d ≥ 1/2` for `b = s + 2`, `r (b - a₀) ≤ 1`, `d ≤ 1/2`. -/
theorem alpha_ge_half (b a₀ s r d : ℝ) (hb : b = s + 2) (hr : r * (b - a₀) ≤ 1) (hd : d ≤ 1 / 2) :
    1 / 2 ≤ b - (b - a₀) * r - s - d := by
  subst hb
  nlinarith [hr, hd]

#print axioms GppExteriorConstants.tail_inv_sq_le
#print axioms GppExteriorConstants.tail_inv_sq_le_inv
#print axioms GppExteriorConstants.leakage_ratio_le
#print axioms GppExteriorConstants.exteriorTail_le_half
#print axioms GppExteriorConstants.alpha_ge_half

end GppExteriorConstants
