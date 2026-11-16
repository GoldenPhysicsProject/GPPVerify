import GppVerify.RiemannHypothesis.ArchimedeanMultiplier

/-!
# Exact low-order Legendre prime-cap diagonals on the first rung

On the first rung `log 2 < L < log 3` only the prime `2` is visible, and (Turbo relay `bfbdb91`, unit (iii))
its quadratic form in the Legendre basis `e_n(x) = √((2n+1)/L) P_n(2x/L)` has the entries

`J_{nm}(α) = ½ ∫_{α−1}^{1} P_n(t) P_m(t − α) dt`,   `α = 2 log 2 / L`,   `h := 2 − α = 2(1 − log 2 / L)`.

This file proves the exact polynomial identities for `P₀ = 1`, `P₁ = t` (`P₂` is defined but `J₂₂` is not
proved here):

* `J₀₀ = h/2`, `J₁₁ = −h(h² − 6h + 6)/12`, and the parity relation `J₀₁ = −J₁₀`;
* on the whole first rung, `0 < h < 1`, so `J₀₀ > 0` and `J₁₁ < 0` (since `h² − 6h + 6 ≥ 1` there);
* hence the prime contributions `W^prime_{nn} = −2 v A_{nn}`, `v = log 2/√2 > 0`, have opposite signs in
  the two lowest modes: `W^prime_{00} = −v h < 0`, `W^prime_{11} = + v h(h² − 6h + 6)/2 > 0`
  (with the normalisation `A_{nn} = (2n+1) J_{nn}`).

**Scope.** Pure algebra on finitely many explicit polynomial integrals. The identification of `J_{nm}` with
the Legendre-basis entries of `A_f(log 2)` (the substitution `x = Lt/2` and Haar–Plancherel unitary) is
not formalised here. No claim about positivity of the Weil form; this is the sign law of two prime entries.

No `sorry`, no axiom.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace GppFirstPrime

/-- `P₀ = 1`, `P₁ = t`, `P₂ = (3t² − 1)/2`. -/
def P0 (_t : ℝ) : ℝ := 1
def P1 (t : ℝ) : ℝ := t
def P2 (t : ℝ) : ℝ := (3 * t ^ 2 - 1) / 2

/-- The cap entry `J_{nm}(α) = ½ ∫_{α−1}^{1} P_n(t) P_m(t − α) dt`. -/
def capJ (P Q : ℝ → ℝ) (α : ℝ) : ℝ := (1 / 2) * ∫ t in (α - 1)..1, P t * Q (t - α)

theorem capJ_00 (α : ℝ) : capJ P0 P0 α = (2 - α) / 2 := by
  unfold capJ P0
  simp
  ring

theorem capJ_11 (α : ℝ) :
    capJ P1 P1 α = -((2 - α) * ((2 - α) ^ 2 - 6 * (2 - α) + 6)) / 12 := by
  unfold capJ P1
  have : (fun t : ℝ => t * (t - α)) = fun t => t ^ 2 - α * t := by funext t; ring
  rw [this, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul]
  simp [integral_pow]
  ring

theorem capJ_01 (α : ℝ) : capJ P0 P1 α = -(α * (2 - α)) / 4 := by
  unfold capJ P0 P1
  simp
  ring

theorem capJ_10 (α : ℝ) : capJ P1 P0 α = (α * (2 - α)) / 4 := by
  unfold capJ P1 P0
  simp
  ring

/-- **Parity relation** `J₀₁ = −J₁₀`. -/
theorem capJ_01_eq_neg_10 (α : ℝ) : capJ P0 P1 α = -capJ P1 P0 α := by
  rw [capJ_01, capJ_10]; ring

/-! ### Sign law on the first rung -/

/-- `h = 2(1 − log 2 / L)`. -/
def capH (L : ℝ) : ℝ := 2 * (1 - Real.log 2 / L)

theorem capH_eq (L : ℝ) : 2 - 2 * Real.log 2 / L = capH L := by unfold capH; ring

/-- On the first rung, `0 < h < 1`. -/
theorem capH_mem {L : ℝ} (h2 : Real.log 2 < L) (h3 : L < Real.log 3) : 0 < capH L ∧ capH L < 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := hl2.trans h2
  have hl4 : Real.log 3 < 2 * Real.log 2 := by
    have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  unfold capH
  constructor
  · have : Real.log 2 / L < 1 := by rw [div_lt_one hL]; exact h2
    linarith
  · have : 1 / 2 < Real.log 2 / L := by
      rw [lt_div_iff₀ hL]; linarith
    linarith

theorem capH_quad_ge_one {h : ℝ} (_h0 : 0 < h) (h1 : h < 1) : 1 ≤ h ^ 2 - 6 * h + 6 := by
  nlinarith

/-- `J₀₀ = h/2 > 0` on the first rung. -/
theorem capJ_00_pos {L : ℝ} (h2 : Real.log 2 < L) (h3 : L < Real.log 3) :
    0 < capJ P0 P0 (2 * Real.log 2 / L) := by
  rw [capJ_00, capH_eq]
  have := (capH_mem h2 h3).1
  linarith

/-- `J₁₁ < 0` on the first rung. -/
theorem capJ_11_neg {L : ℝ} (h2 : Real.log 2 < L) (h3 : L < Real.log 3) :
    capJ P1 P1 (2 * Real.log 2 / L) < 0 := by
  rw [capJ_11, capH_eq]
  obtain ⟨h0, h1⟩ := capH_mem h2 h3
  have := capH_quad_ge_one h0 h1
  have : 0 < capH L * (capH L ^ 2 - 6 * capH L + 6) := mul_pos h0 (by linarith)
  linarith

/-- The first-prime coefficient `v = log 2 / √2`. -/
def primeV : ℝ := Real.log 2 / Real.sqrt 2

theorem primeV_pos : 0 < primeV := by
  unfold primeV
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

/-- **Prime contribution in the lowest Legendre mode is negative:** `−2 v J₀₀ = −v h < 0`. -/
theorem primeW_00 {L : ℝ} (h2 : Real.log 2 < L) (h3 : L < Real.log 3) :
    -2 * primeV * capJ P0 P0 (2 * Real.log 2 / L) = -primeV * capH L ∧
      -2 * primeV * capJ P0 P0 (2 * Real.log 2 / L) < 0 := by
  have h := (capH_mem h2 h3).1
  have e : -2 * primeV * capJ P0 P0 (2 * Real.log 2 / L) = -primeV * capH L := by
    rw [capJ_00, capH_eq]; ring
  exact ⟨e, by rw [e]; have := primeV_pos; nlinarith⟩

/-- **Prime contribution in the first odd mode is positive:**
`−2 v · 3 J₁₁ = + v h (h² − 6h + 6)/2 > 0`. -/
theorem primeW_11 {L : ℝ} (h2 : Real.log 2 < L) (h3 : L < Real.log 3) :
    -2 * primeV * (3 * capJ P1 P1 (2 * Real.log 2 / L)) =
        primeV * capH L * (capH L ^ 2 - 6 * capH L + 6) / 2 ∧
      0 < -2 * primeV * (3 * capJ P1 P1 (2 * Real.log 2 / L)) := by
  obtain ⟨h0, h1⟩ := capH_mem h2 h3
  have e : -2 * primeV * (3 * capJ P1 P1 (2 * Real.log 2 / L)) =
      primeV * capH L * (capH L ^ 2 - 6 * capH L + 6) / 2 := by
    rw [capJ_11, capH_eq]; ring
  refine ⟨e, ?_⟩
  rw [e]
  have := capH_quad_ge_one h0 h1
  have hv := primeV_pos
  have : 0 < capH L * (capH L ^ 2 - 6 * capH L + 6) := mul_pos h0 (by linarith)
  have : 0 < primeV * (capH L * (capH L ^ 2 - 6 * capH L + 6)) := mul_pos hv this
  nlinarith

end GppFirstPrime

#print axioms GppFirstPrime.primeW_00
#print axioms GppFirstPrime.primeW_11
#print axioms GppFirstPrime.capJ_01_eq_neg_10
