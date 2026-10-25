import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# The free angular spectrum at the Hawking temperature has bounded entropy

Source: Codex, GPP-bridge PR #11 comments 6392046099 and 6392063911 (Discovery2 PR #23), item 3,
the "thermal falsifier" of naive horizon state counting. Daniel Toupin / Golden Physics Project,
with AI assistance from Codex (statement) and Claude Code (formalization).

Each angular level `ℓ` of a free SU(2)-invariant fermion with `ε_ℓ = ℓ/R` carries `2ℓ+1` modes.
At the Schwarzschild inverse temperature `β_H = 4πR`, a mode has `βε = 4πℓ`. Its occupation is
`f = 1/(e^x + 1)`, and its entropy is `h_F(x) = −f log f − (1−f) log(1−f)`.

* `hF_eq_binary`: `h_F(x) = log(1 + e^{−x}) + x/(e^x + 1)` is the binary entropy of `f`.
* `hF_le`: `h_F(x) ≤ (1 + x) e^{−x}` for `x ≥ 0`.
* `thermalEntropy_le`: for **every** `N`,
  `S_N = Σ_{ℓ<N} (2ℓ+1) h_F(4πℓ) ≤ log 2 + 1/1000`.
  So the thermal entropy stays bounded, while the CAR Fock space over `End(H_N)` has maximal
  entropy `N² log 2`. Codex's sharper constant is `≈ 0.693289114`. This file proves the cruder
  `log 2 + 10⁻³ ≈ 0.69415`, which already rules out `N²` growth.

**Scope.** This is a falsifier of one naive model (free spectrum `ℓ/R` at `β_H`), not a statement
about black-hole entropy. The SU(2)-singlet census `ln d_N = N² ln 2 + O(ln N)`, the soft spectrum
`ℓ/(NR)`, and the quarter-coefficient discussion are not formalized. No claim about RH or BSD.
-/

set_option autoImplicit false

open Real Finset

namespace GppEquatorThermal

/-- Fermion mode entropy at `x = βε`. -/
noncomputable def hF (x : ℝ) : ℝ := Real.log (1 + exp (-x)) + x / (exp x + 1)

/-- `h_F` is the binary entropy of the Fermi occupation `f = 1/(e^x + 1)`. -/
theorem hF_eq_binary (x : ℝ) :
    hF x = -(1 / (exp x + 1)) * Real.log (1 / (exp x + 1)) -
      (1 - 1 / (exp x + 1)) * Real.log (1 - 1 / (exp x + 1)) := by
  have hpos : 0 < exp x + 1 := by positivity
  have h1 : 1 - 1 / (exp x + 1) = exp x / (exp x + 1) := by field_simp; try ring
  have h2 : 1 + exp (-x) = (exp x + 1) / exp x := by
    rw [exp_neg]; field_simp; try ring
  rw [h1, hF, h2, Real.log_div hpos.ne' (exp_pos x).ne', Real.log_div (exp_pos x).ne' hpos.ne',
    one_div, Real.log_inv, Real.log_exp]
  field_simp
  ring

theorem hF_le {x : ℝ} (hx : 0 ≤ x) : hF x ≤ (1 + x) * exp (-x) := by
  have h1 : Real.log (1 + exp (-x)) ≤ exp (-x) := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + exp (-x)); linarith
  have h2 : x / (exp x + 1) ≤ x * exp (-x) := by
    rw [exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hx (exp_pos x) (by linarith)
  unfold hF; nlinarith

theorem hF_zero : hF 0 = Real.log 2 := by
  simp [hF]; norm_num

/-- `S_N = Σ_{ℓ<N} (2ℓ+1) h_F(4πℓ)`. -/
noncomputable def thermalEntropy (N : ℕ) : ℝ := ∑ ℓ ∈ range N, (2 * ℓ + 1 : ℝ) * hF (4 * π * ℓ)

lemma nat_sq_le_three_pow (n : ℕ) : n ^ 2 ≤ 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num
    · have : (n + 1) ^ 2 ≤ 3 * n ^ 2 := by nlinarith
      calc (n + 1) ^ 2 ≤ 3 * n ^ 2 := this
        _ ≤ 3 * 3 ^ n := by omega
        _ = 3 ^ (n + 1) := by ring

lemma exp_neg_twelve_le : exp (-12) ≤ 1 / 126100 := by
  have h : (126100 : ℝ) ≤ exp 12 := by
    have h1 : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
    have : exp 12 = exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (126100 : ℝ) ≤ 2.7182818283 ^ 12 := by norm_num
      _ ≤ exp 1 ^ 12 := by gcongr
  rw [exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h

/-- One level `ℓ ≥ 1`: `(2ℓ+1) h_F(4πℓ) ≤ 42 r^ℓ` with `r = 3e^{−12}`. -/
lemma term_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (2 * ℓ + 1 : ℝ) * hF (4 * π * ℓ) ≤ 42 * (3 * exp (-12)) ^ ℓ := by
  have hl : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hx : 0 ≤ 4 * π * ℓ := by positivity
  have hh := hF_le hx
  have he : exp (-(4 * π * ℓ)) ≤ exp (-12) ^ ℓ := by
    rw [← Real.exp_nat_mul]; exact exp_le_exp.mpr (by nlinarith)
  have hsq : ((ℓ : ℝ)) ^ 2 ≤ 3 ^ ℓ := by exact_mod_cast nat_sq_le_three_pow ℓ
  have hpoly : (2 * ℓ + 1 : ℝ) * (1 + 4 * π * ℓ) ≤ 42 * (ℓ : ℝ) ^ 2 := by nlinarith
  calc (2 * ℓ + 1 : ℝ) * hF (4 * π * ℓ)
      ≤ (2 * ℓ + 1 : ℝ) * ((1 + 4 * π * ℓ) * exp (-(4 * π * ℓ))) := by gcongr
    _ ≤ (2 * ℓ + 1 : ℝ) * (1 + 4 * π * ℓ) * exp (-12) ^ ℓ := by
        rw [← mul_assoc]; gcongr
    _ ≤ 42 * (ℓ : ℝ) ^ 2 * exp (-12) ^ ℓ := by gcongr
    _ ≤ 42 * 3 ^ ℓ * exp (-12) ^ ℓ := by gcongr
    _ = 42 * (3 * exp (-12)) ^ ℓ := by rw [mul_pow]; ring

/-- **The thermal falsifier.** For every `N`, `S_N ≤ log 2 + 1/1000`. -/
theorem thermalEntropy_le (N : ℕ) : thermalEntropy N ≤ Real.log 2 + 1 / 1000 := by
  rcases N with _ | N
  · simp [thermalEntropy]; positivity
  set r := 3 * exp (-12) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 3 / 126100 := by rw [hr]; linarith [exp_neg_twelve_le]
  have hrl : r < 1 := by linarith
  rw [thermalEntropy, sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, hF_zero, Nat.cast_succ]
  have hsum : ∑ ℓ ∈ range N, (2 * ((ℓ : ℝ) + 1) + 1) * hF (4 * π * ((ℓ : ℝ) + 1)) ≤
      ∑ ℓ ∈ range N, 42 * r ^ (ℓ + 1) := by
    refine sum_le_sum fun ℓ _ => ?_
    have := term_le (ℓ := ℓ + 1) (by omega)
    push_cast at this; exact this
  have hgeom : ∑ ℓ ∈ range N, 42 * r ^ (ℓ + 1) ≤ 42 * (r / (1 - r)) := by
    have hg : (∑ ℓ ∈ range N, r ^ ℓ) * (1 - r) ≤ 1 := by
      rw [geom_sum_mul_neg]; linarith [pow_nonneg hr0 N]
    have hg' : ∑ ℓ ∈ range N, r ^ ℓ ≤ 1 / (1 - r) := (le_div_iff₀ (by linarith)).mpr hg
    have hs : ∑ ℓ ∈ range N, 42 * r ^ (ℓ + 1) = 42 * r * ∑ ℓ ∈ range N, r ^ ℓ := by
      rw [mul_sum]; exact sum_congr rfl fun ℓ _ => by ring
    rw [hs, mul_div_assoc', show 42 * r / (1 - r) = 42 * r * (1 / (1 - r)) by ring]
    exact mul_le_mul_of_nonneg_left hg' (by positivity)
  have hfin : 42 * (r / (1 - r)) ≤ 1 / 1000 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  linarith

end GppEquatorThermal
