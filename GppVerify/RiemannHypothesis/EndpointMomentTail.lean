import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Endpoint-moment tail: the exact geometric remainder and its pointwise bound

Source: Astra, `work/2026-10-20_astra_endpoint_moment_arithmetic_tail.md` ("Setup and exact
remainder"). Daniel Toupin / Golden Physics Project, with AI assistance from Astra (statement) and
Claude Code (formalization).

For a finite family of complex coefficients `c_j`, real frequencies `a_j` with `|a_j| ≤ A`, and a real
`t` with `|t| > A`, put `M_r = Σ_j c_j a_j^r` and `B_m = Σ_j |c_j| |a_j|^m`. Then:

* `geom_remainder`: `1/(t+a) − Σ_{r<m} (−a)^r / t^{r+1} = (−a)^m / (t^m (t+a))` (exact, any `t ≠ 0`,
  `t + a ≠ 0`).
* `tail_remainder_bound`:
  `‖Σ_j c_j/(t+a_j) − Σ_{r<m} (−1)^r M_r / t^{r+1}‖ ≤ B_m / (|t|^m (|t| − A))`.
* `sin_scaled_remainder_bound`: the same with the factor `√(2/L) sin(tL)` in front, giving
  `|F − F_m| ≤ √(2/L) B_m / (|t|^m (|t| − A))` for `F(t) = √(2/L) sin(tL) Σ_j c_j/(t+a_j)` (here
  `c_j = (−1)^j v_j`).

**Scope.** Only the finite geometric division and the resulting pointwise bound, exactly as in the
note's "Setup and exact remainder". The envelope for the arithmetic multiplier (the digamma
estimate, DLMF 5.7.6), the integrated error theorem, the Plancherel bookkeeping and every numerical
evaluation in the note are not formalized. No claim about RH.
-/

set_option autoImplicit false

open Finset

namespace GppEndpointMomentTail

/-- Exact geometric remainder: `1/(t+a) − Σ_{r<m} (−a)^r / t^{r+1} = (−a)^m / (t^m (t+a))`. -/
theorem geom_remainder (t a : ℂ) (ht : t ≠ 0) (hta : t + a ≠ 0) (m : ℕ) :
    1 / (t + a) - ∑ r ∈ range m, (-a) ^ r / t ^ (r + 1) = (-a) ^ m / (t ^ m * (t + a)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    field_simp
    ring

/-- Pointwise bound for the coefficient sum: with `|a_j| ≤ A < |t|` (`0 ≤ A`),
`‖Σ_j c_j/(t+a_j) − Σ_{r<m} (−1)^r M_r / t^{r+1}‖ ≤ B_m / (|t|^m (|t| − A))`. -/
theorem tail_remainder_bound {ι : Type*} (s : Finset ι) (c : ι → ℂ) (a : ι → ℝ) (A t : ℝ)
    (hA0 : 0 ≤ A) (hA : ∀ j ∈ s, |a j| ≤ A) (ht : A < |t|) (m : ℕ) :
    ‖∑ j ∈ s, c j / ((t : ℂ) + a j) -
        ∑ r ∈ range m, (-1 : ℂ) ^ r * (∑ j ∈ s, c j * (a j : ℂ) ^ r) / (t : ℂ) ^ (r + 1)‖ ≤
      (∑ j ∈ s, ‖c j‖ * |a j| ^ m) / (|t| ^ m * (|t| - A)) := by
  have htpos : 0 < |t| := lt_of_le_of_lt hA0 ht
  have ht0 : (t : ℂ) ≠ 0 := by
    have : t ≠ 0 := abs_pos.mp htpos
    exact_mod_cast this
  have hlow : ∀ j ∈ s, |t| - A ≤ ‖(t : ℂ) + a j‖ := by
    intro j hj
    have h1 := norm_sub_norm_le (t : ℂ) (-(a j : ℂ))
    rw [sub_neg_eq_add, norm_neg] at h1
    have h2 : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h3 : ‖(a j : ℂ)‖ = |a j| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h2, h3] at h1
    linarith [hA j hj]
  have hne : ∀ j ∈ s, (t : ℂ) + a j ≠ 0 := by
    intro j hj h
    have := hlow j hj
    rw [h, norm_zero] at this
    linarith
  have key : ∑ j ∈ s, c j / ((t : ℂ) + a j) -
        ∑ r ∈ range m, (-1 : ℂ) ^ r * (∑ j ∈ s, c j * (a j : ℂ) ^ r) / (t : ℂ) ^ (r + 1) =
      ∑ j ∈ s, c j * ((-(a j : ℂ)) ^ m / ((t : ℂ) ^ m * ((t : ℂ) + a j))) := by
    have e : ∑ r ∈ range m, (-1 : ℂ) ^ r * (∑ j ∈ s, c j * (a j : ℂ) ^ r) / (t : ℂ) ^ (r + 1) =
        ∑ j ∈ s, c j * ∑ r ∈ range m, (-(a j : ℂ)) ^ r / (t : ℂ) ^ (r + 1) := by
      simp_rw [Finset.mul_sum, Finset.sum_div]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun r _ => ?_))
      rw [neg_pow]; ring
    rw [e, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hg := geom_remainder (t : ℂ) (a j) ht0 (hne j hj) m
    calc c j / ((t : ℂ) + a j) - c j * ∑ r ∈ range m, (-(a j : ℂ)) ^ r / (t : ℂ) ^ (r + 1)
        = c j * (1 / ((t : ℂ) + a j) - ∑ r ∈ range m, (-(a j : ℂ)) ^ r / (t : ℂ) ^ (r + 1)) := by
          ring
      _ = _ := by rw [hg]
  rw [key]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum (fun j hj => ?_)
  rw [norm_mul, norm_div, norm_pow, norm_neg, norm_mul, norm_pow]
  have h3 : ‖(a j : ℂ)‖ = |a j| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h3, h2]
  have hden : 0 < |t| - A := by linarith
  have hpowpos : 0 < |t| ^ m := pow_pos htpos m
  have hnorm : 0 < ‖(t : ℂ) + a j‖ := lt_of_lt_of_le hden (hlow j hj)
  rw [mul_div_assoc']
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact mul_le_mul_of_nonneg_left (hlow j hj) hpowpos.le

/-- The same bound with the prefactor `K sin(tL)`, `K ≥ 0`: for
`F(t) = K sin(tL) Σ_j c_j/(t+a_j)` and `F_m(t) = K sin(tL) Σ_{r<m} (−1)^r M_r / t^{r+1}`,
`|F − F_m| ≤ K B_m / (|t|^m (|t| − A))`. -/
theorem sin_scaled_remainder_bound {ι : Type*} (s : Finset ι) (c : ι → ℂ) (a : ι → ℝ)
    (A t K L : ℝ) (hK : 0 ≤ K) (hA0 : 0 ≤ A) (hA : ∀ j ∈ s, |a j| ≤ A) (ht : A < |t|) (m : ℕ) :
    ‖((K * Real.sin (t * L) : ℝ) : ℂ) *
        (∑ j ∈ s, c j / ((t : ℂ) + a j) -
          ∑ r ∈ range m, (-1 : ℂ) ^ r * (∑ j ∈ s, c j * (a j : ℂ) ^ r) / (t : ℂ) ^ (r + 1))‖ ≤
      K * ((∑ j ∈ s, ‖c j‖ * |a j| ^ m) / (|t| ^ m * (|t| - A))) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
  have hs : |Real.sin (t * L)| ≤ 1 := Real.abs_sin_le_one _
  have hb := tail_remainder_bound s c a A t hA0 hA ht m
  have hnn := norm_nonneg (∑ j ∈ s, c j / ((t : ℂ) + a j) -
        ∑ r ∈ range m, (-1 : ℂ) ^ r * (∑ j ∈ s, c j * (a j : ℂ) ^ r) / (t : ℂ) ^ (r + 1))
  generalize ‖∑ j ∈ s, c j / ((t : ℂ) + a j) -
        ∑ r ∈ range m, (-1 : ℂ) ^ r * (∑ j ∈ s, c j * (a j : ℂ) ^ r) / (t : ℂ) ^ (r + 1)‖ = X
    at hb hnn ⊢
  generalize (∑ j ∈ s, ‖c j‖ * |a j| ^ m) / (|t| ^ m * (|t| - A)) = B at hb ⊢
  calc K * |Real.sin (t * L)| * X ≤ K * 1 * X := by gcongr
    _ = K * X := by ring
    _ ≤ K * B := by gcongr

end GppEndpointMomentTail
