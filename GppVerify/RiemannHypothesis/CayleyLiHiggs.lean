import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Cayley–Li finite positivity with inverse-square UV suppression

Source: Codex, `codex.formalization_queue` item "Cayley-Li Higgs finite positivity"
(2026-09-25, thread "RH / Higgs-Cayley-Li"); formalized here 2026-09-27.

For real `t`, the Cayley map `u(t) = (t + i/2)/(t - i/2)` is exactly the Li ratio of a
critical-line point: `u(t) = 1 - 1/ρ` for `ρ = 1/2 + i t` (`cayley_eq_li_ratio`). Li's
coefficients are `λ_n = Σ_ρ (1 - (1 - 1/ρ)^n)`, so for a zero on the critical line each Li term
is `1 - u(t)^n`.

## Proved here (unconditional, for every real `t` and every `n`)

* `norm_cayley`: `‖u(t)‖ = 1`;
* `one_sub_re_cayley`: `1 - Re u(t) = 1/(2(t² + 1/4))`;
* `one_sub_re_pow_nonneg`: `0 ≤ 1 - Re(u(t)^n)` (finite positivity);
* `one_sub_re_pow_le`: `1 - Re(u(t)^n) ≤ n²/(2(t² + 1/4))` (inverse-square UV suppression);
* `finite_li_sum_bounds`: the same two bounds summed over any finite family of real ordinates,
  i.e. the trace of `1 - Re Cⁿ` for the Cayley transform `C` of a diagonal (spectral) Hermitian
  model.

The mechanism is purely algebraic: for `‖z‖ = 1`, `‖1 - z‖² = 2(1 - Re z)`, and
`1 - uⁿ = (1 - u) Σ_{k<n} uᵏ` with `‖Σ uᵏ‖ ≤ n`, so `1 - Re uⁿ ≤ n² (1 - Re u)`.

## Scope

This is the finite, unconditional positivity of the critical-line Li terms. It does not
assert convergence of any finite sum to the true Li coefficients, it does not place any zero on
the critical line, and it is not a step that proves RH. The matrix/unitary-trace form is given
only in its diagonal (spectral) version; a statement for general unitary matrices is not
formalized here.
-/

open Complex Finset

namespace GppCayleyLiHiggs

/-- The Cayley map `u(t) = (t + i/2)/(t - i/2)`. -/
noncomputable def cayley (t : ℝ) : ℂ := ((t : ℂ) + I / 2) / ((t : ℂ) - I / 2)

lemma denom_ne_zero (t : ℝ) : (t : ℂ) - I / 2 ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

/-- `u(t) = 1 - 1/ρ` for `ρ = 1/2 + i t`: the Cayley map is the Li ratio on the critical line. -/
theorem cayley_eq_li_ratio (t : ℝ) : cayley t = 1 - 1 / (1 / 2 + I * t) := by
  have h1 : (1 / 2 + I * t : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h2 := denom_ne_zero t
  have e : (1 : ℂ) - 1 / (1 / 2 + I * t) = (1 / 2 + I * t - 1) / (1 / 2 + I * t) := by
    rw [sub_div, div_self h1]
  unfold cayley
  rw [e, div_eq_div_iff h2 h1]
  linear_combination (t : ℂ) * Complex.I_sq

lemma normSq_num (t : ℝ) : Complex.normSq ((t : ℂ) + I / 2) = t ^ 2 + 1 / 4 := by
  rw [Complex.normSq_apply]; simp; ring

lemma normSq_den (t : ℝ) : Complex.normSq ((t : ℂ) - I / 2) = t ^ 2 + 1 / 4 := by
  rw [Complex.normSq_apply]; simp; ring

/-- `‖u(t)‖ = 1`. -/
theorem norm_cayley (t : ℝ) : ‖cayley t‖ = 1 := by
  have hpos : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
  unfold cayley
  rw [norm_div, Complex.norm_def, Complex.norm_def, normSq_num, normSq_den,
    div_self (Real.sqrt_pos.mpr hpos).ne']

/-- For `‖z‖ = 1`, `‖1 - z‖² = 2 (1 - Re z)`. -/
lemma norm_one_sub_sq {z : ℂ} (hz : ‖z‖ = 1) : ‖1 - z‖ ^ 2 = 2 * (1 - z.re) := by
  have h1 : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz, one_pow]
  rw [Complex.normSq_apply] at h1
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  linear_combination h1

/-- `1 - Re u(t) = 1/(2(t² + 1/4))`. -/
theorem one_sub_re_cayley (t : ℝ) : 1 - (cayley t).re = 1 / (2 * (t ^ 2 + 1 / 4)) := by
  have hpos : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
  have key : ‖1 - cayley t‖ ^ 2 = 1 / (t ^ 2 + 1 / 4) := by
    have : 1 - cayley t = -I / ((t : ℂ) - I / 2) := by
      unfold cayley
      rw [eq_div_iff (denom_ne_zero t), sub_mul, one_mul, div_mul_cancel₀ _ (denom_ne_zero t)]
      ring
    rw [this, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, normSq_den]
    simp
  have h := norm_one_sub_sq (norm_cayley t)
  rw [key] at h
  field_simp at h ⊢
  linarith

/-- Finite positivity: `0 ≤ 1 - Re(u(t)^n)`. -/
theorem one_sub_re_pow_nonneg (t : ℝ) (n : ℕ) : 0 ≤ 1 - ((cayley t) ^ n).re := by
  have : ((cayley t) ^ n).re ≤ ‖(cayley t) ^ n‖ := Complex.re_le_norm _
  rw [norm_pow, norm_cayley, one_pow] at this
  linarith

/-- On the unit circle, `1 - Re zⁿ ≤ n² (1 - Re z)`. -/
lemma one_sub_re_pow_le_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    1 - (z ^ n).re ≤ (n : ℝ) ^ 2 * (1 - z.re) := by
  have hzn : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hsum : ‖∑ k ∈ range n, z ^ k‖ ≤ n := by
    calc ‖∑ k ∈ range n, z ^ k‖ ≤ ∑ k ∈ range n, ‖z ^ k‖ := norm_sum_le _ _
      _ = n := by simp [norm_pow, hz]
  have hfac : ‖1 - z ^ n‖ ≤ n * ‖1 - z‖ := by
    rw [← mul_neg_geom_sum, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have hsq : ‖1 - z ^ n‖ ^ 2 ≤ ((n : ℝ) * ‖1 - z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hfac 2
  rw [norm_one_sub_sq hzn, mul_pow, norm_one_sub_sq hz] at hsq
  linarith

/-- Inverse-square UV suppression: `1 - Re(u(t)^n) ≤ n² / (2(t² + 1/4))`. -/
theorem one_sub_re_pow_le (t : ℝ) (n : ℕ) :
    1 - ((cayley t) ^ n).re ≤ (n : ℝ) ^ 2 / (2 * (t ^ 2 + 1 / 4)) := by
  have h := one_sub_re_pow_le_of_norm_one (norm_cayley t) n
  rw [one_sub_re_cayley] at h
  calc 1 - ((cayley t) ^ n).re ≤ (n : ℝ) ^ 2 * (1 / (2 * (t ^ 2 + 1 / 4))) := h
    _ = (n : ℝ) ^ 2 / (2 * (t ^ 2 + 1 / 4)) := by ring

/-- **Finite spectral (trace) form.** For any finite family of real ordinates `t_j`,
`0 ≤ Σ_j (1 - Re u(t_j)^n) ≤ (n²/2) Σ_j 1/(t_j² + 1/4)`. -/
theorem finite_li_sum_bounds {ι : Type*} (s : Finset ι) (t : ι → ℝ) (n : ℕ) :
    0 ≤ ∑ j ∈ s, (1 - ((cayley (t j)) ^ n).re) ∧
      ∑ j ∈ s, (1 - ((cayley (t j)) ^ n).re) ≤
        (n : ℝ) ^ 2 / 2 * ∑ j ∈ s, 1 / ((t j) ^ 2 + 1 / 4) := by
  refine ⟨sum_nonneg (fun j _ => one_sub_re_pow_nonneg (t j) n), ?_⟩
  rw [mul_sum]
  refine sum_le_sum (fun j _ => (one_sub_re_pow_le (t j) n).trans (le_of_eq ?_))
  have : (0 : ℝ) < t j ^ 2 + 1 / 4 := by positivity
  field_simp

end GppCayleyLiHiggs
