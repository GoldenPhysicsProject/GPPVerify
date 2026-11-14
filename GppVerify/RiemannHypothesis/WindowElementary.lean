import GppVerify.Upstream.ExpTaylorImaginary
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary local expansions for the window minorant check

The lower bound `G_M` of the window symbol (`GppWindowGM.GM`) is built from three kinds of
elementary function. Around a centre `c`, with `u = r - c`:

* **rational terms** `a/(a² + r²/4) = Re 1/(a + i r/2)` (`re_inv_eq`), expanded by the exact finite
  geometric identity `1/(s₀ + w) = Σ_{n<N} (-w)^n/s₀^{n+1} + (-w)^N/(s₀^N (s₀ + w))`
  (`inv_add_eq_geom`), so that `|Re 1/(a + i r/2) - Σ_{n<N} t_n u^n| ≤ (|u|/2)^N / (a^N · a)`
  (`abs_re_inv_sub_taylor_le`), with `t_n = Re((-i/2)^n / s₀^{n+1})`, `s₀ = a + i c/2`;
* **the logarithm**, by `1 - 1/x ≤ log x`: `log Q(r) ≥ log Q(c) + 1 - Q(c)/Q(r)` (`log_ge_tangent`);
* **the cosine**, `cos(rL) = Re(e^{icL} e^{iuL})`, with the sharp Taylor bound for `e^{iuL}`
  (`abs_cos_sub_taylor_le`).

`poly_ge_of_abs_le`: on `|u| ≤ h`, `Σ_{n<N} d_n u^n ≥ d_0 - Σ_{0<n<N} |d_n| h^n`.

Unconditional; no `sorry`, no axioms.
-/

namespace GppWindowElementary

open Complex Finset

/-- `a/(a² + b²) = Re 1/(a + i b)`. -/
theorem re_inv_eq (a b : ℝ) : a / (a ^ 2 + b ^ 2) = ((a : ℂ) + b * I)⁻¹.re := by
  rw [Complex.inv_re]
  simp [Complex.normSq_apply, sq]

/-- **The finite geometric identity.** For `s₀ ≠ 0`, `s₀ + w ≠ 0`. -/
theorem inv_add_eq_geom {s w : ℂ} (hs : s ≠ 0) (hsw : s + w ≠ 0) (N : ℕ) :
    (s + w)⁻¹ = ∑ n ∈ range N, (-w) ^ n / s ^ (n + 1) + (-w) ^ N / (s ^ N * (s + w)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, sum_range_succ]
    field_simp
    ring

/-- **The rational terms around a centre.** For `a > 0` and real `c, u`, with `s₀ = a + i c/2`. -/
theorem abs_re_inv_sub_taylor_le {a : ℝ} (ha : 0 < a) (c u : ℝ) (N : ℕ) :
    |((a : ℂ) + ((c + u) / 2 : ℝ) * I)⁻¹.re -
        ∑ n ∈ range N, ((-(I / 2)) ^ n / ((a : ℂ) + (c / 2 : ℝ) * I) ^ (n + 1)).re * u ^ n| ≤
      (|u| / 2) ^ N / (a ^ N * a) := by
  set s : ℂ := (a : ℂ) + (c / 2 : ℝ) * I
  set w : ℂ := (u / 2 : ℝ) * I
  have hsw' : (a : ℂ) + ((c + u) / 2 : ℝ) * I = s + w := by
    simp only [s, w]; push_cast; ring
  have hs_re : s.re = a := by simp [s]
  have hsw_re : (s + w).re = a := by simp [s, w]
  have hs : s ≠ 0 := fun h => by rw [h] at hs_re; simp at hs_re; linarith
  have hsw : s + w ≠ 0 := fun h => by rw [h] at hsw_re; simp at hsw_re; linarith
  rw [hsw', inv_add_eq_geom hs hsw N]
  have hterm : ∀ n, ((-w) ^ n / s ^ (n + 1)).re = ((-(I / 2)) ^ n / s ^ (n + 1)).re * u ^ n := by
    intro n
    have : (-w) ^ n / s ^ (n + 1) = ((u : ℂ)) ^ n * ((-(I / 2)) ^ n / s ^ (n + 1)) := by
      simp only [w]; push_cast; ring
    rw [this, ← Complex.ofReal_pow, Complex.re_ofReal_mul]; ring
  rw [Complex.add_re, Complex.re_sum]
  simp_rw [hterm]
  rw [add_sub_cancel_left]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg]
  have hw : ‖w‖ = |u| / 2 := by
    simp only [w, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_div, abs_two]
  have hs_ge : a ≤ ‖s‖ := by rw [← hs_re]; exact Complex.re_le_norm s
  have hsw_ge : a ≤ ‖s + w‖ := by rw [← hsw_re]; exact Complex.re_le_norm _
  rw [hw]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul (pow_le_pow_left₀ ha.le hs_ge N) hsw_ge ha.le (by positivity)

/-- **The logarithm, tangent bound.** For `0 < q` and `0 < x`, `log q + 1 - q/x ≤ log x`. -/
theorem log_ge_tangent {q x : ℝ} (hq : 0 < q) (hx : 0 < x) : Real.log q + 1 - q / x ≤ Real.log x := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hq)
  rw [Real.log_div hx.ne' hq.ne', inv_div] at h
  linarith

/-- **The cosine around a centre.** `cos((c + u)L) = Re(e^{icL} Σ_{n<N} (iuL)^n/n!) + R` with
`|R| ≤ (|u| L)^N / N!` (`L ≥ 0`). -/
theorem abs_cos_sub_taylor_le (c u L : ℝ) (N : ℕ) :
    |Real.cos ((c + u) * L) -
        (Complex.exp (I * (c * L : ℝ)) * ∑ m ∈ range N, (I * (u * L : ℝ)) ^ m / m.factorial).re| ≤
      |u * L| ^ N / N.factorial := by
  have hsplit : Complex.exp (I * ((c + u) * L : ℝ)) =
      Complex.exp (I * (c * L : ℝ)) * Complex.exp (I * (u * L : ℝ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hcos : Real.cos ((c + u) * L) = (Complex.exp (I * ((c + u) * L : ℝ))).re := by
    rw [mul_comm I, Complex.exp_ofReal_mul_I_re]
  rw [hcos, hsplit, ← Complex.sub_re, ← mul_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  have h1 : ‖Complex.exp (I * ((c * L : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, h1, one_mul]
  exact Complex.norm_exp_I_mul_sub_taylor_le N (u * L)

/-- **A polynomial on a small interval.** If `|u| ≤ h`, then
`d_0 - Σ_{0<n<N} |d_n| h^n ≤ Σ_{n<N} d_n u^n`. -/
theorem poly_ge_of_abs_le {N : ℕ} (d : ℕ → ℝ) {u h : ℝ} (hu : |u| ≤ h) (hN : 0 < N) :
    d 0 - ∑ n ∈ (range N).erase 0, |d n| * h ^ n ≤ ∑ n ∈ range N, d n * u ^ n := by
  rw [← sum_erase_add _ _ (mem_range.mpr hN)]
  simp only [pow_zero, mul_one]
  have : ∀ n ∈ (range N).erase 0, -(|d n| * h ^ n) ≤ d n * u ^ n := by
    intro n _
    have h1 : |d n * u ^ n| ≤ |d n| * h ^ n := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg u) hu n) (abs_nonneg _)
    exact (abs_le.mp h1).1
  have hs := sum_le_sum this
  rw [sum_neg_distrib] at hs
  linarith

end GppWindowElementary

#print axioms GppWindowElementary.abs_re_inv_sub_taylor_le
#print axioms GppWindowElementary.abs_cos_sub_taylor_le
#print axioms GppWindowElementary.poly_ge_of_abs_le
