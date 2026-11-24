import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Exponential

/-!
# Fixed-angle dilation stencils of `log (1 - exp (-t))`

With `ℓ(t) = log (1 - exp (-t))` and the dilation `T f (t) = f (2t)`:

* `evenS f` is the stencil `(T + T⁻¹ - 2)(T + T⁻¹ - 5/2) f`, weights `(1, -9/2, 7, -9/2, 1)` on
  the scales `4t, 2t, t, t/2, t/4` (`evenS_factor`); `halfS f` is the half-turn stencil
  `(T - T⁻¹)(T + T⁻¹ - 5/2) f`, weights `(1, -5/2, 0, 5/2, -1)` (`halfS_factor`).
* `ell_eq`: `ℓ(t) = -t/2 + log t + g(t/2)` for `t > 0`, where `g(u) = log (sinh u / u)` (`gS`).
  Both stencils annihilate the linear term and the `log t` term; the half-turn stencil leaves
  the constant `-log 2` (`evenS_ell`, `halfS_ell`).
* `gS_bound`: `|g(u) - u²/6| ≤ u⁴/10` for `0 < u ≤ 1`, from the degree-five exponential bound and
  the second-order logarithm bound (`sinh_taylor_bound`, `log_one_add_bound`).
* `evenS_ell_bound`: `|B(t) - (21/128) t²| ≤ 3 t⁴` and `halfS_ell_bound`:
  `|A(t) + log 2 - (35/128) t²| ≤ 3 t⁴`, for `0 < t ≤ 1/2`, where `B = evenS ℓ`, `A = halfS ℓ`.
  The coefficients are `Σ aⱼ 4ʲ / 24` over the stencil weights: `(63/16)/24 = 21/128` and
  `(105/16)/24 = 35/128`.

These are the finite dilation identities of the fixed-angle oscillator filing (Codex,
GPPDiscovery2 `24e7f78`, `experiments/cesaro_statehood/oscillator_window.md`), audited by Turbo,
here kernel-checked with explicit constants.
-/

open Real Finset

namespace GppDilationStencil

theorem sinh_taylor_bound {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |sinh u - u - u ^ 3 / 6| ≤ u ^ 5 / 50 := by
  have hp := Real.exp_bound (x := u) (by rw [abs_of_nonneg h0]; exact h1) (n := 5) (by norm_num)
  have hm := Real.exp_bound (x := -u) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 5)
    (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, abs_neg, abs_of_nonneg h0] at hp hm
  norm_num at hp hm
  rw [sinh_eq]
  have e1 := abs_le.1 hp
  have e2 := abs_le.1 hm
  rw [abs_le]
  constructor <;> nlinarith [pow_nonneg h0 5]

theorem log_one_add_bound {x : ℝ} (hx : |x| ≤ 1 / 2) : |log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 1
  simp only [sum_range_succ, sum_range_zero, abs_neg, sub_neg_eq_add] at h
  norm_num at h
  have hlt : 0 < 1 - |x| := by linarith
  have h2 : x ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ hlt]
    nlinarith [sq_nonneg x, abs_nonneg x]
  calc |log (1 + x) - x| = |-x + log (1 + x)| := by ring_nf
    _ ≤ x ^ 2 / (1 - |x|) := h
    _ ≤ 2 * x ^ 2 := h2

/-- `g u = log (sinh u / u)`, the even analytic part of `log (1 - exp (-t))`. -/
noncomputable def gS (u : ℝ) : ℝ := log (sinh u / u)

theorem gS_bound {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) : |gS u - u ^ 2 / 6| ≤ u ^ 4 / 10 := by
  have hs := sinh_taylor_bound h0.le h1
  set R := sinh u / u - 1 - u ^ 2 / 6 with hR
  have hRb : |R| ≤ u ^ 4 / 50 := by
    have : R = (sinh u - u - u ^ 3 / 6) / u := by rw [hR]; field_simp
    rw [this, abs_div, abs_of_pos h0, div_le_iff₀ h0]
    calc |sinh u - u - u ^ 3 / 6| ≤ u ^ 5 / 50 := hs
      _ = u ^ 4 / 50 * u := by ring
  set x := u ^ 2 / 6 + R with hx
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  have hu4 : u ^ 4 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
  have hxb : |x| ≤ u ^ 2 / 5 := by
    calc |x| ≤ |u ^ 2 / 6| + |R| := abs_add_le _ _
      _ ≤ u ^ 2 / 6 + u ^ 4 / 50 := by
          rw [abs_of_nonneg (by positivity)]; linarith
      _ ≤ u ^ 2 / 5 := by nlinarith
  have hx12 : |x| ≤ 1 / 2 := by linarith
  have hlog := log_one_add_bound hx12
  have hgx : gS u = log (1 + x) := by
    unfold gS; congr 1; rw [hx, hR]; ring
  rw [hgx]
  have hx2 : x ^ 2 ≤ u ^ 4 / 25 := by
    have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    rw [this]
    calc |x| ^ 2 ≤ (u ^ 2 / 5) ^ 2 := by gcongr
      _ = u ^ 4 / 25 := by ring
  calc |log (1 + x) - u ^ 2 / 6| = |(log (1 + x) - x) + R| := by rw [hx]; ring_nf
    _ ≤ |log (1 + x) - x| + |R| := abs_add_le _ _
    _ ≤ 2 * x ^ 2 + u ^ 4 / 50 := by linarith
    _ ≤ u ^ 4 / 10 := by nlinarith

/-- `ℓ t = log (1 - exp (-t))`. -/
noncomputable def ell (t : ℝ) : ℝ := log (1 - exp (-t))

theorem ell_eq {t : ℝ} (ht : 0 < t) : ell t = -t / 2 + log t + gS (t / 2) := by
  have hs : 0 < sinh (t / 2) := sinh_pos_iff.2 (by linarith)
  have key : 1 - exp (-t) = exp (-t / 2) * (t * (sinh (t / 2) / (t / 2))) := by
    have h3 : t * (sinh (t / 2) / (t / 2)) = exp (t / 2) - exp (-(t / 2)) := by
      rw [sinh_eq]; field_simp
    rw [h3, mul_sub, ← exp_add, ← exp_add]
    have e1 : -t / 2 + t / 2 = 0 := by ring
    have e2 : -t / 2 + -(t / 2) = -t := by ring
    rw [e1, e2, exp_zero]
  unfold ell gS
  rw [key, log_mul (exp_pos _).ne' (by positivity), log_exp,
    log_mul ht.ne' (by positivity)]
  ring

/-- The even dilation stencil, weights `(1, -9/2, 7, -9/2, 1)` on scales `4, 2, 1, 1/2, 1/4`. -/
noncomputable def evenS (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (4 * t) - 9 / 2 * f (2 * t) + 7 * f t - 9 / 2 * f (t / 2) + f (t / 4)

/-- The half-turn stencil, weights `(1, -5/2, 0, 5/2, -1)` on scales `4, 2, 1, 1/2, 1/4`. -/
noncomputable def halfS (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (4 * t) - 5 / 2 * f (2 * t) + 5 / 2 * f (t / 2) - f (t / 4)

/-- The even stencil is `(T + T⁻¹ - 2)(T + T⁻¹ - 5/2)` with `T f (t) = f (2t)`. -/
theorem evenS_factor (f : ℝ → ℝ) (t : ℝ) :
    evenS f t = (fun s => f (2 * s) + f (s / 2) - 5 / 2 * f s) (2 * t) +
      (fun s => f (2 * s) + f (s / 2) - 5 / 2 * f s) (t / 2) -
      2 * (fun s => f (2 * s) + f (s / 2) - 5 / 2 * f s) t := by
  simp only [evenS]
  have a1 : 2 * (2 * t) = 4 * t := by ring
  have a2 : 2 * t / 2 = t := by ring
  have a3 : 2 * (t / 2) = t := by ring
  have a4 : t / 2 / 2 = t / 4 := by ring
  rw [a1, a2, a3, a4]
  ring

/-- The half-turn stencil is `T² - (5/2) T + (5/2) T⁻¹ - T⁻²`, the even stencil's odd partner:
`(T - T⁻¹)(T + T⁻¹ - 5/2)`. -/
theorem halfS_factor (f : ℝ → ℝ) (t : ℝ) :
    halfS f t = (fun s => f (2 * s) + f (s / 2) - 5 / 2 * f s) (2 * t) -
      (fun s => f (2 * s) + f (s / 2) - 5 / 2 * f s) (t / 2) := by
  simp only [halfS]
  have a1 : 2 * (2 * t) = 4 * t := by ring
  have a2 : 2 * t / 2 = t := by ring
  have a3 : 2 * (t / 2) = t := by ring
  have a4 : t / 2 / 2 = t / 4 := by ring
  rw [a1, a2, a3, a4]
  ring

theorem evenS_ell {t : ℝ} (ht : 0 < t) :
    evenS ell t = gS (2 * t) - 9 / 2 * gS t + 7 * gS (t / 2) - 9 / 2 * gS (t / 4) + gS (t / 8) := by
  unfold evenS
  rw [ell_eq (by positivity), ell_eq (by positivity), ell_eq ht, ell_eq (by positivity),
    ell_eq (by positivity), log_mul (by norm_num) ht.ne', log_mul (by norm_num) ht.ne',
    log_div ht.ne' (by norm_num), log_div ht.ne' (by norm_num)]
  have l4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  have e1 : 4 * t / 2 = 2 * t := by ring
  have e2 : 2 * t / 2 = t := by ring
  have e3 : t / 2 / 2 = t / 4 := by ring
  have e4 : t / 4 / 2 = t / 8 := by ring
  rw [l4, e1, e2, e3, e4]
  ring

theorem halfS_ell {t : ℝ} (ht : 0 < t) :
    halfS ell t = -log 2 + gS (2 * t) - 5 / 2 * gS t + 5 / 2 * gS (t / 4) - gS (t / 8) := by
  unfold halfS
  rw [ell_eq (by positivity), ell_eq (by positivity), ell_eq (by positivity),
    ell_eq (by positivity), log_mul (by norm_num) ht.ne', log_mul (by norm_num) ht.ne',
    log_div ht.ne' (by norm_num), log_div ht.ne' (by norm_num)]
  have l4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  have e1 : 4 * t / 2 = 2 * t := by ring
  have e2 : 2 * t / 2 = t := by ring
  have e3 : t / 2 / 2 = t / 4 := by ring
  have e4 : t / 4 / 2 = t / 8 := by ring
  rw [l4, e1, e2, e3, e4]
  ring

/-- The even stencil of `ℓ` at small scale: `B(t) = (21/128) t² + O(t⁴)`, with the explicit
constant `3` for `0 < t ≤ 1/2`. -/
theorem evenS_ell_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    |evenS ell t - 21 / 128 * t ^ 2| ≤ 3 * t ^ 4 := by
  rw [evenS_ell ht]
  have b1 := abs_le.1 (gS_bound (u := 2 * t) (by positivity) (by linarith))
  have b2 := abs_le.1 (gS_bound (u := t) ht (by linarith))
  have b3 := abs_le.1 (gS_bound (u := t / 2) (by positivity) (by linarith))
  have b4 := abs_le.1 (gS_bound (u := t / 4) (by positivity) (by linarith))
  have b5 := abs_le.1 (gS_bound (u := t / 8) (by positivity) (by linarith))
  have ht4 : 0 ≤ t ^ 4 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2]

/-- The half-turn stencil of `ℓ` at small scale: `A(t) = -log 2 + (35/128) t² + O(t⁴)`, with the
explicit constant `3` for `0 < t ≤ 1/2`. -/
theorem halfS_ell_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    |halfS ell t + log 2 - 35 / 128 * t ^ 2| ≤ 3 * t ^ 4 := by
  rw [halfS_ell ht]
  have b1 := abs_le.1 (gS_bound (u := 2 * t) (by positivity) (by linarith))
  have b2 := abs_le.1 (gS_bound (u := t) ht (by linarith))
  have b4 := abs_le.1 (gS_bound (u := t / 4) (by positivity) (by linarith))
  have b5 := abs_le.1 (gS_bound (u := t / 8) (by positivity) (by linarith))
  have ht4 : 0 ≤ t ^ 4 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2, b4.1, b4.2, b5.1, b5.2]

#print axioms sinh_taylor_bound
#print axioms gS_bound
#print axioms ell_eq
#print axioms evenS_factor
#print axioms halfS_factor
#print axioms evenS_ell_bound
#print axioms halfS_ell_bound

end GppDilationStencil
