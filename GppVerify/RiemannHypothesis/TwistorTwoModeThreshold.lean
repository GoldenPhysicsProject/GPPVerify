import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The sharp two-mode threshold for real-rootedness of a cosh mixture

Source: Codex/GPP, `work/codex/2026-10-16_twistor_theta_mixture_fisher_variance_obstruction.md`
(Pick comment 6222904247) and the sharp-threshold commits `01ceb3c`/`74c3bfe`; independently checked
numerically (sympy, float) in the bridge channel on 2026-10-16. Grok S49's Lean ask
`0 < Re(1/w²) ↔ |Im w| < |Re w|` is included.

For real `c`, the function `F_c(z) = cosh(2z) + c·cosh z` has **all its zeros on the imaginary axis
iff `|c| ≤ 1`**. With `y = cosh z`, `F_c = 2y² + c y − 1`, so the roots are
`y = (−c ± √(c²+8))/4`, both real; they lie in `[−1,1]` exactly when `|c| ≤ 1`.

* `onAxis_of_abs_le_one`: `|c| ≤ 1` ⇒ every zero has real part `0`.
* `offAxis_of_one_lt_abs`: `1 < |c|` ⇒ there is a zero with nonzero real part.
* `zeros_on_axis_iff`: the two combined.
* `re_inv_sq_pos_iff`: `0 < Re (1/w²) ↔ |Im w| < |Re w|`.

**Correction recorded.** The note states the threshold as `0 ≤ c ≤ 1`. The statement as an "iff over
real `c`" is `|c| ≤ 1` (the shift `z ↦ z + iπ` sends `c` to `−c`); for the positive mixtures the
note actually uses (`c ≥ 0`) the two agree, so no claim in the note is affected.

**Scope.** This is the finite algebra of one two-mode example (the fake filter). It does not touch
the Fisher-variance identity, the true `ξ` margin, or any statement about zeros of `ξ` or `ζ`.
No RH claim.
-/

namespace GppTwistorTwoModeThreshold

open Complex
open scoped Real

/-- `cosh (2z) = 2 cosh² z − 1`, so `F_c` is a quadratic in `y = cosh z`. -/
theorem F_eq (c : ℝ) (z : ℂ) :
    cosh (2 * z) + c * cosh z = 2 * cosh z ^ 2 + c * cosh z - 1 := by
  rw [cosh_two_mul]
  linear_combination (-1 : ℂ) * cosh_sq z

/-- Real and imaginary parts of `cosh z`. -/
theorem cosh_re_im (z : ℂ) :
    cosh z = ((Real.cosh z.re * Real.cos z.im : ℝ) : ℂ) +
      ((Real.sinh z.re * Real.sin z.im : ℝ) : ℂ) * I := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := (re_add_im z).symm
  conv_lhs => rw [hz]
  rw [cosh_add, cosh_mul_I, sinh_mul_I]
  push_cast
  simp only [← ofReal_cosh, ← ofReal_sinh, ← ofReal_cos, ← ofReal_sin]
  ring

/-- A `z` with `cosh z = y` real, `y ∈ [-1,1]`, has `Re z = 0`. -/
theorem re_eq_zero_of_cosh_real {z : ℂ} {y : ℝ} (hy : cosh z = y) (h1 : -1 ≤ y) (h2 : y ≤ 1) :
    z.re = 0 := by
  have h := cosh_re_im z
  rw [hy] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [ofReal_re, add_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero,
    add_im, mul_im, add_zero, mul_one] at hre him
  by_contra hz
  have hs : Real.sinh z.re ≠ 0 := fun h0 => hz (Real.sinh_eq_zero.mp h0)
  have hsin : Real.sin z.im = 0 := by
    rcases mul_eq_zero.mp (show Real.sinh z.re * Real.sin z.im = 0 by linarith) with h0 | h0
    · exact absurd h0 hs
    · exact h0
  have hcos : Real.cos z.im ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq z.im
    rw [hsin] at this; linarith
  have hcosh : 1 < Real.cosh z.re := Real.one_lt_cosh.mpr hz
  have hy2 : y ^ 2 = Real.cosh z.re ^ 2 := by
    have : y = Real.cosh z.re * Real.cos z.im := by linarith
    rw [this]; nlinarith [hcos]
  nlinarith [hcosh, hy2]

/-- A real `y` with `1 < |y|` is `cosh z` for some `z` with `Re z ≠ 0`. -/
theorem exists_cosh_offAxis {y : ℝ} (hy : 1 < |y|) : ∃ z : ℂ, z.re ≠ 0 ∧ cosh z = y := by
  set x := |y| with hx
  have hx1 : 1 < x := hy
  set a := Real.arsinh (√(x ^ 2 - 1)) with ha
  have hsq : √(x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hca : Real.cosh a = x := by
    rw [ha, Real.cosh_arsinh, show 1 + √(x ^ 2 - 1) ^ 2 = x ^ 2 by rw [hsq]; ring]
    exact Real.sqrt_sq (by linarith)
  have hapos : 0 < a := by
    rw [ha]
    exact Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr (by nlinarith))
  rcases le_or_gt 0 y with hy0 | hy0
  · refine ⟨(a : ℂ), by simpa using hapos.ne', ?_⟩
    rw [← ofReal_cosh, hca, hx, abs_of_nonneg hy0]
  · refine ⟨(a : ℂ) + π * I, by simpa using hapos.ne', ?_⟩
    rw [cosh_add, cosh_mul_I, sinh_mul_I, ← ofReal_cosh, ← ofReal_sinh]
    have : Complex.cos (π : ℂ) = -1 := by exact_mod_cast Real.cos_pi
    have h2 : Complex.sin (π : ℂ) = 0 := by exact_mod_cast Real.sin_pi
    rw [this, h2, hca, hx, abs_of_neg hy0]
    push_cast; ring

/-- If `|c| ≤ 1`, every zero of `cosh 2z + c cosh z` lies on the imaginary axis. -/
theorem onAxis_of_abs_le_one {c : ℝ} (hc : |c| ≤ 1) {z : ℂ}
    (hz : cosh (2 * z) + c * cosh z = 0) : z.re = 0 := by
  rw [F_eq] at hz
  set s := √(c ^ 2 + 8) with hs
  have hs2 : s ^ 2 = c ^ 2 + 8 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hc1 := abs_le.mp hc
  have hs3 : s ≤ 3 := by nlinarith [sq_nonneg c]
  have hs_ge : 2 ≤ s := by nlinarith [sq_nonneg c]
  have hq : (4 * cosh z + c) ^ 2 = (s : ℂ) ^ 2 := by
    have : ((s : ℂ)) ^ 2 = (c : ℂ) ^ 2 + 8 := by exact_mod_cast hs2
    rw [this]; linear_combination 8 * hz
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hq with h | h
  · refine re_eq_zero_of_cosh_real (y := (s - c) / 4) ?_ (by linarith [hc1.1, hc1.2]) (by linarith [hc1.1, hc1.2])
    push_cast; linear_combination h / 4
  · refine re_eq_zero_of_cosh_real (y := (-s - c) / 4) ?_ (by linarith [hc1.1, hc1.2]) (by linarith [hc1.1, hc1.2])
    push_cast; linear_combination h / 4

/-- If `1 < |c|`, some zero of `cosh 2z + c cosh z` is off the imaginary axis. -/
theorem offAxis_of_one_lt_abs {c : ℝ} (hc : 1 < |c|) :
    ∃ z : ℂ, z.re ≠ 0 ∧ cosh (2 * z) + c * cosh z = 0 := by
  set s := √(c ^ 2 + 8) with hs
  have hs2 : s ^ 2 = c ^ 2 + 8 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- a real root y of 2y² + c y − 1 with |y| > 1
  obtain ⟨y, hy1, hyroot⟩ : ∃ y : ℝ, 1 < |y| ∧ 2 * y ^ 2 + c * y - 1 = 0 := by
    rcases lt_abs.mp hc with h | h
    · refine ⟨(-c - s) / 4, ?_, by nlinarith⟩
      have : 4 - c < s := by
        by_contra hh
        have hh := not_lt.mp hh
        nlinarith
      rw [abs_of_neg (by linarith)]; linarith
    · refine ⟨(-c + s) / 4, ?_, by nlinarith⟩
      have : 4 + c < s := by
        by_contra hh
        have hh := not_lt.mp hh
        nlinarith
      rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨z, hz0, hz⟩ := exists_cosh_offAxis hy1
  refine ⟨z, hz0, ?_⟩
  rw [F_eq, hz]
  exact_mod_cast hyroot

/-- **Sharp two-mode threshold**: all zeros of `cosh 2z + c cosh z` are on the imaginary axis iff
`|c| ≤ 1`. -/
theorem zeros_on_axis_iff (c : ℝ) :
    (∀ z : ℂ, cosh (2 * z) + c * cosh z = 0 → z.re = 0) ↔ |c| ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨z, hz0, hz⟩ := offAxis_of_one_lt_abs (not_le.mp hc)
    exact hz0 (h z hz)
  · intro hc z hz
    exact onAxis_of_abs_le_one hc hz

/-- Grok S49's Lean ask: `0 < Re (1/w²) ↔ |Im w| < |Re w|`. -/
theorem re_inv_sq_pos_iff (w : ℂ) : 0 < ((1 : ℂ) / w ^ 2).re ↔ |w.im| < |w.re| := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hn : 0 < Complex.normSq (w ^ 2) := Complex.normSq_pos.mpr (pow_ne_zero 2 hw)
  have hnum : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [pow_two]
  rw [one_div, Complex.inv_re, hnum, div_pos_iff_of_pos_right hn, sub_pos]
  exact sq_lt_sq

end GppTwistorTwoModeThreshold
