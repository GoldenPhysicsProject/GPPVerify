import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The fixed-window transform and its exact zero set

Source: Codex, GPPDiscovery2 `discovery/rh/RH_VACUUM_INSTABILITY_EXPONENT_2026-09-24.md`, §1
(formalized here 2026-09-27).

For a window width `ℓ > 0`, the normalized box `f_ℓ = ℓ^{-1/2} 1_{[0,ℓ]}` has autocorrelation the
triangle `h_ℓ(u) = (1 - |u|/ℓ)_+`, and the note's window transform is its two-sided Laplace
transform

  H_ℓ(z) = ∫_{-ℓ}^{ℓ} (1 - |u|/ℓ) e^{zu} du = ℓ (sinh(ℓz/2) / (ℓz/2))².

## Proved here

* `windowTransform_eq`: for `z ≠ 0`, `H_ℓ(z) = (e^{ℓz/2} - e^{-ℓz/2})² / (ℓ z²)`, which is the
  note's `ℓ (sinh(ℓz/2)/(ℓz/2))²` (`windowTransform_eq_sinh`);
* `windowTransform_zero`: `H_ℓ(0) = ℓ`;
* `windowTransform_eq_zero_iff`: `H_ℓ(z) = 0 ↔ z = 2πik/ℓ` for some integer `k ≠ 0`;
* `windowTransform_ne_zero_of_re_ne_zero`: `H_ℓ(z) ≠ 0` whenever `Re z ≠ 0`.

## Correction to the note

The note states that `H_ℓ` "does not vanish at any nontrivial zeta exponent `λ_ρ = ρ - 1/2`".
By `windowTransform_eq_zero_iff` that holds exactly when no zero has `ρ = 1/2 + 2πik/ℓ`,
`k ≠ 0` — i.e. it can fail for a critical-line zero whose ordinate is a nonzero multiple of
`2π/ℓ`, and it is not known to hold for any particular `ℓ`. The note's lower-bound argument
only evaluates `H_ℓ` at an exponent with `Re λ_ρ > α ≥ 0`, which is off the imaginary axis, so
`windowTransform_ne_zero_of_re_ne_zero` is exactly what that argument needs, and it survives.

## Not formalized here

The exponent theorem `σ_ℓ = κ_ℓ = Θ` itself (and `RH ⟺ κ_ℓ = 0`) rests on the explicit-formula
zero sum and on Landau's theorem for Laplace transforms of nonnegative functions; neither is
available in the pinned Mathlib.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real

namespace GppFixedWindowTransform

/-- The fixed-window transform `H_ℓ(z) = ∫_{-ℓ}^{ℓ} (1 - |u|/ℓ) e^{zu} du`. -/
noncomputable def windowTransform (ℓ : ℝ) (z : ℂ) : ℂ :=
  ∫ u in (-ℓ)..ℓ, ((1 - |u| / ℓ : ℝ) : ℂ) * cexp (z * u)

/-- Right half: `∫_0^ℓ (1 - u/ℓ) e^{zu} du = e^{zℓ}/(ℓz²) - 1/z - 1/(ℓz²)`. -/
lemma integral_right (ℓ : ℝ) (hℓ : 0 < ℓ) (z : ℂ) (hz : z ≠ 0) :
    ∫ u in (0 : ℝ)..ℓ, ((1 - |u| / ℓ : ℝ) : ℂ) * cexp (z * u) =
      cexp (z * ℓ) / (ℓ * z ^ 2) - 1 / z - 1 / (ℓ * z ^ 2) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  let F : ℝ → ℂ := fun u => cexp (z * u) * ((1 - (u : ℂ) / ℓ) / z + 1 / (ℓ * z ^ 2))
  have hF : ∀ u : ℝ, HasDerivAt F (((1 - u / ℓ : ℝ) : ℂ) * cexp (z * u)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => cexp (z * u)) (cexp (z * u) * z) u := by
      have := ((hasDerivAt_id (u : ℂ)).const_mul z).cexp.comp_ofReal
      simpa using this
    have h2 : HasDerivAt (fun u : ℝ => (1 - (u : ℂ) / ℓ) / z + 1 / (ℓ * z ^ 2))
        (-(1 / ℓ) / z) u := by
      have := (((hasDerivAt_id (u : ℂ)).div_const (ℓ : ℂ)).const_sub 1).div_const z
      have := (this.comp_ofReal).add_const (1 / (ℓ * z ^ 2))
      simpa using this
    have h : HasDerivAt F (cexp (z * u) * z * ((1 - (u : ℂ) / ℓ) / z + 1 / (ℓ * z ^ 2)) +
        cexp (z * u) * (-(1 / ℓ) / z)) u := h1.mul h2
    refine h.congr_deriv ?_
    push_cast
    field_simp
    ring
  have hint : ∫ u in (0 : ℝ)..ℓ, ((1 - |u| / ℓ : ℝ) : ℂ) * cexp (z * u) =
      ∫ u in (0 : ℝ)..ℓ, ((1 - u / ℓ : ℝ) : ℂ) * cexp (z * u) := by
    refine integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le hℓ.le] at hu
    simp only [abs_of_nonneg hu.1]
  rw [hint, integral_eq_sub_of_hasDerivAt (fun u _ => hF u)
    ((by fun_prop : Continuous fun u : ℝ => ((1 - u / ℓ : ℝ) : ℂ) * cexp (z * u)).intervalIntegrable
      _ _)]
  simp only [F, Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_div, sub_zero, one_mul]
  field_simp
  ring

/-- Left half: `∫_{-ℓ}^0 (1 + u/ℓ) e^{zu} du = 1/z - 1/(ℓz²) + e^{-zℓ}/(ℓz²)`. -/
lemma integral_left (ℓ : ℝ) (hℓ : 0 < ℓ) (z : ℂ) (hz : z ≠ 0) :
    ∫ u in (-ℓ)..0, ((1 - |u| / ℓ : ℝ) : ℂ) * cexp (z * u) =
      1 / z - 1 / (ℓ * z ^ 2) + cexp (-(z * ℓ)) / (ℓ * z ^ 2) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  let G : ℝ → ℂ := fun u => cexp (z * u) * ((1 + (u : ℂ) / ℓ) / z - 1 / (ℓ * z ^ 2))
  have hG : ∀ u : ℝ, HasDerivAt G (((1 + u / ℓ : ℝ) : ℂ) * cexp (z * u)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => cexp (z * u)) (cexp (z * u) * z) u := by
      have := ((hasDerivAt_id (u : ℂ)).const_mul z).cexp.comp_ofReal
      simpa using this
    have h2 : HasDerivAt (fun u : ℝ => (1 + (u : ℂ) / ℓ) / z - 1 / (ℓ * z ^ 2))
        ((1 / ℓ) / z) u := by
      have := (((hasDerivAt_id (u : ℂ)).div_const (ℓ : ℂ)).const_add 1).div_const z
      have := (this.comp_ofReal).sub_const (1 / (ℓ * z ^ 2))
      simpa using this
    have h : HasDerivAt G (cexp (z * u) * z * ((1 + (u : ℂ) / ℓ) / z - 1 / (ℓ * z ^ 2)) +
        cexp (z * u) * ((1 / ℓ) / z)) u := h1.mul h2
    refine h.congr_deriv ?_
    push_cast
    field_simp
    ring
  have hint : ∫ u in (-ℓ)..0, ((1 - |u| / ℓ : ℝ) : ℂ) * cexp (z * u) =
      ∫ u in (-ℓ)..0, ((1 + u / ℓ : ℝ) : ℂ) * cexp (z * u) := by
    refine integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by linarith)] at hu
    simp only [abs_of_nonpos hu.2]
    congr 2
    ring
  rw [hint, integral_eq_sub_of_hasDerivAt (fun u _ => hG u)
    ((by fun_prop : Continuous fun u : ℝ => ((1 + u / ℓ : ℝ) : ℂ) * cexp (z * u)).intervalIntegrable
      _ _)]
  simp only [G, Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_div, add_zero, one_mul,
    Complex.ofReal_neg]
  field_simp
  ring

lemma integrable_window (ℓ : ℝ) (z : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => ((1 - |u| / ℓ : ℝ) : ℂ) * cexp (z * u)) volume a b :=
  (by fun_prop : Continuous fun u : ℝ => ((1 - |u| / ℓ : ℝ) : ℂ) * cexp (z * u)).intervalIntegrable
    _ _

/-- **Closed form**, factored: for `z ≠ 0`, `H_ℓ(z) = (e^{ℓz} - 1)² e^{-ℓz} / (ℓ z²)`. -/
theorem windowTransform_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (z : ℂ) (hz : z ≠ 0) :
    windowTransform ℓ z = (cexp (z * ℓ) - 1) ^ 2 * cexp (-(z * ℓ)) / (ℓ * z ^ 2) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  unfold windowTransform
  rw [← integral_add_adjacent_intervals (b := 0) (integrable_window ℓ z _ _)
    (integrable_window ℓ z _ _), integral_left ℓ hℓ z hz, integral_right ℓ hℓ z hz]
  have hE : cexp (z * ℓ) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.exp_neg]
  field_simp
  ring

/-- The note's form `H_ℓ(z) = ℓ (sinh(ℓz/2) / (ℓz/2))²`, for `z ≠ 0`. -/
theorem windowTransform_eq_sinh (ℓ : ℝ) (hℓ : 0 < ℓ) (z : ℂ) (hz : z ≠ 0) :
    windowTransform ℓ z = ℓ * (Complex.sinh (ℓ * z / 2) / (ℓ * z / 2)) ^ 2 := by
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  rw [windowTransform_eq ℓ hℓ z hz]
  have h2 : 2 * Complex.sinh (ℓ * z / 2) = cexp (ℓ * z / 2) - cexp (-(ℓ * z / 2)) :=
    Complex.two_sinh _
  have hs : Complex.sinh (ℓ * z / 2) = (cexp (ℓ * z / 2) - cexp (-(ℓ * z / 2))) / 2 := by
    rw [← h2]; ring
  have e1 : cexp (z * ℓ) = cexp (ℓ * z / 2) ^ 2 := by
    rw [sq, ← Complex.exp_add]; ring_nf
  have hA : cexp (ℓ * z / 2) ≠ 0 := Complex.exp_ne_zero _
  rw [hs, Complex.exp_neg, Complex.exp_neg, e1]
  field_simp

/-- `H_ℓ(0) = ∫_{-ℓ}^{ℓ} (1 - |u|/ℓ) du = ℓ`. -/
theorem windowTransform_zero (ℓ : ℝ) (hℓ : 0 < ℓ) : windowTransform ℓ 0 = ℓ := by
  have hreal : ∫ u in (-ℓ)..ℓ, (1 - |u| / ℓ) = ℓ := by
    have hi : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => 1 - |u| / ℓ) volume a b :=
      fun a b => (by fun_prop : Continuous fun u : ℝ => 1 - |u| / ℓ).intervalIntegrable _ _
    rw [← integral_add_adjacent_intervals (b := 0) (hi _ _) (hi _ _)]
    have hL : ∫ u in (-ℓ)..0, (1 - |u| / ℓ) = ∫ u in (-ℓ)..0, (1 + u / ℓ) := by
      refine integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by linarith)] at hu
      simp only [abs_of_nonpos hu.2]; ring
    have hR : ∫ u in (0 : ℝ)..ℓ, (1 - |u| / ℓ) = ∫ u in (0 : ℝ)..ℓ, (1 - u / ℓ) := by
      refine integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le hℓ.le] at hu
      simp only [abs_of_nonneg hu.1]
    have dL : ∀ u : ℝ, HasDerivAt (fun u : ℝ => u + u ^ 2 / (2 * ℓ)) (1 + u / ℓ) u := by
      intro u
      have := (hasDerivAt_id u).add ((hasDerivAt_pow 2 u).div_const (2 * ℓ))
      refine this.congr_deriv ?_
      field_simp; ring
    have dR : ∀ u : ℝ, HasDerivAt (fun u : ℝ => u - u ^ 2 / (2 * ℓ)) (1 - u / ℓ) u := by
      intro u
      have := (hasDerivAt_id u).sub ((hasDerivAt_pow 2 u).div_const (2 * ℓ))
      refine this.congr_deriv ?_
      field_simp; ring
    rw [hL, hR, integral_eq_sub_of_hasDerivAt (fun u _ => dL u)
        ((by fun_prop : Continuous fun u : ℝ => 1 + u / ℓ).intervalIntegrable _ _),
      integral_eq_sub_of_hasDerivAt (fun u _ => dR u)
        ((by fun_prop : Continuous fun u : ℝ => 1 - u / ℓ).intervalIntegrable _ _)]
    field_simp
    ring
  unfold windowTransform
  simp only [zero_mul, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, hreal]

/-- **Exact zero set.** `H_ℓ(z) = 0` iff `z = 2πik/ℓ` for some integer `k ≠ 0`. -/
theorem windowTransform_eq_zero_iff (ℓ : ℝ) (hℓ : 0 < ℓ) (z : ℂ) :
    windowTransform ℓ z = 0 ↔ ∃ k : ℤ, k ≠ 0 ∧ z = k * (2 * π * I) / ℓ := by
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  constructor
  · intro h
    by_cases hz : z = 0
    · rw [hz, windowTransform_zero ℓ hℓ] at h
      exact absurd h (by exact_mod_cast hℓ.ne')
    rw [windowTransform_eq ℓ hℓ z hz] at h
    have hden : (ℓ : ℂ) * z ^ 2 ≠ 0 := mul_ne_zero hℓc (pow_ne_zero 2 hz)
    have h1 : (cexp (z * ℓ) - 1) ^ 2 * cexp (-(z * ℓ)) = 0 := by
      rwa [div_eq_zero_iff, or_iff_left hden] at h
    have h2 : cexp (z * ℓ) = 1 := by
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3)
      · exact absurd h3 (Complex.exp_ne_zero _)
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h2
    refine ⟨k, ?_, ?_⟩
    · rintro rfl
      simp only [Int.cast_zero, zero_mul, mul_eq_zero, Complex.ofReal_eq_zero] at hk
      rcases hk with hk | hk
      · exact hz hk
      · exact hℓ.ne' hk
    · rw [eq_div_iff hℓc, hk]
  · rintro ⟨k, hk, rfl⟩
    have hz : (k : ℂ) * (2 * π * I) / ℓ ≠ 0 := by
      refine div_ne_zero (mul_ne_zero (by exact_mod_cast hk) ?_) hℓc
      exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    rw [windowTransform_eq ℓ hℓ _ hz]
    have : cexp ((k : ℂ) * (2 * π * I) / ℓ * ℓ) = 1 := by
      rw [div_mul_cancel₀ _ hℓc]
      exact Complex.exp_eq_one_iff.mpr ⟨k, rfl⟩
    rw [this]
    simp

/-- `H_ℓ` has no zeros off the imaginary axis: `Re z ≠ 0 → H_ℓ(z) ≠ 0`. This is what the
note's lower-bound argument uses (at an exponent with `Re λ_ρ > α ≥ 0`). -/
theorem windowTransform_ne_zero_of_re_ne_zero (ℓ : ℝ) (hℓ : 0 < ℓ) (z : ℂ) (hz : z.re ≠ 0) :
    windowTransform ℓ z ≠ 0 := by
  intro h
  obtain ⟨k, -, rfl⟩ := (windowTransform_eq_zero_iff ℓ hℓ z).mp h
  apply hz
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  rw [show (k : ℂ) * (2 * π * I) / ℓ = ((2 * π * k / ℓ : ℝ) : ℂ) * I by
    push_cast; field_simp]
  simp

end GppFixedWindowTransform
