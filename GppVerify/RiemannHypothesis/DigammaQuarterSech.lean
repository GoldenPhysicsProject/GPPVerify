import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Davenport–Heilbronn archimedean difference is a `sech` kernel

Source: Grok S47 (`work/grok/2026-10-16_s47_dh_actual_vs_planted.md`, bridge), Lean ask
`digamma_quarter_diff_sech`: `Re[ψ(3/4 + ir/2) − ψ(1/4 + ir/2)] = π / cosh(πr)`.

Proved here from Mathlib's `Complex.digamma = logDeriv Gamma` and the Gamma reflection formula:
* `digamma_reflection`: `ψ(1−z) − ψ(z) = π cos(πz)/sin(πz)` whenever neither `z` nor `1−z` is a
  non-positive integer (logarithmic derivative of `Γ(z)Γ(1−z) = π/sin(πz)`).
* `digamma_conj`: `ψ(z̄) = conj ψ(z)` off the poles.
* `re_digamma_quarter_sub`: the stated identity, for every real `r`.

**Scope.** This is the pointwise digamma identity only. Grok's alternative form through
`∫₀^∞ cos(rx)/cosh(x/2) dx` is not formalized here, and nothing below uses the Davenport–Heilbronn
Weil form itself. No RH claim.
-/

namespace GppDigammaQuarterSech

open Complex
open scoped Real

/-- **Digamma reflection**, derived from `Γ(z)Γ(1−z) = π / sin(πz)`. -/
theorem digamma_reflection {z : ℂ} (hz : ∀ m : ℕ, z ≠ -m) (hz1 : ∀ m : ℕ, 1 - z ≠ -m) :
    digamma (1 - z) - digamma z = π * (cos (π * z) / sin (π * z)) := by
  have h0 : Gamma z ≠ 0 := Gamma_ne_zero hz
  have h1 : Gamma (1 - z) ≠ 0 := Gamma_ne_zero hz1
  have hP := Gamma_mul_Gamma_one_sub z
  have hsin : sin (π * z) ≠ 0 := by
    intro h
    rw [h, div_zero] at hP
    exact mul_ne_zero h0 h1 hP
  have hdz : HasDerivAt Gamma (deriv Gamma z) z := (differentiableAt_Gamma z hz).hasDerivAt
  have hd1 : HasDerivAt Gamma (deriv Gamma (1 - z)) (1 - z) :=
    (differentiableAt_Gamma (1 - z) hz1).hasDerivAt
  have hf : HasDerivAt (fun w => Gamma w * Gamma (1 - w))
      (deriv Gamma z * Gamma (1 - z) + Gamma z * (-(deriv Gamma (1 - z)))) z :=
    hdz.mul (hd1.comp_const_sub 1 z)
  have hsn : HasDerivAt (fun w => sin (π * w)) (cos (π * z) * (π : ℂ)) z := by
    have := ((hasDerivAt_id z).const_mul (π : ℂ)).csin
    simpa using this
  have hg : HasDerivAt (fun w => (π : ℂ) / sin (π * w))
      ((0 * sin (π * z) - (π : ℂ) * (cos (π * z) * (π : ℂ))) / sin (π * z) ^ 2) z :=
    (hasDerivAt_const z (π : ℂ)).div hsn hsin
  have hfg : (fun w => Gamma w * Gamma (1 - w)) = fun w => (π : ℂ) / sin (π * w) :=
    funext fun w => Gamma_mul_Gamma_one_sub w
  rw [hfg] at hf
  have E := hf.unique hg
  have E' : deriv Gamma z * Gamma (1 - z) - Gamma z * deriv Gamma (1 - z) =
      -((π : ℂ) ^ 2 * cos (π * z)) / sin (π * z) ^ 2 := by
    calc deriv Gamma z * Gamma (1 - z) - Gamma z * deriv Gamma (1 - z)
        = deriv Gamma z * Gamma (1 - z) + Gamma z * (-(deriv Gamma (1 - z))) := by ring
      _ = (0 * sin (π * z) - (π : ℂ) * (cos (π * z) * (π : ℂ))) / sin (π * z) ^ 2 := E
      _ = -((π : ℂ) ^ 2 * cos (π * z)) / sin (π * z) ^ 2 := by ring
  rw [digamma_def, logDeriv_apply, logDeriv_apply, div_sub_div _ _ h1 h0,
    div_eq_iff (mul_ne_zero h1 h0)]
  calc deriv Gamma (1 - z) * Gamma z - Gamma (1 - z) * deriv Gamma z
      = -(deriv Gamma z * Gamma (1 - z) - Gamma z * deriv Gamma (1 - z)) := by ring
    _ = (π : ℂ) ^ 2 * cos (π * z) / sin (π * z) ^ 2 := by rw [E']; ring
    _ = (π : ℂ) * (cos (π * z) / sin (π * z)) * (Gamma (1 - z) * Gamma z) := by
        rw [mul_comm (Gamma (1 - z)) (Gamma z), hP]
        field_simp

/-- `ψ(z̄) = conj ψ(z)` away from the poles. -/
theorem digamma_conj {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    digamma ((starRingEnd ℂ) s) = (starRingEnd ℂ) (digamma s) := by
  have hd : HasDerivAt Gamma (deriv Gamma s) s := (differentiableAt_Gamma s hs).hasDerivAt
  have hc := hd.conj_conj
  have hfun : (starRingEnd ℂ) ∘ Gamma ∘ (starRingEnd ℂ) = Gamma :=
    funext fun w => by simp [Function.comp, ← Gamma_conj]
  rw [hfun] at hc
  have hc' : HasDerivAt Gamma ((starRingEnd ℂ) (deriv Gamma s)) ((starRingEnd ℂ) s) := hc
  rw [digamma_def, logDeriv_apply, logDeriv_apply, hc'.deriv, Gamma_conj, map_div₀]

/-- For real `c`, the complex number `cos(a+ib)/sin(a+ib)` at `a = π/4`: its real part is
`1 / cosh (2b)`. -/
theorem re_cot_quarter (r : ℝ) :
    (cos (π * (1 / 4 + (r / 2 : ℝ) * I)) / sin (π * (1 / 4 + (r / 2 : ℝ) * I))).re =
      1 / Real.cosh (π * r) := by
  have hz : π * (1 / 4 + ((r / 2 : ℝ) : ℂ) * I) = (π / 4 : ℝ) + ((π * r / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hz, cos_add, sin_add, cos_mul_I, sin_mul_I]
  simp only [← ofReal_cos, ← ofReal_sin, ← ofReal_cosh, ← ofReal_sinh]
  have hc : Real.cos (π / 4) = Real.sin (π / 4) := by
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hcpos : 0 < Real.cos (π / 4) := by rw [Real.cos_pi_div_four]; positivity
  set b := π * r / 2 with hb
  set c := Real.cos (π / 4)
  set C := Real.cosh b
  set S := Real.sinh b
  have hC : 0 < C := Real.cosh_pos b
  have hCS : C ^ 2 - S ^ 2 = 1 := by rw [Real.cosh_sq]; ring
  have h2 : Real.cosh (π * r) = C ^ 2 + S ^ 2 := by
    rw [show π * r = 2 * b by rw [hb]; ring, Real.cosh_two_mul]
  have hden : (C : ℂ) + S * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  rw [← hc]
  have key : ((c : ℂ) * C - (c * S) * I) / ((c : ℂ) * C + (c * S) * I) =
      (((C ^ 2 - S ^ 2) / (C ^ 2 + S ^ 2) : ℝ) : ℂ) - ((2 * C * S / (C ^ 2 + S ^ 2) : ℝ) : ℂ) * I := by
    have hpos : (C : ℂ) ^ 2 + S ^ 2 ≠ 0 := by exact_mod_cast (by positivity : C ^ 2 + S ^ 2 ≠ 0)
    have hden' : (c : ℂ) * C + (c * S) * I ≠ 0 := by
      have : (c : ℂ) * C + (c * S) * I = c * (C + S * I) := by ring
      rw [this]; exact mul_ne_zero hcne hden
    rw [div_eq_iff hden']
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]
    ring
  have e : ((c : ℂ) * C - (c : ℂ) * (S * I)) / ((c : ℂ) * C + (c : ℂ) * (S * I)) =
      ((c : ℂ) * C - (c * S) * I) / ((c : ℂ) * C + (c * S) * I) := by ring_nf
  have hre : ∀ x y : ℝ, ((x : ℂ) - (y : ℂ) * I).re = x := by intro x y; simp
  rw [e, key, hre, hCS, h2]

/-- **Grok S47's lemma**: `Re[ψ(3/4 + ir/2) − ψ(1/4 + ir/2)] = π / cosh(πr)`. -/
theorem re_digamma_quarter_sub (r : ℝ) :
    (digamma (3 / 4 + (r / 2 : ℝ) * I)).re - (digamma (1 / 4 + (r / 2 : ℝ) * I)).re =
      π / Real.cosh (π * r) := by
  set z : ℂ := 1 / 4 + (r / 2 : ℝ) * I with hz
  have hz1 : ∀ m : ℕ, z ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp [hz] at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hw : (1 : ℂ) - z = (starRingEnd ℂ) (3 / 4 + (r / 2 : ℝ) * I) := by
    rw [hz]
    simp only [map_add, map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hw1 : ∀ m : ℕ, 1 - z ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp [hz] at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hw2 : ∀ m : ℕ, (3 / 4 + (r / 2 : ℝ) * I : ℂ) ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hrefl := digamma_reflection hz1 hw1
  have hcj := digamma_conj hw2
  rw [← hw] at hcj
  have hre : (digamma (3 / 4 + (r / 2 : ℝ) * I)).re = (digamma (1 - z)).re := by
    rw [hcj, Complex.conj_re]
  have h3 := congrArg Complex.re hrefl
  rw [Complex.sub_re, Complex.re_ofReal_mul] at h3
  have hcot := re_cot_quarter r
  rw [← hz] at hcot
  rw [hre]
  rw [h3, hcot]
  ring

end GppDigammaQuarterSech
