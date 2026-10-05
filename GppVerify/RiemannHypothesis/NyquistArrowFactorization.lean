import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Nyquist-fold prime kernel as a two-arrow Gram difference

This file formalizes the exact trigonometric factorization found in the
GPPDiscovery2 RH arrow-roadmap execution note dated 2026-10-05.

For a real bandwidth parameter c, define the band kernel

  T_c(x,y) = 2 sin(c(x-y)/2) / (pi(x-y))       if x != y,
             c/pi                              if x = y,

and the folded divided-difference kernel

  q_c(x,y) = (sin(cx)-sin(cy))/(pi(x-y))       if x != y,
             (c/pi) cos(cx)                    if x = y.

Writing

  C_c(x)=cos(cx/2),  S_c(x)=sin(cx/2),

one has pointwise

  q_c(x,y)
    = T_c(x,y) (C_c(x) C_c(y) - S_c(x) S_c(y)).

Thus every finite matrix cut from q_c is the difference of two congruences
of the same band kernel. Analytically the band kernel is a positive Gram
kernel; that integral/PSD statement is deliberately not asserted here.
The present file is exact finite algebra only and contains no RH claim.
-/

namespace GppNyquistArrow

noncomputable def bandKernel (c x y : ℝ) : ℝ :=
  if x = y then c / Real.pi
  else 2 * Real.sin (c * (x - y) / 2) / (Real.pi * (x - y))

noncomputable def foldedKernel (c x y : ℝ) : ℝ :=
  if x = y then (c / Real.pi) * Real.cos (c * x)
  else (Real.sin (c * x) - Real.sin (c * y)) / (Real.pi * (x - y))

noncomputable def evenChannel (c x : ℝ) : ℝ := Real.cos (c * x / 2)
noncomputable def oddChannel (c x : ℝ) : ℝ := Real.sin (c * x / 2)

/-- The elementary product-to-difference identity behind the arrow split. -/
lemma two_sin_sub_mul_cos_add (A B : ℝ) :
    2 * Real.sin (A - B) * Real.cos (A + B)
      = Real.sin (2 * A) - Real.sin (2 * B) := by
  rw [Real.sin_sub, Real.cos_add, Real.sin_two_mul, Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B]

/-- Exact two-arrow factorization of the Nyquist-fold kernel. -/
theorem foldedKernel_factor (c x y : ℝ) :
    foldedKernel c x y =
      bandKernel c x y *
        (evenChannel c x * evenChannel c y - oddChannel c x * oddChannel c y) := by
  by_cases hxy : x = y
  · subst y
    simp only [foldedKernel, bandKernel, hxy, if_true, evenChannel, oddChannel]
    rw [show c * x = c * x / 2 + c * x / 2 by ring, Real.cos_add]
    ring
  · simp only [foldedKernel, bandKernel, hxy, if_false, evenChannel, oddChannel]
    have hden : Real.pi * (x - y) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hxy)
    have htrig :
        2 * Real.sin (c * (x - y) / 2) *
            (Real.cos (c * x / 2) * Real.cos (c * y / 2) -
              Real.sin (c * x / 2) * Real.sin (c * y / 2))
          = Real.sin (c * x) - Real.sin (c * y) := by
      rw [← Real.cos_add]
      have hA :
          c * (x - y) / 2 = c * x / 2 - c * y / 2 := by ring
      rw [hA]
      have h := two_sin_sub_mul_cos_add (c * x / 2) (c * y / 2)
      convert h using 1 <;> ring
    field_simp [hden]
    nlinarith

/-- At a half-turn, two diagonal entries have opposite signs. -/
theorem half_turn_signature :
    foldedKernel Real.pi 0 0 = 1 ∧ foldedKernel Real.pi 1 1 = -1 := by
  constructor <;> simp [foldedKernel, Real.pi_ne_zero]

end GppNyquistArrow

#print axioms GppNyquistArrow.foldedKernel_factor
#print axioms GppNyquistArrow.half_turn_signature
