import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Finite arrow-dictionary identities

Small unconditional lemmas used by the RH/WWIF discovery program.
They formalize only the finite algebraic dictionary; no RH claim is made.
-/

namespace GppArrowDictionaryFinite

open Complex

/-- Arithmetic complete reversal: rho ↦ 1 - conjugate rho. -/
def D (rho : ℂ) : ℂ := 1 - starRingEnd ℂ rho

/-- The fixed locus of arithmetic complete reversal is exactly Re rho = 1/2. -/
theorem D_fixed_iff_re_half (rho : ℂ) :
    D rho = rho ↔ rho.re = (1 : ℝ) / 2 := by
  constructor
  · intro h
    have hre : (1 - starRingEnd ℂ rho).re = rho.re := congrArg Complex.re h
    simp [Complex.sub_re, Complex.one_re, RCLike.star_def, Complex.conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp [D, Complex.sub_re, Complex.one_re, RCLike.star_def, Complex.conj_re]
      linarith
    · simp [D, Complex.sub_im, Complex.one_im, RCLike.star_def, Complex.conj_im]

/-- Centered real displacement changes sign under complete reversal. -/
theorem centered_bias_reversal (rho : ℂ) :
    (D rho).re - (1 : ℝ) / 2 = -(rho.re - (1 : ℝ) / 2) := by
  simp [D, Complex.sub_re, Complex.one_re, RCLike.star_def, Complex.conj_re]
  ring

/-- The two members of a reversal orbit have exactly zero signed mean bias. -/
theorem orbit_bias_cancels (rho : ℂ) :
    (rho.re - (1 : ℝ) / 2) + ((D rho).re - (1 : ℝ) / 2) = 0 := by
  rw [centered_bias_reversal]
  ring

/-- The sigma_1 quadratic form is indefinite: it has both signs. -/
def sigmaOneForm (x y : ℝ) : ℝ := 2 * x * y

theorem sigmaOne_indefinite :
    sigmaOneForm 1 1 > 0 ∧ sigmaOneForm 1 (-1) < 0 := by
  norm_num [sigmaOneForm]

/-- A positive and negative orientation label cannot be identified pointwise
    unless the centered displacement is zero. -/
theorem eq_neg_iff_zero (delta : ℝ) :
    delta = -delta ↔ delta = 0 := by
  constructor
  · intro h
    linarith
  · intro h
    simp [h]

/-- If an orbit collapses to one point under complete reversal, it lies on
    the critical line. -/
theorem collapsed_orbit_principal {rho : ℂ} (h : D rho = rho) :
    rho.re = (1 : ℝ) / 2 :=
  (D_fixed_iff_re_half rho).mp h

end GppArrowDictionaryFinite
