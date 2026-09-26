import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-!
# Half-shifted Gamma modulus identity

For real `y`, Euler reflection at `z = 1/2 + i y` gives

  Gamma(1/2+i y) Gamma(1/2-i y) = pi / cosh(pi y).

This is the exact boundary identity behind the Gamma half-plane factorization of
`sech(k/2)^2` after the scaling `y = k/(2*pi)`.
-/

namespace GppGammaHalfModulus

open Complex

/-- Sine on the shifted imaginary axis: `sin(pi(1/2+i y)) = cosh(pi y)`. -/
theorem sin_pi_half_add_I (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (((1 : ℂ) / 2) + (y : ℂ) * I)) =
      Complex.cosh ((Real.pi : ℂ) * (y : ℂ)) := by
  rw [show (Real.pi : ℂ) * (((1 : ℂ) / 2) + (y : ℂ) * I) =
      (Real.pi : ℂ) / 2 + ((Real.pi : ℂ) * (y : ℂ)) * I by ring]
  rw [Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I]
  simp

/-- **Half-shifted Gamma modulus identity.** -/
theorem gamma_half_add_mul_gamma_half_sub (y : ℝ) :
    Complex.Gamma (((1 : ℂ) / 2) + (y : ℂ) * I) *
      Complex.Gamma (((1 : ℂ) / 2) - (y : ℂ) * I) =
        ((Real.pi / Real.cosh (Real.pi * y) : ℝ) : ℂ) := by
  let z : ℂ := ((1 : ℂ) / 2) + (y : ℂ) * I
  have href := Complex.Gamma_mul_Gamma_one_sub z
  have hone : 1 - z = ((1 : ℂ) / 2) - (y : ℂ) * I := by
    dsimp [z]
    ring
  have hsin : Complex.sin ((Real.pi : ℂ) * z) =
      Complex.cosh ((Real.pi : ℂ) * (y : ℂ)) := by
    dsimp [z]
    exact sin_pi_half_add_I y
  rw [hone, hsin] at href
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh] at href
  push_cast at href
  simpa [z] using href

end GppGammaHalfModulus

#print axioms GppGammaHalfModulus.gamma_half_add_mul_gamma_half_sub
