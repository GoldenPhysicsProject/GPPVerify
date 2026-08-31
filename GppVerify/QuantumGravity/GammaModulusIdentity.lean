import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The Gamma-modulus face: `Γ(1+iλ)·Γ(1-iλ) = πλ/sinh(πλ)`

From `blackbody_law_qg_dtoupin_v1.tex` (Test T2 of `verify_blackbody_capstone.py`): the
Planck spectral weight `P(λ) = πλ/sinh(πλ)` (`StefanBoltzmannFamily.P`) equals the squared
modulus `|Γ(1+iλ)|² = Γ(1+iλ)Γ(1-iλ)` of the Gamma function at the principal-series point
`1+iλ`. This is Euler's reflection formula in disguise.

## Proof

Euler's reflection formula (`Complex.Gamma_mul_Gamma_one_sub`, unconditional on `ℂ`) gives
`Γ(iλ)·Γ(1-iλ) = π/sin(π·iλ)` for every `λ`. Shift by one factor of `iλ` via
`Complex.Gamma_add_one` (valid since `λ ≠ 0 ⟹ iλ ≠ 0`): `Γ(1+iλ) = iλ·Γ(iλ)`, so
`Γ(1+iλ)·Γ(1-iλ) = iλπ/sin(π·iλ)`. The complex identity `sin(x·i) = sinh(x)·i`
(`Complex.sin_mul_I`) turns the denominator into `sinh(πλ)·i`, and the two factors of `i`
cancel exactly, leaving `πλ/sinh(πλ)` — real-valued, matching the paper's claim that the
imaginary part vanishes identically (not merely at the sampled `λ`).
-/

namespace GppGammaModulus

open Complex

/-- **The Gamma-modulus identity**: for every real `λ ≠ 0`,
    `Γ(1+iλ)·Γ(1-iλ) = πλ/sinh(πλ)` as complex numbers (the right side being the real
    cast of `GppStefanBoltzmann.P`). -/
theorem gamma_one_add_mul_gamma_one_sub (lam : ℝ) (hlam : lam ≠ 0) :
    Complex.Gamma (1 + (lam:ℂ) * I) * Complex.Gamma (1 - (lam:ℂ) * I)
      = ((Real.pi * lam / Real.sinh (Real.pi * lam) : ℝ) : ℂ) := by
  have hlamI : (lam:ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hlam) I_ne_zero
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((lam:ℂ) * I)
  have hshift : Complex.Gamma (1 + (lam:ℂ) * I) = (lam:ℂ) * I * Complex.Gamma ((lam:ℂ) * I) := by
    rw [add_comm]
    exact Complex.Gamma_add_one ((lam:ℂ) * I) hlamI
  have hsinarg : Complex.sin (↑Real.pi * ((lam:ℂ) * I)) = Complex.sinh (↑Real.pi * (lam:ℂ)) * I := by
    rw [show (↑Real.pi * ((lam:ℂ) * I)) = (↑Real.pi * (lam:ℂ)) * I by ring, Complex.sin_mul_I]
  rw [hshift, mul_assoc, hrefl, hsinarg]
  have hsinh_ne : Complex.sinh ((Real.pi:ℂ) * (lam:ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hlam)
  push_cast
  field_simp

end GppGammaModulus
