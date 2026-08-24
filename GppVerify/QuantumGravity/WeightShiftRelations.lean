import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The weight-shift relations for the Plancherel weight

From `Principal_Series_Kinematic_Blocks.tex`, Theorem "Weight-shift relations and the
resulting differential equation" — the first half of that theorem (the shift relations
themselves, which are digamma-free), stated for the complex-analytic continuation of the
Plancherel weight `P(λ) = Γ(1+iλ)Γ(1-iλ)`:
```
P(λ∓i) = (1±iλ)/(∓iλ) · P(λ)
```
This is one integer weight-shift `Δ ↦ Δ±1` on the principal series (`Δ = 1+iλ`), a pure
consequence of `Γ(z+1) = z·Γ(z)` applied to each Gamma factor separately.

## What this file proves

`Pc`: the complex-analytic continuation of `P`, `Pc z := Γ(1+iz)·Γ(1-iz)` for `z : ℂ`
(matching `GppGammaModulusIdentity`'s real-variable identity `Γ(1+iλ)Γ(1-iλ) = πλ/sinh(πλ)`
at real `λ`, but stated directly via `Complex.Gamma` here since the shift theorem's own
proof works entirely at the level of the Gamma recursion, not the `sinh` closed form).

`shift_sub_I`/`shift_add_I`: the two weight-shift relations, for `z ≠ 0` (needed since the
recursion divides by `∓iz`) and `z ≠ ∓I` (needed for `Complex.Gamma_add_one`'s own
nonvanishing hypothesis on the shifted argument `1±iz`) — vacuous restrictions for the
paper's actual use case of real `λ`, where `λ ≠ ±i` always holds (proved below as
`one_add_I_mul_real_ne_zero`/`one_sub_I_mul_real_ne_zero`).

## What this file does NOT do

Does not attempt the second half of the paper's own theorem — the resulting first-order
ODE `½sinh(x)·p̂'(x) = p̂(x) − p̂(0)` for the Fourier partner `p̂` of `P`, or its consequence
(`thm:resolved`, identifying the digamma first moment with the ladder moment `𝓜₁`) — both
of those route through the digamma function, absent from Mathlib at the pinned commit
(the same gap named throughout `docs/FORMALIZATION_PLAN.md`). No axiom, no sorry.
-/

namespace GppWeightShift

open Complex

/-- The complex-analytic continuation of the Plancherel weight, as a Gamma product. -/
noncomputable def Pc (z : ℂ) : ℂ := Gamma (1 + Complex.I * z) * Gamma (1 - Complex.I * z)

/-- **The `λ ↦ λ - i` weight-shift relation**: `P(z-i) = [(1+iz)/(-iz)]·P(z)`, for `z ≠ 0`
and `1+iz ≠ 0` (automatic whenever `z` is real). -/
theorem shift_sub_I {z : ℂ} (hz0 : z ≠ 0) (hz1 : 1 + Complex.I * z ≠ 0) :
    Pc (z - Complex.I) = (1 + Complex.I * z) / (-Complex.I * z) * Pc z := by
  have hiz : -Complex.I * z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h1 : (1:ℂ) + Complex.I * (z - Complex.I) = (1 + Complex.I * z) + 1 := by
    have e : Complex.I * (z - Complex.I) = Complex.I * z - Complex.I * Complex.I := by ring
    rw [e, hIsq]; ring
  have h2 : (1:ℂ) - Complex.I * (z - Complex.I) = -Complex.I * z := by
    have e : Complex.I * (z - Complex.I) = Complex.I * z - Complex.I * Complex.I := by ring
    rw [e, hIsq]; ring
  have hgam1 : Gamma ((1 + Complex.I * z) + 1) = (1 + Complex.I * z) * Gamma (1 + Complex.I * z) :=
    Gamma_add_one _ hz1
  have hgam2' : Gamma (1 - Complex.I * z) = (-Complex.I * z) * Gamma (-Complex.I * z) := by
    have := Gamma_add_one (-Complex.I * z) hiz
    rwa [show (-Complex.I * z) + 1 = (1:ℂ) - Complex.I * z by ring] at this
  have hgamneg : Gamma (-Complex.I * z) = Gamma (1 - Complex.I * z) / (-Complex.I * z) := by
    rw [hgam2']; field_simp
  unfold Pc
  rw [h1, h2, hgam1, hgamneg]
  field_simp
  ring

/-- **The `λ ↦ λ + i` weight-shift relation**: `P(z+i) = [(1-iz)/(iz)]·P(z)`, for `z ≠ 0`
and `1-iz ≠ 0` (automatic whenever `z` is real). -/
theorem shift_add_I {z : ℂ} (hz0 : z ≠ 0) (hz1 : 1 - Complex.I * z ≠ 0) :
    Pc (z + Complex.I) = (1 - Complex.I * z) / (Complex.I * z) * Pc z := by
  have hiz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h1 : (1:ℂ) + Complex.I * (z + Complex.I) = Complex.I * z := by
    have e : Complex.I * (z + Complex.I) = Complex.I * z + Complex.I * Complex.I := by ring
    rw [e, hIsq]; ring
  have h2 : (1:ℂ) - Complex.I * (z + Complex.I) = (1 - Complex.I * z) + 1 := by
    have e : Complex.I * (z + Complex.I) = Complex.I * z + Complex.I * Complex.I := by ring
    rw [e, hIsq]; ring
  have hgam2 : Gamma ((1 - Complex.I * z) + 1) = (1 - Complex.I * z) * Gamma (1 - Complex.I * z) :=
    Gamma_add_one _ hz1
  have hgam1' : Gamma (1 + Complex.I * z) = (Complex.I * z) * Gamma (Complex.I * z) := by
    have := Gamma_add_one (Complex.I * z) hiz
    rwa [show (Complex.I * z) + 1 = (1:ℂ) + Complex.I * z by ring] at this
  have hgampos : Gamma (Complex.I * z) = Gamma (1 + Complex.I * z) / (Complex.I * z) := by
    rw [hgam1']; field_simp
  unfold Pc
  rw [h1, h2, hgam2, hgampos]
  field_simp
  ring

/-- **For real `λ`, the exclusion hypotheses of `shift_sub_I`/`shift_add_I` are vacuous**:
`1 + iλ ≠ 0` for every real `λ`. -/
theorem one_add_I_mul_real_ne_zero (lam : ℝ) : (1 : ℂ) + Complex.I * (lam : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.add_re, Complex.mul_re] at hre

/-- `1 - iλ ≠ 0` for every real `λ`. -/
theorem one_sub_I_mul_real_ne_zero (lam : ℝ) : (1 : ℂ) - Complex.I * (lam : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.sub_re, Complex.mul_re] at hre

end GppWeightShift
