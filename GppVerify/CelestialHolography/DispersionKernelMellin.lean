import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Beta-reflection integral underlying the dispersion-kernel Mellin identity

From `Loops_from_Cuts_in_Celestial_Holography.tex`'s dispersion-relation reconstruction
(`thm:disp`, `thm:celdisp`), whose Mellin kernel is
```
∫₀^∞ S^{σ-1}/(s'+S) dS = s'^{σ-1} · π / sin(πσ).
```
Substituting `S = s'·u` reduces this to the base case `s'=1`:
`∫₀^∞ u^{σ-1}/(1+u) du = π/sin(πσ)`, the "second Euler Beta integral" on `(0,∞)`. Confirmed
this session, by direct grep of the pinned Mathlib source, that no such `(0,∞)` form exists
anywhere in Mathlib (only the `(0,1)` form, `Complex.betaIntegral`, in
`Mathlib.Analysis.SpecialFunctions.Gamma.Beta`) — this is genuinely new content for this repo.

## What this file proves

The **Beta-reflection integral** this identity ultimately rests on, in real `intervalIntegral`
form: for `0 < s < 1`,
```
∫ x in (0:ℝ)..1, x^(s-1) * (1-x)^(-s) = π / sin(π s).
```
This is `Complex.betaIntegral s (1-s)` (unfolded to its defining real interval integral),
evaluated via `Complex.Gamma_mul_Gamma_eq_betaIntegral` (`Γ(u)Γ(v) = Γ(u+v)·B(u,v)`, with
`u+v=1` so `Γ(u+v)=Γ(1)=1`) combined with `Complex.Gamma_mul_Gamma_one_sub` (the reflection
formula `Γ(z)Γ(1-z) = π/sin(πz)`) — both already in Mathlib. The real-valued statement is
extracted from the complex one via `Complex.ofReal_cpow` (valid uniformly on `x ∈ [0,1]`,
including both endpoints, since Mathlib's `0 ^ y` convention for `rpow`/`cpow` already agree
there) and `intervalIntegral.integral_ofReal`.

## What this file does NOT do

Does **not** carry the substitution `x = t/(1+t)` (mapping `(0,1) ↔ (0,∞)`) needed to convert
this `(0,1)` identity into the paper's actual `(0,∞)` dispersion kernel
`∫₀^∞ u^{σ-1}/(1+u) du = π/sin(πσ)`. That substitution is genuinely new infrastructure this
repo has never built: the natural tool is
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` (`Mathlib.MeasureTheory.Function.
Jacobian`) applied with `s = Set.Ioo 0 1`, `f x = x/(1-x)` (image `Set.Ioi 0`, `f' x =
1/(1-x)^2`), which after simplification reduces the `(0,∞)` integrand exactly back down to
this file's `(0,1)` integrand — the algebra was checked by hand (`x/(1-x) ↦ u`: `u^{σ-1}/(1+u)
· du = x^{σ-1}(1-x)^{-σ} dx`) but not yet coded, and is left open as the well-scoped next step.
No axiom, no sorry.
-/

open Complex MeasureTheory intervalIntegral Real

namespace GppDispersionKernel

/-- **The Beta-reflection integral** (real form): for `0 < s < 1`,
`∫ x in (0:ℝ)..1, x^(s-1) * (1-x)^(-s) = π / sin(π s)`. -/
theorem beta_reflection_real (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    (∫ x in (0:ℝ)..1, x ^ (s - 1) * (1 - x) ^ (-s)) = π / Real.sin (π * s) := by
  have hu : 0 < (s : ℂ).re := by simpa using h0
  have hv : 0 < ((1 : ℂ) - (s : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hkey : Complex.Gamma (s : ℂ) * Complex.Gamma (1 - (s : ℂ)) =
      Complex.betaIntegral (s : ℂ) (1 - (s : ℂ)) := by
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv
    rwa [show (s : ℂ) + (1 - (s : ℂ)) = 1 from by ring, Complex.Gamma_one, one_mul] at h
  rw [Complex.Gamma_mul_Gamma_one_sub (s : ℂ)] at hkey
  have hexp : ((1 : ℂ) - (s : ℂ)) - 1 = -(s : ℂ) := by ring
  rw [Complex.betaIntegral, hexp] at hkey
  have heq : Set.EqOn (fun x : ℝ => (x : ℂ) ^ ((s : ℂ) - 1) * (1 - (x : ℂ)) ^ (-(s : ℂ)))
      (fun x : ℝ => ((x ^ (s - 1) * (1 - x) ^ (-s) : ℝ) : ℂ)) (Set.uIcc (0 : ℝ) 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    simp only []
    have h1x0 : (0 : ℝ) ≤ 1 - x := by linarith
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0, Complex.ofReal_cpow h1x0]
    push_cast
    ring
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_ofReal] at hkey
  have hlhs : (π : ℂ) / Complex.sin (↑π * ↑s) = ((π / Real.sin (π * s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_mul]
  rw [hlhs] at hkey
  exact_mod_cast hkey.symm

end GppDispersionKernel
