import Mathlib.Tactic

/-!
# Fubini-Study antipodal invariance on the celestial sphere (corrected)

Source: qg_foundations.tex, Lemma "Antipodal Symmetry" (`lem:antipodal`).
That lemma claims the Fubini-Study density alone satisfies
ω_FS(z) = ω_FS(-1/z̄), and its "algebraic" proof asserts
1/(1+|-1/z̄|²)² = 1/(1+|z|²)² directly. This is false in general: writing
r = |z|², the two sides are 1/(1+1/r)² and 1/(1+r)², which agree only at
r = 1 (see `fs_density_not_invariant_without_jacobian` below for an
explicit counterexample at r = 2).

What is actually true, and what the antipodal-invariance-of-the-measure
claim genuinely rests on, is that the *area form* dz∧dz̄/(1+|z|²)² is
invariant once the Jacobian of the antiholomorphic map z ↦ -1/z̄ is
included: |∂w/∂z̄|² = 1/|z|⁴ at w = -1/z̄. This file formalizes that
corrected, Jacobian-inclusive identity as an actual algebraic theorem
about the radial density, verified independently via SymPy before being
written as a Lean proof.
-/

namespace GppFubiniStudy

/-- The radial part of the Fubini-Study density on ℂP¹, at
    `r = |z|²`, i.e. `ω_FS(z) = 1/(1+|z|²)²` written as a function of `r`. -/
noncomputable def fsDensity (r : ℝ) : ℝ := 1 / (1 + r) ^ 2

/-- The antipodal map `z ↦ -1/z̄` sends `r = |z|²` to `1/r`, with Jacobian
    factor `|∂w/∂z̄|² = 1/r²`. The corrected antipodal-invariance statement:
    density-at-the-image times the Jacobian equals density-at-the-source. -/
theorem fs_measure_antipodal_invariant (r : ℝ) (hr : 0 < r) :
    fsDensity r⁻¹ * (1 / r ^ 2) = fsDensity r := by
  unfold fsDensity
  have hr' : r ≠ 0 := hr.ne'
  have h1 : (1 : ℝ) + r ≠ 0 := by positivity
  have h2 : (1 : ℝ) + r⁻¹ ≠ 0 := by positivity
  field_simp
  try ring

/-- Counterexample showing the *bare* density is not itself antipodal
    invariant (the claim as literally stated in the source lemma) --
    at r = 2 the two sides are 4/9 and 1/9. -/
theorem fs_density_not_invariant_without_jacobian :
    fsDensity (2 : ℝ)⁻¹ ≠ fsDensity 2 := by
  unfold fsDensity
  norm_num

end GppFubiniStudy
