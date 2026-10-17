import Mathlib.Tactic

/-!
# Entire celestial shadow cut: an exact OS reflection-positivity failure

The scalar two-particle cut in loops_from_cuts_celestial_v19.tex has
the full Mellin shadow spectral density
  Phi(λ)=λ/(8 sinh(πλ)) > 0  (λ ∈ R, continuous at 0).
Its COMPLETE infinite Fourier integral is
  K(t)=∫_R Phi(λ)e^(i λ t)dλ=sech(t/2)^2/16.
These analytic Fourier/phase-space identities are independently verified
in the companion Wolfram script, not proved in this Lean module.

For x>0 put q=e^(-x). Then K(x)=q/[4(1+q)^2].
For positive times t1=log(2), t2=log(3), its Hankel reflection
matrix [K(ti+tj)] is exactly:
  [[1/25, 3/98],
   [3/98, 9/400]].
This file kernel-verifies the STRICT NEGATIVE determinant and an
explicit negative real quadratic vector, using only rational arithmetic.

Conclusion: a positive full-spectrum principal-series cut and positive
Fubini–Study/Haar measure do NOT imply Osterwalder–Schrader positivity.
No claim about a completed arithmetic Weil kernel or RH is made.
-/

namespace GppCelestialShadowCutOS

def heatFromQ (q : ℚ) : ℚ := q / (4 * (1 + q)^2)

theorem cutoffless_shadow_kernel_2log2 :
    heatFromQ (1/4) = 1/25 := by norm_num [heatFromQ]

theorem cutoffless_shadow_kernel_log6 :
    heatFromQ (1/6) = 3/98 := by norm_num [heatFromQ]

theorem cutoffless_shadow_kernel_2log3 :
    heatFromQ (1/9) = 9/400 := by norm_num [heatFromQ]

theorem exact_reflection_determinant :
    heatFromQ (1/4) * heatFromQ (1/9) -
      (heatFromQ (1/6))^2 = -(891/24010000 : ℚ) := by
  norm_num [heatFromQ]

theorem negative_reflection_determinant :
    heatFromQ (1/4) * heatFromQ (1/9) -
      (heatFromQ (1/6))^2 < 0 := by
  rw [exact_reflection_determinant]
  norm_num

/-- Explicit negative OS quadratic: with x=-K12/K11=-75/98, vector
(x,1), the matrix [[K11,K12],[K12,K22]] has x^T K x
equal to K22-K12²/K11 < 0. -/
theorem explicit_negative_reflection_witness :
    let x : ℚ := -(75/98)
    (1/25) * x^2 + 2 * (3/98) * x + (9/400) < 0 := by
  norm_num

end GppCelestialShadowCutOS
