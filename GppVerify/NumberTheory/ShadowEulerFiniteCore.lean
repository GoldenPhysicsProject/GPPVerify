import GppVerify.NumberTheory.HadamardShadowPairAlgebra
import Mathlib.Tactic

/-!
# Finite algebraic core of the Shadow Euler evaluation

This file connects the unconditional Hadamard zero-pair algebra to the glueball
coordinate `s = kN/(k+N)`.  No infinite product, zero-location hypothesis, or RH claim
appears here.
-/

namespace GppShadowEulerFiniteCore

open GppHadamardShadowPairAlgebra

/-- The arithmetic glueball evaluation point. -/
noncomputable def glueballS (k N : ℂ) : ℂ := k * N / (k + N)

/-- Exact perfect-square defect at the glueball evaluation point:

`1 - 4 s(1-s) = ((k+N-2kN)/(k+N))²`.

This is the field-valued form of the integer-cleared perfect-square identity used in
the Shadow Euler paper. -/
theorem one_sub_four_glueball_invariant
    (k N : ℂ) (hden : k + N ≠ 0) :
    1 - 4 * reflectionInvariant (glueballS k N) =
      ((k + N - 2 * k * N) / (k + N)) ^ 2 := by
  simp [reflectionInvariant, glueballS]
  field_simp [hden]
  ring

/-- Equivalently, the celestial quadratic invariant at
`Delta = 2 kN/(k+N)` differs from `1` by the same exact square. -/
theorem celestial_glueball_defect
    (k N : ℂ) (hden : k + N ≠ 0) :
    1 - celestialWeight (glueballS k N) *
        (2 - celestialWeight (glueballS k N)) =
      ((k + N - 2 * k * N) / (k + N)) ^ 2 := by
  rw [← four_reflectionInvariant_eq_celestial]
  exact one_sub_four_glueball_invariant k N hden

/-- SU(3) at level `k=1` gives `s=3/4`. -/
theorem su3_glueballS : glueballS 1 3 = (3 : ℂ) / 4 := by
  norm_num [glueballS]

/-- For SU(3), level one, the unscaled quadratic defect is exactly `1/4`:
`1 - 4 s(1-s) = 4(s-1/2)^2 = 1/4` at `s=3/4`. -/
theorem su3_unscaled_defect :
    1 - 4 * reflectionInvariant (glueballS 1 3) = (1 : ℂ) / 4 := by
  rw [one_sub_four_glueball_invariant 1 3 (by norm_num)]
  norm_num

/-- The Shadow Euler coupling uses one further factor of `1/4`, hence its square is
`1/16` in the SU(3), level-one case. -/
theorem su3_shadowCoupling_sq :
    (1 - 4 * reflectionInvariant (glueballS 1 3)) / 4 = (1 : ℂ) / 16 := by
  rw [su3_unscaled_defect]
  norm_num

/-- Substituting a glueball point into the unconditional normalized pair kernel produces
the exact celestial numerator used before any infinite Hadamard product is invoked. -/
theorem normalized_glueball_pair_kernel
    {rho k N : ℂ}
    (hrho : reflectionInvariant rho ≠ 1 / 4) :
    (reflectionInvariant rho - reflectionInvariant (glueballS k N)) /
        (reflectionInvariant rho - 1 / 4) =
      (4 * reflectionInvariant rho -
          celestialWeight (glueballS k N) *
            (2 - celestialWeight (glueballS k N))) /
        (4 * reflectionInvariant rho - 1) := by
  exact normalized_pair_kernel_celestial hrho

end GppShadowEulerFiniteCore

#print axioms GppShadowEulerFiniteCore.one_sub_four_glueball_invariant
#print axioms GppShadowEulerFiniteCore.celestial_glueball_defect
#print axioms GppShadowEulerFiniteCore.su3_unscaled_defect
#print axioms GppShadowEulerFiniteCore.su3_shadowCoupling_sq
#print axioms GppShadowEulerFiniteCore.normalized_glueball_pair_kernel
