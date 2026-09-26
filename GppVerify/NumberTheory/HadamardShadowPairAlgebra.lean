import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Unconditional Hadamard shadow pair algebra

This file isolates the finite algebra behind the zero-pair form of the Shadow Euler
identity.  It does not assert a Hadamard product for the completed zeta function and
uses no hypothesis on the location of Riemann zeros.

For a spectral parameter `rho` and evaluation point `s`, the paired numerator
associated with `rho` and `1-rho` is

  (rho - s) * (1 - rho - s)
    = rho * (1-rho) - s * (1-s).

Normalizing at `s = 1/2` gives the exact rational pair kernel. Under the celestial
coordinate `Delta = 2s`, the numerator becomes

  4 rho(1-rho) - Delta(2-Delta).

These are purely algebraic statements; convergence and identification with the
completed-zeta Hadamard product remain separate analytic tasks.
-/

namespace GppHadamardShadowPairAlgebra

/-- Quadratic invariant under the reflection `z ↦ 1-z`. -/
def reflectionInvariant (z : ℂ) : ℂ := z * (1 - z)

/-- Celestial transport `Delta = 2s`. -/
def celestialWeight (s : ℂ) : ℂ := 2 * s

/-- Exact paired-factor numerator identity. -/
theorem pair_numerator_identity (rho s : ℂ) :
    (rho - s) * (1 - rho - s) =
      reflectionInvariant rho - reflectionInvariant s := by
  simp [reflectionInvariant]
  ring

/-- The quadratic invariant is exactly reflection symmetric. -/
theorem reflectionInvariant_one_sub (z : ℂ) :
    reflectionInvariant (1 - z) = reflectionInvariant z := by
  simp [reflectionInvariant]
  ring

/-- At the shadow-symmetric point `1/2`, the invariant is `1/4`. -/
theorem reflectionInvariant_half :
    reflectionInvariant (1 / 2 : ℂ) = 1 / 4 := by
  simp [reflectionInvariant]
  norm_num

/-- Clearing the celestial factor of four gives
`4 s(1-s) = Delta(2-Delta)` for `Delta = 2s`. -/
theorem four_reflectionInvariant_eq_celestial (s : ℂ) :
    4 * reflectionInvariant s =
      celestialWeight s * (2 - celestialWeight s) := by
  simp [reflectionInvariant, celestialWeight]
  ring

/-- Exact normalized pair kernel, written directly in the invariant variable. -/
theorem normalized_pair_kernel
    {rho s : ℂ} (hden : reflectionInvariant rho ≠ 1 / 4) :
    (reflectionInvariant rho - reflectionInvariant s) /
        (reflectionInvariant rho - 1 / 4) =
      (4 * reflectionInvariant rho - 4 * reflectionInvariant s) /
        (4 * reflectionInvariant rho - 1) := by
  have hd : reflectionInvariant rho - 1 / 4 ≠ 0 :=
    sub_ne_zero.mpr hden
  have hfactor :
      4 * reflectionInvariant rho - 1 =
        4 * (reflectionInvariant rho - 1 / 4) := by
    ring
  have hden4 : 4 * reflectionInvariant rho - 1 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (by norm_num) hd
  apply (div_eq_div_iff hd hden4).2
  ring

/-- Celestial form of the exact normalized pair kernel. -/
theorem normalized_pair_kernel_celestial
    {rho s : ℂ} (hden : reflectionInvariant rho ≠ 1 / 4) :
    (reflectionInvariant rho - reflectionInvariant s) /
        (reflectionInvariant rho - 1 / 4) =
      (4 * reflectionInvariant rho -
          celestialWeight s * (2 - celestialWeight s)) /
        (4 * reflectionInvariant rho - 1) := by
  rw [normalized_pair_kernel hden]
  rw [← four_reflectionInvariant_eq_celestial]

end GppHadamardShadowPairAlgebra

#print axioms GppHadamardShadowPairAlgebra.pair_numerator_identity
#print axioms GppHadamardShadowPairAlgebra.reflectionInvariant_one_sub
#print axioms GppHadamardShadowPairAlgebra.normalized_pair_kernel
#print axioms GppHadamardShadowPairAlgebra.normalized_pair_kernel_celestial
