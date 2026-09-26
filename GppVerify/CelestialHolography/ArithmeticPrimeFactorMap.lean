import GppVerify.CelestialHolography.ArithmeticPrimeLocalOS
import GppVerify.CelestialHolography.ArithmeticOSFactorization
import Mathlib

/-!
# Explicit finite prime-local AFT factor map

For a fixed real prime scale `p >= 1` and a finite prime-power cutoff, define

  A(m,i) = sqrt(w_m) exp(-m log(p) t_i),

where `w_m = log(p) exp(-(m/2) log(p)) >= 0`.
Then the reflected finite prime kernel is literally `Aᴴ A`.

This constructs the local arithmetic factor map rather than merely proving its
quadratic form nonnegative.  It still does not solve the completed
prime--Archimedean sign/gluing problem and does not prove RH.
-/

namespace GppArithmeticPrimeFactorMap

open scoped BigOperators ComplexOrder Matrix
open GppArithmeticPrimeLocalOS

noncomputable def primeFactor
    {M N : ℕ} (p : ℝ) (t : Fin N → ℝ) : Matrix (Fin M) (Fin N) ℂ :=
  fun m i => ((Real.sqrt (modeWeight p (m.1 + 1)) *
    modeValue p (m.1 + 1) (t i) : ℝ) : ℂ)

noncomputable def primeKernel
    {M N : ℕ} (p : ℝ) (t : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  (primeFactor (M := M) p t)ᴴ * primeFactor (M := M) p t

/-- The finite prime-local reflected kernel has an explicit `Aᴴ A` factorization. -/
theorem primeKernel_factorization
    {M N : ℕ} (p : ℝ) (t : Fin N → ℝ) :
    primeKernel (M := M) p t =
      (primeFactor (M := M) p t)ᴴ * primeFactor (M := M) p t := rfl

/-- Consequently every finite prime-local factor kernel is positive semidefinite. -/
theorem primeKernel_posSemidef
    {M N : ℕ} (p : ℝ) (t : Fin N → ℝ) :
    (primeKernel (M := M) p t).PosSemidef := by
  exact GppArithmeticOSFactorization.kernel_posSemidef_of_factorization
    (primeKernel (M := M) p t) (primeFactor (M := M) p t)
    (primeKernel_factorization (M := M) p t)

/-- On the arithmetic domain `p >= 1`, squaring the factor amplitude recovers
exactly the positive prime-power weight times the squared transfer mode. -/
theorem primeFactor_norm_sq_real
    {p : ℝ} (hp : 1 ≤ p) (m : ℕ) (t : ℝ) :
    (Real.sqrt (modeWeight p m) * modeValue p m t) ^ 2 =
      modeWeight p m * (modeValue p m t) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (modeWeight_nonneg hp m)]

end GppArithmeticPrimeFactorMap

#print axioms GppArithmeticPrimeFactorMap.primeKernel_factorization
#print axioms GppArithmeticPrimeFactorMap.primeKernel_posSemidef
#print axioms GppArithmeticPrimeFactorMap.primeFactor_norm_sq_real
