import GppVerify.CelestialHolography.ArithmeticOSGram
import Mathlib

/-!
# Arithmetic OS factorization criterion

The decisive finite-dimensional AFT step can be isolated without relying on any
post-v4.19 Gram-matrix API.  If a reflected kernel has a genuine factorization

  K = Aᴴ A,

then it is positive semidefinite.  This is the finite matrix form of the desired
arithmetic factor map.  The file does not construct `A` from prime--Archimedean
data, identify the completed arithmetic kernel with `Aᴴ A`, or prove RH.
-/

namespace GppArithmeticOSFactorization

open scoped ComplexOrder Matrix

/-- Every finite complex factor `A` gives a positive-semidefinite kernel `Aᴴ A`. -/
theorem conjTranspose_mul_self_posSemidef
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n ℂ) :
    (Aᴴ * A).PosSemidef := by
  have hI : (1 : Matrix m m ℂ).PosSemidef := Matrix.PosSemidef.one
  simpa using hI.conjTranspose_mul_mul_same A

/-- Abstract finite AFT/OS factorization criterion.  Once the reflected arithmetic
kernel is identified with `Aᴴ A`, OS positivity is automatic; the hard theorem is
constructing that factorization from zero-independent arithmetic data. -/
theorem kernel_posSemidef_of_factorization
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (K : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hK : K = Aᴴ * A) :
    K.PosSemidef := by
  rw [hK]
  exact conjTranspose_mul_self_posSemidef A

end GppArithmeticOSFactorization

#print axioms GppArithmeticOSFactorization.conjTranspose_mul_self_posSemidef
#print axioms GppArithmeticOSFactorization.kernel_posSemidef_of_factorization
