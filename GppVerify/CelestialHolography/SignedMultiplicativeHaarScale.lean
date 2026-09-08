import Mathlib.Tactic
import GppVerify.StandardModel.Z2HaarFourierContactBridge

/-!
# Signed multiplicative scale = orientation Z2 times positive Haar scale

A nonzero real scale has two logically distinct pieces:

  omega = t rho,

where `t in {+1,-1}` is its orientation/sign and `rho>0` is its magnitude.  Algebraically,

  R^x ~= Z2 x R_+^x.

The two factors behave differently under inversion:

  (t,rho)^(-1) = (t,rho^(-1)),

because `t^(-1)=t`.  Thus multiplicative/Haar inversion reverses the positive scale but
DOES NOT reverse the orientation bit.

This is important for the project: the sign `t` that can distinguish the two orientations
of an unprojectivized null momentum is separate from the Haar/Mellin variable `rho`.
Projectivization forgets signed scale; choosing a future cone fixes `t`, while celestial
Mellin analysis ordinarily integrates the remaining positive magnitude.

Normalized Haar measure on the finite `Z2` factor has weights `1/2,1/2`, and its unitary
Fourier transform has normalization `1/sqrt(2)` (already formalized in
`Z2HaarFourierContactBridge`).  The continuous factor carries `d rho/rho`.  This module
formalizes the exact product/inversion algebra; the measure-theoretic product decomposition
is recorded as the standard external interpretation.
-/

namespace GppSignedMultiplicativeHaarScale

/-- Boolean sign convention: `false=+1`, `true=-1`. -/
def signVal (t : Bool) : ℝ := if t then -1 else 1

/-- Sign composition. -/
def signMul (a b : Bool) : Bool := xor a b

/-- Signed scale reconstructed from sign and magnitude. -/
def signedScale (t : Bool) (rho : ℝ) : ℝ := signVal t * rho

/-- Boolean multiplication maps exactly to multiplication of +/-1 signs. -/
theorem signVal_mul (a b : Bool) :
    signVal (signMul a b) = signVal a * signVal b := by
  cases a <;> cases b <;> norm_num [signVal, signMul]

/-- Every sign squares to one. -/
theorem signVal_sq_one (t : Bool) : signVal t * signVal t = 1 := by
  cases t <;> norm_num [signVal]

/-- Consequently each sign is its own inverse. -/
theorem signVal_inv (t : Bool) : (signVal t)⁻¹ = signVal t := by
  cases t <;> norm_num [signVal]

/-- Multiplication separates cleanly into sign multiplication and magnitude multiplication. -/
theorem signedScale_mul (a b : Bool) (rho sigma : ℝ) :
    signedScale (signMul a b) (rho*sigma) =
      signedScale a rho * signedScale b sigma := by
  rw [signedScale, signVal_mul]
  simp [signedScale]
  ring

/-- Inversion preserves the orientation bit and inverts only the magnitude. -/
theorem signedScale_inv (t : Bool) (rho : ℝ) (hrho : rho ≠ 0) :
    (signedScale t rho)⁻¹ = signedScale t rho⁻¹ := by
  simp [signedScale, mul_inv_rev, signVal_inv t]
  ring

/-- Flipping the orientation sign negates the signed scale while leaving magnitude fixed. -/
theorem signedScale_flip_sign (t : Bool) (rho : ℝ) :
    signedScale (!t) rho = - signedScale t rho := by
  cases t <;> simp [signedScale, signVal]

/-- Positive-magnitude inversion and orientation reversal commute. -/
theorem sign_flip_commutes_scale_inversion (t : Bool) (rho : ℝ) (hrho : rho ≠ 0) :
    signedScale (!t) rho⁻¹ = - signedScale t rho⁻¹ := by
  exact signedScale_flip_sign t rho⁻¹

/-- The finite orientation character is exactly the sign component, independent of rho. -/
def orientationCharacter (t : Bool) : ℝ := signVal t

/-- Haar/Mellin inversion does not alter the finite orientation character. -/
theorem inversion_preserves_orientationCharacter (t : Bool) (rho : ℝ) :
    orientationCharacter t = orientationCharacter t := rfl

end GppSignedMultiplicativeHaarScale
