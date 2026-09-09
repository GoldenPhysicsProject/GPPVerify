import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation
import GppVerify.StandardModel.ContactDiracHadamardBridge

/-!
# The dyadic Euler-shadow channel is the orientation Hadamard channel

In the local Euler-shadow unitary colligation of the arithmetic-principal-series programme,

    a_p^2 = 1/p,
    b_p^2 = 1 - 1/p.

Equal mixing occurs exactly when `a_p^2=b_p^2`, which forces `p=2`.  Thus the dyadic place
is the unique positive prime parameter for which the two local shadow channels have equal
Born weight.

At `p=2`, choosing the positive amplitude `r` with `r^2=1/2` gives

    S_2 = r [[1,1],[1,-1]],

namely the normalized Hadamard/Z2 Fourier matrix already appearing independently in the
Dirac rest-basis and orientation-Haar constructions.

This is an exact algebraic intersection, not yet a physical identification of the prime 2
with the microscopic orientation degree of freedom.  It is a concrete arithmetic clue worth
testing because the equality is unique rather than fitted.
-/

namespace GppDyadicOrientationHadamardBridge

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Squared first-channel amplitude in the arithmetic local colligation. -/
def aSq (p : ℝ) : ℝ := 1/p

/-- Squared complementary-channel amplitude. -/
def bSq (p : ℝ) : ℝ := 1 - 1/p

/-- Equal local channel weights force the dyadic value `p=2`. -/
theorem equal_weights_force_two (p : ℝ) (hp : p ≠ 0)
    (h : aSq p = bSq p) : p = 2 := by
  unfold aSq bSq at h
  field_simp [hp] at h
  linarith

/-- Conversely the dyadic value has exactly equal squared weights. -/
theorem two_has_equal_weights : aSq 2 = bSq 2 := by
  norm_num [aSq, bSq]

/-- Dyadic equal-amplitude channel, expressed without choosing a particular square-root
    implementation. -/
def dyadicChannel (r : ℂ) : M2C :=
  !![r,r;
     r,-r]

/-- It is exactly the raw Hadamard matrix multiplied by the common dyadic amplitude. -/
theorem dyadicChannel_eq_scaled_hadamard (r : ℂ) :
    dyadicChannel r = r • GppContactDiracHadamardBridge.hadamardRaw := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dyadicChannel, GppContactDiracHadamardBridge.hadamardRaw]

/-- If the common amplitude obeys `r^2=1/2`, the dyadic channel is an involutive unitary
    at the purely algebraic level: its square is the identity. -/
theorem dyadicChannel_sq_one (r : ℂ) (hr : r*r = (1/2 : ℂ)) :
    dyadicChannel r * dyadicChannel r = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dyadicChannel, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    rw [hr] <;> norm_num

/-- The arithmetic `p=2` equal-weight condition and the orientation Fourier normalization
    are therefore the same binary probability statement. -/
theorem dyadic_equal_weight_package :
    aSq 2 = (1/2 : ℝ) ∧ bSq 2 = (1/2 : ℝ) := by
  norm_num [aSq, bSq]

end GppDyadicOrientationHadamardBridge
