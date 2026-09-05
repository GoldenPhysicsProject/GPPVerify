import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorAnnihilatorIncidence

/-!
# Split factorization of the twistor/dual-twistor Fourier kernel

A split twistor has two real two-component spinor blocks.  The natural four-dimensional
pairing with a dual twistor is the sum of the pairings of those blocks.  Consequently any
exponential-type Fourier kernel factorizes into the product of two complementary chiral
kernels.

Brown--Gowdy--Spence describe the full Fourier transform as the composition of the two
half-Fourier transforms.  This file proves the finite-dimensional algebra responsible for
that statement without formalizing an integral or invoking Fubini: `pair4` splits exactly
into two rank-two phases, and any function `E` satisfying `E(a+b)=E(a)E(b)` factorizes on
that split.  The physical choice is the oscillatory exponential `E(t)=exp(i t)`.
-/

namespace GppSplitFourierKernelFactorization

open GppTwistorAnnihilatorIncidence

abbrev V2 := ℝ × ℝ

/-- First two-spinor block of a four-twistor. -/
def firstBlock (x : V4) : V2 := (x.1,x.2.1)

/-- Second two-spinor block of a four-twistor. -/
def secondBlock (x : V4) : V2 := (x.2.2.1,x.2.2.2)

/-- Standard bilinear pairing on one two-component block. -/
def pair2 (x y : V2) : ℝ := x.1*y.1+x.2*y.2

/-- The four-dimensional twistor/dual-twistor phase is exactly the sum of the two
complementary rank-two phases. -/
theorem pair4_eq_two_chiral_phases (x y : V4) :
    pair4 x y = pair2 (firstBlock x) (firstBlock y) +
      pair2 (secondBlock x) (secondBlock y) := by
  rcases x with ⟨x0,x1,x2,x3⟩
  rcases y with ⟨y0,y1,y2,y3⟩
  simp [pair4, pair2, firstBlock, secondBlock]
  ring

/-- Abstract exponential-kernel factorization.  Any multiplicative exponential of the
full phase splits into a product of the two chiral kernels. -/
theorem multiplicative_kernel_factorization
    {R : Type*} [Mul R]
    (E : ℝ → R) (hE : ∀ a b : ℝ, E (a+b) = E a * E b)
    (x y : V4) :
    E (pair4 x y) =
      E (pair2 (firstBlock x) (firstBlock y)) *
      E (pair2 (secondBlock x) (secondBlock y)) := by
  rw [pair4_eq_two_chiral_phases]
  exact hE _ _

/-- The two chiral phase functions are independent coordinate projections of the full
phase. -/
def leftPhase (x y : V4) : ℝ := pair2 (firstBlock x) (firstBlock y)

def rightPhase (x y : V4) : ℝ := pair2 (secondBlock x) (secondBlock y)

/-- Repackaged phase decomposition used by the two-step Fourier/light diamond. -/
theorem fullPhase_eq_left_plus_right (x y : V4) :
    pair4 x y = leftPhase x y + rightPhase x y := by
  exact pair4_eq_two_chiral_phases x y

/-- If one chiral block of the dual variable vanishes, the full phase reduces exactly
to the complementary half-Fourier phase. -/
theorem fullPhase_reduces_to_left
    (x : V4) (y0 y1 : ℝ) :
    pair4 x (y0,y1,0,0) = leftPhase x (y0,y1,0,0) := by
  simp [pair4, leftPhase, pair2, firstBlock]

/-- And conversely for the other chiral block. -/
theorem fullPhase_reduces_to_right
    (x : V4) (y2 y3 : ℝ) :
    pair4 x (0,0,y2,y3) = rightPhase x (0,0,y2,y3) := by
  simp [pair4, rightPhase, pair2, secondBlock]

end GppSplitFourierKernelFactorization
