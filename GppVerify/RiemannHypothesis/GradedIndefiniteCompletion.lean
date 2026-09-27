import GppVerify.RiemannHypothesis.FinitePrimeDiracCompletion
import Mathlib.Tactic

/-!
# Grading-twisted indefinite completion

`FinitePrimeDiracCompletion` proves that an independent completion channel with
nonnegative scalar square cannot cancel a strictly positive finite-prime Hodge energy.

This file records the complementary first-order mechanism.  If `Gamma` is a fixed
involution which anticommutes with a Dirac operator `D`, then the orientation-twisted
channel `i m Gamma` has NEGATIVE square:

  (i m Gamma)^2 = -m^2 I.

Hence

  (D + i m Gamma)^2 = (E - m^2) I

whenever `D^2 = E I`.  The cross term vanishes because the grading anticommutes with
`D`.  This algebra is the finite counterpart of an indefinite/null parent factorization.

It does not identify `m` with the Archimedean zeta channel and makes no RH claim.
-/

namespace GppGradedIndefiniteCompletion

open Complex

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Scaling an anticommuting grading preserves anticommutation. -/
lemma anticommute_imul_grading
    (D Gamma : Matrix κ κ ℂ) (m : ℂ)
    (hanti : D * Gamma + Gamma * D = 0) :
    D * ((Complex.I * m) • Gamma) +
      ((Complex.I * m) • Gamma) * D = 0 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_add]
  rw [hanti]
  simp

/-- The imaginary grading channel has the opposite scalar square. -/
lemma imul_grading_sq
    (Gamma : Matrix κ κ ℂ) (m : ℂ)
    (hGamma : Gamma * Gamma = (1 : Matrix κ κ ℂ)) :
    ((Complex.I * m) • Gamma) * ((Complex.I * m) • Gamma) =
      (-(m^2)) • (1 : Matrix κ κ ℂ) := by
  rw [smul_mul_smul, hGamma]
  have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  rw [show (Complex.I * m) * (Complex.I * m) = -(m^2) by
    calc
      (Complex.I * m) * (Complex.I * m) =
          (Complex.I * Complex.I) * (m * m) := by ring
      _ = -(m^2) := by rw [hI]; ring]

/--
**Exact negative-square escape from the positive-completion no-go.**

A fixed anticommuting grading converts a positive scalar magnitude into a negative
first-order square before the final quadratic shell is formed.
-/
theorem graded_completion_sq
    (D Gamma : Matrix κ κ ℂ) (E m : ℂ)
    (hD : D * D = E • (1 : Matrix κ κ ℂ))
    (hGamma : Gamma * Gamma = (1 : Matrix κ κ ℂ))
    (hanti : D * Gamma + Gamma * D = 0) :
    (D + (Complex.I * m) • Gamma) *
      (D + (Complex.I * m) • Gamma) =
      (E - m^2) • (1 : Matrix κ κ ℂ) := by
  have hanti' := anticommute_imul_grading D Gamma m hanti
  rw [GppFinitePrimeCompletion.add_sq_of_anticommute D
    ((Complex.I * m) • Gamma) hanti']
  rw [hD, imul_grading_sq Gamma m hGamma]
  rw [← add_smul]
  congr 1

/-- On the matching shell `E=m^2`, the completed first-order operator is nilpotent. -/
theorem graded_completion_sq_zero_of_match
    (D Gamma : Matrix κ κ ℂ) (E m : ℂ)
    (hD : D * D = E • (1 : Matrix κ κ ℂ))
    (hGamma : Gamma * Gamma = (1 : Matrix κ κ ℂ))
    (hanti : D * Gamma + Gamma * D = 0)
    (hmatch : E = m^2) :
    (D + (Complex.I * m) • Gamma) *
      (D + (Complex.I * m) • Gamma) = 0 := by
  rw [graded_completion_sq D Gamma E m hD hGamma hanti, hmatch]
  simp

end GppGradedIndefiniteCompletion

#print axioms GppGradedIndefiniteCompletion.graded_completion_sq
#print axioms GppGradedIndefiniteCompletion.graded_completion_sq_zero_of_match
