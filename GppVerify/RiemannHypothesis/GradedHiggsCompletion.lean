import GppVerify.RiemannHypothesis.FinitePrimeDiracCompletion
import Mathlib.Tactic

/-!
# Grading Higgs mass completion

This file records the positive-mass companion to the older grading-twisted
negative-square construction.

If a fixed involution `Gamma` anticommutes with a Dirac operator `D`, then a
real Higgs mass `sigma Gamma` has positive square and no cross term:

  (D + sigma Gamma)^2 = D^2 + sigma^2 I.

For a scalar Hodge shell `D^2 = E I` with `E >= 0`, every nonzero real
`sigma` makes the massive square strictly nonzero.  In the intended delay-line
application `sigma = Re(s)-1/2`; hence a zero mode of a fixed positive-metric
completed pencil can occur only on the principal-series line.

This is an algebraic mechanism only.  It does not assert that the completed
zeta determinant is already the determinant of such a fixed pencil.
-/

namespace GppGradedHiggsCompletion

open Complex

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Scaling an anticommuting grading by a scalar preserves anticommutation. -/
lemma anticommute_smul_grading
    (D Gamma : Matrix κ κ ℂ) (m : ℂ)
    (hanti : D * Gamma + Gamma * D = 0) :
    D * (m • Gamma) + (m • Gamma) * D = 0 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_add]
  rw [hanti]
  simp

/-- A scalar multiple of an involution has positive scalar square. -/
lemma smul_grading_sq
    (Gamma : Matrix κ κ ℂ) (m : ℂ)
    (hGamma : Gamma * Gamma = (1 : Matrix κ κ ℂ)) :
    (m • Gamma) * (m • Gamma) =
      (m^2) • (1 : Matrix κ κ ℂ) := by
  rw [smul_mul_smul, hGamma]
  congr 1
  ring

/-- **Exact Higgs mass identity.** An anticommuting involution adds its mass in
quadrature. -/
theorem higgs_completion_sq
    (D Gamma : Matrix κ κ ℂ) (m : ℂ)
    (hGamma : Gamma * Gamma = (1 : Matrix κ κ ℂ))
    (hanti : D * Gamma + Gamma * D = 0) :
    (D + m • Gamma) * (D + m • Gamma) =
      D * D + (m^2) • (1 : Matrix κ κ ℂ) := by
  have hanti' := anticommute_smul_grading D Gamma m hanti
  rw [GppFinitePrimeCompletion.add_sq_of_anticommute D (m • Gamma) hanti']
  rw [smul_grading_sq Gamma m hGamma]

/-- On a scalar Hodge shell, the Higgs mass simply shifts the shell energy by
`m^2`. -/
theorem higgs_completion_sq_energy
    (D Gamma : Matrix κ κ ℂ) (E m : ℂ)
    (hD : D * D = E • (1 : Matrix κ κ ℂ))
    (hGamma : Gamma * Gamma = (1 : Matrix κ κ ℂ))
    (hanti : D * Gamma + Gamma * D = 0) :
    (D + m • Gamma) * (D + m • Gamma) =
      (E + m^2) • (1 : Matrix κ κ ℂ) := by
  rw [higgs_completion_sq D Gamma m hGamma hanti, hD]
  exact (add_smul E (m^2) (1 : Matrix κ κ ℂ)).symm

/-- A nonzero real Higgs mass cannot close a nonnegative scalar Hodge shell. -/
theorem higgs_energy_sum_ne_zero
    {E sigma : ℝ} (hE : 0 ≤ E) (hsigma : sigma ≠ 0) :
    (((E + sigma^2 : ℝ) : ℂ)) ≠ 0 := by
  exact_mod_cast ne_of_gt (add_pos_of_nonneg_of_pos hE (sq_pos_of_ne_zero hsigma))

/-- Consequently the massive scalar Hodge square is nonzero for every nonzero
real off-critical displacement. -/
theorem higgs_square_nonzero_of_nonnegative_energy
    [Nonempty κ]
    (D Gamma : Matrix κ κ ℂ) (E sigma : ℝ)
    (hE : 0 ≤ E) (hsigma : sigma ≠ 0)
    (hD : D * D = (E : ℂ) • (1 : Matrix κ κ ℂ))
    (hGamma : Gamma * Gamma = (1 : Matrix κ κ ℂ))
    (hanti : D * Gamma + Gamma * D = 0) :
    (D + (sigma : ℂ) • Gamma) * (D + (sigma : ℂ) • Gamma) ≠ 0 := by
  rw [higgs_completion_sq_energy D Gamma (E : ℂ) (sigma : ℂ) hD hGamma hanti]
  intro hzero
  have hscalar : (((E + sigma^2 : ℝ) : ℂ)) = 0 := by
    simpa using congrArg
      (fun M : Matrix κ κ ℂ =>
        M (Classical.choice inferInstance) (Classical.choice inferInstance))
      hzero
  exact higgs_energy_sum_ne_zero hE hsigma hscalar

end GppGradedHiggsCompletion

#print axioms GppGradedHiggsCompletion.higgs_completion_sq
#print axioms GppGradedHiggsCompletion.higgs_completion_sq_energy
#print axioms GppGradedHiggsCompletion.higgs_square_nonzero_of_nonnegative_energy
