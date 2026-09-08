import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.StandardModel.RelativePhaseDiracEnergy

/-!
# A nonzero Dirac mass collapses independent left/right scaling to the diagonal

Before a left/right coupling is introduced, the two chiral components admit independent
rescalings

    S(r,s) = diag(r,s).

The rest mass operator is proportional to

    beta = sigma1,

which exchanges the two components.  The elementary commutator calculation is

    S(r,s) beta = beta S(r,s)    iff    r=s.

Thus a nonzero symmetric mass coupling identifies the two independent scale factors and
reduces the continuous product scaling to its diagonal subgroup.  Equivalently,

    beta S(r,s) beta = S(s,r),

so the symmetries surviving the mass term are exactly the fixed points of factor exchange.
For phases this is the familiar statement that a Dirac mass preserves the common/vector
phase while breaking the relative/axial phase; for positive real dilations it preserves
only common scaling between the two chiral carriers.

This is a finite representation-theoretic symmetry-breaking theorem.  It does not derive a
nonzero numerical mass from scale-free dynamics; it identifies precisely which relative
symmetry is lost once the mass coupling is nonzero.
-/

namespace GppMassBreaksRelativeScale

open GppRelativePhaseDiracEnergy

/-- Independent complex rescaling of the two chiral components. -/
def chiralScale (r s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![r,0;
     0,s]

/-- Multiplying by beta exchanges the two scale slots. -/
theorem beta_conjugates_scale_slots (r s : ℂ) :
    betaRest * chiralScale r s * betaRest = chiralScale s r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [betaRest, chiralScale, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- Exact symmetry criterion: independent chiral scaling commutes with the mass-exchange
operator iff the two scale factors agree. -/
theorem chiralScale_commutes_beta_iff (r s : ℂ) :
    chiralScale r s * betaRest = betaRest * chiralScale r s ↔ r = s := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    simpa [chiralScale, betaRest, Matrix.mul_apply, Fin.sum_univ_two] using h01
  · intro hrs
    subst s
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true })
        [chiralScale, betaRest, Matrix.mul_apply, Fin.sum_univ_two]

/-- Matrix form of a rest mass coupling with arbitrary complex energy coefficient. -/
def massMatrix (E : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := E • betaRest

/-- A nonzero mass coefficient has exactly the same surviving scaling symmetry: the
diagonal subgroup. -/
theorem chiralScale_commutes_nonzero_mass_iff
    (E r s : ℂ) (hE : E ≠ 0) :
    chiralScale r s * massMatrix E = massMatrix E * chiralScale r s ↔ r = s := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    simp [chiralScale, massMatrix, betaRest, Matrix.mul_apply,
      Fin.sum_univ_two] at h01
    exact (mul_left_cancel₀ hE h01)
  · intro hrs
    subst s
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true })
        [chiralScale, massMatrix, betaRest, Matrix.mul_apply, Fin.sum_univ_two]

/-- In contrast, the massless zero coupling commutes with every independent left/right scale. -/
theorem massless_commutes_all_chiralScales (r s : ℂ) :
    chiralScale r s * massMatrix 0 = massMatrix 0 * chiralScale r s := by
  simp [massMatrix]

/-- A common scale is always preserved by the exchange/mass operator. -/
theorem diagonal_scale_commutes_beta (r : ℂ) :
    chiralScale r r * betaRest = betaRest * chiralScale r r := by
  exact (chiralScale_commutes_beta_iff r r).2 rfl

/-- For an anti-diagonal pair `(a,a^{-1})`, survival of the mass coupling forces the two
slots to coincide.  This is the algebraic reduction of a continuous relative phase/scale
symmetry to the fixed locus of inversion. -/
theorem antidiagonal_mass_symmetry_implies_fixed_point
    (a : ℂ) :
    chiralScale a a⁻¹ * betaRest = betaRest * chiralScale a a⁻¹ → a = a⁻¹ := by
  intro h
  exact (chiralScale_commutes_beta_iff a a⁻¹).1 h

end GppMassBreaksRelativeScale
