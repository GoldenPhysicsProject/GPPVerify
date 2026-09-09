import Mathlib.Tactic

/-!
# Opposite CAR polarizations: finite-cutoff core of the Shale--Stinespring obstruction

For fermionic Fock representations determined by orthogonal complex structures `J1,J2` on
an infinite-dimensional real Hilbert space, the Shale--Stinespring equivalence criterion
says that the representations are unitarily equivalent iff `J1-J2` is Hilbert--Schmidt.

For the exactly opposite polarization `J2=-J1`,

    J1 - J2 = 2 J1.

Because an orthogonal complex structure has norm one on every orthonormal basis vector, each
mode contributes `||2J e_n||^2 = 4` to the Hilbert--Schmidt sum.  Hence an N-mode cutoff has
squared HS norm `4N`, which diverges with N.  Therefore in an infinite-dimensional field
the Fock representations associated with `J` and `-J` are not related by an internal
unitary Bogoliubov implementer.

The full Shale--Stinespring theorem is an external functional-analytic input and is not
reproved here.  This file machine-checks the elementary load-bearing divergence arithmetic
used when applying it to the exact opposite polarization.

Physical consequence for the orientation programme: a universe-wide reversal of the
positive-energy complex structure should not be pictured as a coherent `50/50` state inside
the same ordinary Fock representation.  In finite mode truncations the two polarizations
are equivalent, but the global infinite-mode limit leaves that representation class.
-/

namespace GppOppositePolarizationShaleObstruction

/-- Squared Hilbert--Schmidt contribution from one normalized mode of `J-(-J)=2J`. -/
def perModeHSSq : ℕ := 4

/-- N-mode cutoff of the squared Hilbert--Schmidt norm. -/
def cutoffHSSq (N : ℕ) : ℕ := perModeHSSq * N

 theorem cutoffHSSq_eq (N : ℕ) : cutoffHSSq N = 4 * N := by
  rfl

/-- Adding one mode increases the squared cutoff norm by exactly four. -/
theorem cutoffHSSq_succ (N : ℕ) : cutoffHSSq (N+1) = cutoffHSSq N + 4 := by
  simp [cutoffHSSq, perModeHSSq]
  omega

/-- The cutoff sequence is strictly increasing. -/
theorem cutoffHSSq_strict (N : ℕ) : cutoffHSSq N < cutoffHSSq (N+1) := by
  rw [cutoffHSSq_succ]
  omega

/-- Elementary unboundedness: every natural bound is exceeded by a sufficiently large
    finite-mode cutoff. -/
theorem cutoffHSSq_unbounded (B : ℕ) : B < cutoffHSSq (B+1) := by
  simp [cutoffHSSq, perModeHSSq]
  omega

/-- In particular there is no finite natural number bounding every cutoff. -/
theorem no_uniform_finite_cutoff_bound :
    ¬ ∃ B : ℕ, ∀ N : ℕ, cutoffHSSq N ≤ B := by
  rintro ⟨B,hB⟩
  have h := hB (B+1)
  have hu := cutoffHSSq_unbounded B
  omega

end GppOppositePolarizationShaleObstruction
