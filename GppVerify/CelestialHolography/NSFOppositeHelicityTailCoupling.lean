import Mathlib.Tactic

/-!
# Opposite-helicity structure of the quadratic NSF tail sector

Kozameh--Depaola (2026), in the definite-helicity null-surface formulation, decompose the
quadratic cone-source two-annihilation sector as

  Z++ a+ a+ + Z+- a+ a- + Z-+ a- a+ + Z-- a- a-.

They derive from the operator/spin-weight structure that

  Z++ = 0,   Z-- = 0,

so the physical two-annihilation tail source contains only the mixed-helicity terms

  Z+- a+ a- + Z-+ a- a+.

This file formalizes only that finite algebraic selection pattern.  It does NOT claim that
all nonlinear graviton interactions require opposite helicities: the same 2026 paper has
nonzero equal-helicity four-graviton channels (for example `++ -> ++`).  The theorem here
is scoped to the quadratic cone-source `aa`/tail sector.
-/

namespace GppNSFOppositeHelicityTailCoupling

/-- Four helicity coefficients of a generic quadratic two-annihilation source. -/
structure HelicitySource where
  zpp : ℝ
  zpm : ℝ
  zmp : ℝ
  zmm : ℝ
  deriving DecidableEq

/-- Generic scalar helicity source evaluated on amplitudes `aPlus,aMinus`. -/
def fullSource (Z : HelicitySource) (aPlus aMinus : ℝ) : ℝ :=
  Z.zpp * aPlus * aPlus +
  Z.zpm * aPlus * aMinus +
  Z.zmp * aMinus * aPlus +
  Z.zmm * aMinus * aMinus

/-- NSF quadratic-tail selection rule: the equal-helicity source coefficients vanish. -/
def NSFQuadraticTailSelection (Z : HelicitySource) : Prop :=
  Z.zpp = 0 ∧ Z.zmm = 0

/-- The mixed-helicity part of the source. -/
def mixedSource (Z : HelicitySource) (aPlus aMinus : ℝ) : ℝ :=
  Z.zpm * aPlus * aMinus + Z.zmp * aMinus * aPlus

/-- Under the 2026 NSF selection rule, the full `aa` source is exactly its mixed-helicity
part. -/
theorem selected_fullSource_eq_mixedSource
    (Z : HelicitySource) (hZ : NSFQuadraticTailSelection Z)
    (aPlus aMinus : ℝ) :
    fullSource Z aPlus aMinus = mixedSource Z aPlus aMinus := by
  rcases hZ with ⟨hpp,hmm⟩
  simp [fullSource, mixedSource, hpp, hmm]
  ring

/-- If the positive-helicity annihilation sector is absent, the selected quadratic tail
source vanishes. -/
theorem mixed_tail_vanishes_without_plus
    (Z : HelicitySource) (aMinus : ℝ) :
    mixedSource Z 0 aMinus = 0 := by
  simp [mixedSource]

/-- If the negative-helicity annihilation sector is absent, the selected quadratic tail
source vanishes. -/
theorem mixed_tail_vanishes_without_minus
    (Z : HelicitySource) (aPlus : ℝ) :
    mixedSource Z aPlus 0 = 0 := by
  simp [mixedSource]

/-- Hence a nonzero selected tail source requires both helicity amplitudes to be nonzero. -/
theorem nonzero_mixed_tail_requires_both_helicities
    (Z : HelicitySource) (aPlus aMinus : ℝ)
    (hS : mixedSource Z aPlus aMinus ≠ 0) :
    aPlus ≠ 0 ∧ aMinus ≠ 0 := by
  constructor
  · intro hp
    subst aPlus
    exact hS (mixed_tail_vanishes_without_plus Z aMinus)
  · intro hm
    subst aMinus
    exact hS (mixed_tail_vanishes_without_minus Z aPlus)

/-- The same necessity statement written for the full selected source. -/
theorem nonzero_selected_fullSource_requires_both_helicities
    (Z : HelicitySource) (hZ : NSFQuadraticTailSelection Z)
    (aPlus aMinus : ℝ)
    (hS : fullSource Z aPlus aMinus ≠ 0) :
    aPlus ≠ 0 ∧ aMinus ≠ 0 := by
  apply nonzero_mixed_tail_requires_both_helicities Z aPlus aMinus
  rw [← selected_fullSource_eq_mixedSource Z hZ aPlus aMinus]
  exact hS

/-- Pure `+` input gives zero in this particular selected tail sector. -/
theorem pure_plus_tail_sector_zero
    (Z : HelicitySource) (hZ : NSFQuadraticTailSelection Z) (aPlus : ℝ) :
    fullSource Z aPlus 0 = 0 := by
  rw [selected_fullSource_eq_mixedSource Z hZ]
  exact mixed_tail_vanishes_without_minus Z aPlus

/-- Pure `-` input likewise gives zero in this particular selected tail sector. -/
theorem pure_minus_tail_sector_zero
    (Z : HelicitySource) (hZ : NSFQuadraticTailSelection Z) (aMinus : ℝ) :
    fullSource Z 0 aMinus = 0 := by
  rw [selected_fullSource_eq_mixedSource Z hZ]
  exact mixed_tail_vanishes_without_plus Z aMinus

end GppNSFOppositeHelicityTailCoupling
