import Mathlib.Tactic
import GppVerify.RiemannHypothesis.OrientationCriticalRealStructureBridge

/-!
# Arrow pairing and gauge-conjugation lemmas

This file machine-checks two finite statements used in the RH Arrow Dictionary.

1. On a two-point reversal orbit, the reversal is the swap (the sigma_1 block).
   Its D-twisted Hermitian form has one positive and one negative direction.
2. Conjugating a one-parameter action by an invertible change of gauge does not
   change its eigencharacter.

Neither theorem proves RH.  They isolate exactly why reflection symmetry and
half-density conjugation alone cannot move an off-line zero to the critical line.
-/

namespace GppArrowDictionary

open Complex

/-- The two-point complete reversal: exchange the two members of an orbit. -/
def orbitReverse (v : ℂ × ℂ) : ℂ × ℂ := (v.2, v.1)

/-- The reversal is involutive. -/
theorem orbitReverse_sq (v : ℂ × ℂ) :
    orbitReverse (orbitReverse v) = v := by
  rcases v with ⟨a,b⟩
  rfl

/-- Symmetric and antisymmetric orbit vectors are the +1 and -1 directions. -/
theorem orbitReverse_eigenvectors :
    orbitReverse ((1 : ℂ), 1) = ((1 : ℂ), 1) ∧
    orbitReverse ((1 : ℂ), -1) = - • ((1 : ℂ), -1) := by
  constructor
  · rfl
  · ext <;> simp [orbitReverse]

/-- The real D-twisted form associated with the swap block. -/
def twistedPairing (v : ℂ × ℂ) : ℝ :=
  (starRingEnd ℂ v.1 * v.2 + starRingEnd ℂ v.2 * v.1).re

/-- The coherent (+) direction has positive D-twisted norm. -/
theorem twistedPairing_coherent :
    twistedPairing ((1 : ℂ), 1) = 2 := by
  norm_num [twistedPairing]

/-- The anti-coherent (-) direction has negative D-twisted norm. -/
theorem twistedPairing_antiCoherent :
    twistedPairing ((1 : ℂ), -1) = -2 := by
  norm_num [twistedPairing]

/-- Consequently the two-point D-twisted form is indefinite. -/
theorem twistedPairing_indefinite :
    (∃ v : ℂ × ℂ, 0 < twistedPairing v) ∧
    (∃ w : ℂ × ℂ, twistedPairing w < 0) := by
  constructor
  · refine ⟨((1 : ℂ), 1), ?_⟩
    rw [twistedPairing_coherent]
    norm_num
  · refine ⟨((1 : ℂ), -1), ?_⟩
    rw [twistedPairing_antiCoherent]
    norm_num

section Gauge

variable {R X T : Type*} [SMul R X]

/-- Conjugate an action by an invertible change of variables. -/
def conjugatedAction (M : X ≃ X) (V : T → X → X) (t : T) (x : X) : X :=
  M (V t (M.symm x))

/-- Lemma G: an invertible gauge conjugation preserves every eigencharacter.

No topology, positivity, or group law is required for this algebraic statement.
The only needed compatibility is that the gauge map respects the relevant scalar action.
-/
theorem conjugation_preserves_eigencharacter
    (M : X ≃ X)
    (hsmul : ∀ (c : R) (x : X), M (c • x) = c • M x)
    (V : T → X → X)
    (χ : T → R)
    (v : X)
    (heig : ∀ t : T, V t v = χ t • v) :
    ∀ t : T, conjugatedAction M V t (M v) = χ t • M v := by
  intro t
  simp only [conjugatedAction, Equiv.symm_apply_apply]
  rw [heig t, hsmul]

end Gauge

/-- The arithmetic complete reversal fixes a point exactly on the critical line.
This restates the bridge theorem in the dictionary's notation. -/
theorem arithmetic_reversal_fixed_iff_critical (s : ℂ) :
    (1 - starRingEnd ℂ s = s) ↔ s.re = (1 / 2 : ℝ) :=
  GppOrientationCriticalRealStructureBridge.s_fixed_iff_critical s

end GppArrowDictionary

#print axioms GppArrowDictionary.twistedPairing_indefinite
#print axioms GppArrowDictionary.conjugation_preserves_eigencharacter
#print axioms GppArrowDictionary.arithmetic_reversal_fixed_iff_critical
