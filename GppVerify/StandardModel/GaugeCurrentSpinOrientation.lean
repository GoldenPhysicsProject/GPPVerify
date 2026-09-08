import Mathlib.Tactic
import GppVerify.StandardModel.GaugeSpinCenterRelationalMatter
import GppVerify.StandardModel.MassiveSpinCenterOrientation

/-!
# Gauge current sees charge times oriented four-momentum

For a point/worldline source the Abelian current is proportional to

  j ~ q u,

or, after multiplying by mass/using momentum,

  j ~ q P.

The relative center of the two spinor factors reverses the oriented null or massive
momentum `P -> -P` while leaving the invariant mass unchanged.  Gauge conjugation reverses
`q -> -q`.  Therefore the combined operation leaves the source current unchanged:

  (-q)(-P) = q P.

This is the vector-level realization of the project's `q*t` character.  The second sign is
not postulated: it is the nontrivial center character of the doubled spinor factorization,
i.e. the sign of the oriented four-vector representative forgotten by projectivization.

The theorem is kinematic.  It does not claim that two separately measurable microscopic
species with `(q,P)` and `(-q,-P)` coexist; if every observable factors through the current,
the diagonal pair is instead a redundancy/quotient description.  Distinguishing those
possibilities requires additional global or quantum-field-theoretic structure.
-/

namespace GppGaugeCurrentSpinOrientation

open GppFlatInfinityCelestialFactorization
open GppSpinProductCenterTimeOrientation
open GppMassiveSpinCenterOrientation

/-- Matrix carrier for a charge-weighted four-current/momentum source. -/
def sourceCurrent (q : ℝ) (P : M2) : M2 := scaleM2 q P

/-- Multiplying both charge and oriented momentum by `-1` leaves the current exactly fixed. -/
theorem diagonal_charge_momentum_flip_invariant (q : ℝ) (P : M2) :
    sourceCurrent (-q) (scaleM2 (-1) P) = sourceCurrent q P := by
  rcases P with ⟨a,b,c,d⟩
  apply Prod.ext
  · simp [sourceCurrent, scaleM2]; ring
  · apply Prod.ext
    · simp [sourceCurrent, scaleM2]; ring
    · apply Prod.ext
      · simp [sourceCurrent, scaleM2]; ring
      · simp [sourceCurrent, scaleM2]; ring

/-- Charge flip alone reverses the source current. -/
theorem charge_flip_only_reverses_current (q : ℝ) (P : M2) :
    sourceCurrent (-q) P = scaleM2 (-1) (sourceCurrent q P) := by
  rcases P with ⟨a,b,c,d⟩
  apply Prod.ext
  · simp [sourceCurrent, scaleM2]; ring
  · apply Prod.ext
    · simp [sourceCurrent, scaleM2]; ring
    · apply Prod.ext
      · simp [sourceCurrent, scaleM2]; ring
      · simp [sourceCurrent, scaleM2]; ring

/-- Orientation flip alone likewise reverses the source current. -/
theorem momentum_flip_only_reverses_current (q : ℝ) (P : M2) :
    sourceCurrent q (scaleM2 (-1) P) = scaleM2 (-1) (sourceCurrent q P) := by
  rcases P with ⟨a,b,c,d⟩
  apply Prod.ext
  · simp [sourceCurrent, scaleM2]; ring
  · apply Prod.ext
    · simp [sourceCurrent, scaleM2]; ring
    · apply Prod.ext
      · simp [sourceCurrent, scaleM2]; ring
      · simp [sourceCurrent, scaleM2]; ring

/-- On a factorized null momentum, gauge dualization together with either one-sided spin
center flip leaves the current invariant. -/
theorem null_source_diagonal_flip_invariant
    (q : ℝ) (lambda lambdatilde : Spinor2) :
    sourceCurrent (-q)
      (nullMomentum (centerScale (-1) lambda) lambdatilde) =
    sourceCurrent q (nullMomentum lambda lambdatilde) := by
  rw [left_center_flip_reverses_vector]
  exact diagonal_charge_momentum_flip_invariant q _

/-- Massive version: gauge dualization plus the relative spin-center reversal preserves the
current while the mass square remains unchanged. -/
theorem massive_source_diagonal_flip_package
    (q : ℝ) (l1 lt1 l2 lt2 : Spinor2) :
    sourceCurrent (-q)
      (massiveMomentumFromTwoNull (centerScale (-1) l1) lt1
        (centerScale (-1) l2) lt2) =
      sourceCurrent q (massiveMomentumFromTwoNull l1 lt1 l2 lt2) ∧
    det2 (massiveMomentumFromTwoNull (centerScale (-1) l1) lt1
        (centerScale (-1) l2) lt2) =
      det2 (massiveMomentumFromTwoNull l1 lt1 l2 lt2) := by
  constructor
  · rw [left_center_flip_reverses_massive_momentum]
    exact diagonal_charge_momentum_flip_invariant q _
  · exact massSq_preserved_under_left_center_flip l1 lt1 l2 lt2

end GppGaugeCurrentSpinOrientation
