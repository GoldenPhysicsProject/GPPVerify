import Mathlib.Tactic
import GppVerify.StandardModel.GaugeCurrentSpinOrientation
import GppVerify.CelestialHolography.LorentzHermitianDiscreteGeometry

/-!
# Gauge and gravitational source data are blind to the diagonal `(q,u)->(-q,-u)` flip

For an oriented point-particle/worldline source, the two simplest local source tensors are

  j^mu       ~ q u^mu,
  T^{mu nu}  ~ m u^mu u^nu.

Under simultaneous charge dualization and worldline-orientation reversal,

  q -> -q,
  u -> -u,

both are unchanged:

  (-q)(-u) = q u,
  (-u) tensor (-u) = u tensor u.

Thus electromagnetism/gauge current AND the quadratic gravitational stress tensor are
simultaneously blind to the diagonal flip.  This considerably sharpens the project's
`q*t` intuition: at the classical source level, the `(+,+)` and `(-,-)` descriptions are
not merely similar; the standard linear gauge source and quadratic gravitational source
are exactly identical.

This theorem does not decide ontology.  If every observable factors through these invariant
sources, the diagonal pair is a redundancy rather than two measurable species.  Distinct
hidden sectors would require additional global/topological/quantum structure that does not
factor through the quotient.
-/

namespace GppGaugeGravityDiagonalBlindness

open GppLorentzHermitianDiscreteGeometry

/-- Scale a real four-vector. -/
def scaleR4 (a : ℝ) (u : R4) : R4 :=
  (a*u.1,a*u.2.1,a*u.2.2.1,a*u.2.2.2)

/-- Charge-weighted worldline current. -/
def current4 (q : ℝ) (u : R4) : R4 := scaleR4 q u

/-- Rank-one quadratic stress carrier `m u tensor u`, stored as a 4x4 function. -/
def stress4 (m : ℝ) (u : R4) : Fin 4 → Fin 4 → ℝ :=
  let v : Fin 4 → ℝ := ![u.1,u.2.1,u.2.2.1,u.2.2.2]
  fun i j => m * v i * v j

/-- Simultaneous charge and worldline reversal leaves the current invariant. -/
theorem current_diagonal_flip_invariant (q : ℝ) (u : R4) :
    current4 (-q) (scaleR4 (-1) u) = current4 q u := by
  rcases u with ⟨t,x,y,z⟩
  simp [current4, scaleR4]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

/-- Gravitational quadratic source is even under worldline orientation reversal. -/
theorem stress_orientation_even (m : ℝ) (u : R4) :
    stress4 m (scaleR4 (-1) u) = stress4 m u := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [stress4, scaleR4] <;> ring

/-- The pair `(gauge current, gravitational source)` is exactly blind to the diagonal flip. -/
theorem gauge_gravity_diagonal_blindness (q m : ℝ) (u : R4) :
    current4 (-q) (scaleR4 (-1) u) = current4 q u ∧
    stress4 m (scaleR4 (-1) u) = stress4 m u := by
  exact ⟨current_diagonal_flip_invariant q u, stress_orientation_even m u⟩

/-- Charge-only reversal changes the current. -/
theorem charge_only_current_odd (q : ℝ) (u : R4) :
    current4 (-q) u = scaleR4 (-1) (current4 q u) := by
  rcases u with ⟨t,x,y,z⟩
  simp [current4, scaleR4]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

/-- Worldline-only reversal also changes the current while leaving stress unchanged. -/
theorem orientation_only_package (q m : ℝ) (u : R4) :
    current4 q (scaleR4 (-1) u) = scaleR4 (-1) (current4 q u) ∧
    stress4 m (scaleR4 (-1) u) = stress4 m u := by
  constructor
  · rcases u with ⟨t,x,y,z⟩
    simp [current4, scaleR4]
    constructor
    · ring
    · constructor
      · ring
      · constructor <;> ring
  · exact stress_orientation_even m u

end GppGaugeGravityDiagonalBlindness
