import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinSpinorIncidence

/-!
# Off-quadric mass reduction from an eight-dimensional null extension

This file formalizes the finite algebraic core of a doubled-spacetime mass mechanism.

Start with the six-dimensional Klein carrier `P6` and adjoin a positive two-plane with
coordinates `(u,v)`.  The extended quadratic form is

  Q8(p,u,v) = kleinQ(p) + u^2 + v^2.

Thus an extended-null point with transverse radius `m` satisfies

  kleinQ(p) = -m^2.

The existing Klein-spinor incidence module proves

  cMinus(p) cPlus(p) = -kleinQ(p) id,
  cPlus(p) cMinus(p) = -kleinQ(p) id.

Therefore on the off-quadric level `kleinQ(p)=-m^2` the two chiral Clifford maps
compose to `m^2 id`.  For `m != 0` either four-component twistor determines the
opposite chirality by division by `m`, and the second massive coupling equation then
follows automatically.

This is a finite-dimensional algebraic theorem.  It does NOT identify the added
two-plane with physical extra dimensions, prove a dynamical compactification or
confinement mechanism, or fix the dimensionful normalization of `m`.
-/

namespace GppDoubledSpacetimeMassReduction

open GppGrassmannianGooglyDecomposition
open GppTwistorAnnihilatorIncidence
open GppKleinSpinorIncidence

/-- Quadratic form of the Klein carrier with an added positive two-plane. -/
def extendedQ (p : P6) (u v : ℝ) : ℝ :=
  kleinQ p + u^2 + v^2

/-- An extended-null point whose transverse two-plane has radius `m` lies on the
off-Klein level `kleinQ = -m^2`. -/
theorem extended_null_implies_off_quadric_mass_shell
    (p : P6) (u v m : ℝ)
    (hnull : extendedQ p u v = 0)
    (hradius : u^2 + v^2 = m^2) :
    kleinQ p = -(m^2) := by
  unfold extendedQ at hnull
  linarith

/-- Conversely, an off-Klein point with `kleinQ=-m^2` becomes null after adding
a transverse two-plane of squared radius `m^2`. -/
theorem off_quadric_mass_shell_implies_extended_null
    (p : P6) (u v m : ℝ)
    (hQ : kleinQ p = -(m^2))
    (hradius : u^2 + v^2 = m^2) :
    extendedQ p u v = 0 := by
  unfold extendedQ
  rw [hQ, hradius]
  ring

/-- Componentwise scaling composes multiplicatively. -/
theorem scale4_mul (a b : ℝ) (z : V4) :
    scale4 a (scale4 b z) = scale4 (a*b) z := by
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [scale4]
  ring

/-- `cPlus` is homogeneous in its spinor argument. -/
theorem cPlus_scale4 (p : P6) (a : ℝ) (z : V4) :
    cPlus p (scale4 a z) = scale4 a (cPlus p z) := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases z with ⟨z0,z1,z2,z3⟩
  apply Prod.ext
  · simp [cPlus, scale4]
    ring
  · apply Prod.ext
    · simp [cPlus, scale4]
      ring
    · apply Prod.ext
      · simp [cPlus, scale4]
        ring
      · simp [cPlus, scale4]
        ring

/-- `cMinus` is homogeneous in its dual-spinor argument. -/
theorem cMinus_scale4 (p : P6) (a : ℝ) (alpha : V4) :
    cMinus p (scale4 a alpha) = scale4 a (cMinus p alpha) := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases alpha with ⟨a0,a1,a2,a3⟩
  apply Prod.ext
  · simp [cMinus, scale4]
    ring
  · apply Prod.ext
    · simp [cMinus, scale4]
      ring
    · apply Prod.ext
      · simp [cMinus, scale4]
        ring
      · simp [cMinus, scale4]
        ring

/-- On the off-quadric mass shell, the ordinary-to-dual-to-ordinary Clifford
composition is multiplication by `m^2`. -/
theorem cMinus_cPlus_mass_shell
    (p : P6) (m : ℝ) (z : V4)
    (hQ : kleinQ p = -(m^2)) :
    cMinus p (cPlus p z) = scale4 (m^2) z := by
  simpa [hQ] using cMinus_cPlus p z

/-- The opposite chiral composition obeys the same mass-square identity. -/
theorem cPlus_cMinus_mass_shell
    (p : P6) (m : ℝ) (alpha : V4)
    (hQ : kleinQ p = -(m^2)) :
    cPlus p (cMinus p alpha) = scale4 (m^2) alpha := by
  simpa [hQ] using cPlus_cMinus p alpha

/-- For nonzero mass, construct the dual-twistor component from an ordinary twistor. -/
noncomputable def dualFromMass (p : P6) (m : ℝ) (z : V4) : V4 :=
  scale4 (1/m) (cPlus p z)

/-- The constructed dual component satisfies the first massive coupling equation. -/
theorem cPlus_eq_mass_dualFromMass
    (p : P6) (m : ℝ) (z : V4) (hm : m ≠ 0) :
    cPlus p z = scale4 m (dualFromMass p m z) := by
  unfold dualFromMass
  rw [scale4_mul]
  have h : m * (1 / m) = 1 := by
    field_simp [hm]
  rw [h]
  rcases cPlus p z with ⟨z0,z1,z2,z3⟩
  simp [scale4]

/-- On `kleinQ=-m^2`, the second massive coupling equation follows automatically. -/
theorem cMinus_dualFromMass_eq_mass
    (p : P6) (m : ℝ) (z : V4)
    (hm : m ≠ 0)
    (hQ : kleinQ p = -(m^2)) :
    cMinus p (dualFromMass p m z) = scale4 m z := by
  unfold dualFromMass
  rw [cMinus_scale4, cMinus_cPlus_mass_shell p m z hQ, scale4_mul]
  have h : (1 / m) * (m^2) = m := by
    field_simp [hm]
    ring
  rw [h]

/-- For nonzero mass, construct the ordinary-twistor component from a dual twistor. -/
noncomputable def primalFromMass (p : P6) (m : ℝ) (alpha : V4) : V4 :=
  scale4 (1/m) (cMinus p alpha)

/-- The constructed ordinary component satisfies the second massive coupling equation. -/
theorem cMinus_eq_mass_primalFromMass
    (p : P6) (m : ℝ) (alpha : V4) (hm : m ≠ 0) :
    cMinus p alpha = scale4 m (primalFromMass p m alpha) := by
  unfold primalFromMass
  rw [scale4_mul]
  have h : m * (1 / m) = 1 := by
    field_simp [hm]
  rw [h]
  rcases cMinus p alpha with ⟨a0,a1,a2,a3⟩
  simp [scale4]

/-- On `kleinQ=-m^2`, the first massive coupling equation follows automatically. -/
theorem cPlus_primalFromMass_eq_mass
    (p : P6) (m : ℝ) (alpha : V4)
    (hm : m ≠ 0)
    (hQ : kleinQ p = -(m^2)) :
    cPlus p (primalFromMass p m alpha) = scale4 m alpha := by
  unfold primalFromMass
  rw [cPlus_scale4, cPlus_cMinus_mass_shell p m alpha hQ, scale4_mul]
  have h : (1 / m) * (m^2) = m := by
    field_simp [hm]
    ring
  rw [h]

/-- Massive twistor/dual-twistor locking, packaged from the ordinary-twistor side. -/
theorem massive_pair_from_primal
    (p : P6) (m : ℝ) (z : V4)
    (hm : m ≠ 0)
    (hQ : kleinQ p = -(m^2)) :
    cPlus p z = scale4 m (dualFromMass p m z) ∧
    cMinus p (dualFromMass p m z) = scale4 m z := by
  exact ⟨cPlus_eq_mass_dualFromMass p m z hm,
         cMinus_dualFromMass_eq_mass p m z hm hQ⟩

end GppDoubledSpacetimeMassReduction
