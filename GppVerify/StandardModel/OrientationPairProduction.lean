import Mathlib.Tactic

/-!
# Relative-orientation charge and pair-production arithmetic

Finite algebra accompanying the orientation programme in
Daniel Toupin, "Which Way Is Forward?".

The intended interpretation is deliberately modest:

* a charged particle/antiparticle pair is represented by opposite values
  of a relative orientation grading chi = ±1;
* a fixed-standard half flip chi -> -chi reverses the corresponding
  Abelian charge;
* if that Abelian charge is exactly conserved, an isolated charged
  one-particle half flip is impossible;
* creating one particle and one antiparticle together preserves total charge;
* creating a lone antiparticle does not.

This is charge bookkeeping, not a derivation of a production cross section,
baryogenesis, or a microscopic collision mechanism.
-/

namespace GppOrientationPairProduction

/-- Relative Abelian charge carried by a state of grading chi. -/
def relativeCharge (q chi : ℤ) : ℤ := q * chi

/-- A fixed-standard half flip reverses the relative charge. -/
theorem halfFlip_reverses_charge (q chi : ℤ) :
    relativeCharge q (-chi) = - relativeCharge q chi := by
  simp [relativeCharge]

/-- For a nonzero charge quantum and chi = ±1, exact charge conservation
forbids an isolated transition from chi to -chi. -/
theorem isolated_charged_halfFlip_forbidden
    (q chi : ℤ)
    (hq : q ≠ 0)
    (hchi : chi = 1 ∨ chi = -1)
    (hconserve : relativeCharge q (-chi) = relativeCharge q chi) :
    False := by
  rw [halfFlip_reverses_charge] at hconserve
  have hz : relativeCharge q chi = 0 := by
    linarith
  unfold relativeCharge at hz
  rcases hchi with rfl | rfl
  · simp at hz
    exact hq hz
  · simp at hz
    exact hq hz

/-- Net charge of matter and antimatter occupation numbers. -/
def occupationCharge (q nMatter nAntimatter : ℤ) : ℤ :=
  q * (nMatter - nAntimatter)

/-- Creating a particle-antiparticle pair preserves total Abelian charge. -/
theorem pair_creation_preserves_charge
    (q nMatter nAntimatter : ℤ) :
    occupationCharge q (nMatter + 1) (nAntimatter + 1) =
      occupationCharge q nMatter nAntimatter := by
  simp [occupationCharge]

/-- Creating a lone antiparticle changes total charge by -q. -/
theorem lone_antiparticle_changes_charge
    (q nMatter nAntimatter : ℤ) :
    occupationCharge q nMatter (nAntimatter + 1) =
      occupationCharge q nMatter nAntimatter - q := by
  simp [occupationCharge]
  ring

/-- Creating a lone particle changes total charge by +q. -/
theorem lone_particle_changes_charge
    (q nMatter nAntimatter : ℤ) :
    occupationCharge q (nMatter + 1) nAntimatter =
      occupationCharge q nMatter nAntimatter + q := by
  simp [occupationCharge]
  ring

/-- Equal-mass particle-antiparticle creation has rest-energy threshold 2 m c^2
before kinetic/recoil energy is included. -/
def pairRestEnergy (m c : ℝ) : ℝ := 2 * m * c^2

theorem pairRestEnergy_eq_two_rest_energies (m c : ℝ) :
    pairRestEnergy m c = m*c^2 + m*c^2 := by
  unfold pairRestEnergy
  ring

end GppOrientationPairProduction
