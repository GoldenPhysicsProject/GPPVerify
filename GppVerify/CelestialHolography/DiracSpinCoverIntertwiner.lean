import Mathlib.Tactic

/-!
# Spin-cover / Dirac two-state intertwiner

Finite algebraic core of the cover identification used in
Daniel Toupin, "Which Way Is Forward?", v15.

The geometric determinant square-root cover and the transverse Spin(2) cover
both have the same central deck sign.  The paper then represents Spin(2) on the
free Dirac particle/antiparticle two-sector carrier.  This file formalizes the
small matrix-free algebra of that representation:

* `coverAction z` has weights `z⁻¹` and `z`.
* The central deck element `z = -1` acts as minus the identity on both sectors.
* The visible half flip exchanges the two sectors and inverts `z`.
* The base/vector phase is `z²`, so `z` and `-z` have the same base phase.
* The quarter element `z = i` squares to the central deck sign and has order four.
* In the unnormalised Hadamard basis this quarter element is exactly
  `-i * SWAP`, the rest-frame Dirac mass quarter-turn.

This is finite complex algebra only.  It does not formalize the topology of
GL(2,C), winding number, Lorentz covariance of gamma matrices, interacting QED,
or the full Standard Model.
-/

namespace GppDiracSpinCoverIntertwiner

/-- Two-sector Spin(2) action: opposite half-angle weights on the two sectors. -/
noncomputable def coverAction (z : ℂ) (ψ : ℂ × ℂ) : ℂ × ℂ :=
  (z⁻¹ * ψ.1, z * ψ.2)

/-- The action is multiplicative in the cover coordinate. -/
theorem coverAction_mul (z₁ z₂ : ℂ) (ψ : ℂ × ℂ) :
    coverAction z₁ (coverAction z₂ ψ) = coverAction (z₁ * z₂) ψ := by
  rcases ψ with ⟨a, b⟩
  simp [coverAction, mul_assoc, mul_comm, mul_left_comm]

/-- The identity cover element acts trivially. -/
theorem coverAction_one (ψ : ℂ × ℂ) :
    coverAction 1 ψ = ψ := by
  rcases ψ with ⟨a, b⟩
  simp [coverAction]

/-- The nontrivial central deck element acts by the common sign -1. -/
theorem coverAction_neg_one (ψ : ℂ × ℂ) :
    coverAction (-1) ψ = (-ψ.1, -ψ.2) := by
  rcases ψ with ⟨a, b⟩
  simp [coverAction]

/-- Observable/base vector phase obtained by squaring the spin lift. -/
def vectorPhase (z : ℂ) : ℂ := z^2

/-- The two spin lifts z and -z project to the same vector/base phase. -/
theorem vectorPhase_deck_invariant (z : ℂ) :
    vectorPhase (-z) = vectorPhase z := by
  simp [vectorPhase]
  ring

/-- Exchange the two relative-frequency sectors. -/
def halfFlip (ψ : ℂ × ℂ) : ℂ × ℂ := (ψ.2, ψ.1)

/-- A fixed-arrow half flip exchanges the two sectors and inverts the Spin(2) phase. -/
theorem halfFlip_intertwines_inverse (z : ℂ) (ψ : ℂ × ℂ) :
    halfFlip (coverAction z ψ) = coverAction z⁻¹ (halfFlip ψ) := by
  rcases ψ with ⟨a, b⟩
  simp [halfFlip, coverAction]

/-- Unnormalised Hadamard change of basis between lift and energy/frequency bases. -/
def hadamardRaw (ψ : ℂ × ℂ) : ℂ × ℂ :=
  (ψ.1 + ψ.2, ψ.1 - ψ.2)

/-- Rest-frame mass quarter-turn, algebraically -i times sector exchange. -/
def massQuarter (ψ : ℂ × ℂ) : ℂ × ℂ :=
  (-Complex.I * ψ.2, -Complex.I * ψ.1)

/-- The mass quarter-turn squares to the central deck sign. -/
theorem massQuarter_sq (ψ : ℂ × ℂ) :
    massQuarter (massQuarter ψ) = (-ψ.1, -ψ.2) := by
  rcases ψ with ⟨a, b⟩
  simp [massQuarter]
  ring_nf
  simp [Complex.I_mul_I]

/-- Therefore the mass quarter-turn has exact fourth power one. -/
theorem massQuarter_four (ψ : ℂ × ℂ) :
    massQuarter (massQuarter (massQuarter (massQuarter ψ))) = ψ := by
  rw [massQuarter_sq]
  rcases ψ with ⟨a, b⟩
  simp [massQuarter]
  ring_nf
  simp [Complex.I_mul_I]

/-- The Hadamard basis exactly intertwines the Dirac mass quarter-turn with z=i
in the diagonal Spin(2) cover representation. -/
theorem hadamard_intertwines_quarter (ψ : ℂ × ℂ) :
    hadamardRaw (massQuarter ψ) =
      coverAction Complex.I (hadamardRaw ψ) := by
  rcases ψ with ⟨a, b⟩
  simp [hadamardRaw, massQuarter, coverAction]
  ring_nf
  simp [Complex.I_mul_I]

/-- One full vector/base circuit corresponds to the central spinor sign:
the square of the quarter element is the deck element. -/
theorem quarter_squared_is_deck (ψ : ℂ × ℂ) :
    coverAction Complex.I (coverAction Complex.I ψ) =
      coverAction (-1) ψ := by
  rw [coverAction_mul]
  simp [Complex.I_mul_I]

end GppDiracSpinCoverIntertwiner
