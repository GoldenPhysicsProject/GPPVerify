import Mathlib.Tactic

/-!
# Finite Fock toy after the diagonal orientation quotient

The diagonal-even one-particle sector has two physical amplitudes: matter `M` and
antimatter `A`, carrying relational U(1) weights `+1` and `-1`.  This file second-quantizes
only the finite occupation-number bookkeeping for one fermionic mode of each sector.

A basis state is `(nM,nA)` with Boolean occupations.  Define

    Q = nM - nA,
    N = nM + nA,
    H = eps * N.

The four Fock basis states are

    vacuum      (0,0): Q=0,  H=0
    matter      (1,0): Q=+1, H=eps
    antimatter  (0,1): Q=-1, H=eps
    pair        (1,1): Q=0,  H=2 eps.

Thus the hidden four-lift kinematic cover, once quotiented by the diagonal reversal, does
not force extra low-energy charged species: its ordinary finite fermionic Fock bookkeeping
is exactly one particle mode plus one antiparticle mode, both with positive excitation
energy.  Charge conjugation swaps the two occupations, reverses Q, and preserves N/H.

This is not yet a CAR-algebra construction; it is the exact occupation-spectrum skeleton
that the future CAR/Fock formalization must reproduce.
-/

namespace GppRelationalChargeFiniteFockToy

abbrev Occupation := Bool × Bool

/-- Convert a fermionic Boolean occupation to an integer. -/
def occZ (b : Bool) : ℤ := if b then 1 else 0

/-- Relational physical charge. -/
def totalCharge (x : Occupation) : ℤ := occZ x.1 - occZ x.2

/-- Total particle/antiparticle occupation number. -/
def totalNumber (x : Occupation) : ℤ := occZ x.1 + occZ x.2

/-- Finite-mode Hamiltonian in units where one excitation has energy `eps`. -/
def energy (eps : ℝ) (x : Occupation) : ℝ := eps * (totalNumber x : ℝ)

/-- Charge conjugation swaps matter and antimatter occupations. -/
def chargeConj (x : Occupation) : Occupation := (x.2,x.1)

/-- The exact four-state spectrum. -/
theorem fock_basis_spectrum (eps : ℝ) :
    totalCharge (false,false) = 0 ∧ energy eps (false,false) = 0 ∧
    totalCharge (true,false) = 1 ∧ energy eps (true,false) = eps ∧
    totalCharge (false,true) = -1 ∧ energy eps (false,true) = eps ∧
    totalCharge (true,true) = 0 ∧ energy eps (true,true) = 2*eps := by
  simp [totalCharge, totalNumber, occZ, energy]
  ring

/-- Charge conjugation is involutive. -/
theorem chargeConj_sq (x : Occupation) : chargeConj (chargeConj x) = x := by
  rcases x with ⟨a,b⟩
  rfl

/-- Charge conjugation reverses physical charge. -/
theorem chargeConj_flips_charge (x : Occupation) :
    totalCharge (chargeConj x) = - totalCharge x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

/-- Charge conjugation preserves total occupation. -/
theorem chargeConj_preserves_number (x : Occupation) :
    totalNumber (chargeConj x) = totalNumber x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

/-- Hence charge conjugation preserves the positive excitation Hamiltonian. -/
theorem chargeConj_preserves_energy (eps : ℝ) (x : Occupation) :
    energy eps (chargeConj x) = energy eps x := by
  simp [energy, chargeConj_preserves_number]

/-- If eps is nonnegative, every Fock basis energy is nonnegative. -/
theorem energy_nonnegative (eps : ℝ) (heps : 0 ≤ eps) (x : Occupation) :
    0 ≤ energy eps x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;>
    simp [energy, totalNumber, occZ] <;> positivity

/-- The one-particle matter and antimatter sectors have opposite charge but equal energy. -/
theorem one_particle_pair_same_energy_opposite_charge (eps : ℝ) :
    totalCharge (true,false) = - totalCharge (false,true) ∧
    energy eps (true,false) = energy eps (false,true) := by
  simp [totalCharge, totalNumber, occZ, energy]

end GppRelationalChargeFiniteFockToy
