import Mathlib.Tactic
import GppVerify.StandardModel.FourOrientationGaugeProjection

/-!
# Parity is an exchange operator, not a third orientation sign

Finite algebra accompanying Daniel Toupin,
"Which Way Is Forward?", v19.

The orientation carrier uses two independent microscopic signs q,t with
relational grading chi=q*t.  Weak/Lorentz chirality is modeled by a separate
two-component carrier.  Parity swaps the two chiral components, hence
anticommutes with weak chirality, while acting trivially on the q,t carrier.

This is the finite algebraic content of the Clifford statement
P gamma5 P^{-1} = - gamma5.  It deliberately does NOT identify the weak
Spin(4) factor with the q,t orientation carrier.
-/

namespace GppParityExchangeOrientationSeparation

open GppFourOrientationGaugeProjection

abbrev ChiralPair := ℂ × ℂ
abbrev LocalCarrier := Orientation4 × ChiralPair

/-- Weak/chiral grading: + on the first component and - on the second. -/
def weakChirality (v : ChiralPair) : ChiralPair :=
  (v.1, -v.2)

/-- Parity exchanges left and right chiral components. -/
def paritySwap (v : ChiralPair) : ChiralPair :=
  (v.2, v.1)

/-- Parity is an involution. -/
theorem paritySwap_sq (v : ChiralPair) :
    paritySwap (paritySwap v) = v := by
  rcases v with ⟨a,b⟩
  rfl

/-- Parity anticommutes with the chiral grading. -/
theorem parity_anticommutes_weakChirality (v : ChiralPair) :
    paritySwap (weakChirality v) =
      - weakChirality (paritySwap v) := by
  rcases v with ⟨a,b⟩
  simp [paritySwap, weakChirality]

/-- Local parity acts only on the independent chiral factor. -/
def localParity (v : LocalCarrier) : LocalCarrier :=
  (v.1, paritySwap v.2)

/-- Lift the q,t relational grading to the local product carrier. -/
def localChi (v : LocalCarrier) : LocalCarrier :=
  (chi v.1, v.2)

/-- Parity commutes with the q,t relational grading. -/
theorem parity_commutes_localChi (v : LocalCarrier) :
    localParity (localChi v) = localChi (localParity v) := by
  rcases v with ⟨o,c⟩
  rfl

/-- Lift the charge-orientation half flip to the local carrier. -/
def localChargeFlip (v : LocalCarrier) : LocalCarrier :=
  (chargeFlip v.1, v.2)

/-- Lift the microscopic temporal half flip to the local carrier. -/
def localTemporalFlip (v : LocalCarrier) : LocalCarrier :=
  (temporalFlip v.1, v.2)

/-- Parity commutes with either orientation half flip because they act on
different tensor factors. -/
theorem parity_commutes_half_flips (v : LocalCarrier) :
    localParity (localChargeFlip v) = localChargeFlip (localParity v) ∧
    localParity (localTemporalFlip v) = localTemporalFlip (localParity v) := by
  rcases v with ⟨o,c⟩
  exact ⟨rfl,rfl⟩

/-- On a diagonal-even orientation state, either half flip exchanges matter
and antimatter amplitudes while parity leaves those amplitudes untouched. -/
theorem half_flip_vs_parity_on_physicalLift
    (a b : ℂ) (c : ChiralPair) :
    localChargeFlip (physicalLift a b, c) = (physicalLift b a, c) ∧
    localTemporalFlip (physicalLift a b, c) = (physicalLift b a, c) ∧
    localParity (physicalLift a b, c) = (physicalLift a b, paritySwap c) := by
  exact ⟨rfl,rfl,rfl⟩

/-- If one incorrectly identifies the q,t grading with weak chirality, parity
would reverse it.  This is the finite obstruction motivating separate factors. -/
theorem identified_chirality_would_be_parity_odd (v : ChiralPair) :
    paritySwap (weakChirality v) =
      - weakChirality (paritySwap v) :=
  parity_anticommutes_weakChirality v

end GppParityExchangeOrientationSeparation
