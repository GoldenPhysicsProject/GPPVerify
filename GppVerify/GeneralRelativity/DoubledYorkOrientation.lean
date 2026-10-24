import Mathlib.Tactic

/-!
# Double-sided York evolution: relative volume versus common volume

For a two-sided canonical phase space whose past/future halves carry
opposite symplectic orientations,
  Omega_tot = Omega_+ - Omega_-,
the *diagonal* York momentum generator Y_diag=(Y,Y) has moment map
  i_Ydiag Omega_tot = c (dV_+ - dV_-).
Consequently equal variations of the two spatial volumes cancel
even if their COMMON volume changes nontrivially.

By contrast, the *anti-diagonal* York generator Y_anti=(Y,-Y) has
  i_Yanti Omega_tot = c (dV_+ + dV_-).
On a matched-volume variation, nullity of this generator does force
the common variation to vanish for c != 0.

This is an exact finite canonical calculation, not a demonstration
that nature chooses Y_diag or Y_anti in any specific causal diamond.
The physical identification of a microscopic orientation lift,
Wigner time reversal and the two-sided Einstein--Hilbert/quantum
modular symplectic gluing remains an independent problem.
-/

namespace GppDoubledYorkOrientation

/-- Coordinates on two oppositely oriented one-degree-of-freedom
canonical phases: ((q+,p+),(q-,p-)). -/
abbrev DoubledState := (ℝ × ℝ) × (ℝ × ℝ)

def oppositeSymplectic (u v : DoubledState) : ℝ :=
  (u.1.2 * v.1.1 - v.1.2 * u.1.1) -
    (u.2.2 * v.2.1 - v.2.2 * u.2.1)

def diagonalYork (c : ℝ) : DoubledState :=
  ((0,c),(0,c))

def antiDiagonalYork (c : ℝ) : DoubledState :=
  ((0,c),(0,-c))

def matchedVariation (dq : ℝ) : DoubledState :=
  ((dq,0),(dq,0))

/-- With opposite symplectic orientation, the diagonal generator
couples only to the *relative* variation of two spatial volumes. -/
theorem diagonal_york_relative_volume
    (c : ℝ) (v : DoubledState) :
    oppositeSymplectic (diagonalYork c) v =
      c * (v.1.1 - v.2.1) := by
  simp [oppositeSymplectic, diagonalYork]
  ring

/-- The anti-diagonal generator instead couples to their sum. -/
theorem anti_diagonal_york_total_volume
    (c : ℝ) (v : DoubledState) :
    oppositeSymplectic (antiDiagonalYork c) v =
      c * (v.1.1 + v.2.1) := by
  simp [oppositeSymplectic, antiDiagonalYork]
  ring

/-- Matching future/past volume variations makes diagonal York
symplectically null, despite arbitrarily large common volume motion. -/
theorem diagonal_york_null_on_matched_variation
    (c dq : ℝ) :
    oppositeSymplectic (diagonalYork c) (matchedVariation dq) = 0 := by
  simp [diagonal_york_relative_volume, matchedVariation]

/-- In particular the common volume may vary nontrivially while
the diagonal York pairing vanishes identically. -/
theorem common_volume_not_fixed_by_diagonal_reduction (c : ℝ) :
    ∃ v : DoubledState,
      v.1.1 = v.2.1 ∧ v.1.1 ≠ 0 ∧
        oppositeSymplectic (diagonalYork c) v = 0 := by
  refine ⟨matchedVariation 1, rfl, by norm_num, ?_⟩
  exact diagonal_york_null_on_matched_variation c 1

/-- Anti-diagonal nullity DOES force the common volume to be
stationary if the two variations are matched. -/
theorem anti_diagonal_null_iff_common_volume_fixed
    (c dq : ℝ) (hc : c ≠ 0) :
    oppositeSymplectic (antiDiagonalYork c)
      (matchedVariation dq) = 0 ↔ dq = 0 := by
  rw [anti_diagonal_york_total_volume]
  simp only [matchedVariation]
  constructor
  · intro h
    have h2 : (2*c)*dq=0 := by
      calc
        (2*c)*dq = c*(dq+dq) := by ring
        _ = 0 := h
    exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero (by norm_num) hc)
  · intro hdq
    simp [hdq]

end GppDoubledYorkOrientation

#print axioms GppDoubledYorkOrientation.diagonal_york_relative_volume
#print axioms GppDoubledYorkOrientation.common_volume_not_fixed_by_diagonal_reduction
#print axioms GppDoubledYorkOrientation.anti_diagonal_null_iff_common_volume_fixed
