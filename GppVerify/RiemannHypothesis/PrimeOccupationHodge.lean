import Mathlib.Tactic

/-!
# Finite prime-occupation Hodge geometry

This file formalizes the elementary Hodge--Lefschetz geometry of the finite prime
occupation cube used in the arithmetic-principal-series program.

For finite channel set iota and cutoffs N_i, an occupation is a tuple
m_i in {0,...,N_i}.  Poincare duality is the occupation reversal m -> N-m.
The algebraic Hodge star weights a basis state by

  product_i m_i! / (N_i-m_i)!

before reversing it.  The resulting basis norm is strictly positive.

This is zero-independent finite geometry.  It does not assert that the completed
prime--Archimedean Weil form is this Hodge metric; the global boundary identification is
the separate load-bearing theorem.
-/

namespace GppPrimeOccupationHodge

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite occupation tuple with channel-dependent cutoff. -/
abbrev Occupation (N : ι → ℕ) := ∀ i : ι, Fin (N i + 1)

/-- Poincare-dual occupation: reverse every channel about its cutoff. -/
def shadow (N : ι → ℕ) (m : Occupation N) : Occupation N :=
  fun i =>
    ⟨N i - (m i).val, by
      have hm : (m i).val ≤ N i := Nat.lt_succ_iff.mp (m i).isLt
      omega⟩

/-- Occupation reversal is an involution. -/
theorem shadow_shadow (N : ι → ℕ) (m : Occupation N) :
    shadow N (shadow N m) = m := by
  funext i
  apply Fin.ext
  simp only [shadow]
  have hm : (m i).val ≤ N i := Nat.lt_succ_iff.mp (m i).isLt
  omega

/-- Occupation reversal is injective. -/
theorem shadow_injective (N : ι → ℕ) :
    Function.Injective (shadow N) := by
  intro m n h
  have h' := congrArg (shadow N) h
  simpa [shadow_shadow] using h'

/-- The positive diagonal weight supplied by the algebraic Hodge star. -/
noncomputable def hodgeWeight (N : ι → ℕ) (m : Occupation N) : ℝ :=
  ∏ i : ι,
    (Nat.factorial (m i).val : ℝ) /
      (Nat.factorial (N i - (m i).val) : ℝ)

/-- Every occupation basis vector has strictly positive Hodge norm-square. -/
theorem hodgeWeight_pos (N : ι → ℕ) (m : Occupation N) :
    0 < hodgeWeight N m := by
  unfold hodgeWeight
  apply Finset.prod_pos
  intro i hi
  positivity

/-- Matrix entry of finite Poincare duality on the occupation basis. -/
def poincareEntry (N : ι → ℕ) (m n : Occupation N) : ℝ :=
  if n = shadow N m then 1 else 0

/-- Composing Poincare duality with the weighted Hodge star diagonalizes the basis pairing:
distinct occupation states are orthogonal, and the diagonal entry is the positive Hodge
weight. -/
theorem poincare_hodge_diagonal
    (N : ι → ℕ) (m n : Occupation N) :
    poincareEntry N m (shadow N n) * hodgeWeight N n =
      if m = n then hodgeWeight N n else 0 := by
  by_cases hmn : m = n
  · subst n
    simp [poincareEntry]
  · have hs : shadow N n ≠ shadow N m := by
      intro h
      exact hmn (shadow_injective N h).symm
    simp [poincareEntry, hmn, hs]

/-- One-channel Lefschetz commutator coefficient:
Lambda S - S Lambda = N - 2m. -/
theorem lefschetz_commutator_coefficient (N m : ℝ) :
    (m + 1) * (N - m) - m * (N - m + 1) = N - 2 * m := by
  ring

end GppPrimeOccupationHodge
