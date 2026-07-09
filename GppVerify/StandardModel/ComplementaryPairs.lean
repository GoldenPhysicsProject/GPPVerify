import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Exactly three complementary-pair partitions of {0,1,2,3}

Source: ONON5213.tex, "Counting Complementary Pairs" (thm:three-partitions),
an independent argument for exactly three fermion generations: the number
of ways to partition the standard basis {e₀,e₁,e₂,e₃} of ℂ⁴ into two
complementary 2-dimensional subspaces `span(e_i,e_j) ⊕ span(e_k,e_l)`.

A partition into two pairs is exactly a fixed-point-free involution on
`Fin 4` (the "partner" map). This file formalizes that count as an
actual `Finset` cardinality, decided over all 4⁴ = 256 functions
`Fin 4 → Fin 4`, independently of the Gr(2,4)/Plücker-coordinate
machinery used to derive it in the source. This is a genuinely
different combinatorial route to "exactly three" than the Cayley-Dickson
doubling count already in `ThreeGenerations.lean`.
-/

namespace GppComplementaryPairs

/-- The fixed-point-free involutions on `Fin 4`, i.e. exactly the ways to
    partition `{0,1,2,3}` into two complementary pairs (the "partner" map
    of each partition). -/
def complementaryPairings : Finset (Fin 4 → Fin 4) :=
  Finset.univ.filter (fun f => (∀ i, f (f i) = i) ∧ ∀ i, f i ≠ i)

/-- There are exactly three ways to partition `{0,1,2,3}` into two
    complementary pairs. -/
theorem exactly_three_complementary_pairings : complementaryPairings.card = 3 := by
  native_decide

end GppComplementaryPairs
