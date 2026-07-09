import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Point counts for E : y² = x³ - x over 𝔽_p, and the BSD rank-formula gap

Source: ONON monograph, BSD chapter, worked example "BSD for E: y² = x³ - x"
(Cremona label 32a2, conductor 32, E(ℚ) ≅ ℤ/2 × ℤ/2, rank 0).

This file formalizes the one part of that chapter that is genuinely finite
and decidable: the trace of Frobenius a_p = p + 1 - #E(𝔽_p) at small primes
of good reduction (p ≠ 2), computed as an actual `Finset` cardinality over
`ZMod p`, together with the resulting Hasse bound a_p² ≤ 4p. Every value
below was independently cross-checked against a brute-force point count in
Python before being written as a Lean theorem.

The rest of the chapter (the parity conjecture, Kolyvagin's theorem,
Gross-Zagier, and the general BSD rank formula) rests on deep automorphic
representation theory with no Mathlib support; those are recorded honestly
below as `True := trivial` gaps rather than disguised as proofs.
-/

namespace GppBSD

/-- The affine points of E : y² = x³ - x over 𝔽_p, as a decidable `Finset`. -/
def affinePoints (p : ℕ) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun xy => xy.2 ^ 2 = xy.1 ^ 3 - xy.1)

/-- #E(𝔽_p) = #(affine points) + 1, for the point at infinity. -/
def pointCount (p : ℕ) : ℕ := (affinePoints p).card + 1

/-- The trace of Frobenius a_p = p + 1 - #E(𝔽_p). -/
def tracePairing (p : ℕ) : ℤ := (p : ℤ) + 1 - (pointCount p : ℤ)

theorem pointCount_three : pointCount 3 = 4 := by decide
theorem tracePairing_three : tracePairing 3 = 0 := by decide

theorem pointCount_five : pointCount 5 = 8 := by decide
theorem tracePairing_five : tracePairing 5 = -2 := by decide

theorem pointCount_seven : pointCount 7 = 8 := by decide
theorem tracePairing_seven : tracePairing 7 = 0 := by decide

theorem pointCount_eleven : pointCount 11 = 12 := by decide
theorem tracePairing_eleven : tracePairing 11 = 0 := by decide

theorem pointCount_thirteen : pointCount 13 = 8 := by decide
theorem tracePairing_thirteen : tracePairing 13 = 6 := by decide

theorem pointCount_seventeen : pointCount 17 = 16 := by decide
theorem tracePairing_seventeen : tracePairing 17 = 2 := by decide

theorem pointCount_nineteen : pointCount 19 = 20 := by decide
theorem tracePairing_nineteen : tracePairing 19 = 0 := by decide

theorem pointCount_twentythree : pointCount 23 = 24 := by decide
theorem tracePairing_twentythree : tracePairing 23 = 0 := by decide

/-- The Hasse bound |a_p| ≤ 2√p, stated integrally as a_p² ≤ 4p to avoid
    irrational square roots, verified at each test prime above. -/
theorem hasse_bound_three : tracePairing 3 ^ 2 ≤ 4 * 3 := by decide
theorem hasse_bound_five : tracePairing 5 ^ 2 ≤ 4 * 5 := by decide
theorem hasse_bound_seven : tracePairing 7 ^ 2 ≤ 4 * 7 := by decide
theorem hasse_bound_eleven : tracePairing 11 ^ 2 ≤ 4 * 11 := by decide
theorem hasse_bound_thirteen : tracePairing 13 ^ 2 ≤ 4 * 13 := by decide
theorem hasse_bound_seventeen : tracePairing 17 ^ 2 ≤ 4 * 17 := by decide
theorem hasse_bound_nineteen : tracePairing 19 ^ 2 ≤ 4 * 19 := by decide
theorem hasse_bound_twentythree : tracePairing 23 ^ 2 ≤ 4 * 23 := by decide

/-- BSD rank formula (open in general): ord_{s=1} L(E,s) = rank E(ℚ).
    Source: ONON monograph, BSD chapter, "What We Prove" (via modularity
    and Kolyvagin's theorem for analytic rank ≤ 1).
    NOTE: requires the full analytic continuation of L(E,s), modularity,
    Gross-Zagier heights, and Kolyvagin's Euler-system bound on Sha — none
    of which exist in Mathlib. Left as an honestly-labeled gap. -/
theorem bsd_rank_formula_gap : True := trivial

/-- Parity conjecture: (-1)^(rank E(ℚ)) = w_E, the global root number.
    Source: ONON monograph, BSD chapter, proof from Haar self-duality of
    the local root number and the Cassels-Tate pairing on Selmer groups.
    NOTE: depends on local root-number computations and Selmer-group
    parity, not attempted here. -/
theorem parity_conjecture_gap : True := trivial

end GppBSD
