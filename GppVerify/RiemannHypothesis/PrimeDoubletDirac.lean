import GppVerify.NumberTheory.TwinPrimeDoublets
import GppVerify.RiemannHypothesis.PrimeFermionDirac
import Mathlib.LinearAlgebra.Matrix.PosDef
-- Mathlib 4.33 split the analytic `PosSemidef` API (`re_dotProduct_nonneg`, which needs
-- `RCLike`) out into `Mathlib.Analysis.Matrix.PosDef`. Without it `PosSemidef` unfolds to
-- its bare `And` and `hPSD.re_dotProduct_nonneg` is read as a structure projection.
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Gap-two prime doublets as exact Dirac blocks

The gap-two graph on the primes has an exact singlet/doublet decomposition above the
exceptional chain `3 -- 5 -- 7`: `TwinPrimeDoublets.lean` proves that every prime greater
than `5` has degree at most one.  This file records the corresponding finite operator
blocks.

* an isolated prime carries the `1 × 1` zero adjacency block;
* a twin-prime pair carries the `2 × 2` exchange block
  `[[0,1],[1,0]]`;
* that exchange block is exactly the one-generator Hodge--Dirac operator `D(1)` from
  `PrimeFermionDirac.lean`;
* it has symmetric and antisymmetric eigenstates with eigenvalues `+1` and `-1`, so the
  raw adjacency is not positive semidefinite;
* its square is the identity and therefore is positive semidefinite.

Thus the mathematically correct physics analogy is Dirac-like: the first-order doublet
operator has paired signs, while its Laplacian is positive.  This theorem does not say
that twin primes form a physical `SU(2)` representation, that infinitely many twin pairs
exist, or that the doublet Laplacian is already the global Weil operator.
-/

open scoped ComplexOrder

namespace GppPrimeDoublet

/-- The adjacency block of an isolated prime. -/
def singletAdjacency : Matrix (Fin 1) (Fin 1) ℂ := 0

/-- The unweighted gap-two adjacency block of a twin-prime pair. -/
def doubletAdjacency : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The symmetric state of a doublet. -/
def symmetricState : Fin 2 → ℂ := ![1, 1]

/-- The antisymmetric state of a doublet. -/
def antisymmetricState : Fin 2 → ℂ := ![1, -1]

/-- The gap-two exchange block is the one-generator Hodge--Dirac operator at unit
holonomy. -/
theorem doubletAdjacency_eq_dirac_one :
    doubletAdjacency = GppPrimeFermion.dirac 1 := by
  rw [GppPrimeFermion.dirac_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [doubletAdjacency]

theorem doubletAdjacency_selfAdjoint :
    Matrix.conjTranspose doubletAdjacency = doubletAdjacency := by
  rw [doubletAdjacency_eq_dirac_one]
  exact GppPrimeFermion.dirac_selfAdjoint 1

/-- The symmetric combination has eigenvalue `+1`. -/
theorem doubletAdjacency_mulVec_symmetric :
    doubletAdjacency.mulVec symmetricState = symmetricState := by
  funext i
  fin_cases i <;>
    norm_num [doubletAdjacency, symmetricState, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- The antisymmetric combination has eigenvalue `-1`. -/
theorem doubletAdjacency_mulVec_antisymmetric :
    doubletAdjacency.mulVec antisymmetricState = -antisymmetricState := by
  funext i
  fin_cases i <;>
    norm_num [doubletAdjacency, antisymmetricState, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

theorem antisymmetricState_ne_zero : antisymmetricState ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [antisymmetricState] at h0

/-- The first-order doublet adjacency is sign-indefinite. -/
theorem doubletAdjacency_not_posSemidef : ¬ doubletAdjacency.PosSemidef := by
  intro hPSD
  have hle :
      0 ≤ RCLike.re
        (dotProduct (star antisymmetricState)
          (doubletAdjacency.mulVec antisymmetricState)) :=
    hPSD.re_dotProduct_nonneg antisymmetricState
  rw [doubletAdjacency_mulVec_antisymmetric, dotProduct_neg, map_neg] at hle
  have hpos : 0 < dotProduct (star antisymmetricState) antisymmetricState :=
    Matrix.dotProduct_star_self_pos_iff.mpr antisymmetricState_ne_zero
  have hpos_re :
      0 < RCLike.re (dotProduct (star antisymmetricState) antisymmetricState) :=
    (RCLike.pos_iff.mp hpos).1
  linarith

/-- Squaring the doublet Dirac block removes the paired sign. -/
theorem doubletAdjacency_sq :
    doubletAdjacency * doubletAdjacency = 1 := by
  rw [doubletAdjacency_eq_dirac_one]
  simpa using GppPrimeFermion.dirac_sq (1 : ℂ)

/-- The squared doublet block is positive semidefinite. -/
theorem doubletLaplacian_posSemidef :
    (doubletAdjacency * doubletAdjacency).PosSemidef := by
  rw [doubletAdjacency_sq]
  exact Matrix.PosSemidef.one

/-- The singlet adjacency block is positive semidefinite but has a zero mode. -/
theorem singletAdjacency_posSemidef : singletAdjacency.PosSemidef := by
  exact Matrix.PosSemidef.zero

end GppPrimeDoublet
