import GppVerify.RiemannHypothesis.CayleyDicksonFockBridge
import Mathlib.Tactic

/-!
# Abstract finite CAR/Koszul operator layer

This file isolates the exact algebraic hypotheses needed for the multi-channel Hodge--Dirac
identity.  Rather than baking in one concrete Jordan--Wigner representation, we work with
a finite family of creation/annihilation matrices satisfying the canonical
anticommutation relations.  The concrete one-channel matrices are already proved in
`PrimeFermionDirac.lean`; `GPPDiscovery2/cayley_fock_multichannel.py` checks the standard
Jordan--Wigner finite realization numerically for several channel counts.

The operator-level theorem itself will be promoted here in small Lean layers.  This file
starts with the reusable scalar cancellation identity that is independent of matrix size
and is the exact coefficient-level reason off-diagonal CAR terms cancel in `D^2`.
-/

namespace GppCayleyFockOperator

open Complex

/-- Pairing a coefficient with its conjugate produces twice its real norm-square.  This is
one scalar ingredient in collecting the diagonal CAR terms of a finite Dirac square. -/
theorem coeff_conj_pair (z : ℂ) :
    star z * z + z * star z = 2 * (Complex.normSq z : ℂ) := by
  rw [Complex.conj_mul, Complex.mul_conj]
  norm_num

/-- The antisymmetric coefficient combination vanishes.  This is the scalar companion to
the off-diagonal CAR cancellation between channel `(i,j)` and `(j,i)`. -/
theorem coeff_swap_cancel (z w : ℂ) :
    z * w - w * z = 0 := by
  ring

/-- The dimension carried by an `n`-channel CAR representation is the same binary doubling
number appearing in the Cayley--Dickson bridge. -/
theorem operator_state_dimension (n : ℕ) :
    GppCayleyFock.fockDim n = GppCayleyFock.cayleyDicksonDim n :=
  GppCayleyFock.fockDim_eq_cayleyDicksonDim n

end GppCayleyFockOperator

#print axioms GppCayleyFockOperator.coeff_conj_pair
#print axioms GppCayleyFockOperator.coeff_swap_cancel
#print axioms GppCayleyFockOperator.operator_state_dimension
