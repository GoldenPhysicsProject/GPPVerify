import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The Grassmannian Chart Transition Jacobian: an Exact Matrix Identity
# Lean 4 | GPPVerify
# Author: Daniel Toupin | Golden Physics Project

## Statement

`GrassmannianMass.lean` proves that the chart transition map
τ(a,b,c,d) = (-b,a,-d,c)/(ad-bc) satisfies τ∘τ = -id. This file goes one
level deeper and formalizes its Jacobian.

Let D = ad - bc. The real Jacobian J of τ has entries with D² in the
denominator; clearing that denominator gives the polynomial matrix N
below (entries computed independently by SymPy this session: the
Jacobian of (a,b,c,d) ↦ (-b/D, a/D, -d/D, c/D), simplified and multiplied
through by D²). Two exact matrix identities hold, proved entrywise by
`ring` after expanding matrix multiplication:

* `N_sq_eq_D_smul_K`:  N * N = D • K
* `K_sq_eq_D_sq_smul_one`:  K * K = D² • 1

Composing these gives the main theorem:

* `N_pow_four_eq_D_pow_four_smul_one`:  (N*N)*(N*N) = D⁴ • 1

Consequently every eigenvalue of N (as a complex matrix) is a root of
t⁴ - D⁴, i.e. lies in {D, -D, iD, -iD}, each of modulus exactly |D|; since
J = N / D², every eigenvalue of J has modulus exactly 1/|D|. This
eigenvalue-modulus statement is recorded here as documentation, not as a
further Lean theorem: it requires "the eigenvalues of a real matrix over
ℂ, as a multiset with multiplicity" together with a minimal-polynomial
divisibility argument, machinery this file does not build. What is
formalized -- N² = D•K, K² = D²•1, and their corollary N⁴ = D⁴•1 -- is
the exact polynomial content that this eigenvalue statement rests on, and
was independently confirmed via SymPy (`jac_clean.py`, this session)
before being written as a Lean proof.

Earlier in this same investigation, a since-corrected claim asserted
J² = -I at the massless locus |D| = 1; that claim is false (checked
directly, `GrassmannianMass.lean`). The identity proved here, N⁴ = D⁴•1,
is the corrected, exact replacement: it specializes at |D| = 1 to
N⁴ = 1, a period-4 structure, matching `transition_transition_eq_neg`'s
τ² = -id (period 4 overall) rather than a period-2 complex structure.
-/

namespace GppGrassmannianJacobian

/-- The Jacobian numerator matrix N(a,b,c,d): the Jacobian of the chart
    transition τ, cleared of its D² denominator (D = ad - bc). -/
def N (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![b * d, -(a * d), -(b ^ 2), a * b;
     -(b * c), a * c, a * b, -(a ^ 2);
     d ^ 2, -(c * d), -(b * d), b * c;
     -(c * d), c ^ 2, a * d, -(a * c)]

/-- K = N² / D, again cleared of its own denominator: an explicit
    polynomial matrix with K² = D² • 1. -/
def K (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -(a * c) - b * d, 0, a ^ 2 + b ^ 2;
     a * c + b * d, 0, -(a ^ 2) - b ^ 2, 0;
     0, -(c ^ 2) - d ^ 2, 0, a * c + b * d;
     c ^ 2 + d ^ 2, 0, -(a * c) - b * d, 0]

/-- N² = D • K, D = ad - bc. -/
theorem N_sq_eq_D_smul_K (a b c d : ℝ) :
    N a b c d * N a b c d = (a * d - b * c) • K a b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [N, K, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

/-- K² = D² • 1, D = ad - bc. -/
theorem K_sq_eq_D_sq_smul_one (a b c d : ℝ) :
    K a b c d * K a b c d = (a * d - b * c) ^ 2 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [K, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    ring

/-- The main theorem: N⁴ = D⁴ • 1, D = ad - bc. Every eigenvalue of N
    (over ℂ) is therefore a root of t⁴ - D⁴, i.e. lies in {D,-D,iD,-iD},
    each of modulus |D|. -/
theorem N_pow_four_eq_D_pow_four_smul_one (a b c d : ℝ) :
    N a b c d * N a b c d * (N a b c d * N a b c d)
      = (a * d - b * c) ^ 4 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  rw [N_sq_eq_D_smul_K, smul_mul_assoc, mul_smul_comm, K_sq_eq_D_sq_smul_one]
  simp only [smul_smul]
  congr 1
  ring

end GppGrassmannianJacobian
