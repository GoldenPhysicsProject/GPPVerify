import Mathlib.Tactic

/-!
# Two-dimensional symmetric-square trace algebra

A massive spin-one little-group state is the symmetric square of the SU(2) doublet.
For a two-dimensional endomorphism `C`, the trace on `Sym^2` is

  1/2 * ((tr C)^2 + tr(C^2)) = (tr C)^2 - det C.

This file certifies only the universal 2 by 2 algebra.  No spinor-helicity convention
or Lorentz identification of the matrix entries is assumed here.
-/

namespace GppMassiveVectorSym2Algebra

/-- Cayley-Hamilton trace identity for an abstract `2×2` matrix written by entries. -/
theorem trace_sq_entry_identity
    (a b c d : ℂ) :
    (a ^ 2 + 2 * b * c + d ^ 2) =
      (a + d) ^ 2 - 2 * (a * d - b * c) := by
  ring

/-- Trace of the symmetric-square representation in terms of trace and determinant. -/
theorem sym2_trace_eq_trace_sq_sub_det
    (a b c d : ℂ) :
    (1 / 2 : ℂ) *
        ((a + d) ^ 2 + (a ^ 2 + 2 * b * c + d ^ 2)) =
      (a + d) ^ 2 - (a * d - b * c) := by
  ring

end GppMassiveVectorSym2Algebra

#print axioms GppMassiveVectorSym2Algebra.trace_sq_entry_identity
#print axioms GppMassiveVectorSym2Algebra.sym2_trace_eq_trace_sq_sub_det
