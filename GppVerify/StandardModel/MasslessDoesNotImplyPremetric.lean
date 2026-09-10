import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation

/-!
# Masslessness does not imply metric degeneracy

The orientation programme uses a genuinely premetric Big-Bang boundary as a possible
physical hypothesis.  It is important not to confuse that with the ordinary statement
`m=0`.

A perfectly nondegenerate Lorentz metric admits nonzero null vectors.  In the two-dimensional
Minkowski toy model

    eta = diag(-1,+1),
    q(t,x) = -t^2 + x^2,

one has `det eta = -1 != 0`, while `(1,1)` is nonzero and null.  Thus a massless/null sector
can live on an entirely well-defined nondegenerate metric.

Therefore the proposed premetric epoch needs an additional geometric order parameter
(such as invertibility of a tetrad/soldering form or an equivalent Grassmannian incidence
structure).  Physical mass may co-emerge with that structure, but `m=0` alone cannot be the
mathematical definition of "metric undefined".
-/

namespace GppMasslessDoesNotImplyPremetric

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev V2R := Fin 2 → ℝ

/-- Two-dimensional Lorentz metric. -/
def eta : M2R := !![-1,0;0,1]

/-- Associated quadratic form in coordinates. -/
def lorentzQ (v : V2R) : ℝ := -(v 0)^2 + (v 1)^2

/-- A concrete nonzero null vector. -/
def nullVec : V2R := ![1,1]

/-- The Lorentz metric is nondegenerate. -/
theorem eta_det_nonzero : Matrix.det eta ≠ 0 := by
  norm_num [eta, Matrix.det_fin_two]

/-- The chosen vector is null. -/
theorem nullVec_is_null : lorentzQ nullVec = 0 := by
  norm_num [lorentzQ, nullVec]

/-- The chosen null vector is not zero. -/
theorem nullVec_nonzero : nullVec ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : V2R => v 0) h
  norm_num [nullVec] at h0

/-- Explicit counterexample to the implication "massless/null -> degenerate metric". -/
theorem nondegenerate_metric_has_nonzero_null_state :
    Matrix.det eta ≠ 0 ∧ nullVec ≠ 0 ∧ lorentzQ nullVec = 0 := by
  exact ⟨eta_det_nonzero, nullVec_nonzero, nullVec_is_null⟩

end GppMasslessDoesNotImplyPremetric
