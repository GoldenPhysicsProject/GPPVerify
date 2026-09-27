import Mathlib.Tactic

/-!
# Dimensional state-sum reconstruction: 4D/5D baseline bridge

For a fixed D-dimensional loop momentum with four-dimensional projection satisfying
`ell^2 = mu^2`, dimensional reconstruction varies the internal spin dimension `D_s`
without changing that loop momentum.  The physical input is that each extra spin
direction relative to `D_s = 4` behaves as one real adjoint-scalar species on external
four-dimensional gluons.

This file does not assert that physical input as an axiom.  Instead it records the exact
algebra that follows once two cut identities are supplied:

  C_Ds = C_4 + (D_s - 4) C_S,
  C_V  = C_4 + C_S,

where `C_V` is the five-dimensional massless-vector state sum, equivalently the
three-polarization four-dimensional massive-vector cut.  These imply

  C_Ds = C_V + (D_s - 5) C_S,
  C_4  = C_V - C_S.

This is the precise bridge needed before the genuinely dynamical task of evaluating the
massive-vector trees and their three-state sewing.
-/

namespace GppDimensionalStateSumReconstruction

/-- Shifting the dimensional-reconstruction baseline from `D_s=4` to `D_s=5`.
The physical statements are explicit hypotheses; the conclusion is exact algebra. -/
theorem reconstruct_from_massiveVector_baseline
    {Cds C4 CV CS Ds : ℂ}
    (hDs : Cds = C4 + (Ds - 4) * CS)
    (hV : CV = C4 + CS) :
    Cds = CV + (Ds - 5) * CS := by
  rw [hDs, hV]
  ring

/-- The nonzero-`mu`, `D_s=4` baseline is massive-vector minus one real scalar. -/
theorem fourDimensional_baseline_eq_massiveVector_sub_scalar
    {C4 CV CS : ℂ} (hV : CV = C4 + CS) :
    C4 = CV - CS := by
  rw [hV]
  ring

/-- Conversely, the five-dimensional massive-vector baseline is recovered by adding
one scalar species to the `D_s=4` baseline. -/
theorem massiveVector_eq_fourDimensional_add_scalar
    {C4 CV CS : ℂ} (h4 : C4 = CV - CS) :
    CV = C4 + CS := by
  rw [h4]
  ring

/-- State-count consistency of the five-dimensional baseline:
`3 + (D_s - 5) = D_s - 2`. -/
theorem state_count_from_five (Ds : ℤ) :
    3 + (Ds - 5) = Ds - 2 := by
  ring

/-- At `D_s=4`, the five-dimensional reconstruction coefficient is exactly `-1`. -/
theorem scalar_coefficient_at_four :
    ((4 : ℤ) - 5) = -1 := by
  norm_num

/-- At `D_s=5`, the scalar correction about the massive-vector baseline vanishes. -/
theorem scalar_coefficient_at_five :
    ((5 : ℤ) - 5) = 0 := by
  norm_num

end GppDimensionalStateSumReconstruction

#print axioms GppDimensionalStateSumReconstruction.reconstruct_from_massiveVector_baseline
#print axioms GppDimensionalStateSumReconstruction.fourDimensional_baseline_eq_massiveVector_sub_scalar
#print axioms GppDimensionalStateSumReconstruction.state_count_from_five
