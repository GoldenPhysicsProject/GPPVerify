import Mathlib.Tactic

/-!
# Massive-vector / scalar state-count reconstruction

This file isolates only the exact state-count algebra justified by the symbolic
adjacent-MHV audit and dimensional-reconstruction bookkeeping. It does not identify
couplings, color factors, cut orientation, or loop-measure normalizations with any
particular amplitude convention, and it does not compute the still-missing
`D_s = 4`, `mu != 0` gluon sewing numerator.
-/

namespace GppMassiveVectorStateSumReconstruction

/-- Three equal massive-vector polarization contributions sum to three times the
corresponding scalar contribution. -/
theorem three_equal_vector_states
    (C : ℝ) : C + C + C = 3 * C := by
  ring

/-- In the dimensional-reconstruction convention where the four-dimensional cut is
obtained by subtracting one scalar state from the three-state massive-vector sum,
the resulting state factor is exactly two scalar cuts. -/
theorem four_dimensional_reconstruction
    (Cscalar Cvector C4 : ℝ)
    (hvector : Cvector = 3 * Cscalar)
    (hsub : C4 = Cvector - Cscalar) :
    C4 = 2 * Cscalar := by
  rw [hsub, hvector]
  ring

/-- Equivalent abstract formulation directly from three identical vector states. -/
theorem four_dimensional_reconstruction_from_equal_states
    (Cscalar C4 : ℝ)
    (hsub : C4 = (Cscalar + Cscalar + Cscalar) - Cscalar) :
    C4 = 2 * Cscalar := by
  rw [hsub]
  ring

/-- The same algebra with an arbitrary state multiplicity `D-2`: subtracting one
scalar state leaves the factor `D-3`.  This is an algebraic bookkeeping identity,
not a claim that an arbitrary-dimensional amplitude has already been normalized. -/
theorem dimensional_state_subtraction
    (D Cscalar Cdim Csub : ℝ)
    (hdim : Cdim = (D - 2) * Cscalar)
    (hsub : Csub = Cdim - Cscalar) :
    Csub = (D - 3) * Cscalar := by
  rw [hsub, hdim]
  ring

/-! ## Spin-dimension reconstruction at fixed loop momentum

Changing the spin-state dimension `D_s` while holding the D-dimensional loop
momentum fixed adds one real adjoint-scalar polarization per additional spin
direction beyond four. The formulas below encode only that linear state-counting
law. In particular `D_s = 4` does **not** set the dimensional mass `mu` to zero.
-/

/-- Linear dimensional-reconstruction model at fixed loop momentum:
`C^(D_s) = C^(4) + (D_s - 4) C_scalar`, where `C_scalar` denotes one real
adjoint-scalar species. -/
def spinDimReconstruction (Ds C4 Cscalar : ℝ) : ℝ :=
  C4 + (Ds - 4) * Cscalar

/-- The reconstruction returns the massive `D_s=4` baseline exactly. -/
@[simp] theorem spinDimReconstruction_four (C4 Cscalar : ℝ) :
    spinDimReconstruction 4 C4 Cscalar = C4 := by
  simp [spinDimReconstruction]

/-- Changing spin dimension from `Ds1` to `Ds2` changes the cut by exactly
`(Ds2-Ds1)` real-adjoint-scalar contributions. -/
theorem spinDimReconstruction_sub
    (Ds1 Ds2 C4 Cscalar : ℝ) :
    spinDimReconstruction Ds2 C4 Cscalar -
      spinDimReconstruction Ds1 C4 Cscalar =
        (Ds2 - Ds1) * Cscalar := by
  unfold spinDimReconstruction
  ring

/-- In the 't Hooft--Veltman bookkeeping specialization `D_s = 4 - 2 epsilon`,
the spin-state correction relative to the fixed-`mu` `D_s=4` baseline is
`-2 epsilon` times the one-real-scalar cut. -/
theorem spinDimReconstruction_HV
    (ε C4 Cscalar : ℝ) :
    spinDimReconstruction (4 - 2 * ε) C4 Cscalar =
      C4 - 2 * ε * Cscalar := by
  unfold spinDimReconstruction
  ring

/-- If the scalar-tree convention packages two real scalars into one complex
adjoint scalar contribution `Ccomplex = 2*Cscalar`, the reconstruction coefficient
is `(D_s-4)/2` in that convention. -/
theorem spinDimReconstruction_complex_scalar
    (Ds C4 Cscalar Ccomplex : ℝ)
    (hcomplex : Ccomplex = 2 * Cscalar) :
    spinDimReconstruction Ds C4 Cscalar =
      C4 + ((Ds - 4) / 2) * Ccomplex := by
  rw [hcomplex]
  unfold spinDimReconstruction
  ring

end GppMassiveVectorStateSumReconstruction

#print axioms GppMassiveVectorStateSumReconstruction.three_equal_vector_states
#print axioms GppMassiveVectorStateSumReconstruction.four_dimensional_reconstruction
#print axioms GppMassiveVectorStateSumReconstruction.four_dimensional_reconstruction_from_equal_states
#print axioms GppMassiveVectorStateSumReconstruction.dimensional_state_subtraction
#print axioms GppMassiveVectorStateSumReconstruction.spinDimReconstruction_sub
#print axioms GppMassiveVectorStateSumReconstruction.spinDimReconstruction_HV
#print axioms GppMassiveVectorStateSumReconstruction.spinDimReconstruction_complex_scalar
