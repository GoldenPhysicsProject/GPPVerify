import Mathlib.Tactic

/-!
# Four-point adjacent-MHV bubble subtraction algebra

This file formalizes only the convention-independent rational algebra extracted from
the direct Badger/Forde `s23` scalar-loop audit.  It deliberately does **not** identify
one scalar-flow orientation with one complex scalar.  That multiplicity is a separate
physics/state-space input.

In the rational frame used by the discovery calculation,

  s23 = 1,
  s12 = -u^2/(1+u^2),
  Q   = 1.

The surviving triangle subtraction is controlled by a quadratic pole in `y`, and after
the symmetric root sum and the `T₁,T₂,T₃` moment map its real coefficient is affine in
`mu2`.  The theorems below certify the algebra needed to recover the published reduced
bubble coefficient once the complex-scalar multiplicity two is supplied explicitly.
-/

namespace GppFourPointMHVBubbleSubtractionAlgebra

/-- Coefficient `B` of the triangle-pole quadratic
`u*y^2 + B*y + C`. -/
def poleB (u t : ℝ) : ℝ := t * (1 - u ^ 2) - u

/-- Constant term `C` of the triangle-pole quadratic. -/
def poleC (u t mu2 : ℝ) : ℝ :=
  u * mu2 - u * t ^ 2 + u ^ 2 * t

/-- The triangle-root discriminant admits the exact square-minus-mass normal form. -/
theorem triangle_pole_discriminant
    (u t mu2 : ℝ) :
    poleB u t ^ 2 - 4 * u * poleC u t mu2 =
      (t * (1 + u ^ 2) - u) ^ 2 - 4 * mu2 * u ^ 2 := by
  unfold poleB poleC
  ring

/-- The rational-frame denominator never vanishes on the real axis. -/
theorem one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := by
  nlinarith [sq_nonneg u]

/-- Real part of the fully moment-mapped surviving triangle subtraction before
Badger's explicit `-1/2` subtraction prefactor.  The physical expression is `i` times
this real coefficient. -/
noncomputable def mappedSubtractionReal (u mu2 : ℝ) : ℝ :=
  (10 * mu2 * u ^ 2 + 6 * mu2 - u ^ 2) / (3 * (1 + u ^ 2))

/-- The mapped subtraction is exactly affine in `mu2`; its slope is the rational
coefficient selected by the `mu^2` extraction. -/
theorem mappedSubtractionReal_affine
    (u mu2 delta : ℝ) :
    mappedSubtractionReal u (mu2 + delta) - mappedSubtractionReal u mu2 =
      delta * (2 * (5 * u ^ 2 + 3) / (3 * (1 + u ^ 2))) := by
  unfold mappedSubtractionReal
  field_simp [(one_add_sq_pos u).ne']
  ring

/-- In particular the unit finite difference is the exact `mu2` coefficient. -/
theorem mappedSubtractionReal_unit_difference
    (u mu2 : ℝ) :
    mappedSubtractionReal u (mu2 + 1) - mappedSubtractionReal u mu2 =
      2 * (5 * u ^ 2 + 3) / (3 * (1 + u ^ 2)) := by
  simpa using mappedSubtractionReal_affine u mu2 1

/-- Real coefficient for one scalar-flow orientation after Badger's `-1/2` prefactor. -/
noncomputable def oneFlowBubbleReal (u : ℝ) : ℝ :=
  -(5 * u ^ 2 + 3) / (3 * (1 + u ^ 2))

/-- The frame value of `s12` used by the rational cut parametrization. -/
noncomputable def frameS12 (u : ℝ) : ℝ :=
  -(u ^ 2) / (1 + u ^ 2)

/-- Pure rational restoration identity.  If the state-space convention supplies two
equal scalar-flow orientations, twice the one-flow result is exactly the phase-normal
adjacent-MHV bubble coefficient in the frame `s23=1`, `Q=1`.

The theorem proves only the algebraic equality; it does not prove the multiplicity-two
state-space statement. -/
theorem two_mul_oneFlow_eq_frame_target
    (u : ℝ) :
    2 * oneFlowBubbleReal u = (2 / 3 : ℝ) * (2 * frameS12 u - 3) := by
  unfold oneFlowBubbleReal frameS12
  field_simp [(one_add_sq_pos u).ne']
  ring

/-- Explicit hypothesis boundary for the complex-scalar convention.  Any quantity
`Ccomplex` known independently to equal twice the one-flow coefficient inherits the
frame target.  The factor two is an assumption here, not hidden in a definition. -/
theorem complexScalar_frame_target_of_two_flows
    {u Ccomplex : ℝ}
    (hcomplex : Ccomplex = 2 * oneFlowBubbleReal u) :
    Ccomplex = (2 / 3 : ℝ) * (2 * frameS12 u - 3) := by
  rw [hcomplex, two_mul_oneFlow_eq_frame_target]

end GppFourPointMHVBubbleSubtractionAlgebra

#print axioms GppFourPointMHVBubbleSubtractionAlgebra.triangle_pole_discriminant
#print axioms GppFourPointMHVBubbleSubtractionAlgebra.one_add_sq_pos
#print axioms GppFourPointMHVBubbleSubtractionAlgebra.mappedSubtractionReal_affine
#print axioms GppFourPointMHVBubbleSubtractionAlgebra.mappedSubtractionReal_unit_difference
#print axioms GppFourPointMHVBubbleSubtractionAlgebra.two_mul_oneFlow_eq_frame_target
#print axioms GppFourPointMHVBubbleSubtractionAlgebra.complexScalar_frame_target_of_two_flows
