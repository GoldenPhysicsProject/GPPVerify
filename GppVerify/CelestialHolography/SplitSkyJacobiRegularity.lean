import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatSkyJacobiCurve

/-!
# Split-signature regularity of the flat sky Jacobi curve

The general sky/Jacobi programme needs only *regularity* for the canonical projective
structure: the velocity quadratic form of the curve in the Lagrangian Grassmannian must
be nondegenerate.  Positivity/monotonicity is a stronger condition used by some moving-
frame classification results, but is not required by the original Agrachev--Zelenko
projective-structure construction.

For a null geodesic in split signature `(2,2)`, the transverse screen has signature
`(1,1)`.  In the flat model of `FlatSkyJacobiCurve`, replace the positive screen pairing
by

  <(x0,x1),(y0,y1)>_split = x0*y0 - x1*y1.

The corresponding Wronskian form on Jacobi initial data remains symplectic, and the
velocity quadratic form of the sky curve

  L_s = {(-s v, v)}

is exactly the split screen norm `<v,v>_split`.  Hence it is indefinite but nondegenerate:
the curve is regular, not monotonous.

This is the precise finite-dimensional reason the projective-Ricci/Schwarzian mechanism
survives the GPP split `(2,2)` working slice even though definite normal-frame arguments
must not be imported blindly.
-/

namespace GppSplitSkyJacobiRegularity

open GppFlatInfinityCelestialFactorization
open GppFlatSkyJacobiCurve

/-- Standard `(1,1)` split pairing on the two-dimensional null screen. -/
def splitDot2 (x y : Spinor2) : ℝ := x.1*y.1 - x.2*y.2

/-- Split Wronskian symplectic form on Jacobi initial data `(value,derivative)`. -/
def splitSkyOmega (u v : SkyState) : ℝ :=
  splitDot2 u.1 v.2 - splitDot2 u.2 v.1

/-- Parameter derivative of `s ↦ skyState s v` with the screen label `v` held fixed. -/
def skyParameterDerivative (v : Spinor2) : SkyState :=
  ((-v.1,-v.2),(0,0))

/-- The split sky planes remain isotropic for the split Wronskian form. -/
theorem split_sky_plane_isotropic (s : ℝ) (v w : Spinor2) :
    splitSkyOmega (skyState s v) (skyState s w) = 0 := by
  rcases v with ⟨v0,v1⟩
  rcases w with ⟨w0,w1⟩
  simp [splitSkyOmega, splitDot2, skyState]
  ring

/-- The velocity quadratic form of the sky Jacobi curve is exactly the split screen norm. -/
theorem sky_velocity_quadratic_eq_split_norm (s : ℝ) (v : Spinor2) :
    splitSkyOmega (skyState s v) (skyParameterDerivative v) = splitDot2 v v := by
  rcases v with ⟨v0,v1⟩
  simp [splitSkyOmega, splitDot2, skyState, skyParameterDerivative]
  ring

/-- More generally the polarized velocity form is the split screen bilinear form. -/
theorem sky_velocity_bilinear_eq_split_pairing (s : ℝ) (v w : Spinor2) :
    splitSkyOmega (skyState s v) (skyParameterDerivative w) = splitDot2 v w := by
  rcases v with ⟨v0,v1⟩
  rcases w with ⟨w0,w1⟩
  simp [splitSkyOmega, splitDot2, skyState, skyParameterDerivative]
  ring

/-- The split screen pairing is nondegenerate. -/
theorem splitDot2_nondegenerate
    (v : Spinor2) (h : ∀ w : Spinor2, splitDot2 v w = 0) :
    v = (0,0) := by
  have h0 := h (1,0)
  have h1 := h (0,1)
  rcases v with ⟨v0,v1⟩
  simp [splitDot2] at h0 h1 ⊢
  constructor
  · exact h0
  · linarith

/-- Therefore the sky velocity bilinear form is nondegenerate at every parameter. -/
theorem split_sky_velocity_nondegenerate
    (s : ℝ) (v : Spinor2)
    (h : ∀ w : Spinor2,
      splitSkyOmega (skyState s v) (skyParameterDerivative w) = 0) :
    v = (0,0) := by
  apply splitDot2_nondegenerate v
  intro w
  rw [← sky_velocity_bilinear_eq_split_pairing s v w]
  exact h w

/-- Positive direction exists. -/
theorem split_velocity_positive_witness (s : ℝ) :
    splitSkyOmega (skyState s (1,0)) (skyParameterDerivative (1,0)) = 1 := by
  rw [sky_velocity_quadratic_eq_split_norm]
  norm_num [splitDot2]

/-- Negative direction exists. -/
theorem split_velocity_negative_witness (s : ℝ) :
    splitSkyOmega (skyState s (0,1)) (skyParameterDerivative (0,1)) = -1 := by
  rw [sky_velocity_quadratic_eq_split_norm]
  norm_num [splitDot2]

/-- Exact signature-safe summary: the split sky curve has a nondegenerate velocity form,
while that form is not definite.  This is the finite algebraic content of “regular but
not monotonous”. -/
theorem split_sky_regular_but_indefinite (s : ℝ) :
    (∀ v : Spinor2,
      (∀ w : Spinor2,
        splitSkyOmega (skyState s v) (skyParameterDerivative w) = 0) →
      v = (0,0)) ∧
    (∃ vp vn : Spinor2,
      splitSkyOmega (skyState s vp) (skyParameterDerivative vp) > 0 ∧
      splitSkyOmega (skyState s vn) (skyParameterDerivative vn) < 0) := by
  constructor
  · intro v h
    exact split_sky_velocity_nondegenerate s v h
  · refine ⟨(1,0),(0,1), ?_, ?_⟩
    · rw [split_velocity_positive_witness]
      norm_num
    · rw [split_velocity_negative_witness]
      norm_num

end GppSplitSkyJacobiRegularity
