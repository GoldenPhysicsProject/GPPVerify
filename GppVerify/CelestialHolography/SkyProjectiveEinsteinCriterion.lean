import Mathlib.Tactic
import GppVerify.CelestialHolography.SpinorEinsteinCorrespondenceSelector

/-!
# Sky-projective null-ray criterion for Einstein Ricci data

For an affinely parametrized null geodesic in four dimensions, the trace of the optical
tidal/Jacobi curvature on the two-dimensional screen is, up to the Riemann-sign
convention, `-Ric(k,k)`.  The 2022 Bautista--Ibort--Lafuente sky construction calls a
light-ray parameter *projective* exactly when the trace of its conformal Jacobi curvature
vanishes.

Consequently, for an affine parameter of a chosen metric representative, the sky
projective condition is exactly

  Ric(k,k) = 0.

A metric is Einstein iff its symmetric Ricci tensor is pure trace.  In split signature,
`SpinorEinsteinCorrespondenceSelector` already proves the needed null-cone rigidity:
vanishing of a quadratic tensor on every spinor-factorized null direction is equivalent
to being a scalar multiple of the determinant metric.

This module packages that exact finite-dimensional criterion.  The identification of
`skyAffineTrace` with the differential-geometric optical/Jacobi trace is an external
geometric input; the iff theorem below is pure coordinate algebra once that input is
made.
-/

namespace GppSkyProjectiveEinsteinCriterion

open GppGrassmannianGooglyDecomposition
open GppFlatInfinityCelestialFactorization
open GppNullConeEinsteinSelector
open GppSpinorEinsteinCorrespondenceSelector

/-- Ricci quadratic form evaluated on the split null vector `lambda tensor lambdatilde`. -/
def nullRicciQuadratic
    (A B C D E F G H I J : ℝ)
    (lambda lambdatilde : Spinor2) : ℝ :=
  let X := nullMomentum lambda lambdatilde
  quad4 A B C D E F G H I J X.1 X.2.1 X.2.2.1 X.2.2.2

/-- Four-dimensional optical trace convention: the `2x2` Ricci focusing contribution
has trace `-Ric(k,k)`.  Only its zero locus is used below, so the overall sign convention
is immaterial to the Einstein criterion. -/
def skyAffineTrace
    (A B C D E F G H I J : ℝ)
    (lambda lambdatilde : Spinor2) : ℝ :=
  - nullRicciQuadratic A B C D E F G H I J lambda lambdatilde

/-- Algebraic version of: every affine null-ray parameter of the metric is sky-projective. -/
def AllAffineNullRaysSkyProjective
    (A B C D E F G H I J : ℝ) : Prop :=
  ∀ lambda lambdatilde : Spinor2,
    skyAffineTrace A B C D E F G H I J lambda lambdatilde = 0

/-- Vanishing of the sky optical trace is equivalent to vanishing of the underlying null
Ricci quadratic form. -/
theorem skyAffineTrace_zero_iff_nullRicci_zero
    (A B C D E F G H I J : ℝ)
    (lambda lambdatilde : Spinor2) :
    skyAffineTrace A B C D E F G H I J lambda lambdatilde = 0 ↔
      nullRicciQuadratic A B C D E F G H I J lambda lambdatilde = 0 := by
  unfold skyAffineTrace
  constructor <;> intro h <;> linarith

/-- Main criterion: all affine null-ray parameters are sky-projective iff the Ricci
quadratic form is pure trace, i.e. proportional to the split conformal metric. -/
theorem all_affine_null_rays_sky_projective_iff_pure_trace
    (A B C D E F G H I J : ℝ) :
    AllAffineNullRaysSkyProjective A B C D E F G H I J ↔
    ∃ mu : ℝ, ∀ a b c d : ℝ,
      quad4 A B C D E F G H I J a b c d = mu * det2 (a,b,c,d) := by
  constructor
  · intro hproj
    apply spinor_vanishing_implies_pure_trace
    intro lambda lambdatilde
    have htr := hproj lambda lambdatilde
    have hzero :=
      (skyAffineTrace_zero_iff_nullRicci_zero
        A B C D E F G H I J lambda lambdatilde).mp htr
    exact hzero
  · intro hpure
    have hspin :=
      (spinor_vanishing_iff_pure_trace A B C D E F G H I J).2 hpure
    intro lambda lambdatilde
    apply (skyAffineTrace_zero_iff_nullRicci_zero
      A B C D E F G H I J lambda lambdatilde).2
    exact hspin lambda lambdatilde

/-- Spinor form of the same criterion: a pure-trace Ricci tensor has zero optical trace
on every celestial/null spinor pair. -/
theorem pure_trace_implies_zero_sky_trace
    (A B C D E F G H I J mu : ℝ)
    (hpure : ∀ a b c d : ℝ,
      quad4 A B C D E F G H I J a b c d = mu * det2 (a,b,c,d))
    (lambda lambdatilde : Spinor2) :
    skyAffineTrace A B C D E F G H I J lambda lambdatilde = 0 := by
  apply (skyAffineTrace_zero_iff_nullRicci_zero
    A B C D E F G H I J lambda lambdatilde).2
  unfold nullRicciQuadratic
  rw [hpure]
  rw [nullMomentum_det_zero]
  ring

end GppSkyProjectiveEinsteinCriterion
