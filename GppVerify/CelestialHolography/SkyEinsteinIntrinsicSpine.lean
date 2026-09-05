import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatSkyJacobiCurve
import GppVerify.CelestialHolography.SplitSkyJacobiRegularity
import GppVerify.CelestialHolography.SkyProjectiveEinsteinCriterion
import GppVerify.CelestialHolography.SkyProjectiveSpinLift
import GppVerify.CelestialHolography.OrientationProjectorSwap

/-!
# Intrinsic sky-Jacobi spine for Einstein recognition

The real light-ray formulation of a conformal spacetime is not exhausted by the bare
contact manifold.  The distinguished family of skies `S(x)` is essential reconstruction
data.  For each light ray `gamma`, the tangent planes

  T_gamma S(gamma(s))

form a Jacobi curve in the Lagrangian Grassmannian of the contact hyperplane.  Modern
sky/Jacobi geometry supplies an intrinsic projective parameter class on this curve.

The companion modules formalize the finite algebra relevant to the proposed Einstein
recognition mechanism:

* `FlatSkyJacobiCurve`: flat sky tangents are exactly Jacobi fields vanishing at a point,
  are isotropic for the Wronskian form, and evolve by symplectic Jacobi transport;
* `SplitSkyJacobiRegularity`: in the GPP split `(2,2)` working slice, the sky velocity
  bilinear form is the `(1,1)` screen pairing.  It is nondegenerate but indefinite, so the
  flat sky curve is regular but non-monotonous.  This is exactly enough for the original
  Agrachev--Zelenko canonical projective-structure construction; stronger definite
  normal-frame results are not imported here;
* `SkyProjectiveEinsteinCriterion`: if the intrinsic sky optical trace is identified with
  the standard null Ricci focusing trace, then vanishing for every null spinor pair is
  equivalent, by exact split null-cone rigidity, to the Ricci tensor being pure trace;
* `SkyProjectiveSpinLift`: the central `±I` ambiguity of the rank-two `SL(2)` solution
  system is invisible projectively, isolating the finite algebra behind the standard
  PSL(2)-to-SL(2) theta/spin lift;
* `OrientationProjectorSwap`: four-orientation reversal leaves the underlying field fixed
  and swaps its two Hodge/Weyl projectors.

External geometric input, not formalized here:

1. the sky-tangent family of a curved light ray is a Lagrangian Jacobi curve;
2. for a regular Jacobi curve, generalized Ricci curvature supplies a canonical projective
   parameter class, with projective reparametrizations related by Möbius maps;
3. the ratio of solutions of the corresponding second-order projective equation gives a
   developing projective coordinate;
4. after a theta/spin choice that projective system lifts to a rank-two `SL(2)` local
   system;
5. LeBrun's rank-two holomorphic Einstein bundle exists over complex ambitwistor space and
   nonzero holomorphic sections correspond to Einstein representatives.

Signature caveat: the projective-Ricci/Schwarzian mechanism is supported by the original
regular-curve theory and therefore does not require definite velocity.  By contrast,
later complete Cartan/eigenframe classification results may use stronger admissibility or
definiteness hypotheses and are not part of the current split-signature argument.

Current open theorem:

  E_sky ?= E_LeBrun.

The fibrewise rank, `SL(2)` structure, and second-order projective equation now match.
What remains is the transverse/holomorphic gluing across neighboring light rays/skies and
proof that the resulting bundle agrees with LeBrun's Einstein bundle, not merely with the
same one-dimensional equation on each ray.
-/

namespace GppSkyEinsteinIntrinsicSpine

open GppGrassmannianGooglyDecomposition
open GppFlatInfinityCelestialFactorization
open GppNullConeEinsteinSelector
open GppSpinorEinsteinCorrespondenceSelector
open GppSkyProjectiveEinsteinCriterion

/-- Finite algebraic core of intrinsic Einstein recognition: the condition that every
spinor-factorized null direction have vanishing sky optical trace is equivalent to the
underlying symmetric quadratic tensor being pure trace. -/
theorem sky_spinor_selector_is_pure_trace
    (A B C D E F G H I J : ℝ) :
    AllAffineNullRaysSkyProjective A B C D E F G H I J ↔
    ∃ mu : ℝ, ∀ a b c d : ℝ,
      quad4 A B C D E F G H I J a b c d = mu * det2 (a,b,c,d) :=
  all_affine_null_rays_sky_projective_iff_pure_trace A B C D E F G H I J

/-- Equivalent spinor-correspondence formulation of the same pure-trace selector. -/
theorem correspondence_spinor_selector_is_pure_trace
    (A B C D E F G H I J : ℝ) :
    (∀ lambda lambdatilde : Spinor2,
      let X := nullMomentum lambda lambdatilde
      quad4 A B C D E F G H I J X.1 X.2.1 X.2.2.1 X.2.2.2 = 0) ↔
    (∃ mu : ℝ, ∀ a b c d : ℝ,
      quad4 A B C D E F G H I J a b c d = mu * det2 (a,b,c,d)) :=
  spinor_vanishing_iff_pure_trace A B C D E F G H I J

/-- Consequently the sky-trace condition and the direct spinor-correspondence condition
are equivalent at the exact finite quadratic level. -/
theorem sky_selector_iff_correspondence_selector
    (A B C D E F G H I J : ℝ) :
    AllAffineNullRaysSkyProjective A B C D E F G H I J ↔
    (∀ lambda lambdatilde : Spinor2,
      let X := nullMomentum lambda lambdatilde
      quad4 A B C D E F G H I J X.1 X.2.1 X.2.2.1 X.2.2.2 = 0) := by
  rw [sky_spinor_selector_is_pure_trace,
    correspondence_spinor_selector_is_pure_trace]

end GppSkyEinsteinIntrinsicSpine
