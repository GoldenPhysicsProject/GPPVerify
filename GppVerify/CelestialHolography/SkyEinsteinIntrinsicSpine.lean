import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatSkyJacobiCurve
import GppVerify.CelestialHolography.SplitSkyJacobiRegularity
import GppVerify.CelestialHolography.SkyProjectiveEinsteinCriterion
import GppVerify.CelestialHolography.SkyProjectiveSpinLift
import GppVerify.CelestialHolography.PenroseLocalTwistorRayReduction
import GppVerify.CelestialHolography.PenroseLocalTwistorEinsteinQuotient
import GppVerify.CelestialHolography.PenroseLocalTwistorRayGaugeCovariance
import GppVerify.CelestialHolography.PenroseQuotientTautologicalTwist
import GppVerify.CelestialHolography.RayFieldSkyDescent
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
* `PenroseLocalTwistorRayReduction`: Penrose's local-twistor transport, when restricted
  to the natural null-incidence line along a ray, reduces algebraically to the SAME
  two-component projective/Sturm system `f'=p`, `p'=-kappa f`.  The curvature coefficient
  `kappa` is deliberately convention-neutral because Penrose and modern conformal
  references use different displayed Schouten/Riemann signs;
* `PenroseLocalTwistorEinsteinQuotient`: strengthens the preceding scalar reduction by
  keeping all four adapted local-twistor components.  The ray-aligned three-dimensional
  subspace is transport-invariant; its one-dimensional kernel is exactly the invariant
  ray-twistor line; quotienting by that line leaves a two-dimensional carrier whose
  induced generator squares to `-U`, with `U=P(k,k)` in the spinorial geometry;
* `PenroseLocalTwistorRayGaugeCovariance`: proves that the quotient dynamics is equivariant
  under null-spinor little-group rescaling and independent, after projection, of changes
  in the complementary adapted spinors.  Thus the projective ray system is not an artifact
  of one adapted frame;
* `PenroseQuotientTautologicalTwist`: records the important bundle-weight correction.  The
  quotient coordinates `(x,p)` transform by a common factor `a^{-1}` when
  `lambda -> a lambda`; the invariant object is `lambda tensor (x,p)`.  Therefore the raw
  quotient is naturally twisted by the tautological ray-spinor line.  Its projectivization
  is canonical, but comparison with an untwisted scalar Einstein-scale solution bundle
  must include the corresponding line dual/twist;
* `RayFieldSkyDescent`: proves the exact set-theoretic descent principle that a family of
  raywise values comes from one spacetime field iff it agrees on all samples representing
  the same spacetime point.  This isolates the logical content that NSF metricity or an
  ambitwistor holomorphic transition law must provide;
* `OrientationProjectorSwap`: four-orientation reversal leaves the underlying field fixed
  and swaps its two Hodge/Weyl projectors.

The Penrose quotient is especially important conceptually.  The same second-order
projective/Sturm dynamics found from skies and the null almost-Einstein equation occurs as
an exact quotient of Penrose's own raywise local-twistor transport.  However, gauge
covariance shows that the strongest correct bundle-level statement is now

  projectivization(E_sky,gamma)
      = projectivization(T_gamma^aligned / <Z_gamma>)

at the finite coordinate level, together with an explicit common tautological spinor-line
weight on the Penrose quotient coordinates.  A literal untwisted vector-bundle equality
requires identifying and cancelling this line twist.  This replaces an earlier overly
strong wording which treated the raw quotient coordinate `x` as if it were already a
little-group-neutral scalar Einstein scale.

External geometric input, not formalized here:

1. the sky-tangent family of a curved light ray is a Lagrangian Jacobi curve;
2. for a regular Jacobi curve, generalized Ricci curvature supplies a canonical projective
   parameter class, with projective reparametrizations related by Möbius maps;
3. the ratio of solutions of the corresponding second-order projective equation gives a
   developing projective coordinate;
4. after a theta/spin choice that projective system lifts to a rank-two `SL(2)` local
   system;
5. Penrose's full local-twistor transport along each null ray is conformally natural, and
   generic curved spacetime does not canonically identify the different `T_gamma` fibres;
6. the null-surface formulation supplies metricity equations which couple the raywise data
   transversely so that one spacetime metric descends.  The NSF literature explicitly
   combines the raywise second-order Einstein-bundle equation with metricity to recover the
   full Einstein system;
7. LeBrun's rank-two holomorphic Einstein bundle exists over complex ambitwistor space and
   nonzero holomorphic sections correspond to Einstein representatives.  In the standard
   correspondence-space description its pullback is characterized as the kernel of a
   conformally invariant second-order operator on a conformal density line.

Signature caveat: the projective-Ricci/Schwarzian mechanism is supported by the original
regular-curve theory and therefore does not require definite velocity.  By contrast,
later complete Cartan/eigenframe classification results may use stronger admissibility or
definiteness hypotheses and are not part of the current split-signature argument.

Current open theorem, with the line twist now explicit:

  E_sky ?= L_ray^* tensor (T_gamma^aligned / <Z_gamma>) glued over ray space ?= E_LeBrun,

up to the precise convention for which tautological spinor line/dual carries the local
frame weight.  The projective dynamics and gauge covariance are exact; the remaining hard
steps are:

* identify the correct holomorphic tautological line factor globally;
* prove transverse/sky compatibility across neighbouring rays;
* show NSF metricity is the same descent law as the transition/gluing condition of the
  LeBrun Einstein bundle;
* prove the resulting rank-two holomorphic bundle is LeBrun's `E`.

The historical Penrose/newsletter review strongly supports this formulation: his googly
maps repeatedly become projective before a scale is chosen, and the unresolved obstruction
repeatedly migrates from local propagation to global consistency/gluing.
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
