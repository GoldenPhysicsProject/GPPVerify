import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatSkyJacobiCurve
import GppVerify.CelestialHolography.SplitSkyJacobiRegularity
import GppVerify.CelestialHolography.SkyProjectiveEinsteinCriterion
import GppVerify.CelestialHolography.SkyProjectiveSpinLift
import GppVerify.CelestialHolography.PenroseLocalTwistorRayReduction
import GppVerify.CelestialHolography.PenroseLocalTwistorEinsteinQuotient
import GppVerify.CelestialHolography.PenroseLocalTwistorRayGaugeCovariance
import GppVerify.CelestialHolography.PenroseQuotientTautologicalTwist
import GppVerify.CelestialHolography.AmbidextrousPenroseRayQuotients
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
  quotient carries the inverse character of the actual tautological `lambda` line;
* `AmbidextrousPenroseRayQuotients`: constructs the mirror/dual local-twistor quotient at
  the same finite algebraic level.  Its quotient state has the SAME Sturm generator but
  transforms by `a`, opposite to the ordinary side.  Hence the two actual neutral
  rank-two presentations are

      L_lambda tensor Q_left,
      L_lambdatilde tensor Q_right,

  where `L_lambda` and `L_lambdatilde` are the lines spanned by the two null spinors.
  This corrects an earlier schematic `L_lambda^* tensor Q_left`: with `L_lambda` defined as
  the actual line spanned by `lambda`, its `+1` character cancels the quotient's `-1`
  character directly, without a dual;
* `RayFieldSkyDescent`: proves the exact set-theoretic descent principle that a family of
  raywise values comes from one spacetime field iff it agrees on all samples representing
  the same spacetime point.  This isolates the logical content that NSF metricity or an
  ambitwistor holomorphic transition law must provide;
* `OrientationProjectorSwap`: four-orientation reversal leaves the underlying field fixed
  and swaps its two Hodge/Weyl projectors.

The Penrose quotient is especially important conceptually.  The same second-order
projective/Sturm dynamics found from skies and the null almost-Einstein equation occurs as
an exact quotient of Penrose's own raywise local-twistor transport.  Gauge covariance and
the mirror construction now sharpen the statement:

  P(Q_left,gamma) = P(Q_right,gamma) = P(E_sky,gamma)

at the level of the common two-dimensional Sturm/projective carrier, after the stated
constant phase convention.  The two one-sided vector representatives have opposite
little-group weights.  Tensoring each with its ACTUAL tautological ray-spinor line cancels
that weight.  A canonical vector-bundle isomorphism between the two neutralized objects is
NOT proved: the unprimed and primed spinor lines remain distinct, and identifying them
would require additional parity/reality/spin data.  The correct nonlinear target is thus
ambidextrous rather than a hidden pointwise `S ≅ S'` identification.

External geometric input, not formalized here:

1. the sky-tangent family of a curved light ray is a Lagrangian Jacobi curve;
2. for a regular Jacobi curve, generalized Ricci curvature supplies a canonical projective
   parameter class, with projective reparametrizations related by Möbius maps;
3. the ratio of solutions of the corresponding second-order projective equation gives a
   developing projective coordinate;
4. after a theta/spin choice that projective system lifts to a rank-two `SL(2)` local
   system;
5. ordinary and dual local-twistor transport are conformally natural and reduce along an
   adapted null ray to the two mirror calculations encoded above;
6. modern four-dimensional projective ambitwistor space has the redundant anti-diagonal
   action `Z -> a Z`, `Ztilde -> a^{-1} Ztilde`; line bundles `O(p,q)` have corresponding
   character `a^(p-q)`.  Therefore the present finite calculation fixes only
   `p-q=-1` for `Q_left` and `p-q=+1` for `Q_right`.  Their separate `(p,q)` homogeneities
   are NOT yet determined because simultaneous/projective ray scaling also reparametrizes
   the affine ray and acts non-uniformly on `(field,derivative)` state coordinates;
7. the null-surface formulation supplies metricity equations which couple the raywise data
   transversely so that one spacetime metric descends.  NSF explicitly describes these as
   the conditions making the celestial-direction-dependent metric representatives one and
   the same spacetime metric;
8. LeBrun's generic rank-two holomorphic Einstein bundle exists over complex ambitwistor
   space and nonzero holomorphic sections correspond to Einstein representatives.  Its
   correspondence-space pullback is characterized by a conformally invariant second-order
   operator on a conformal density line.  Right-flat reductions admit additional one-sided
   descriptions such as `E ≅ Omega^1 P tensor L^{-2}`; those one-sided bundles have different
   rank bookkeeping and must NOT be identified mechanically with the generic rank-two
   ambitwistor bundle or with the present ray quotient.

Signature caveat: the projective-Ricci/Schwarzian mechanism is supported by the original
regular-curve theory and therefore does not require definite velocity.  By contrast,
later complete Cartan/eigenframe classification results may use stronger admissibility or
definiteness hypotheses and are not part of the current split-signature argument.

Current open theorem, with the ambidextrous line weights now explicit:

  glue(L_lambda tensor Q_left) ?= glue(L_lambdatilde tensor Q_right)
      ?= E_LeBrun,

where the first `?=` means an isomorphism of the appropriate neutral rank-two
holomorphic/projective systems, not an identification of the unprimed and primed spinor
lines themselves.  The remaining hard steps are:

* determine the full holomorphic homogeneity/transition data, not just the anti-diagonal
  little-group character;
* prove transverse/sky compatibility across neighbouring rays;
* show NSF metricity realizes the same descent law as the transition/gluing condition of
  LeBrun's generic Einstein bundle;
* identify the resulting neutral rank-two holomorphic bundle with LeBrun's `E`.

The historical Penrose/newsletter review strongly supports this formulation: his googly
maps repeatedly become projective before a scale is chosen, his later work demands
symmetry between twistor and dual-twistor data, and the unresolved obstruction repeatedly
migrates from local propagation to global consistency/gluing.
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
