import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import GppVerify.CelestialHolography.PenroseLocalTwistorEinsteinQuotient
import GppVerify.CelestialHolography.PenroseLocalTwistorRayGaugeCovariance
import GppVerify.CelestialHolography.PenroseQuotientTautologicalTwist

/-!
# Ambidextrous Penrose ray quotients

The ordinary local-twistor ray quotient previously formalized carries the projective
Sturm equation but has little-group weight `-1` under

  lambda -> a lambda,
  lambdatilde -> a^{-1} lambdatilde.

The standard dual local-twistor connection provides the mirror construction.  In the
usual notation a dual local twistor may be represented by a primed primary spinor and an
unprimed secondary spinor.  Along

  k^{AA'} = lambda^A lambdatilde^{A'},

restrict the primary spinor to the ray line

  pi_{A'} = xt * lambdatilde_{A'}

and contract the secondary spinor with `lambda` to obtain `pt`.  After a harmless constant
phase convention, dual local-twistor transport reduces to

  xt' = pt,
  pt' = -U xt,

where `U=P(k,k)` up to the global curvature-sign convention.  Thus the mirror quotient
has the SAME projective/Sturm dynamics as the ordinary quotient.

Under the same little-group rescaling, however,

  (xt,pt) -> a * (xt,pt),

so its weight is `+1`, opposite to the ordinary quotient.

Consequently the neutral rank-two objects are

  L_lambda tensor Q_left,
  L_lambdatilde tensor Q_right,

where the actual tautological spinor lines have weights `+1` and `-1`, respectively.
This corrects an earlier schematic use of `L_lambda^* tensor Q_left`: with the convention
that `L_lambda` is the line SPANNED BY lambda, no dual is required for cancellation.

External geometric input: the displayed mirror transport follows from the standard dual
local-twistor connection.  This file proves the finite quotient, Sturm intertwining, and
little-group weight algebra; it does not construct the curved holomorphic line bundles.
-/

namespace GppAmbidextrousPenroseRayQuotients

open Complex
open GppPenroseLocalTwistorEinsteinQuotient
open GppPenroseLocalTwistorRayGaugeCovariance
open GppPenroseQuotientTautologicalTwist

abbrev SturmState := ℂ × ℂ

/-- Convention-neutral projective/Sturm generator. -/
def sturmGenerator (U : ℂ) (u : SturmState) : SturmState :=
  (u.2, -U*u.1)

/-- Its square is `-U` times the identity. -/
theorem sturmGenerator_sq (U : ℂ) (u : SturmState) :
    sturmGenerator U (sturmGenerator U u) = (-U*u.1,-U*u.2) := by
  rcases u with ⟨x,p⟩
  simp [sturmGenerator]
  constructor <;> ring

/-- Convert the ordinary Penrose quotient coordinates `(x,g)` to projective momentum
`p=-i g`. -/
def leftToSturm (u : EinsteinRayState) : SturmState :=
  (u.1,-I*u.2)

/-- The ordinary local-twistor quotient generator intertwines exactly with the standard
Sturm generator after `p=-i g`. -/
theorem left_generator_intertwines_sturm (U : ℂ) (u : EinsteinRayState) :
    leftToSturm (einsteinRayGenerator U u) =
      sturmGenerator U (leftToSturm u) := by
  rcases u with ⟨x,g⟩
  simp [leftToSturm, einsteinRayGenerator, sturmGenerator]
  constructor <;> ring_nf

/-- Adapted coordinate carrier for the mirror/dual local-twistor ray calculation. -/
structure DualRayLocalTwistor where
  xt : ℂ
  yt : ℂ
  pt : ℂ
  qt : ℂ
  deriving Repr, DecidableEq

/-- Phase-normalized mirror generator.  The coefficients `C,D,E` encode adapted-frame
curvature components discarded by the aligned quotient, exactly as on the ordinary side. -/
def dualLocalTwistorGenerator
    (U C D E : ℂ) (W : DualRayLocalTwistor) : DualRayLocalTwistor :=
  ⟨W.pt,
   0,
   -(U*W.xt + C*W.yt),
   -(D*W.xt + E*W.yt)⟩

/-- Mirror primary spinor aligned with the dual null-spinor line. -/
def DualRayAligned (W : DualRayLocalTwistor) : Prop := W.yt = 0

/-- Mirror invariant ray line. -/
def InDualRayLine (W : DualRayLocalTwistor) : Prop :=
  W.xt = 0 ∧ W.yt = 0 ∧ W.pt = 0

/-- Mirror aligned subspace is invariant. -/
theorem dualRayAligned_preserved
    (U C D E : ℂ) (W : DualRayLocalTwistor) (hW : DualRayAligned W) :
    DualRayAligned (dualLocalTwistorGenerator U C D E W) := by
  rfl

/-- Mirror ray line is annihilated by the generator. -/
theorem dualRayLine_generator_zero
    (U C D E : ℂ) (W : DualRayLocalTwistor) (hW : InDualRayLine W) :
    dualLocalTwistorGenerator U C D E W = ⟨0,0,0,0⟩ := by
  rcases hW with ⟨hx,hy,hp⟩
  apply DualRayLocalTwistor.ext <;>
    simp [dualLocalTwistorGenerator, hx, hy, hp]

/-- Mirror quotient projection. -/
def dualQuotientProjection (W : DualRayLocalTwistor) : SturmState :=
  (W.xt,W.pt)

/-- Canonical aligned mirror lift. -/
def dualQuotientLift (u : SturmState) : DualRayLocalTwistor :=
  ⟨u.1,0,u.2,0⟩

/-- Projection after lift is identity. -/
theorem dualQuotientProjection_lift (u : SturmState) :
    dualQuotientProjection (dualQuotientLift u) = u := by
  rcases u with ⟨x,p⟩
  rfl

/-- Mirror quotient is surjective onto the rank-two Sturm carrier. -/
theorem dualQuotientProjection_surjective :
    Function.Surjective dualQuotientProjection := by
  intro u
  exact ⟨dualQuotientLift u, dualQuotientProjection_lift u⟩

/-- On aligned states, the mirror quotient kernel is exactly the mirror ray line. -/
theorem dual_aligned_projection_zero_iff_rayLine
    (W : DualRayLocalTwistor) (hW : DualRayAligned W) :
    dualQuotientProjection W = (0,0) ↔ InDualRayLine W := by
  constructor
  · intro h
    have hx : W.xt = 0 := congrArg Prod.fst h
    have hp : W.pt = 0 := congrArg Prod.snd h
    exact ⟨hx,hW,hp⟩
  · rintro ⟨hx,hy,hp⟩
    simp [dualQuotientProjection, hx, hp]

/-- Main mirror quotient theorem: the projected dual transport is exactly the SAME Sturm
generator as on the ordinary side after its constant phase normalization. -/
theorem dualLocalTwistor_projects_to_sturm
    (U C D E : ℂ) (W : DualRayLocalTwistor) (hW : DualRayAligned W) :
    dualQuotientProjection (dualLocalTwistorGenerator U C D E W) =
      sturmGenerator U (dualQuotientProjection W) := by
  rcases W with ⟨x,y,p,q⟩
  simp [DualRayAligned] at hW
  subst y
  simp [dualQuotientProjection, dualLocalTwistorGenerator, sturmGenerator]
  constructor <;> ring

/-- Common scaling on the mirror quotient. -/
def scaleSturmState (c : ℂ) (u : SturmState) : SturmState :=
  (c*u.1,c*u.2)

/-- Sturm dynamics is equivariant under common scaling. -/
theorem sturmGenerator_scale_equivariant
    (U c : ℂ) (u : SturmState) :
    sturmGenerator U (scaleSturmState c u) =
      scaleSturmState c (sturmGenerator U u) := by
  rcases u with ⟨x,p⟩
  simp [sturmGenerator, scaleSturmState]
  constructor <;> ring

/-- Ordinary quotient under anti-diagonal little group has weight `-1`, expressed in
Sturm coordinates. -/
def leftLittleGroup (a : ℂ) (ha : a ≠ 0) (u : SturmState) : SturmState :=
  scaleSturmState a⁻¹ u

/-- Mirror quotient has the opposite little-group weight `+1`. -/
def rightLittleGroup (a : ℂ) (ha : a ≠ 0) (u : SturmState) : SturmState :=
  scaleSturmState a u

/-- Both chiral quotient dynamics are little-group covariant. -/
theorem both_littleGroup_actions_commute_with_sturm
    (U a : ℂ) (ha : a ≠ 0) (uL uR : SturmState) :
    sturmGenerator U (leftLittleGroup a ha uL) =
        leftLittleGroup a ha (sturmGenerator U uL) ∧
    sturmGenerator U (rightLittleGroup a ha uR) =
        rightLittleGroup a ha (sturmGenerator U uR) := by
  constructor
  · exact sturmGenerator_scale_equivariant U a⁻¹ uL
  · exact sturmGenerator_scale_equivariant U a uR

/-- Concrete carrier for a spinor line tensored with a rank-two quotient state. -/
def spinorTensorState (lambda : CSpinor2) (u : SturmState) :
    ℂ × ℂ × ℂ × ℂ :=
  (lambda.1*u.1,lambda.1*u.2,lambda.2*u.1,lambda.2*u.2)

/-- Left neutralization: the actual lambda line has weight `+1`, cancelling the ordinary
quotient weight `-1`. -/
theorem left_tautological_tensor_is_littleGroup_neutral
    (a : ℂ) (ha : a ≠ 0) (lambda : CSpinor2) (u : SturmState) :
    spinorTensorState (scaleCSpinor a lambda) (leftLittleGroup a ha u) =
      spinorTensorState lambda u := by
  rcases lambda with ⟨l0,l1⟩
  rcases u with ⟨x,p⟩
  simp [spinorTensorState, scaleCSpinor, leftLittleGroup, scaleSturmState]
  have hai : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  apply Prod.ext
  · simp [hai]
    ring
  · apply Prod.ext
    · simp [hai]
      ring
    · apply Prod.ext <;> simp [hai] <;> ring

/-- Right neutralization: the actual lambdatilde line has weight `-1`, cancelling the
mirror quotient weight `+1`. -/
theorem right_tautological_tensor_is_littleGroup_neutral
    (a : ℂ) (ha : a ≠ 0) (lambdatilde : CSpinor2) (u : SturmState) :
    spinorTensorState (scaleCSpinor a⁻¹ lambdatilde) (rightLittleGroup a ha u) =
      spinorTensorState lambdatilde u := by
  rcases lambdatilde with ⟨l0,l1⟩
  rcases u with ⟨x,p⟩
  simp [spinorTensorState, scaleCSpinor, rightLittleGroup, scaleSturmState]
  have hai : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
  apply Prod.ext
  · simp [hai]
    ring
  · apply Prod.ext
    · simp [hai]
      ring
    · apply Prod.ext <;> simp [hai] <;> ring

/-- The two quotient characters are opposite: multiplying a left and right state gives a
little-group-neutral rank-four tensor without any additional line factor. -/
def quotientPairTensor (uL uR : SturmState) : ℂ × ℂ × ℂ × ℂ :=
  (uL.1*uR.1,uL.1*uR.2,uL.2*uR.1,uL.2*uR.2)

/-- Direct cancellation of opposite quotient weights. -/
theorem quotientPairTensor_littleGroup_neutral
    (a : ℂ) (ha : a ≠ 0) (uL uR : SturmState) :
    quotientPairTensor (leftLittleGroup a ha uL) (rightLittleGroup a ha uR) =
      quotientPairTensor uL uR := by
  rcases uL with ⟨x,p⟩
  rcases uR with ⟨y,q⟩
  simp [quotientPairTensor, leftLittleGroup, rightLittleGroup, scaleSturmState]
  have h1 : a⁻¹*a = 1 := inv_mul_cancel₀ ha
  apply Prod.ext
  · simp [h1]
    ring
  · apply Prod.ext
    · simp [h1]
      ring
    · apply Prod.ext <;> simp [h1] <;> ring

/-- Finite ambidextrous package: both chiral local-twistor quotients carry one and the same
Sturm generator, their little-group weights are opposite, and each becomes neutral after
tensoring with its ACTUAL tautological ray-spinor line. -/
theorem ambidextrous_ray_quotient_package
    (U a : ℂ) (ha : a ≠ 0)
    (lambda lambdatilde : CSpinor2) (uL uR : SturmState) :
    sturmGenerator U (leftLittleGroup a ha uL) =
        leftLittleGroup a ha (sturmGenerator U uL) ∧
    sturmGenerator U (rightLittleGroup a ha uR) =
        rightLittleGroup a ha (sturmGenerator U uR) ∧
    spinorTensorState (scaleCSpinor a lambda) (leftLittleGroup a ha uL) =
        spinorTensorState lambda uL ∧
    spinorTensorState (scaleCSpinor a⁻¹ lambdatilde) (rightLittleGroup a ha uR) =
        spinorTensorState lambdatilde uR := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sturmGenerator_scale_equivariant U a⁻¹ uL
  · exact sturmGenerator_scale_equivariant U a uR
  · exact left_tautological_tensor_is_littleGroup_neutral a ha lambda uL
  · exact right_tautological_tensor_is_littleGroup_neutral a ha lambdatilde uR

end GppAmbidextrousPenroseRayQuotients
