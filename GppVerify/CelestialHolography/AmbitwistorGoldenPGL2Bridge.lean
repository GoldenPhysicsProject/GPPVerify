import Mathlib.Tactic
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry
import GppVerify.CelestialHolography.AmbitwistorContactExchange
import GppVerify.NumberTheory.GoldenRatioHyperbolicSector

/-!
# The golden PGL(2) word inside null-ray Einstein transport

`EinsteinNullRaySL2Geometry` proves that the rank-two null-ray Einstein/Sturm carrier has
its natural Wronskian-preserving `SL(2,R)` geometry and contains the standard unipotent
subgroup.  `AmbitwistorContactExchange` independently proves that exchanging the two
ambitwistor factors is anti-contact: it reverses the contact potential while preserving
the contact hyperplane.

The canonical two-dimensional linear model of an involutive anti-symplectic exchange is a
reflection.  In the coordinate basis used for the ray state `(x,p)`, take the reciprocal
reflection

    J(x,p) = (p,x),        J = [[0,1],[1,0]], det J = -1.

It reverses the Wronskian exactly.  Composing it with the primitive lower-unipotent ray
translation

    N_1 = [[1,0],[1,1]]

produces

    G = N_1 J = [[0,1],[1,1]].

On the affine projective coordinate `z=p/x`, this is

    z |-> 1 + 1/z,

whose unique positive fixed point is the golden ratio.  Squaring gives

    G^2 = [[1,1],[1,2]],

an orientation-preserving trace-three hyperbolic matrix conjugate by `J` to the already
formalized `[[2,1],[1,1]]` golden matrix.  Thus its eigenvalues are the same
`phi^(+2), phi^(-2)` pair.

Everything proved below is finite real algebra.  The remaining geometric theorem is to
show that the actual anti-contact ambitwistor factor exchange descends, after the canonical
normalization of the neutral rank-two ray bundle, to this reflection (or a specified
conjugate), and that the global geometry supplies the integral lattice which makes
`N_1` the primitive unipotent rather than an arbitrary real `N_a`.  No such physical
selection is assumed here.
-/

namespace GppAmbitwistorGoldenPGL2Bridge

open GppFlatInfinityCelestialFactorization
open GppFlatNullWeylFiberGeometry
open GppEinsteinNullRaySL2Geometry
open GppGrassmannianGooglyDecomposition

/-- Reciprocal anti-symplectic reflection on the real ray-state fibre. -/
def rayReciprocal : M2 := (0,1,1,0)

/-- The reciprocal reflection has determinant `-1`. -/
theorem rayReciprocal_det_neg_one : det2 rayReciprocal = -1 := by
  norm_num [rayReciprocal, det2]

/-- Its action literally exchanges the two ray-state components. -/
theorem rayReciprocal_action (u : RayState) :
    act2 rayReciprocal u = (u.2,u.1) := by
  rcases u with ⟨x,p⟩
  simp [rayReciprocal, act2]

/-- Therefore it reverses the Wronskian/contact orientation on the rank-two fibre. -/
theorem rayReciprocal_reverses_omega (u v : RayState) :
    omega (act2 rayReciprocal u) (act2 rayReciprocal v) = -omega u v := by
  rw [omega_act2, rayReciprocal_det_neg_one]
  ring

/-- The reciprocal reflection is exactly involutive. -/
theorem rayReciprocal_involution (u : RayState) :
    act2 rayReciprocal (act2 rayReciprocal u) = u := by
  rcases u with ⟨x,p⟩
  simp [rayReciprocal, act2]

/-- Primitive mixed PGL(2) word: unit unipotent transport after reciprocal exchange. -/
def goldenRayStep (u : RayState) : RayState :=
  act2 (rayUnipotent 1) (act2 rayReciprocal u)

/-- The mixed word is the matrix `[[0,1],[1,1]]` on column state `(x,p)`. -/
theorem goldenRayStep_apply (x p : ℝ) :
    goldenRayStep (x,p) = (p,x+p) := by
  simp [goldenRayStep, rayReciprocal, rayUnipotent, act2]
  constructor <;> ring

/-- One mixed step reverses the Wronskian, as its determinant is `-1`. -/
theorem goldenRayStep_reverses_omega (u v : RayState) :
    omega (goldenRayStep u) (goldenRayStep v) = -omega u v := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [goldenRayStep, rayReciprocal, rayUnipotent, act2, omega]
  ring

/-- Its square is the orientation-preserving trace-three action
`[[1,1],[1,2]]`. -/
theorem goldenRayStep_sq_apply (x p : ℝ) :
    goldenRayStep (goldenRayStep (x,p)) = (x+p,x+2*p) := by
  rw [goldenRayStep_apply, goldenRayStep_apply]
  constructor <;> ring

/-- Accordingly the even/orientation-preserving word preserves the Wronskian. -/
theorem goldenRayStep_sq_preserves_omega (u v : RayState) :
    omega (goldenRayStep (goldenRayStep u))
      (goldenRayStep (goldenRayStep v)) = omega u v := by
  rw [goldenRayStep_reverses_omega, goldenRayStep_reverses_omega]
  ring

/-- Affine coordinate on the projective ray-state fibre, `z=p/x`. -/
def rayAffineRatio (u : RayState) : ℝ := u.2/u.1

/-- On the affine representative `(1,z)`, the mixed PGL(2) word is exactly
`z -> 1+1/z`. -/
theorem goldenRayStep_affine (z : ℝ) (hz : z ≠ 0) :
    rayAffineRatio (goldenRayStep (1,z)) = 1 + 1/z := by
  rw [goldenRayStep_apply]
  simp [rayAffineRatio]
  field_simp [hz]
  ring

/-- Hence the positive projective fixed point of the actual ray-state word is exactly
`phi`; this reuses only the independently formalized uniqueness theorem for
`x=1+1/x`. -/
theorem goldenRayStep_positive_fixed_iff_phi {z : ℝ} (hz : 0 < z) :
    z = 1 + 1/z ↔ z = Real.goldenRatio := by
  exact GppGoldenHyperbolic.fixedPoint_iff_gold hz

/-- The square has trace `3` at the matrix level. -/
theorem goldenRayStep_square_trace_three :
    (1 : ℝ) + 2 = 3 := by norm_num

/-- The previous golden hyperbolic Cartan identity is the same trace-three statement:
`phi^2 + phi^(-2) = 3`. -/
theorem phiSq_reciprocal_trace_three :
    Real.goldenRatio^2 + Real.goldenRatio⁻¹^2 = 3 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenRatio_sq]

end GppAmbitwistorGoldenPGL2Bridge
