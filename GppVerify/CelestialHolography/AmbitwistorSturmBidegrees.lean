import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import GppVerify.CelestialHolography.AmbidextrousPenroseRayQuotients
import GppVerify.NumberTheory.GoldenRatioHyperbolicSector

/-!
# Ambitwistor bidegrees of the Penrose raywise Sturm systems

The anti-diagonal little-group character of a whole ray quotient does not determine its
full projective ambitwistor homogeneity.  The reason is that a Sturm state consists of a
field value and its derivative along the null ray, and those two components have different
bidegrees under independent rescalings of the two ray spinors.

Let

  lambda -> r lambda,
  lambdatilde -> s lambdatilde.

Then the null tangent `k=lambda lambdatilde` has bidegree `(1,1)`, so differentiation
along the ray has the same bidegree.  The null Schouten contraction

  U=P(k,k)

has bidegree `(2,2)`.

For the ordinary/left Penrose quotient,

  omega = x lambda,
  p = lambdatilde.pi,

so

  x -> r^{-1} x,       weight (-1,0),
  p -> s p,            weight ( 0,1).

Thus `p=D_k x` has exactly the expected weight

  (-1,0) + (1,1) = (0,1),

and both terms in the Sturm equation

  D_k^2 x + U x = 0

have weight `(1,2)`.

For the mirror/dual quotient the bidegrees are reversed:

  xt -> s^{-1} xt,     weight (0,-1),
  pt -> r pt,          weight (1, 0),

and its second-order equation has weight `(2,1)`.

This module proves both the integer weight bookkeeping and the exact finite covariance of
the two Sturm generators under independent complex rescalings.  It gives a precise reason
the rank-two state is a weighted first-jet/projective-connection system rather than two
copies of one `O(p,q)` line bundle.
-/

namespace GppAmbitwistorSturmBidegrees

open Complex
open GppAmbidextrousPenroseRayQuotients

abbrev BiWeight := ℤ × ℤ

/-- Add bidegrees. -/
def addWeight (a b : BiWeight) : BiWeight := (a.1+b.1,a.2+b.2)

/-- Integer bidegrees of the geometric ingredients. -/
def tangentWeight : BiWeight := (1,1)
def curvatureWeight : BiWeight := (2,2)
def leftFieldWeight : BiWeight := (-1,0)
def leftMomentumWeight : BiWeight := (0,1)
def rightFieldWeight : BiWeight := (0,-1)
def rightMomentumWeight : BiWeight := (1,0)
def leftEquationWeight : BiWeight := (1,2)
def rightEquationWeight : BiWeight := (2,1)

/-- One null derivative sends the left field weight to the left momentum weight. -/
theorem left_derivative_weight :
    addWeight leftFieldWeight tangentWeight = leftMomentumWeight := by
  norm_num [addWeight, leftFieldWeight, tangentWeight, leftMomentumWeight]

/-- Two null derivatives of the left field have the same weight as `U*x`. -/
theorem left_second_order_weight :
    addWeight (addWeight leftFieldWeight tangentWeight) tangentWeight =
      leftEquationWeight ∧
    addWeight curvatureWeight leftFieldWeight = leftEquationWeight := by
  constructor <;>
    norm_num [addWeight, leftFieldWeight, tangentWeight, curvatureWeight,
      leftEquationWeight]

/-- Mirror statement for the dual/right field. -/
theorem right_derivative_weight :
    addWeight rightFieldWeight tangentWeight = rightMomentumWeight := by
  norm_num [addWeight, rightFieldWeight, tangentWeight, rightMomentumWeight]

/-- Two null derivatives of the mirror field have the same weight as `U*xt`. -/
theorem right_second_order_weight :
    addWeight (addWeight rightFieldWeight tangentWeight) tangentWeight =
      rightEquationWeight ∧
    addWeight curvatureWeight rightFieldWeight = rightEquationWeight := by
  constructor <;>
    norm_num [addWeight, rightFieldWeight, tangentWeight, curvatureWeight,
      rightEquationWeight]

/-- Independent projective rescaling of a left Sturm state. -/
def leftBiScale (r s : ℂ) (u : SturmState) : SturmState :=
  (r⁻¹*u.1,s*u.2)

/-- Independent projective rescaling of a mirror/right Sturm state. -/
def rightBiScale (r s : ℂ) (u : SturmState) : SturmState :=
  (s⁻¹*u.1,r*u.2)

/-- Null tangent/derivative scaling factor. -/
def derivativeScale (r s : ℂ) : ℂ := r*s

/-- Null Schouten/Sturm-potential scaling. -/
def curvatureScale (r s U : ℂ) : ℂ := (r*s)^2 * U

/-- Exact covariance of the left weighted first-jet system:
`G_{U'} S = (rs) S G_U`. -/
theorem left_sturm_biscale_covariant
    (r s U : ℂ) (u : SturmState) :
    sturmGenerator (curvatureScale r s U) (leftBiScale r s u) =
      scaleSturmState (derivativeScale r s)
        (leftBiScale r s (sturmGenerator U u)) := by
  rcases u with ⟨x,p⟩
  simp [sturmGenerator, curvatureScale, derivativeScale,
    leftBiScale, scaleSturmState]
  constructor <;> ring

/-- Mirror covariance with the bidegrees reversed. -/
theorem right_sturm_biscale_covariant
    (r s U : ℂ) (u : SturmState) :
    sturmGenerator (curvatureScale r s U) (rightBiScale r s u) =
      scaleSturmState (derivativeScale r s)
        (rightBiScale r s (sturmGenerator U u)) := by
  rcases u with ⟨x,p⟩
  simp [sturmGenerator, curvatureScale, derivativeScale,
    rightBiScale, scaleSturmState]
  constructor <;> ring

/-- Anti-diagonal scaling makes both components of the left jet carry the common
little-group character `a^{-1}`. -/
theorem left_antidiagonal_is_common_weight
    (a : ℂ) (ha : a ≠ 0) (u : SturmState) :
    leftBiScale a a⁻¹ u = scaleSturmState a⁻¹ u := by
  rcases u with ⟨x,p⟩
  simp [leftBiScale, scaleSturmState]

/-- The mirror jet carries the opposite common anti-diagonal character `a`. -/
theorem right_antidiagonal_is_common_weight
    (a : ℂ) (ha : a ≠ 0) (u : SturmState) :
    rightBiScale a a⁻¹ u = scaleSturmState a u := by
  rcases u with ⟨x,p⟩
  simp [rightBiScale, scaleSturmState, ha]

/-- Under simultaneous scaling `r=s=b`, the left jet transforms by the Cartan matrix
`diag(b^{-1},b)`. -/
def leftDiagonalScale (b : ℂ) (u : SturmState) : SturmState :=
  leftBiScale b b u

/-- The mirror jet has the same Cartan scaling with the two chiral labels exchanged;
for `r=s=b` the explicit state action is again `diag(b^{-1},b)`. -/
def rightDiagonalScale (b : ℂ) (u : SturmState) : SturmState :=
  rightBiScale b b u

/-- Both chiral jet presentations agree under common diagonal ray scaling. -/
theorem diagonal_scales_agree (b : ℂ) (u : SturmState) :
    leftDiagonalScale b u = rightDiagonalScale b u := by
  rfl

/-- Wronskian on the two-component Sturm carrier. -/
def wronskian (u v : SturmState) : ℂ := u.1*v.2-u.2*v.1

/-- Common diagonal ray scaling preserves the Wronskian exactly: the weighted first-jet
change is an `SL(2)` Cartan action whenever `b` is nonzero. -/
theorem diagonal_scale_preserves_wronskian
    (b : ℂ) (hb : b ≠ 0) (u v : SturmState) :
    wronskian (leftDiagonalScale b u) (leftDiagonalScale b v) = wronskian u v := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [wronskian, leftDiagonalScale, leftBiScale]
  have hbi : b⁻¹*b = 1 := inv_mul_cancel₀ hb
  ring_nf
  simp [hbi]

/-- Under diagonal scaling the curvature potential has weight four and the derivative has
weight two, exactly matching null tangent rescaling. -/
theorem diagonal_geometric_weights (b U : ℂ) :
    derivativeScale b b = b^2 ∧ curvatureScale b b U = b^4*U := by
  constructor
  · simp [derivativeScale, pow_two]
  · simp [curvatureScale]
    ring

/-! ## A finite golden/modular bridge inside the Sturm carrier

The earlier `GoldenRatioHyperbolicSector` theorem found the golden ratio from the modular
word `T J`, where `J : z ↦ 1/z` and `T : z ↦ z+1`.  The present rank-two Sturm carrier
contains exact linear representatives of those same two elementary operations:

* at zero potential, affine free propagation is the unipotent shear
  `(x,p) ↦ (x+t p,p)`;
* component exchange `(x,p) ↦ (p,x)` induces reciprocal inversion on the projective ratio
  `z=x/p`.

At primitive parameter `t=1`, their composite is therefore

    (x,p) ↦ (x+p,x),

represented by `[[1,1],[1,0]]`.  Its square is the orientation-preserving hyperbolic matrix
`[[2,1],[1,1]]` already formalized in `GoldenRatioHyperbolicSector`, and the induced affine
map is `z ↦ 1+1/z`, whose unique positive fixed point is `φ`.

The statements below are finite algebra.  They do **not** identify component exchange with
physical celestial shadow/factor exchange, and they do **not** assert that the physical
normalization selects unit affine propagation.  Those are precisely the geometric bridge
questions still to be proved before `φ` can be called a physical constant of the framework.
-/

/-- Affine/free Sturm shear.  For the flat equation `x''=0`, this is the exact finite
propagation law over affine parameter `t`. -/
def freeShear (t : ℂ) (u : SturmState) : SturmState :=
  (u.1 + t*u.2, u.2)

/-- The free shears form the additive one-parameter subgroup. -/
theorem freeShear_add (s t : ℂ) (u : SturmState) :
    freeShear (s+t) u = freeShear s (freeShear t u) := by
  rcases u with ⟨x,p⟩
  simp [freeShear]
  constructor <;> ring

/-- Free propagation preserves the Sturm Wronskian exactly. -/
theorem freeShear_preserves_wronskian (t : ℂ) (u v : SturmState) :
    wronskian (freeShear t u) (freeShear t v) = wronskian u v := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [wronskian, freeShear]
  ring

/-- Reciprocal component exchange.  On the affine projective coordinate `z=x/p`, this is
`z ↦ 1/z` whenever both ratios are defined. -/
def reciprocalSwap (u : SturmState) : SturmState := (u.2,u.1)

/-- Reciprocal exchange is an involution. -/
theorem reciprocalSwap_involution (u : SturmState) :
    reciprocalSwap (reciprocalSwap u) = u := by
  rcases u with ⟨x,p⟩
  rfl

/-- Reciprocal exchange reverses the Wronskian orientation. -/
theorem reciprocalSwap_reverses_wronskian (u v : SturmState) :
    wronskian (reciprocalSwap u) (reciprocalSwap v) = -wronskian u v := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [wronskian, reciprocalSwap]
  ring

/-- The epsilon quarter-turn `[[0,1],[-1,0]]`, the same finite `Z4` matrix appearing in
the big-cell orientation map `tau(A)=A epsilon/det(A)`. -/
def epsilonTurn (u : SturmState) : SturmState := (u.2,-u.1)

/-- The epsilon turn squares to central sign. -/
theorem epsilonTurn_sq (u : SturmState) :
    epsilonTurn (epsilonTurn u) = scaleSturmState (-1) u := by
  rcases u with ⟨x,p⟩
  simp [epsilonTurn, scaleSturmState]

/-- Hence the epsilon turn has projective order two and vector-level order four. -/
theorem epsilonTurn_four (u : SturmState) :
    epsilonTurn (epsilonTurn (epsilonTurn (epsilonTurn u))) = u := by
  rcases u with ⟨x,p⟩
  simp [epsilonTurn]

/-- Reflection of the momentum component. -/
def momentumReflection (u : SturmState) : SturmState := (u.1,-u.2)

/-- The reciprocal involution is reflection composed with the epsilon quarter-turn:
`diag(1,-1) * epsilon = [[0,1],[1,0]]`. -/
theorem reflection_epsilon_eq_reciprocal (u : SturmState) :
    momentumReflection (epsilonTurn u) = reciprocalSwap u := by
  rcases u with ⟨x,p⟩
  simp [momentumReflection, epsilonTurn, reciprocalSwap]

/-- One primitive orientation-reversing modular/Sturm step: free unit propagation after
reciprocal exchange. -/
def goldenStep (u : SturmState) : SturmState :=
  freeShear 1 (reciprocalSwap u)

/-- The primitive step is exactly the matrix `[[1,1],[1,0]]`. -/
theorem goldenStep_apply (x p : ℂ) :
    goldenStep (x,p) = (x+p,x) := by
  simp [goldenStep, freeShear, reciprocalSwap]
  constructor <;> ring

/-- Squaring gives the orientation-preserving matrix `[[2,1],[1,1]]`. -/
theorem goldenStep_sq_apply (x p : ℂ) :
    goldenStep (goldenStep (x,p)) = (2*x+p,x+p) := by
  rw [goldenStep_apply, goldenStep_apply]
  constructor <;> ring

/-- One golden step reverses the Wronskian, as expected from determinant `-1`. -/
theorem goldenStep_reverses_wronskian (u v : SturmState) :
    wronskian (goldenStep u) (goldenStep v) = -wronskian u v := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [goldenStep, freeShear, reciprocalSwap, wronskian]
  ring

/-- Two golden steps preserve the Wronskian, hence lie in the orientation-preserving
`SL(2)` sector. -/
theorem goldenStep_sq_preserves_wronskian (u v : SturmState) :
    wronskian (goldenStep (goldenStep u)) (goldenStep (goldenStep v)) = wronskian u v := by
  rw [goldenStep_reverses_wronskian, goldenStep_reverses_wronskian]
  ring

/-- On the affine chart `(z,1)`, the primitive Sturm step induces the modular map
`z ↦ 1+1/z`. -/
theorem goldenStep_projective_ratio (z : ℂ) (hz : z ≠ 0) :
    (goldenStep (z,1)).1 / (goldenStep (z,1)).2 = 1 + 1/z := by
  rw [goldenStep_apply]
  simp
  field_simp [hz]
  ring

/-- Real affine form of the projective map induced by `goldenStep`. -/
def goldenMobius (x : ℝ) : ℝ := 1 + 1/x

/-- Reappearance of the previous golden-ratio theorem in the present Sturm carrier: the
induced positive projective fixed point is exactly `φ`. -/
theorem goldenMobius_fixed_iff_gold {x : ℝ} (hx : 0 < x) :
    x = goldenMobius x ↔ x = Real.goldenRatio := by
  simpa [goldenMobius] using
    (GppGoldenHyperbolic.fixedPoint_iff_gold (x := x) hx)

/-- At the previous golden hyperbolic value, the reciprocal Cartan trace is exactly `3`:
`φ² + φ⁻² = 3`.  This is the trace of the minimal orientation-preserving hyperbolic
`SL(2,Z)` element formalized in `GoldenRatioHyperbolicSector`. -/
theorem golden_cartan_trace :
    Real.goldenRatio^2 + Real.goldenRatio⁻¹^2 = 3 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenRatio_sq]

end GppAmbitwistorSturmBidegrees
