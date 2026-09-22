import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Lorentzian Hermitian 2x2 geometry and the discrete reflections

Represent a real Minkowski vector `x=(t,x,y,z)` by the Hermitian matrix

  X(x) = [[t+z, x-i y],
          [x+i y, t-z]].

Its determinant is the Minkowski quadratic form

  det X = t^2-x^2-y^2-z^2.

For a 2x2 matrix define the cofactor/adjugate

  X# = [[d,-b],[-c,a]].

On the Hermitian real slice this is exactly full spatial parity:

  X# = X(t,-x,-y,-z).

Negating the cofactor gives coordinate-time reflection:

  -X# = X(-t,x,y,z),

while central inversion gives

  -X = X(-t,-x,-y,-z).

Thus, on spacetime COORDINATES,

  P  = #,
  T0 = -#,
  PT = -id.

`T0` here is the linear coordinate reflection, NOT Wigner's antiunitary action on quantum
states or the transformation law of four-momentum under physical time reversal.

The key twistor bridge is

  X# = eps X^T eps^{-1},

with `eps=[[0,1],[-1,0]]`.  So the cofactor/parity map is ruling/factor exchange
(transpose) dressed by the canonical epsilon identifications between a spin space and its
dual.  This precisely explains why raw ruling exchange and Hodge/cofactor were distinct in
`InfinityRulingHodgeSeparation`: the missing operation is the epsilon dualization.
-/

namespace GppLorentzHermitianDiscreteGeometry

abbrev R4 := ℝ × ℝ × ℝ × ℝ
abbrev C2M := Matrix (Fin 2) (Fin 2) ℂ

/-- Minkowski vector as a Hermitian 2x2 matrix. -/
def hermitianVec (v : R4) : C2M :=
  let t := v.1
  let x := v.2.1
  let y := v.2.2.1
  let z := v.2.2.2
  !![((t+z : ℝ) : ℂ), ((x : ℂ) - Complex.I*(y : ℂ));
     ((x : ℂ) + Complex.I*(y : ℂ)), ((t-z : ℝ) : ℂ)]

/-- Explicit 2x2 determinant. -/
def detC2 (A : C2M) : ℂ := A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- Minkowski quadratic form in signature (+---). -/
def minkowskiQ (v : R4) : ℝ :=
  v.1^2 - v.2.1^2 - v.2.2.1^2 - v.2.2.2^2

/-- Determinant of the Hermitian matrix is exactly the Minkowski norm. -/
theorem det_hermitianVec (v : R4) :
    detC2 (hermitianVec v) = (minkowskiQ v : ℂ) := by
  rcases v with ⟨t,x,y,z⟩
  simp [detC2, hermitianVec, minkowskiQ, Complex.I_mul_I]
  ring

/-- 2x2 adjugate/cofactor. -/
def adj2 (A : C2M) : C2M :=
  !![A 1 1, -A 0 1;
     -A 1 0, A 0 0]

/-- Adjugation is an involution in dimension two. -/
theorem adj2_involution (A : C2M) : adj2 (adj2 A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj2]

/-- Spatial parity on real Minkowski coordinates. -/
def parity4 (v : R4) : R4 := (v.1,-v.2.1,-v.2.2.1,-v.2.2.2)

/-- Coordinate-time reflection. -/
def timeReflect4 (v : R4) : R4 := (-v.1,v.2.1,v.2.2.1,v.2.2.2)

/-- Full coordinate inversion. -/
def ptInvert4 (v : R4) : R4 := (-v.1,-v.2.1,-v.2.2.1,-v.2.2.2)

/-- On the Hermitian real slice, adjugation is exactly spatial parity. -/
theorem adj2_hermitianVec_eq_parity (v : R4) :
    adj2 (hermitianVec v) = hermitianVec (parity4 v) := by
  rcases v with ⟨t,x,y,z⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj2, hermitianVec, parity4]
  all_goals ring

/-- Minus adjugation is coordinate-time reflection. -/
theorem neg_adj2_hermitianVec_eq_timeReflect (v : R4) :
    -adj2 (hermitianVec v) = hermitianVec (timeReflect4 v) := by
  rcases v with ⟨t,x,y,z⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj2, hermitianVec, timeReflect4]
  all_goals ring

/-- Matrix negation is full coordinate PT inversion. -/
theorem neg_hermitianVec_eq_ptInvert (v : R4) :
    -hermitianVec v = hermitianVec (ptInvert4 v) := by
  rcases v with ⟨t,x,y,z⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianVec, ptInvert4]
  all_goals ring

/-- All three discrete coordinate maps preserve the Minkowski quadratic form. -/
theorem discrete_reflections_preserve_minkowskiQ (v : R4) :
    minkowskiQ (parity4 v) = minkowskiQ v ∧
    minkowskiQ (timeReflect4 v) = minkowskiQ v ∧
    minkowskiQ (ptInvert4 v) = minkowskiQ v := by
  rcases v with ⟨t,x,y,z⟩
  simp [minkowskiQ, parity4, timeReflect4, ptInvert4]
  ring

/-- Canonical epsilon spinor metric. -/
def eps2 : C2M :=
  !![0,1;
     -1,0]

/-- Its inverse is `-eps`. -/
theorem eps2_mul_neg_eps2_one :
    eps2 * (-eps2) = (1 : C2M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [eps2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Core identity: adjugation is epsilon-dressed transpose. -/
theorem adj2_eq_eps_transpose_neg_eps (A : C2M) :
    adj2 A = eps2 * A.transpose * (-eps2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj2, eps2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Therefore parity is factor/ruling exchange plus the two epsilon identifications. -/
theorem parity_is_epsilon_dressed_transpose (v : R4) :
    hermitianVec (parity4 v) = eps2 * (hermitianVec v).transpose * (-eps2) := by
  rw [← adj2_hermitianVec_eq_parity, adj2_eq_eps_transpose_neg_eps]

/-- P and coordinate-time reflection compose to full inversion. -/
theorem parity_timeReflect_eq_ptInvert (v : R4) :
    parity4 (timeReflect4 v) = ptInvert4 v := by
  rcases v with ⟨t,x,y,z⟩
  rfl

/-- The three coordinate reflections are involutions. -/
theorem parity4_sq (v : R4) : parity4 (parity4 v) = v := by
  rcases v with ⟨t,x,y,z⟩
  simp [parity4]

theorem timeReflect4_sq (v : R4) : timeReflect4 (timeReflect4 v) = v := by
  rcases v with ⟨t,x,y,z⟩
  simp [timeReflect4]

theorem ptInvert4_sq (v : R4) : ptInvert4 (ptInvert4 v) = v := by
  rcases v with ⟨t,x,y,z⟩
  simp [ptInvert4]

end GppLorentzHermitianDiscreteGeometry
