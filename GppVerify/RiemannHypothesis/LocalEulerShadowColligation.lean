import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Local Euler-shadow factor as a 2x2 unitary colligation

For scalars `a,b` with `a^2+b^2=1`, consider

  S(a,b) = [[a,b],[b,-a]].

It is an involution, hence (over the reals) an orthogonal/unitary colligation.  With
internal block `A=a`, input/output blocks `B=C=b`, and feed-through `D=-a`, its
transfer function is

  D + z C (1-zA)^(-1) B = (z-a)/(1-az).

For the prime specialization `a=p^(-1/2)`, `b=sqrt(1-a^2)`, this is the local
Euler-shadow Blaschke factor from the August arithmetic-principal-series program.
The finite algebra is proved here; no infinite prime cascade or RH claim is made.
-/

namespace GppLocalEulerShadowColligation

open Matrix

/-- The generic real 2x2 scattering/colligation matrix. -/
def colligation (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, b; b, -a]

/-- If `a^2+b^2=1`, the colligation squares to the identity. -/
theorem colligation_sq_eq_one
    {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    colligation a b * colligation a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colligation, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    nlinarith

/-- The matrix is symmetric, so the preceding involution is also the orthogonality
identity `S * Sᵀ = I`. -/
theorem colligation_mul_transpose_eq_one
    {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    colligation a b * (colligation a b).transpose = 1 := by
  have hsymm : (colligation a b).transpose = colligation a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [colligation]
  rw [hsymm]
  exact colligation_sq_eq_one hab

/-- Scalar transfer function of the one-dimensional colligation. -/
noncomputable def transfer (a b z : ℂ) : ℂ :=
  -a + z * b * (1 - z * a)⁻¹ * b

/-- Exact Blaschke transfer algebra.  The only analytic hypothesis needed for this
pointwise identity is that the denominator does not vanish. -/
theorem transfer_eq_blaschke
    {a b z : ℂ}
    (hab : a ^ 2 + b ^ 2 = 1)
    (hden : 1 - a * z ≠ 0) :
    transfer a b z = (z - a) / (1 - a * z) := by
  unfold transfer
  have hcomm : 1 - z * a = 1 - a * z := by ring
  rw [hcomm]
  apply (eq_div_iff hden).2
  field_simp [hden]
  linear_combination z * hab

/-- On the unit circle, the real-parameter Blaschke factor has unit norm.  This is
proved algebraically from `|z|^2=1`, avoiding any appeal to Hardy-space machinery. -/
theorem blaschke_normSq_eq_one
    {a : ℝ} {z : ℂ}
    (hz : Complex.normSq z = 1)
    (hden : (1 : ℂ) - (a : ℂ) * z ≠ 0) :
    Complex.normSq ((z - (a : ℂ)) / (1 - (a : ℂ) * z)) = 1 := by
  rw [Complex.normSq_div]
  have hz' : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq, pow_two] using hz
  have hnum : Complex.normSq (z - (a : ℂ)) =
      Complex.normSq (1 - (a : ℂ) * z) := by
    simp [Complex.normSq, pow_two]
    ring_nf at hz' ⊢
    nlinarith [hz']
  rw [hnum]
  have hnormSq : Complex.normSq (1 - (a : ℂ) * z) ≠ 0 := by
    intro hzero
    exact hden (Complex.normSq_eq_zero.mp hzero)
  exact div_self hnormSq

end GppLocalEulerShadowColligation

#print axioms GppLocalEulerShadowColligation.colligation_sq_eq_one
#print axioms GppLocalEulerShadowColligation.colligation_mul_transpose_eq_one
#print axioms GppLocalEulerShadowColligation.transfer_eq_blaschke
#print axioms GppLocalEulerShadowColligation.blaschke_normSq_eq_one
