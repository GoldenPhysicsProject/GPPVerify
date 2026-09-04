import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Complex Grassmannian differential and its four modes

This is the physically relevant complex version of the big-cell calculation.
All identities are polynomial/rational identities over `ℂ`.
-/

namespace GppGrassmannianComplexDifferential

/-- Big-cell determinant. -/
def D (a b c d : ℂ) : ℂ := a * d - b * c

/-- The epsilon-duality chart map. -/
noncomputable def tau (a b c d : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (-b / D a b c d, a / D a b c d, -d / D a b c d, c / D a b c d)

/-- The determinant is inverted by one chart duality. -/
theorem tau_det (a b c d : ℂ) (hD : D a b c d ≠ 0) :
    D (-b / D a b c d) (a / D a b c d)
      (-d / D a b c d) (c / D a b c d) = 1 / D a b c d := by
  simp [D]
  field_simp [D] <;> ring

/-- Exact nonlinear order-four core over the complex big cell: `tau²=-id`. -/
theorem tau_tau_eq_neg (a b c d : ℂ) (hD : D a b c d ≠ 0) :
    tau (-b / D a b c d) (a / D a b c d)
      (-d / D a b c d) (c / D a b c d) = (-a,-b,-c,-d) := by
  have hinv : (1 / D a b c d : ℂ) ≠ 0 := one_div_ne_zero hD
  simp only [tau]
  rw [tau_det a b c d hD]
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp [D] <;> ring

/-- Jacobian numerator, so the actual Jacobian is `N/D²`. -/
def N (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![b * d, -(a * d), -(b ^ 2), a * b;
     -(b * c), a * c, a * b, -(a ^ 2);
     d ^ 2, -(c * d), -(b * d), b * c;
     -(c * d), c ^ 2, a * d, -(a * c)]

/-- Coordinate change `X -> A X`. -/
def P (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![a, 0, b, 0;
     0, a, 0, b;
     c, 0, d, 0;
     0, c, 0, d]

/-- Denominator-cleared inverse of `P`. -/
def Q (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![d, 0, -b, 0;
     0, d, 0, -b;
     -c, 0, a, 0;
     0, -c, 0, a]

/-- Point-independent tangent operator. -/
def L : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -1, 0, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, 0, 1, 0]

theorem L_four : L * L * (L * L) = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [L, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    norm_num

theorem QP (a b c d : ℂ) :
    Q a b c d * P a b c d = D a b c d • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [Q,P,D,Matrix.mul_apply,Fin.sum_univ_four,Matrix.one_apply] <;>
    ring

theorem PQ (a b c d : ℂ) :
    P a b c d * Q a b c d = D a b c d • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [Q,P,D,Matrix.mul_apply,Fin.sum_univ_four,Matrix.one_apply] <;>
    ring

/-- Exact universal differential intertwining identity. -/
theorem NP_eq_DPL (a b c d : ℂ) :
    N a b c d * P a b c d = D a b c d • (P a b c d * L) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [N,P,L,D,Matrix.mul_apply,Fin.sum_univ_four] <;>
    ring

/-- `P` is injective on the big cell, proved directly from the adjugate identity. -/
theorem P_mulVec_injective (a b c d : ℂ) (hD : D a b c d ≠ 0)
    {x y : Fin 4 → ℂ} (h : P a b c d *ᵥ x = P a b c d *ᵥ y) : x = y := by
  have hQ := congrArg (fun v => Q a b c d *ᵥ v) h
  simp only [← Matrix.mulVec_mulVec, QP] at hQ
  ext i
  have hi := congrFun hQ i
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply] at hi
  exact mul_left_cancel₀ hD hi

/-- The four universal eigenvectors. -/
def vOne : Fin 4 → ℂ := ![1,-1,1,1]
def vNegOne : Fin 4 → ℂ := ![1,1,-1,1]
def vI : Fin 4 → ℂ := ![1,-Complex.I,-Complex.I,-1]
def vNegI : Fin 4 → ℂ := ![1,Complex.I,Complex.I,-1]

theorem L_vOne : L *ᵥ vOne = (1 : ℂ) • vOne := by
  ext i; fin_cases i <;> norm_num [L,vOne,Matrix.mulVec,Fin.sum_univ_four]
theorem L_vNegOne : L *ᵥ vNegOne = (-1 : ℂ) • vNegOne := by
  ext i; fin_cases i <;> norm_num [L,vNegOne,Matrix.mulVec,Fin.sum_univ_four]
theorem L_vI : L *ᵥ vI = Complex.I • vI := by
  ext i; fin_cases i <;> simp [L,vI,Matrix.mulVec,Fin.sum_univ_four,Complex.I_mul_I]
theorem L_vNegI : L *ᵥ vNegI = (-Complex.I) • vNegI := by
  ext i; fin_cases i <;> simp [L,vNegI,Matrix.mulVec,Fin.sum_univ_four,Complex.I_mul_I]

/-- Transport of any universal eigenmode through the physical tangent-coordinate map. -/
theorem transport_mode (a b c d ζ : ℂ) (v : Fin 4 → ℂ)
    (hLv : L *ᵥ v = ζ • v) :
    N a b c d *ᵥ (P a b c d *ᵥ v)
      = (D a b c d * ζ) • (P a b c d *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, NP_eq_DPL]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_mulVec, hLv, Matrix.mulVec_smul]
  ext i
  simp
  ring

/-- The normalized Jacobian acting on a tangent vector. -/
def Japply (a b c d : ℂ) (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  (D a b c d)⁻¹ ^ 2 • (N a b c d *ᵥ v)

/-- A transported `L`-eigenmode has actual Jacobian eigenvalue `ζ/D`. -/
theorem Japply_transport_mode (a b c d ζ : ℂ) (v : Fin 4 → ℂ)
    (hD : D a b c d ≠ 0) (hLv : L *ᵥ v = ζ • v) :
    Japply a b c d (P a b c d *ᵥ v)
      = (ζ / D a b c d) • (P a b c d *ᵥ v) := by
  rw [Japply, transport_mode a b c d ζ v hLv]
  ext i
  simp [div_eq_mul_inv]
  field_simp [hD]
  ring

end GppGrassmannianComplexDifferential
