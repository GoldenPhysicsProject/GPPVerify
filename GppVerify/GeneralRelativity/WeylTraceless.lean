import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The Weyl tensor is traceless (retires `GppRigidity.open_weyl_traceless`)

For a symmetric metric `g` with symmetric inverse `g⁻¹` (`g⁻¹ g = 1`) on a `d`-dimensional index
set, `d ≥ 3`, and **any** 4-index array `R`, define `Ric_{μν} = g^{αβ} R_{αμβν}`,
`R = g^{μν} Ric_{μν}` and

  `C_{αμβν} = R_{αμβν} − (g_{αβ}Ric_{μν} − g_{αν}Ric_{μβ} − g_{μβ}Ric_{αν} + g_{μν}Ric_{αβ})/(d−2)
             + R (g_{αβ}g_{μν} − g_{αν}g_{μβ})/((d−1)(d−2))`.

Then `g^{αβ} C_{αμβν} = 0` (`weyl_traceless`). No curvature symmetries are needed: the
contraction kills the two correction terms against the Ricci contraction exactly. Specialized to
`d = 4` with the Minkowski metric (`weyl_traceless_minkowski`), which also shows the hypotheses
are satisfiable. Pointwise linear algebra only: no manifold, connection or derivative.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

namespace GppWeylTensor
open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ricci contraction `Ric_{μν} = g^{αβ} R_{αμβν}`. -/
def ricci (gi : Matrix ι ι ℝ) (R : ι → ι → ι → ι → ℝ) (μ ν : ι) : ℝ :=
  ∑ α, ∑ β, gi α β * R α μ β ν

/-- Scalar curvature `R = g^{μν} Ric_{μν}`. -/
def scalarCurv (gi : Matrix ι ι ℝ) (R : ι → ι → ι → ι → ℝ) : ℝ :=
  ∑ μ, ∑ ν, gi μ ν * ricci gi R μ ν

/-- The Weyl tensor in dimension `d = card ι`. -/
noncomputable def weyl (g gi : Matrix ι ι ℝ) (R : ι → ι → ι → ι → ℝ) (α μ β ν : ι) : ℝ :=
  R α μ β ν
    - (1 / ((Fintype.card ι : ℝ) - 2)) * (g α β * ricci gi R μ ν - g α ν * ricci gi R μ β
        - g μ β * ricci gi R α ν + g μ ν * ricci gi R α β)
    + scalarCurv gi R / (((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2))
        * (g α β * g μ ν - g α ν * g μ β)

section contractions
variable (g gi : Matrix ι ι ℝ)

theorem contract_self (hg : gᵀ = g) (hinv : gi * g = 1) :
    ∑ α, ∑ β, gi α β * g α β = (Fintype.card ι : ℝ) := by
  have h : (gi * gᵀ).trace = (Fintype.card ι : ℝ) := by rw [hg, hinv, trace_one]
  rw [← h, trace]
  simp [Matrix.mul_apply, Matrix.transpose_apply]

theorem kron_left (hgi : giᵀ = gi) (hinv : gi * g = 1) (β ν : ι) :
    ∑ α, gi α β * g α ν = if β = ν then 1 else 0 := by
  have h := congrFun (congrFun hinv β) ν
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  refine sum_congr rfl fun α _ => ?_
  have := congrFun (congrFun hgi β) α
  simp only [transpose_apply] at this
  rw [this]

theorem kron_right (hg : gᵀ = g) (hinv : gi * g = 1) (α μ : ι) :
    ∑ β, gi α β * g μ β = if α = μ then 1 else 0 := by
  have h := congrFun (congrFun hinv α) μ
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  refine sum_congr rfl fun β _ => ?_
  have := congrFun (congrFun hg β) μ
  simp only [transpose_apply] at this
  rw [this]

theorem S3 (hgi : giᵀ = gi) (hinv : gi * g = 1) (X : ι → ℝ) (ν : ι) :
    ∑ α, ∑ β, gi α β * g α ν * X β = X ν := by
  rw [sum_comm]
  simp_rw [← sum_mul, kron_left g gi hgi hinv]
  simp

theorem S4 (hg : gᵀ = g) (hinv : gi * g = 1) (X : ι → ℝ) (μ : ι) :
    ∑ α, ∑ β, gi α β * g μ β * X α = X μ := by
  simp_rw [← sum_mul, kron_right g gi hg hinv]
  simp

end contractions

/-- **The Weyl tensor is traceless**: `g^{αβ} C_{αμβν} = 0`, for any symmetric metric with
symmetric inverse, in any dimension `d ≥ 3`, and for any 4-index array `R`. -/
theorem weyl_traceless (g gi : Matrix ι ι ℝ) (hg : gᵀ = g) (hgi : giᵀ = gi)
    (hinv : gi * g = 1) (hd : 3 ≤ Fintype.card ι) (R : ι → ι → ι → ι → ℝ) (μ ν : ι) :
    ∑ α, ∑ β, gi α β * weyl g gi R α μ β ν = 0 := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd'
  set c1 : ℝ := 1 / (d - 2)
  set c2 : ℝ := scalarCurv gi R / ((d - 1) * (d - 2))
  set Ric := ricci gi R
  have expand : ∀ α β, gi α β * weyl g gi R α μ β ν
      = gi α β * R α μ β ν
        - c1 * (gi α β * g α β * Ric μ ν - gi α β * g α ν * Ric μ β
          - gi α β * g μ β * Ric α ν + gi α β * g μ ν * Ric α β)
        + c2 * (gi α β * g α β * g μ ν - gi α β * g α ν * g μ β) := by
    intro α β
    simp only [weyl, c1, c2, Ric, d]
    ring
  simp_rw [expand]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have e1 : ∑ α, ∑ β, gi α β * R α μ β ν = Ric μ ν := rfl
  have e2 : ∑ α, ∑ β, gi α β * g α β * Ric μ ν = d * Ric μ ν := by
    simp_rw [← sum_mul]; rw [contract_self g gi hg hinv]
  have e3 : ∑ α, ∑ β, gi α β * g α ν * Ric μ β = Ric μ ν :=
    S3 g gi hgi hinv (fun β => Ric μ β) ν
  have e4 : ∑ α, ∑ β, gi α β * g μ β * Ric α ν = Ric μ ν :=
    S4 g gi hg hinv (fun α => Ric α ν) μ
  have e5 : ∑ α, ∑ β, gi α β * g μ ν * Ric α β = g μ ν * scalarCurv gi R := by
    simp only [scalarCurv]
    rw [mul_sum]
    refine sum_congr rfl fun α _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun β _ => ?_
    ring
  have e6 : ∑ α, ∑ β, gi α β * g α β * g μ ν = d * g μ ν := by
    simp_rw [← sum_mul]; rw [contract_self g gi hg hinv]
  have e7 : ∑ α, ∑ β, gi α β * g α ν * g μ β = g μ ν :=
    S3 g gi hgi hinv (fun β => g μ β) ν
  rw [e1, e2, e3, e4, e5, e6, e7]
  have h2 : d - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by rw [hd']; exact_mod_cast hd
    linarith
  have h1 : d - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by rw [hd']; exact_mod_cast hd
    linarith
  simp only [c1, c2]
  field_simp
  ring

/-- The Minkowski metric `diag(1, −1, −1, −1)`; it is its own inverse. -/
def minkowski : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

theorem minkowski_transpose : minkowskiᵀ = minkowski := by
  simp [minkowski]

theorem minkowski_mul_self : minkowski * minkowski = 1 := by
  rw [minkowski, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- **In 4D Minkowski signature, the Weyl tensor is traceless.** -/
theorem weyl_traceless_minkowski (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    ∑ α, ∑ β, minkowski α β * weyl minkowski minkowski R α μ β ν = 0 :=
  weyl_traceless minkowski minkowski minkowski_transpose minkowski_transpose minkowski_mul_self
    (by simp) R μ ν

end GppWeylTensor

#print axioms GppWeylTensor.weyl_traceless
