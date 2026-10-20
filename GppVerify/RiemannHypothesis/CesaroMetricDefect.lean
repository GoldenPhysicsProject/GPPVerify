import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Cesàro metric defect and matrix-mean controls (finite facts)

Sources: Astra, GPP-bridge `work/2026-10-20_astra_cesaro_metric_repair.md` and
`work/2026-10-20_astra_matrix_mean_positivity.md`. Formalized by Claude Code, with AI assistance,
for Daniel Toupin / Golden Physics Project.

* `defect_eigen_identity`: if `A v = λ v` then `v* (Aᴴ G + G A) v = 2 Re(λ) · v* G v`
  (no Hermitian hypothesis is needed for the identity), the step behind Astra's bound `2|Re λ| ≤ η_R`;
* `defect_eigen_bound`: if moreover `|v* D v| ≤ η · v* G v` with `v* G v > 0`, then `2|Re λ| ≤ η`;
* `jordan_defect`: for the Jordan block `A = [[0,1],[0,0]]` and any `G = diag(1, g)`,
  `Aᵀ G + G A = [[0,1],[1,0]]` (Astra's third control: zero eigenvalue, nonvanishing defect matrix);
* `norlund_not_symmetric`: the matrix Nörlund mean with weights `P₀ = diag(2,1)`, `P₁ = I` on the
  PSD inputs `X₀ = [[1,1],[1,1]]`, `X₁ = 0` gives `[[1/3,1/3],[1/2,1/2]]`, which is not symmetric;
* `scalar_mean_psd`: a nonnegative scalar combination of PSD quadratic forms is PSD.

Scope: finite linear algebra only. Nothing here bounds an arithmetic defect or concerns RH.
-/

namespace GppCesaroMetricDefect

open Matrix

variable {n : Type*} [Fintype n]

/-- Eigenvector identity for the invariance defect `Aᴴ G + G A`. -/
theorem defect_eigen_identity (A G : Matrix n n ℂ) (v : n → ℂ) (μ : ℂ)
    (hv : A *ᵥ v = μ • v) :
    star v ⬝ᵥ ((Aᴴ * G + G * A) *ᵥ v) = (μ + star μ) * (star v ⬝ᵥ (G *ᵥ v)) := by
  have h1 : star v ⬝ᵥ ((G * A) *ᵥ v) = μ * (star v ⬝ᵥ (G *ᵥ v)) := by
    rw [← mulVec_mulVec, hv]
    rw [mulVec_smul]
    rw [dotProduct_smul, smul_eq_mul]
  have h2 : star v ⬝ᵥ ((Aᴴ * G) *ᵥ v) = star μ * (star v ⬝ᵥ (G *ᵥ v)) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star, hv, star_smul,
      smul_dotProduct, smul_eq_mul]
  rw [add_mulVec, dotProduct_add, h1, h2]
  ring

/-- Astra's bound: a small relative defect forces the eigenvalue near the imaginary axis. -/
theorem defect_eigen_bound {μ : ℂ} {g d η : ℝ} (hg : 0 < g)
    (hid : (d : ℂ) = (μ + star μ) * g) (hdef : |d| ≤ η * g) :
    2 * |μ.re| ≤ η := by
  have hd : d = 2 * μ.re * g := by
    have := congrArg Complex.re hid
    simp [Complex.mul_re, Complex.add_re, Complex.conj_re] at this
    linarith
  rw [hd, abs_mul, abs_mul, abs_of_pos hg, abs_two] at hdef
  have := le_of_mul_le_mul_right (by linarith : 2 * |μ.re| * g ≤ η * g) hg
  linarith

/-- Jordan control: the defect matrix is `σ₁` for every `G = diag(1, g)`. -/
theorem jordan_defect (g : ℝ) :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * !![1, 0; 0, g] +
      !![1, 0; 0, g] * !![0, 1; 0, 0] = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Nörlund counterexample: positive-definite matrix weights on PSD inputs give a
non-symmetric mean. -/
theorem norlund_not_symmetric :
    let S : Matrix (Fin 2) (Fin 2) ℚ := !![3, 0; 0, 2]
    let Y := S⁻¹ * ((1 : Matrix (Fin 2) (Fin 2) ℚ) * !![1, 1; 1, 1] + !![2, 0; 0, 1] * 0)
    Y = !![1/3, 1/3; 1/2, 1/2] ∧ Yᵀ ≠ Y := by
  intro S Y
  have hS : S⁻¹ = !![1/3, 0; 0, 1/2] := by
    rw [Matrix.inv_eq_left_inv]
    ext i j; fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_two]
  have hY : Y = !![1/3, 1/3; 1/2, 1/2] := by
    simp only [Y, hS]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hY, ?_⟩
  rw [hY]
  intro h
  have := congrFun (congrFun h 0) 1
  norm_num at this

/-- A nonnegative scalar combination of PSD quadratic forms is PSD. -/
theorem scalar_mean_psd {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k)
    (q : ι → ℝ) (hq : ∀ k ∈ s, 0 ≤ q k) : 0 ≤ ∑ k ∈ s, w k * q k :=
  Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk) (hq k hk)

end GppCesaroMetricDefect
