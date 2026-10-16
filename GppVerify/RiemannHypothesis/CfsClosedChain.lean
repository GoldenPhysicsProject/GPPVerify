import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Closed-chain algebra behind the causal-fermion bridge (finite, exact)

Source: Codex/GPT's causal-fermion notes of 2026-10-16 (`work/codex/2026-10-16_causal_fermion_closed_chain_prime_kick_exact_bridge.md`,
`..._mirrored_CFS_spin_two_full_squarefree_prime_curvature_theorem.md`), independently re-derived by
Grok S42 (sympy + mpmath). Everything below is finite linear algebra or elementary real/complex
analysis; **none of it involves the zeta function, any arithmetic input, or RH**.

* `lagrangian a = Σ aᵢ² − (Σ aᵢ)²/N`, for `aᵢ = |λᵢ|` the moduli of the `N = 2n` closed-chain
  eigenvalues. `lagrangian_eq_pair_sum`: it equals `(1/2N) Σᵢⱼ (aᵢ − aⱼ)²`. Hence it is `≥ 0` and
  vanishes iff all moduli agree (the *spacelike* case). Spin 1: `(a₁−a₂)²/2`. Spin 2 with spectrum
  `(c₁,c₁,c₂,c₂)`: `(|c₁|−|c₂|)²`.
* `mirror_overlap`: for the mirror overlap `O = [[a,b],[b̄,ā]]` and `J = diag(1,−1)`,
  `J O J O† = (|a|² − |b|²) I`, so a mirrored spin-one closed chain has two equal eigenvalues
  and zero Lagrangian, whatever the input (Codex's "mirror no-go").
* `chain_sq`, `lagrangian_roots`: for real `h`, `m = 1+|h|`, `x = diag(1,−1)` and
  `y_h = [[m+a, v],[v, a−m]]` (`a = (h+1)/2`, `v = (h−1)/2`) the closed chain `A = x y_h` obeys
  `(A − mI)² = hI`; with eigenvalues `m ± w`, `w² = h`, the Lagrangian is `2·max(h,0)`.
* `im_inv_sub_neg`: `Im (1/(u − u₀)) < 0` for every real `u₀` and `Im u > 0`. The sign of the
  imaginary part is the same whether the pole `u₀` is positive or negative, which is Grok S43's
  "Pick positivity alone does not exclude a Siegel zero" in its minimal form.

**Scope, stated plainly.** This formalizes that the CFS map *faithfully re-encodes* a scalar defect
`h` that is supplied from outside (Codex's own "ESSENTIAL GAP"). It supplies no variational
principle, no arithmetic correlation operator, and no statement about zeros. RH/GRH remain open.
-/

namespace GppCfsClosedChain

open Finset

/-- The spin-`n` causal Lagrangian in terms of the moduli `aᵢ = |λᵢ|` of the `N = 2n` closed-chain
eigenvalues: `Σ aᵢ² − (1/N)(Σ aᵢ)²`. -/
noncomputable def lagrangian {ι : Type*} [Fintype ι] (a : ι → ℝ) : ℝ :=
  ∑ i, a i ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ)

theorem lagrangian_eq_pair_sum {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    lagrangian a = (1 / (2 * (Fintype.card ι : ℝ))) * ∑ i, ∑ j, (a i - a j) ^ 2 := by
  classical
  have h : ∑ i, ∑ j, (a i - a j) ^ 2 =
      2 * (Fintype.card ι : ℝ) * ∑ i, a i ^ 2 - 2 * (∑ i, a i) ^ 2 := by
    have : ∀ i j, (a i - a j) ^ 2 = a i ^ 2 + a j ^ 2 - 2 * (a i * a j) := fun i j => by ring
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [pow_two (∑ i, a i)]
    simp only [← Finset.mul_sum]
    ring
  rw [h, lagrangian]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
    simp
  · have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    field_simp

theorem lagrangian_nonneg {ι : Type*} [Fintype ι] (a : ι → ℝ) : 0 ≤ lagrangian a := by
  rw [lagrangian_eq_pair_sum]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    sq_nonneg _)

/-- Spacelike pairs: the Lagrangian vanishes exactly when all eigenvalue moduli agree. -/
theorem lagrangian_eq_zero_iff {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    lagrangian a = 0 ↔ ∀ i j, a i = a j := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [lagrangian]
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [lagrangian_eq_pair_sum]
  have hpos : (0 : ℝ) < 1 / (2 * (Fintype.card ι : ℝ)) := by positivity
  rw [mul_eq_zero, or_iff_right hpos.ne']
  constructor
  · intro h i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      sq_nonneg (a i - a j)).mp h i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (a i - a j)).mp h1 j
      (Finset.mem_univ _)
    nlinarith [h2, sq_nonneg (a i - a j)]
  · intro h
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by simp [h i j]

/-- Spin one (`N = 2`): `L = (|λ₊| − |λ₋|)²/2`. -/
theorem lagrangian_spin_one (x y : ℝ) : lagrangian ![x, y] = (x - y) ^ 2 / 2 := by
  simp [lagrangian, Fin.sum_univ_two]
  ring

/-- Spin two (`N = 4`), spectrum `(c₁,c₁,c₂,c₂)`: `L = (|c₁| − |c₂|)²`. -/
theorem lagrangian_spin_two (x y : ℝ) : lagrangian ![x, x, y, y] = (x - y) ^ 2 := by
  simp [lagrangian, Fin.sum_univ_four]
  ring

/-! ### Mirror overlap -/

/-- Mirror no-go: `J O J O† = (|a|² − |b|²) I` for `O = [[a,b],[b̄,ā]]`, `J = diag(1,−1)`. -/
theorem mirror_overlap (a b : ℂ) :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![a, b; star b, star a] *
        !![1, 0; 0, -1] * (!![a, b; star b, star a] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose =
      ((Complex.normSq a - Complex.normSq b : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.normSq_apply,
      Complex.ext_iff] <;> ring_nf <;> simp

/-! ### Spin-one closed chain of a scalar defect `h` -/

/-- `m = 1 + |h|`. -/
noncomputable def mOf (h : ℝ) : ℝ := 1 + |h|

/-- `x = diag(1,−1)`. -/
def xMat : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- `y_h = [[m + a, v],[v, a − m]]` with `a = (h+1)/2`, `v = (h−1)/2`. -/
noncomputable def yMat (h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![mOf h + (h + 1) / 2, (h - 1) / 2; (h - 1) / 2, (h + 1) / 2 - mOf h]

/-- The closed-chain carrier `A_h = x y_h`. -/
noncomputable def chain (h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := xMat * yMat h

theorem yMat_symm (h : ℝ) : (yMat h).transpose = yMat h := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [yMat]

/-- `det y_h = h − m² < 0`: both `x` and `y_h` have one positive and one negative eigenvalue. -/
theorem det_yMat (h : ℝ) : (yMat h).det = h - mOf h ^ 2 := by
  simp [Matrix.det_fin_two, yMat]
  ring

theorem det_yMat_neg (h : ℝ) : (yMat h).det < 0 := by
  rw [det_yMat, mOf]
  rcases le_or_gt 0 h with h0 | h0
  · rw [abs_of_nonneg h0]; nlinarith
  · rw [abs_of_neg h0]; nlinarith

/-- The carrier satisfies `(A_h − m I)² = h I`. -/
theorem chain_sq (h : ℝ) :
    (chain h - mOf h • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 = h • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chain, xMat, yMat, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring

/-- With eigenvalues `m ± w`, `w² = h`, the spin-one Lagrangian is `2·max(h,0)`: timelike exactly
when `h > 0`, and zero otherwise (including the repeated root at `h = 0`). -/
theorem lagrangian_roots (h : ℝ) (w : ℂ) (hw : w ^ 2 = (h : ℂ)) :
    lagrangian ![‖((mOf h : ℝ) : ℂ) + w‖, ‖((mOf h : ℝ) : ℂ) - w‖] = 2 * max h 0 := by
  rw [lagrangian_spin_one]
  have h1 := congrArg Complex.re hw
  have h2 := congrArg Complex.im hw
  simp [pow_two] at h1 h2
  have hm : mOf h = 1 + |h| := rfl
  rcases mul_eq_zero.mp (show w.re * w.im = 0 by linarith) with hre | him
  · -- w purely imaginary: |m + w| = |m − w|
    have hh : h = -(w.im * w.im) := by rw [hre] at h1; linarith
    have e : ‖((mOf h : ℝ) : ℂ) + w‖ = ‖((mOf h : ℝ) : ℂ) - w‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      congr 1
      simp [Complex.normSq_apply, hre]
    rw [e, max_eq_right (by nlinarith [mul_self_nonneg w.im])]
    ring
  · -- w real
    have hh : h = w.re * w.re := by rw [him] at h1; linarith
    have hn : ∀ s : ℝ, ‖((mOf h : ℝ) : ℂ) + s * w‖ = |mOf h + s * w.re| := by
      intro s
      have : ((mOf h : ℝ) : ℂ) + s * w = ((mOf h + s * w.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hp := hn 1
    have hq := hn (-1)
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, one_mul]
      at hp hq
    rw [hp, hq]
    have hm1 : 0 ≤ mOf h + w.re := by
      rw [hm, abs_of_nonneg (by rw [hh]; exact mul_self_nonneg _)]; nlinarith [sq_nonneg (w.re + 1/2)]
    have hm2 : 0 ≤ mOf h - w.re := by
      rw [hm, abs_of_nonneg (by rw [hh]; exact mul_self_nonneg _)]; nlinarith [sq_nonneg (w.re - 1/2)]
    rw [abs_of_nonneg hm1, abs_of_nonneg hm2,
      max_eq_left (by rw [hh]; exact mul_self_nonneg _)]
    rw [hh]; ring

/-! ### Siegel sign -/

/-- `Im (1/(u − u₀)) = −Im u / |u − u₀|² < 0` for every **real** `u₀`: positive and negative
poles carry the same sign, so the Herglotz/Pick sign alone cannot exclude a positive real pole. -/
theorem im_inv_sub_neg (u : ℂ) (hu : 0 < u.im) (u₀ : ℝ) : (1 / (u - u₀)).im < 0 := by
  have hne : Complex.normSq (u - u₀) ≠ 0 := by
    intro h0
    have := Complex.normSq_eq_zero.mp h0
    have h3 := congrArg Complex.im this
    simp at h3; linarith
  rw [one_div, Complex.inv_im]
  have : (u - (u₀ : ℂ)).im = u.im := by simp
  rw [this]
  have hp : 0 < Complex.normSq (u - u₀) := lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hne)
  have : 0 < u.im / Complex.normSq (u - u₀) := div_pos hu hp
  linarith [neg_div (Complex.normSq (u - u₀)) u.im]

end GppCfsClosedChain
