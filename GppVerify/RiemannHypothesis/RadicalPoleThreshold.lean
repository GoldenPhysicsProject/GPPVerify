import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# The vacuum radical calibrates the pole channels at exactly `∓2`

Source: Codex, 2026-09-29, "Riemann-kernel radical calibrates the split pole channels exactly"
(GPPDiscovery2 `research/2026-09-29_riemann_vacuum_radical_pole_thresholds.md`, §§3–5).

The completed Weil form splits as `Q = A + ½|c⟩⟨c| − ½|s⟩⟨s|`. Here `A` is the
pole-removed prime–Archimedean part, `c` is the even pole channel and `s` is the odd one.
The Riemann kernel `Φ` (with `Φ̂ = Ξ`) and its derivative `Φ'` vanish on every zero
channel, so they are radical vectors of `Q`. This is Codex's §1. It is conditional on the
standard test-space extension of the Weil formula and is **not** formalized here.

The consequences are exact finite linear algebra, and this file certifies them for any
matrix `A`:

* `even_threshold`: if `(A + ½ ccᵀ)Φ = 0`, `A` is invertible and `⟨c, Φ⟩ ≠ 0`, then
  `⟨c, A⁻¹c⟩ = −2`.
* `odd_threshold`: if `(A − ½ ssᵀ)Φ' = 0`, `A` is invertible and `⟨s, Φ'⟩ ≠ 0`, then
  `⟨s, A⁻¹s⟩ = 2`.
* `det_rankOne`: the matrix determinant lemma
  `det(A + t ccᵀ) = det A · (1 + t ⟨c, A⁻¹c⟩)`. In particular
  `rankOne_singular_iff_threshold` says `A + ½ccᵀ` is singular exactly at the threshold
  `⟨c, A⁻¹c⟩ = −2`.

This explains the finite pole-resolvent numbers near `−2` and `+2` that Daniel's Meta-AI
synthesis reported. Scope: Codex's §5 inertia statement (positivity of `Q₊` when `A₊` has
exactly one negative eigenvalue) needs Haynsworth inertia additivity and is not formalized
here. A large radical does **not** imply positivity. No RH claim.
-/

namespace GppRadicalPoleThreshold

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma rankOne_mulVec (c Φ : n → ℝ) : vecMulVec c c *ᵥ Φ = (c ⬝ᵥ Φ) • c := by
  ext i
  simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

/-- **Even threshold.** A radical vector of `A + ½ccᵀ` with nonzero `c`-overlap forces
`⟨c, A⁻¹c⟩ = −2`. -/
theorem even_threshold (A : Matrix n n ℝ) (hA : IsUnit A.det) (c Φ : n → ℝ)
    (hQ : (A + (1 / 2 : ℝ) • vecMulVec c c) *ᵥ Φ = 0) (hc : c ⬝ᵥ Φ ≠ 0) :
    c ⬝ᵥ (A⁻¹ *ᵥ c) = -2 := by
  rw [add_mulVec, smul_mulVec, rankOne_mulVec] at hQ
  have hAΦ : A *ᵥ Φ = (-(1 / 2 : ℝ) * (c ⬝ᵥ Φ)) • c := by
    rw [mul_smul, neg_smul, ← smul_assoc, eq_neg_iff_add_eq_zero, smul_eq_mul]
    simpa [smul_smul] using hQ
  have hΦ : Φ = (-(1 / 2 : ℝ) * (c ⬝ᵥ Φ)) • (A⁻¹ *ᵥ c) := by
    have := congrArg (fun v => A⁻¹ *ᵥ v) hAΦ
    simp only [mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec, mulVec_smul] at this
    exact this
  have hdot : c ⬝ᵥ Φ = (-(1 / 2 : ℝ) * (c ⬝ᵥ Φ)) * (c ⬝ᵥ (A⁻¹ *ᵥ c)) := by
    conv_lhs => rw [hΦ]
    rw [dotProduct_smul, smul_eq_mul]
  have h1 : (1 : ℝ) = -(1 / 2) * (c ⬝ᵥ (A⁻¹ *ᵥ c)) := by
    have := hdot
    field_simp at this ⊢
    nlinarith [this, hc]
  linarith

/-- **Odd threshold.** A radical vector of `A − ½ssᵀ` with nonzero `s`-overlap forces
`⟨s, A⁻¹s⟩ = 2`. -/
theorem odd_threshold (A : Matrix n n ℝ) (hA : IsUnit A.det) (s Ψ : n → ℝ)
    (hQ : (A - (1 / 2 : ℝ) • vecMulVec s s) *ᵥ Ψ = 0) (hs : s ⬝ᵥ Ψ ≠ 0) :
    s ⬝ᵥ (A⁻¹ *ᵥ s) = 2 := by
  have hQ' : (A + (-(1 / 2) : ℝ) • vecMulVec s s) *ᵥ Ψ = 0 := by
    rw [neg_smul, ← sub_eq_add_neg]; exact hQ
  rw [add_mulVec, smul_mulVec, rankOne_mulVec] at hQ'
  have hAΨ : A *ᵥ Ψ = ((1 / 2 : ℝ) * (s ⬝ᵥ Ψ)) • s := by
    rw [smul_smul] at hQ'
    rw [← sub_eq_zero]
    have : A *ᵥ Ψ + (-(1 / 2) * (s ⬝ᵥ Ψ)) • s = 0 := hQ'
    rw [← this, sub_eq_add_neg, ← neg_smul, neg_mul]
  have hΨ : Ψ = ((1 / 2 : ℝ) * (s ⬝ᵥ Ψ)) • (A⁻¹ *ᵥ s) := by
    have := congrArg (fun v => A⁻¹ *ᵥ v) hAΨ
    simp only [mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec, mulVec_smul] at this
    exact this
  have hdot : s ⬝ᵥ Ψ = ((1 / 2 : ℝ) * (s ⬝ᵥ Ψ)) * (s ⬝ᵥ (A⁻¹ *ᵥ s)) := by
    conv_lhs => rw [hΨ]
    rw [dotProduct_smul, smul_eq_mul]
  have h1 : (1 : ℝ) = (1 / 2) * (s ⬝ᵥ (A⁻¹ *ᵥ s)) := by
    field_simp at hdot ⊢
    nlinarith [hdot, hs]
  linarith

/-- **Matrix determinant lemma** for a symmetric rank-one update. -/
theorem det_rankOne (A : Matrix n n ℝ) (hA : IsUnit A.det) (c : n → ℝ) (t : ℝ) :
    (A + t • vecMulVec c c).det = A.det * (1 + t * (c ⬝ᵥ (A⁻¹ *ᵥ c))) := by
  have hvm : t • vecMulVec c c = replicateCol Unit (t • c) * replicateRow Unit c := by
    ext i j; simp [vecMulVec, replicateCol, replicateRow, Matrix.mul_apply, mul_assoc]
  rw [hvm, det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [det_unique]
  simp [Matrix.mul_apply, replicateRow, replicateCol, dotProduct, mulVec, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The even channel `A + ½ccᵀ` is singular exactly at the threshold `⟨c, A⁻¹c⟩ = −2`. -/
theorem rankOne_singular_iff_threshold (A : Matrix n n ℝ) (hA : IsUnit A.det) (c : n → ℝ) :
    (A + (1 / 2 : ℝ) • vecMulVec c c).det = 0 ↔ c ⬝ᵥ (A⁻¹ *ᵥ c) = -2 := by
  rw [det_rankOne A hA c]
  have hdet : A.det ≠ 0 := hA.ne_zero
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hdet
    · linarith
  · intro h; rw [h]; ring

end GppRadicalPoleThreshold
