import GppVerify.RiemannHypothesis.RankOneThresholdControls

/-!
# Rank-one inertia threshold: the inequality form

Source: Grok, GPP-bridge `work/grok/2026-10-21_team_review.md` §1 ("Rank-one inertia, the form we all
need"), answering Astra's question about the even signed gap `1 + uᵀR⁻¹u ≤ 0`; it generalizes the
equality case `GppRankOneControls.pole_threshold_neg`. Formalized by Claude Code, with AI
assistance, for Daniel Toupin / Golden Physics Project.

Let `A` be real symmetric and invertible, `u = A⁻¹c`, `s = cᵀA⁻¹c ≠ 0`, and suppose `A` is positive
definite on the hyperplane `c^⊥`. Writing `x = αu + y` with `yᵀc = 0` (`α = cᵀx/s`):

* `quad_decomp`: `xᵀ(A + κccᵀ)x = yᵀAy + α² s (1 + κ s)`;
* `psd_iff`: `A + κccᵀ ⪰ 0 ⇔ s(1 + κs) ≥ 0`;
* `psd_plus_half_iff`: `A + ½ccᵀ ⪰ 0 ⇔ s ≤ −2 ∨ 0 < s` (the even case: with one negative direction,
  `s < 0`, this is `s ≤ −2`);
* `psd_minus_half_iff`: `A − ½ccᵀ ⪰ 0 ⇔ 0 < s ∧ s ≤ 2` (the odd case).

Scope: finite linear algebra. "Positive definite on `c^⊥`" is the hypothesis used, as in
`RankOneThresholdControls`; its equivalence with "exactly one negative eigenvalue" (Haynsworth) is not
proved. Nothing here bounds the actual Weil-form Schur scalar, and nothing concerns RH.
-/

open Matrix

namespace GppRankOneInertia

variable {n : Type*} [Fintype n] [DecidableEq n]

open GppRankOneControls in
theorem quad_decomp (A : Matrix n n ℝ) (hsymm : A.IsSymm) (hdet : IsUnit A.det) (c : n → ℝ)
    (hs : c ⬝ᵥ (A⁻¹ *ᵥ c) ≠ 0) (κ : ℝ) (x : n → ℝ) :
    let s := c ⬝ᵥ (A⁻¹ *ᵥ c)
    let α := (c ⬝ᵥ x) / s
    let y := x - α • (A⁻¹ *ᵥ c)
    y ⬝ᵥ c = 0 ∧
      x ⬝ᵥ ((A + κ • Matrix.vecMulVec c c) *ᵥ x) = y ⬝ᵥ (A *ᵥ y) + α ^ 2 * (s * (1 + κ * s)) := by
  intro s α y
  have hs' : s ≠ 0 := hs
  set u : n → ℝ := A⁻¹ *ᵥ c with hu
  have hAu : A *ᵥ u = c := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hcu : c ⬝ᵥ u = s := rfl
  have huAu : u ⬝ᵥ (A *ᵥ u) = s := by rw [hAu, dotProduct_comm]
  have hyc : y ⬝ᵥ c = 0 := by
    simp only [y, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [dotProduct_comm u c, hcu, dotProduct_comm x c]
    simp only [α]; field_simp; ring
  refine ⟨hyc, ?_⟩
  have hx : x = y + α • u := by simp only [y]; abel
  have hyAu : y ⬝ᵥ (A *ᵥ u) = 0 := by rw [hAu]; exact hyc
  have hcx : c ⬝ᵥ x = α * s := by simp only [α]; field_simp
  have hexp : x ⬝ᵥ (A *ᵥ x) = y ⬝ᵥ (A *ᵥ y) + α ^ 2 * s := by
    conv_lhs => rw [hx]
    rw [quad_add A hsymm]
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hyAu, huAu]; ring
  have hrank : x ⬝ᵥ ((κ • Matrix.vecMulVec c c) *ᵥ x) = κ * (c ⬝ᵥ x) ^ 2 := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, quad_vecMulVec]
  rw [Matrix.add_mulVec, dotProduct_add, hexp, hrank, hcx]
  ring

/-- `A + κ c cᵀ` is positive semidefinite iff `s (1 + κ s) ≥ 0`. -/
theorem psd_iff (A : Matrix n n ℝ) (hsymm : A.IsSymm) (hdet : IsUnit A.det) (c : n → ℝ)
    (hs : c ⬝ᵥ (A⁻¹ *ᵥ c) ≠ 0)
    (hpd : ∀ y : n → ℝ, y ⬝ᵥ c = 0 → y ≠ 0 → 0 < y ⬝ᵥ (A *ᵥ y)) (κ : ℝ) :
    (∀ x : n → ℝ, 0 ≤ x ⬝ᵥ ((A + κ • Matrix.vecMulVec c c) *ᵥ x)) ↔
      0 ≤ (c ⬝ᵥ (A⁻¹ *ᵥ c)) * (1 + κ * (c ⬝ᵥ (A⁻¹ *ᵥ c))) := by
  constructor
  · intro h
    obtain ⟨hyc, hq⟩ := quad_decomp A hsymm hdet c hs κ (A⁻¹ *ᵥ c)
    have hα : (c ⬝ᵥ (A⁻¹ *ᵥ c)) / (c ⬝ᵥ (A⁻¹ *ᵥ c)) = 1 := div_self hs
    have hy0 : (A⁻¹ *ᵥ c) - ((c ⬝ᵥ (A⁻¹ *ᵥ c)) / (c ⬝ᵥ (A⁻¹ *ᵥ c))) • (A⁻¹ *ᵥ c) = 0 := by
      rw [hα, one_smul, sub_self]
    have := h (A⁻¹ *ᵥ c)
    rw [hq, hy0, hα] at this
    simpa using this
  · intro h x
    obtain ⟨hyc, hq⟩ := quad_decomp A hsymm hdet c hs κ x
    rw [hq]
    have hyy : 0 ≤ (x - (c ⬝ᵥ x / c ⬝ᵥ (A⁻¹ *ᵥ c)) • (A⁻¹ *ᵥ c)) ⬝ᵥ
        (A *ᵥ (x - (c ⬝ᵥ x / c ⬝ᵥ (A⁻¹ *ᵥ c)) • (A⁻¹ *ᵥ c))) := by
      by_cases hy : x - (c ⬝ᵥ x / c ⬝ᵥ (A⁻¹ *ᵥ c)) • (A⁻¹ *ᵥ c) = 0
      · rw [hy]; simp
      · exact (hpd _ hyc hy).le
    have : 0 ≤ (c ⬝ᵥ x / c ⬝ᵥ (A⁻¹ *ᵥ c)) ^ 2 *
        ((c ⬝ᵥ (A⁻¹ *ᵥ c)) * (1 + κ * (c ⬝ᵥ (A⁻¹ *ᵥ c)))) := mul_nonneg (sq_nonneg _) h
    linarith

/-- Even case: `A + ½ccᵀ ⪰ 0 ⇔ s ≤ −2 ∨ 0 < s`. -/
theorem psd_plus_half_iff (A : Matrix n n ℝ) (hsymm : A.IsSymm) (hdet : IsUnit A.det)
    (c : n → ℝ) (hs : c ⬝ᵥ (A⁻¹ *ᵥ c) ≠ 0)
    (hpd : ∀ y : n → ℝ, y ⬝ᵥ c = 0 → y ≠ 0 → 0 < y ⬝ᵥ (A *ᵥ y)) :
    (∀ x : n → ℝ, 0 ≤ x ⬝ᵥ ((A + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x)) ↔
      (c ⬝ᵥ (A⁻¹ *ᵥ c) ≤ -2 ∨ 0 < c ⬝ᵥ (A⁻¹ *ᵥ c)) := by
  rw [psd_iff A hsymm hdet c hs hpd]
  set s := c ⬝ᵥ (A⁻¹ *ᵥ c)
  constructor
  · intro h
    rcases lt_or_gt_of_ne hs with h' | h'
    · left; nlinarith
    · right; exact h'
  · rintro (h | h) <;> nlinarith

/-- Odd case: `A − ½ccᵀ ⪰ 0 ⇔ 0 < s ∧ s ≤ 2`. -/
theorem psd_minus_half_iff (A : Matrix n n ℝ) (hsymm : A.IsSymm) (hdet : IsUnit A.det)
    (c : n → ℝ) (hs : c ⬝ᵥ (A⁻¹ *ᵥ c) ≠ 0)
    (hpd : ∀ y : n → ℝ, y ⬝ᵥ c = 0 → y ≠ 0 → 0 < y ⬝ᵥ (A *ᵥ y)) :
    (∀ x : n → ℝ, 0 ≤ x ⬝ᵥ ((A + (-1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x)) ↔
      (0 < c ⬝ᵥ (A⁻¹ *ᵥ c) ∧ c ⬝ᵥ (A⁻¹ *ᵥ c) ≤ 2) := by
  rw [psd_iff A hsymm hdet c hs hpd]
  set s := c ⬝ᵥ (A⁻¹ *ᵥ c)
  constructor
  · intro h
    rcases lt_or_gt_of_ne hs with h' | h'
    · exfalso; nlinarith
    · exact ⟨h', by nlinarith⟩
  · rintro ⟨h1, h2⟩; nlinarith

end GppRankOneInertia
