import GppVerify.RiemannHypothesis.PrimeCayleyGolden
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The prime channel matrix as a Householder reflection, and the Feshbach projection identity

Source: Codex, bridge `research/codex/`:
* `2026-10-02_golden_householder_dihedral_bridge.md` (exact local algebra);
* `2026-10-02_rank_one_resolvent_feshbach_collapse.md`, and
  `2026-10-02_finite_feshbach_rank_two_and_hodge_obstruction.md` (the finite inner-product facts).

## Householder form

For `c ≥ 0` put `S(c) = (1/(1+c)) [[1−c, 2√c], [2√c, c−1]]`.

* `householder_form`: `S(c) = 2 u uᵀ − I` for the unit vector `u = (1, √c)/√(1+c)`;
* `channel_eq_householder`: at a prime, `S(μ_p) = S(c_p)` with `μ_p = 2/√(p−1)` and
  `c_p = (√p − 1)/(√p + 1)` the Cayley coordinate. So the prime channel is a reflection whose
  mirror line is `u_{c_p}`;
* `reflection_conj`: `S τ S = −τ` whenever `S² = 1` and `S τ = −τ S` (it applies to `S(μ)` by
  `channel_sq` and `channel_anticomm`).

## The Julia colligation

From `2026-09-29_prime_euler_julia_colligation.md` (exact local algebra): for `0 ≤ r < 1` and
`b = √(1 − r²)` the Julia matrix `U = [[r, b], [b, −r]]` (the prime channel `S`, with `r = p^{-1/2}`)
satisfies `U² = I`, `Uᵀ = U` and `det U = −1` (`julia_sq`, `julia_det`), and its transfer function
`−r + w b (1 − r w)⁻¹ b` is the Blaschke map `(w − r)/(1 − r w)` (`julia_transfer`).

## Feshbach projection and Gram identities

* `projection_norm_sq`: for `e ≠ 0` in a complex inner product space and any `q`,
  `‖q − (⟨e,q⟩/⟨e,e⟩) e‖² = ‖q‖² − |⟨e,q⟩|²/‖e‖²`. With `‖e‖² = 1/(2κ)` this is the note's
  `‖q^⊥‖² = ‖q‖² − 2κ |m|²`;
* `wedge_norm_nonneg`: `‖e‖² ‖q‖² − |⟨e,q⟩|² ≥ 0`, the Gram determinant of `(e, q)`, which is the
  note's `‖e ∧ q‖² ≥ 0` (positive semidefiniteness of general Gram matrices is
  `SU11CharacterDefect.gram_psd`).

## Checks

All verified by hand; no corrections. The statement "`P τ P* = S_5`" in the first note concerns a
specific isometry `P` not defined in the excerpt; not formalized.

## Scope

`2 × 2` real algebra and finite-dimensional inner-product identities. No RH claim.
-/

open Matrix GppPrimeCayley GppPrimeCayleyGolden

namespace GppPrimeHouseholder

/-- The channel matrix in Cayley form: `S(c) = (1/(1+c)) [[1−c, 2√c], [2√c, c−1]]`. -/
noncomputable def sOfC (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 - c) / (1 + c), 2 * Real.sqrt c / (1 + c); 2 * Real.sqrt c / (1 + c), (c - 1) / (1 + c)]

/-- **Householder form.** For `c ≥ 0`, `S(c) = 2 u uᵀ − I` with `u = (1, √c)/√(1+c)`. -/
theorem householder_form (c : ℝ) (hc : 0 ≤ c) :
    sOfC c = 2 • Matrix.vecMulVec ![1 / Real.sqrt (1 + c), Real.sqrt c / Real.sqrt (1 + c)]
        ![1 / Real.sqrt (1 + c), Real.sqrt c / Real.sqrt (1 + c)] - 1 := by
  have h1 : 0 < 1 + c := by linarith
  have hs : 0 < Real.sqrt (1 + c) := Real.sqrt_pos.mpr h1
  have hsq : Real.sqrt (1 + c) ^ 2 = 1 + c := Real.sq_sqrt h1.le
  have hc2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sOfC] <;> field_simp <;>
    first
      | (rw [hsq]; done)
      | (rw [hsq]; ring1)
      | (rw [hsq, hc2]; ring1)

/-- **The prime channel is the Householder reflection at the Cayley coordinate.**
For `p > 1`: `S(μ_p) = S(c_p)` where `μ_p = 2/√(p−1)`, `c_p = (√p − 1)/(√p + 1)`. -/
theorem channel_eq_householder (p : ℝ) (hp : 1 < p) :
    channel (2 / Real.sqrt (p - 1)) = sOfC ((Real.sqrt p - 1) / (Real.sqrt p + 1)) := by
  have hp0 : 0 < p := by linarith
  have hs : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hp
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have h1 : (2 / Real.sqrt (p - 1)) / Real.sqrt ((2 / Real.sqrt (p - 1)) ^ 2 + 4) =
      1 / Real.sqrt p := (channel_entries p hp).1
  have h2 : 2 / Real.sqrt ((2 / Real.sqrt (p - 1)) ^ 2 + 4) = Real.sqrt (1 - 1 / p) :=
    (channel_entries p hp).2
  set c := (Real.sqrt p - 1) / (Real.sqrt p + 1) with hcdef
  have hden : Real.sqrt p + 1 ≠ 0 := by linarith
  have hc0 : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  have h1c : 0 < 1 + c := by linarith
  have hsne : Real.sqrt p ≠ 0 := by linarith
  have hcc : (1 - c) / (1 + c) = 1 / Real.sqrt p := by
    have h2s : Real.sqrt p + 1 + (Real.sqrt p - 1) = 2 * Real.sqrt p := by ring
    rw [hcdef]; field_simp; rw [h2s]; field_simp; ring
  have hsc : 2 * Real.sqrt c / (1 + c) = Real.sqrt (1 - 1 / p) := by
    symm
    have hnn : 0 ≤ 1 - 1 / p := by
      have : 1 / p ≤ 1 := by rw [div_le_one hp0]; linarith
      linarith
    have hnn2 : 0 ≤ 2 * Real.sqrt c / (1 + c) := by positivity
    rw [Real.sqrt_eq_iff_mul_self_eq hnn hnn2]
    have hcsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0
    have e : 2 * Real.sqrt c / (1 + c) * (2 * Real.sqrt c / (1 + c)) = 4 * c / (1 + c) ^ 2 := by
      field_simp; nlinarith [hcsq]
    rw [e, hcdef]
    have hp1 : (Real.sqrt p + 1 + (Real.sqrt p - 1)) ^ 2 = 4 * p := by nlinarith [hsq]
    have hpne : p ≠ 0 := hp0.ne'
    field_simp
    rw [hp1]
    field_simp
    nlinarith [hsq]
  have hcc' : (c - 1) / (1 + c) = -(1 / Real.sqrt p) := by
    rw [← hcc, ← neg_div, neg_sub]
  have hchan : channel (2 / Real.sqrt (p - 1)) =
      !![(2 / Real.sqrt (p - 1)) / Real.sqrt ((2 / Real.sqrt (p - 1)) ^ 2 + 4),
          2 / Real.sqrt ((2 / Real.sqrt (p - 1)) ^ 2 + 4);
        2 / Real.sqrt ((2 / Real.sqrt (p - 1)) ^ 2 + 4),
          -((2 / Real.sqrt (p - 1)) / Real.sqrt ((2 / Real.sqrt (p - 1)) ^ 2 + 4))] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [channel, dirac, div_eq_mul_inv, mul_comm]
  rw [hchan, h1, h2]
  unfold sOfC
  rw [hcc, hsc, hcc']

/-- `S τ S = −τ` whenever `S² = 1` and `S τ = −τ S`. -/
theorem reflection_conj {n : Type*} [Fintype n] [DecidableEq n] (S τ : Matrix n n ℝ)
    (hS : S * S = 1) (h : S * τ = -(τ * S)) : S * τ * S = -τ := by
  rw [h, neg_mul, mul_assoc, hS, mul_one]


/-- The Julia matrix `[[r, b], [b, −r]]` of the prime colligation, with `b = √(1 − r²)`. -/
noncomputable def julia (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r, Real.sqrt (1 - r ^ 2); Real.sqrt (1 - r ^ 2), -r]

/-- `U² = I` for the Julia matrix, for `|r| ≤ 1`. -/
theorem julia_sq (r : ℝ) (hr : |r| ≤ 1) : julia r * julia r = 1 := by
  have h : 0 ≤ 1 - r ^ 2 := by nlinarith [abs_nonneg r, sq_abs r]
  have hs : Real.sqrt (1 - r ^ 2) * Real.sqrt (1 - r ^ 2) = 1 - r ^ 2 := Real.mul_self_sqrt h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [julia, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hs]

/-- `det U = −1` for the Julia matrix, for `|r| ≤ 1`. -/
theorem julia_det (r : ℝ) (hr : |r| ≤ 1) : (julia r).det = -1 := by
  have h : 0 ≤ 1 - r ^ 2 := by nlinarith [abs_nonneg r, sq_abs r]
  have hs : Real.sqrt (1 - r ^ 2) * Real.sqrt (1 - r ^ 2) = 1 - r ^ 2 := Real.mul_self_sqrt h
  rw [julia, Matrix.det_fin_two_of]
  nlinarith [hs]

/-- **The Julia transfer function is the Blaschke map.** For `|r| < 1` and `r w ≠ 1`:
`−r + w b (1 − r w)⁻¹ b = (w − r)/(1 − r w)` with `b² = 1 − r²`. -/
theorem julia_transfer (r : ℝ) (hr : |r| < 1) (w : ℂ) (hw : 1 - (r : ℂ) * w ≠ 0) :
    -(r : ℂ) + w * (Real.sqrt (1 - r ^ 2) : ℂ) * (1 - (r : ℂ) * w)⁻¹ *
        (Real.sqrt (1 - r ^ 2) : ℂ) = (w - r) / (1 - r * w) := by
  have h : 0 ≤ 1 - r ^ 2 := by nlinarith [abs_lt.mp hr, sq_abs r]
  have hs : (Real.sqrt (1 - r ^ 2) : ℂ) * (Real.sqrt (1 - r ^ 2) : ℂ) = 1 - (r : ℂ) ^ 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]; push_cast; ring
  field_simp
  linear_combination w * hs

/-- **Projection norm.** For `e ≠ 0` in a complex inner product space and any `q`,
`‖q − (⟨e,q⟩/‖e‖²) e‖² = ‖q‖² − |⟨e,q⟩|²/‖e‖²`. -/
theorem projection_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (e q : E)
    (he : e ≠ 0) :
    ‖q - (inner ℂ e q / ((‖e‖ ^ 2 : ℝ) : ℂ)) • e‖ ^ 2 =
      ‖q‖ ^ 2 - ‖inner ℂ e q‖ ^ 2 / ‖e‖ ^ 2 := by
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hn2 : (‖e‖ ^ 2 : ℝ) ≠ 0 := by positivity
  set a : ℂ := inner ℂ e q with ha
  set α : ℂ := a / ((‖e‖ ^ 2 : ℝ) : ℂ) with hα
  have h1 : ‖q - α • e‖ ^ 2 = ‖q‖ ^ 2 - 2 * (inner ℂ q (α • e)).re + ‖α • e‖ ^ 2 := by
    have := norm_sub_sq (𝕜 := ℂ) q (α • e)
    simpa only [RCLike.re_to_complex] using this
  have h2 : inner ℂ q (α • e) = α * inner ℂ q e := inner_smul_right _ _ _
  have h3 : inner ℂ q e = (starRingEnd ℂ) a := by rw [ha, inner_conj_symm]
  have h4 : (α * inner ℂ q e).re = ‖a‖ ^ 2 / ‖e‖ ^ 2 := by
    rw [h3, hα]
    have : a / ((‖e‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) a = (((Complex.normSq a / ‖e‖ ^ 2 : ℝ)) : ℂ) := by
      push_cast
      rw [div_mul_eq_mul_div, Complex.mul_conj]
    rw [this, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have h5 : ‖α • e‖ ^ 2 = ‖a‖ ^ 2 / ‖e‖ ^ 2 := by
    rw [norm_smul, mul_pow, hα, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp
  rw [h1, h2, h4, h5]
  ring

/-- **The wedge norm is nonnegative.** `‖e‖² ‖q‖² − |⟨e,q⟩|² ≥ 0` (Cauchy–Schwarz). -/
theorem wedge_norm_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (e q : E) :
    0 ≤ ‖e‖ ^ 2 * ‖q‖ ^ 2 - ‖inner ℂ e q‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) e q
  have h0 := norm_nonneg (inner ℂ e q)
  nlinarith [mul_self_le_mul_self h0 h]

end GppPrimeHouseholder
