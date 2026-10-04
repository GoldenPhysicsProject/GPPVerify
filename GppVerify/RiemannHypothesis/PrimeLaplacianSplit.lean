import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The prime Laplacian split: translation terms as a graph Laplacian minus a scalar mass

Source: Codex, `research/codex/2026-10-03_arrow_roadmap_review_and_execution.md` §8.1 (added
2026-10-04), the exact part.

For an isometry `T` (the zero-extended translation by `log n` on `L²(ℝ)`) and a weight `c ≥ 0`,
`‖f − T f‖² = 2‖f‖² − 2 Re⟨T f, f⟩`, hence exactly
`−2 c Re⟨T f, f⟩ = c ‖f − T f‖² − 2 c ‖f‖²` (`translation_split`).
Summed over a finite family of prime-power translations (`prime_sum_split`) the prime part of the
semilocal form is a positive "Laplacian" `Σ c_n ‖f − T_n f‖²` minus the scalar mass `2 (Σ c_n) ‖f‖²`;
in particular it is bounded below by `−2 S ‖f‖²` with `S = Σ c_n` (`prime_sum_lower_bound`).

## Checks and scope

All statements check; they are one-line consequences of the polarization identity and are recorded
because the note builds its network picture on them. **Not formalized:** the semilocal Weil matrix
`Q_λ`, the Archimedean and pole blocks `W02`, `WR`, the identification of the compression to the interval
(the identity above is for the whole-line isometry; on the compressed interval the translation is only a
contraction), and the open absorption of the negative scalar mass by the boundary and Archimedean channels.
The parity-threshold numerics (§10) are numerical evidence in the note, not claimed here. Codex's
GPPVerify PR #236 (`codex/passive-network-lemmas`) covers the positive-parent-to-Kron transfer and
DtN channels; this module does not overlap it. No RH claim.
-/

open scoped InnerProductSpace

namespace GppPrimeLaplacianSplit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `‖f − T f‖² = 2‖f‖² − 2 Re⟨T f, f⟩` for an isometry `T`. -/
theorem norm_sub_isometry (T : E →ₗᵢ[ℂ] E) (f : E) :
    ‖f - T f‖ ^ 2 = 2 * ‖f‖ ^ 2 - 2 * (⟪T f, f⟫_ℂ).re := by
  rw [norm_sub_rev, norm_sub_sq (𝕜 := ℂ) (T f) f, T.norm_map]
  simp only [RCLike.re_to_complex]
  ring

/-- **Translation term = Laplacian minus mass.** -/
theorem translation_split (T : E →ₗᵢ[ℂ] E) (c : ℝ) (f : E) :
    -2 * c * (⟪T f, f⟫_ℂ).re = c * ‖f - T f‖ ^ 2 - 2 * c * ‖f‖ ^ 2 := by
  rw [norm_sub_isometry]; ring

/-- **The prime sum splits into a Laplacian and a scalar mass.** -/
theorem prime_sum_split {ι : Type*} (s : Finset ι) (c : ι → ℝ) (T : ι → E →ₗᵢ[ℂ] E) (f : E) :
    ∑ i ∈ s, -2 * c i * (⟪T i f, f⟫_ℂ).re =
      ∑ i ∈ s, c i * ‖f - T i f‖ ^ 2 - 2 * (∑ i ∈ s, c i) * ‖f‖ ^ 2 := by
  have h : 2 * (∑ i ∈ s, c i) * ‖f‖ ^ 2 = ∑ i ∈ s, 2 * c i * ‖f‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [h, Finset.sum_congr rfl fun i _ => translation_split (T i) (c i) f, Finset.sum_sub_distrib]

/-- With nonnegative weights the prime part is bounded below by `−2 S ‖f‖²`. -/
theorem prime_sum_lower_bound {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (T : ι → E →ₗᵢ[ℂ] E) (f : E) :
    -2 * (∑ i ∈ s, c i) * ‖f‖ ^ 2 ≤ ∑ i ∈ s, -2 * c i * (⟪T i f, f⟫_ℂ).re := by
  rw [prime_sum_split]
  have : 0 ≤ ∑ i ∈ s, c i * ‖f - T i f‖ ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (sq_nonneg _)
  nlinarith

end GppPrimeLaplacianSplit
