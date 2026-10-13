import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Confluent jet matrices of a Stieltjes response are Gram matrices

Source: Codex, `work/codex/2026-10-13_compact_modes_uniform_moments_confluent_witness.md` §5
(GPP-bridge PR #11 comment 6138178435), which corrects Claude Code's 2026-10-12 recommendation
that only spread-node Loewner tests can see `F_θ` (`CLAUDE_CODE_CORRECTIONS.md`, 2026-10-13).

If `m(u) = ∫ (u + t)⁻¹ dμ(t)` with `μ ≥ 0` finite on `[0, ∞)`, its signed Taylor jet at `u₀ > 0` is
the matrix `C i j = ∫ (u₀ + t)^{-(i+j+2)} dμ` (`jetGram`). That matrix is a Gram matrix:
`∑ᵢⱼ vᵢ vⱼ C i j = ∫ (∑ᵢ vᵢ (u₀+t)^{-(i+1)})² dμ ≥ 0` at **every** size
(`jetGram_quadratic_eq`, `jetGram_quadratic_nonneg`). So a single vector `q` with
`qᵀ C q < 0` excludes **every** such representation (`not_stieltjes_of_negative_witness`). Codex's
witnesses are stated for the conditioned matrix `D C D` with `D = diag(16^i)`, and
`diag_congruence_witness` transfers them to `C`.

**Not formalized:** the identification of `C` with `(-1)^{i+j+1} m^{(i+j+1)}(u₀)/(i+j+1)!`
(differentiation under the integral). Also not formalized are the numerical values for `m_*` and
`m_θ`; those are high-precision NUMERICAL results, not interval certificates. **No RH claim:**
positivity of the `m_*` jet at every order is a necessary condition for a Stieltjes representation,
not a proof of one.
-/

namespace GppNoGo.ConfluentStieltjesGram

open MeasureTheory

/-- The confluent jet matrix of the Stieltjes transform of `μ` at base point `u₀`. -/
noncomputable def jetGram (μ : Measure ℝ) (u₀ : ℝ) (n : ℕ) (i j : Fin n) : ℝ :=
  ∫ t, ((u₀ + t)⁻¹) ^ ((i : ℕ) + j + 2) ∂μ

/-- Every resolvent power is integrable against a finite measure supported on `[0, ∞)`. -/
theorem integrable_resolvent_pow (μ : Measure ℝ) [IsFiniteMeasure μ] {u₀ : ℝ} (hu : 0 < u₀)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) (k : ℕ) :
    Integrable (fun t => ((u₀ + t)⁻¹) ^ k) μ := by
  refine Integrable.mono' (integrable_const ((u₀⁻¹) ^ k)) ?_ ?_
  · exact ((measurable_const.add measurable_id).inv.pow_const k).aestronglyMeasurable
  · filter_upwards [hsupp] with t ht
    have hpos : 0 < u₀ + t := by linarith
    rw [Real.norm_eq_abs, abs_pow, abs_of_pos (inv_pos.mpr hpos)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) (inv_anti₀ hu (by linarith)) k

/-- **The jet quadratic form is an integral of a square.** -/
theorem jetGram_quadratic_eq (μ : Measure ℝ) [IsFiniteMeasure μ] {u₀ : ℝ} (hu : 0 < u₀)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) {n : ℕ} (v : Fin n → ℝ) :
    ∑ i, ∑ j, v i * v j * jetGram μ u₀ n i j
      = ∫ t, (∑ i, v i * ((u₀ + t)⁻¹) ^ ((i : ℕ) + 1)) ^ 2 ∂μ := by
  have hint := integrable_resolvent_pow μ hu hsupp
  have key : ∀ t : ℝ, (∑ i : Fin n, v i * ((u₀ + t)⁻¹) ^ ((i : ℕ) + 1)) ^ 2
      = ∑ i : Fin n, ∑ j : Fin n, v i * v j * ((u₀ + t)⁻¹) ^ ((i : ℕ) + j + 2) := by
    intro t
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show (i : ℕ) + j + 2 = ((i : ℕ) + 1) + ((j : ℕ) + 1) by ring, pow_add]
    ring
  simp_rw [key]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hint _).const_mul _))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => (hint _).const_mul _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [jetGram, integral_const_mul]

/-- **Stieltjes jets are positive semidefinite at every size.** -/
theorem jetGram_quadratic_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] {u₀ : ℝ} (hu : 0 < u₀)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * v j * jetGram μ u₀ n i j := by
  rw [jetGram_quadratic_eq μ hu hsupp v]
  exact integral_nonneg (fun t => sq_nonneg _)

/-- **One negative witness excludes every finite positive Stieltjes measure on `[0, ∞)`.** -/
theorem not_stieltjes_of_negative_witness {n : ℕ} {u₀ : ℝ} (hu : 0 < u₀) (C : Fin n → Fin n → ℝ)
    (q : Fin n → ℝ) (hq : ∑ i, ∑ j, q i * q j * C i j < 0) :
    ¬ ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ (∀ᵐ t ∂μ, 0 ≤ t) ∧
      ∀ i j, C i j = jetGram μ u₀ n i j := by
  rintro ⟨μ, hfin, hsupp, hC⟩
  have h := jetGram_quadratic_nonneg μ hu hsupp q
  simp_rw [← hC] at h
  linarith

/-- A witness `q` for the conditioned matrix `D C D`, `D = diag d`, is the witness `D q` for `C`. -/
theorem diag_congruence_witness {n : ℕ} (C : Fin n → Fin n → ℝ) (d q : Fin n → ℝ) :
    ∑ i, ∑ j, q i * q j * (d i * C i j * d j)
      = ∑ i, ∑ j, (d i * q i) * (d j * q j) * C i j := by
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

end GppNoGo.ConfluentStieltjesGram
