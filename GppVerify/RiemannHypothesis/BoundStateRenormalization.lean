import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Renormalizability of the bound-state and principal-series vectors

For a zero `ρ` of `ζ` with `σ = re ρ`, the state `x^{ρ-1}` on `(0, 1]` has regulated squared norm
`regNorm σ ε = ∫_ε^1 x^{2σ-2} dx`. As the cutoff `ε → 0`:

* `σ > 1/2` (`regNorm_tendsto_of_gt`): the norm converges to `1/(2σ-1)`; the state is normalizable,
  a bound state of the arithmetic dilation operator.
* `σ = 1/2` (`regNorm_half`, `renormalized_norm_half`): the norm is exactly `log (1/ε)`, so dividing
  by `log (1/ε)` gives `1`; the state is renormalizable, the delta-normalizable principal series.
* `σ < 1/2` (`regNorm_tendsto_atTop_of_lt`): the norm diverges like a power of `1/ε`, which no
  logarithmic counterterm removes.

In log-scale `u = log x` the renormalization is the Cesàro mean over the scale window `[0, L]`:
`cesaroMean_zero` (the zero frequency has mean `1`) and `cesaroMean_tendsto_zero` (a nonzero
frequency has mean `→ 0`), so distinct on-line states are orthonormal in the Cesàro inner product.

`regNorm_eq_radialNorm` identifies the regulated bound-state norm with the Pasterski–Shao radial
pairing `∫_1^{1/ε} ω^{2c-2} dω` at the shadow dimension `c = 1 - σ`: normalizability of the bound
state and delta-normalizability of the massless conformal primary are the same condition.
-/

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace GppBoundStateRenormalization

/-- The regulated squared norm of the state `x^(σ-1)` on `[ε, 1]`. -/
noncomputable def regNorm (σ ε : ℝ) : ℝ := ∫ x in ε..1, x ^ (2 * σ - 2)

theorem regNorm_of_ne {σ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ : σ ≠ 1 / 2) :
    regNorm σ ε = (1 - ε ^ (2 * σ - 1)) / (2 * σ - 1) := by
  unfold regNorm
  have h : 2 * σ - 2 ≠ -1 := by intro h; apply hσ; linarith
  have hz : (0 : ℝ) ∉ Set.uIcc ε 1 := by
    rw [Set.uIcc_of_le hε1]; intro hm; exact absurd hm.1 (not_le.2 hε)
  rw [integral_rpow (Or.inr ⟨h, hz⟩)]
  have e : 2 * σ - 2 + 1 = 2 * σ - 1 := by ring
  rw [e, Real.one_rpow]

theorem regNorm_half {ε : ℝ} (hε : 0 < ε) :
    regNorm (1 / 2) ε = -Real.log ε := by
  unfold regNorm
  have : (fun x : ℝ => x ^ (2 * (1 / 2 : ℝ) - 2)) = fun x => x⁻¹ := by
    funext x; rw [show 2 * (1 / 2 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  rw [this, integral_inv_of_pos hε one_pos]
  simp

/-- Above the line: the state is normalizable, a bound state. -/
theorem regNorm_tendsto_of_gt {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (regNorm σ) (𝓝[>] 0) (𝓝 (1 / (2 * σ - 1))) := by
  have hpos : 0 < 2 * σ - 1 := by linarith
  have hlim : Tendsto (fun ε : ℝ => ε ^ (2 * σ - 1)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (2 * σ - 1) (Or.inr hpos.le)).tendsto
    rw [Real.zero_rpow hpos.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have : Tendsto (fun ε : ℝ => (1 - ε ^ (2 * σ - 1)) / (2 * σ - 1)) (𝓝[>] 0)
      (𝓝 ((1 - 0) / (2 * σ - 1))) := (tendsto_const_nhds.sub hlim).div_const _
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
  exact (regNorm_of_ne hε.1 hε.2.le (by linarith)).symm

/-- On the line: the regulated norm is exactly `log (1/ε)`, so the renormalized norm is `1`. -/
theorem renormalized_norm_half {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    regNorm (1 / 2) ε / (-Real.log ε) = 1 := by
  rw [regNorm_half hε]
  have h : 0 < -Real.log ε := neg_pos.2 (Real.log_neg hε hε1)
  rw [neg_div_neg_eq]
  exact div_self (by linarith)

/-- Below the line: the regulated norm diverges like a power, no logarithmic counterterm helps. -/
theorem regNorm_tendsto_atTop_of_lt {σ : ℝ} (hσ : σ < 1 / 2) :
    Tendsto (regNorm σ) (𝓝[>] 0) atTop := by
  have hneg : 2 * σ - 1 < 0 := by linarith
  have hlim : Tendsto (fun ε : ℝ => ε ^ (2 * σ - 1)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero hneg
  have h2 : Tendsto (fun ε : ℝ => (ε ^ (2 * σ - 1) - 1) / (1 - 2 * σ)) (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ (2 * σ - 1) - 1) (𝓝[>] 0) atTop :=
      tendsto_atTop_add_const_right _ (-1) hlim |>.congr (fun _ => by ring)
    exact h1.atTop_div_const (by linarith)
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
  rw [regNorm_of_ne hε.1 hε.2.le (by linarith)]
  have h1 : 2 * σ - 1 ≠ 0 := by linarith
  have h2 : 1 - 2 * σ ≠ 0 := by linarith
  rw [div_eq_div_iff h2 h1]
  ring

/-- The Cesàro mean of a plane wave over the scale window `[0, L]`. -/
noncomputable def cesaroMean (Δ L : ℝ) : ℂ := (1 / (L : ℂ)) * ∫ u in (0 : ℝ)..L, Complex.exp (Complex.I * (Δ * u))

theorem cesaroMean_zero {L : ℝ} (hL : 0 < L) : cesaroMean 0 L = 1 := by
  unfold cesaroMean
  have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  simp
  field_simp

/-- **Cesàro orthonormality.** Distinct on-line frequencies are orthogonal in the Cesàro
inner product: the mean of `e^{iΔu}` over `[0, L]` tends to `0` for `Δ ≠ 0`. -/
theorem cesaroMean_tendsto_zero {Δ : ℝ} (hΔ : Δ ≠ 0) :
    Tendsto (cesaroMean Δ) atTop (𝓝 0) := by
  have hc : Complex.I * (Δ : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hΔ)
  have key : ∀ L : ℝ, ∫ u in (0 : ℝ)..L, Complex.exp (Complex.I * (Δ * u)) =
      (Complex.exp (Complex.I * Δ * L) - 1) / (Complex.I * Δ) := by
    intro L
    have := integral_exp_mul_complex (a := 0) (b := L) hc
    simpa [mul_assoc] using this
  have hb : ∀ L : ℝ, ‖(Complex.exp (Complex.I * Δ * L) - 1) / (Complex.I * Δ)‖ ≤ 2 / |Δ| := by
    intro L
    rw [norm_div, Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    calc ‖Complex.exp (Complex.I * Δ * L) - 1‖ ≤ ‖Complex.exp (Complex.I * Δ * L)‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
      _ = 2 := by
          have : Complex.I * Δ * L = ((Δ * L : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hbound : ∀ᶠ L : ℝ in atTop, ‖cesaroMean Δ L‖ ≤ (2 / |Δ|) * L⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    unfold cesaroMean
    rw [key L, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    have := hb L
    calc 1 / L * ‖(Complex.exp (Complex.I * Δ * L) - 1) / (Complex.I * Δ)‖ ≤ 1 / L * (2 / |Δ|) := by
          gcongr
      _ = (2 / |Δ|) * L⁻¹ := by ring
  have hlim : Tendsto (fun L : ℝ => (2 / |Δ|) * L⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (2 / |Δ|)
  exact squeeze_zero_norm' hbound hlim

/-- The Pasterski–Shao radial pairing at celestial dimension `c` in one boundary dimension:
`∫_1^{1/ε} ω^{2c-2} dω`, the energy integral cut off at `ω = 1/ε`. -/
noncomputable def radialNorm (c ε : ℝ) : ℝ := ∫ ω in (1 : ℝ)..ε⁻¹, ω ^ (2 * c - 2)

/-- **The bound-state norm is the radial pairing at the shadow dimension.** With `x = 1/ω`, the
regulated norm of the state `x^(σ-1)` on `[ε, 1]` equals the Pasterski–Shao radial pairing at
`c = 1 - σ`. So normalizability of the bound state and delta-normalizability of the massless mode
are the same condition on the exponent: the log-divergent boundary is `Re c = 1/2 = σ`. -/
theorem regNorm_eq_radialNorm {σ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    regNorm σ ε = radialNorm (1 - σ) ε := by
  unfold regNorm radialNorm
  by_cases hσ : σ = 1 / 2
  · subst hσ
    have h1 : (fun x : ℝ => x ^ (2 * (1 / 2 : ℝ) - 2)) = fun x => x⁻¹ := by
      funext x; rw [show 2 * (1 / 2 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
    have h2 : (fun ω : ℝ => ω ^ (2 * (1 - 1 / 2 : ℝ) - 2)) = fun ω => ω⁻¹ := by
      funext ω; rw [show 2 * (1 - 1 / 2 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
    rw [h1, h2, integral_inv_of_pos hε one_pos, integral_inv_of_pos one_pos (inv_pos.2 hε)]
    simp
  · have hz1 : (0 : ℝ) ∉ Set.uIcc ε 1 := by
      rw [Set.uIcc_of_le hε1]; intro hm; exact absurd hm.1 (not_le.2 hε)
    have hz2 : (0 : ℝ) ∉ Set.uIcc 1 ε⁻¹ := by
      rw [Set.uIcc_of_le (one_le_inv_iff₀.2 ⟨hε, hε1⟩)]; intro hm; linarith [hm.1]
    have n1 : 2 * σ - 2 ≠ -1 := by intro h; apply hσ; linarith
    have n2 : 2 * (1 - σ) - 2 ≠ -1 := by intro h; apply hσ; linarith
    rw [integral_rpow (Or.inr ⟨n1, hz1⟩), integral_rpow (Or.inr ⟨n2, hz2⟩)]
    have e1 : 2 * σ - 2 + 1 = 2 * σ - 1 := by ring
    have e2 : 2 * (1 - σ) - 2 + 1 = 1 - 2 * σ := by ring
    rw [e1, e2, Real.one_rpow, Real.one_rpow, Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]
    have h1 : 2 * σ - 1 ≠ 0 := by intro h; apply hσ; linarith
    have h2 : 1 - 2 * σ ≠ 0 := by intro h; apply hσ; linarith
    have e3 : -(1 - 2 * σ) = 2 * σ - 1 := by ring
    rw [e3, div_eq_div_iff h1 h2]
    ring

#print axioms regNorm_of_ne
#print axioms regNorm_tendsto_of_gt
#print axioms renormalized_norm_half
#print axioms regNorm_tendsto_atTop_of_lt
#print axioms cesaroMean_tendsto_zero
#print axioms regNorm_eq_radialNorm

end GppBoundStateRenormalization
