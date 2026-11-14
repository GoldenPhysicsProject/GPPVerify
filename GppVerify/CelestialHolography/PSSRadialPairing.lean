import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import GppVerify.CelestialHolography.KleinGordonPairing

/-!
# PSS File 3: the radial pairing of conformal primary wavefunctions

Pasterski–Shao, arXiv:1705.01027, §4.2, eqs. (4.7)–(4.8). The Klein–Gordon pairing of two
massless conformal primaries with `Δ_j = c + iν_j` reduces to an angular delta times the radial
integral

  `∫_0^∞ dω ω^{2c − d + i(ν₁ − ν₂) − 1}`.                                    (4.7)

This file formalises the radial integral and what it does, for every real `c`, and the reduction
as far as it goes.

## The radial integral (unconditional)

Write `s = (2c − d) + iν`, `ν = ν₁ − ν₂`, and truncate to `[1/R, R]`:
`radialTrunc s R = ∫_{1/R}^{R} ω^{s−1} dω`.

* `not_integrableOn_radial`: for **every** `s`, the integrand `ω^{s−1}` is not Lebesgue
  integrable on `(0, ∞)`. In particular (4.7) never converges as a Lebesgue integral, not even at
  `c = d/2`; at `c = d/2` it exists only as a distribution.
* `radialTrunc_eq`: closed form `(R^s − R^{−s})/s` for `s ≠ 0`.
* `offDiagonalBounded_iff`: **the dichotomy.** The truncated radial integral stays bounded as
  `R → ∞` at every off-diagonal point `ν ≠ 0` **iff** `2c − d = 0`. For `2c − d ≠ 0` it grows like
  `R^{|2c−d|}` at every `ν`. The parameter `c` is free throughout; the theorem *selects*
  `c = d/2`, it does not assume it (`radial_offDiagonalBounded_iff`).
* `tendsto_smeared_radialTrunc`: **the distributional identity (4.8)** in Mellin form. At
  `c = d/2`, for every continuous integrable `ψ` with integrable Fourier transform (in particular
  every Schwartz function),
  `∫ ψ(ν) (∫_{1/R}^{R} ω^{iν−1} dω) dν → 2π ψ(0)` as `R → ∞`, i.e. `∫_0^∞ ω^{iν−1} dω = 2π δ(ν)`.

## The reduction (4.7) (named obligation; see the end of the file)

`PSSPacketPlancherel d` states the Klein–Gordon pairing of smooth compactly supported
superpositions of the plane waves `e^{iω q(w)·X}` exactly, with constant `(2π)^{d+1} 2^{1−d}` and
radial weight `ω^{1−d}` from the Jacobian of `(ω, w) ↦ ω q⃗(w)`. It is OPEN: never asserted,
never `sorry`. Conditional on it, `kgPairing_mellinPacket` proves the (4.7) shape: the pairing of
two Mellin-weighted packets is the angular overlap times the windowed radial integral with
exponent `2c − d + i(ν₁ − ν₂) − 1`.

The wall: imports only Mathlib and PSS Files 1–2. No arithmetic object appears.
-/

namespace GppPSSRadialPairing

open Complex MeasureTheory Set Filter Topology FourierTransform
open GppConformalPrimaryWavefunction GppKleinGordonPairing

/-! ## The truncated radial integral -/

/-- `∫_{1/R}^{R} ω^{s−1} dω`. -/
noncomputable def radialTrunc (s : ℂ) (R : ℝ) : ℂ := ∫ ω in (1 / R)..R, (ω : ℂ) ^ (s - 1)

theorem zero_notMem_uIcc {R : ℝ} (hR : 0 < R) : (0 : ℝ) ∉ uIcc (1 / R) R := by
  intro h
  rcases mem_uIcc.mp h with h | h
  · have : 0 < 1 / R := by positivity
    linarith [h.1]
  · linarith [h.2]

/-- **Closed form.** For `s ≠ 0` and `R > 0`, `radialTrunc s R = (R^s − (1/R)^s)/s`. -/
theorem radialTrunc_eq {s : ℂ} (hs : s ≠ 0) {R : ℝ} (hR : 0 < R) :
    radialTrunc s R = ((R : ℂ) ^ s - ((1 / R : ℝ) : ℂ) ^ s) / s := by
  unfold radialTrunc
  have hr : s - 1 ≠ -1 := by intro h; apply hs; linear_combination h
  rw [integral_cpow (Or.inr ⟨hr, zero_notMem_uIcc hR⟩)]
  simp only [sub_add_cancel]

theorem norm_cpow_inv {R : ℝ} (hR : 0 < R) (s : ℂ) :
    ‖((1 / R : ℝ) : ℂ) ^ s‖ = R ^ (-s.re) := by
  rw [norm_cpow_eq_rpow_re_of_pos (by positivity), one_div, Real.inv_rpow hR.le,
    Real.rpow_neg hR.le]

/-- **Growth.** `|R^{Re s} − R^{−Re s}| / ‖s‖ ≤ ‖radialTrunc s R‖`. -/
theorem norm_radialTrunc_ge {s : ℂ} (hs : s ≠ 0) {R : ℝ} (hR : 0 < R) :
    |R ^ s.re - R ^ (-s.re)| / ‖s‖ ≤ ‖radialTrunc s R‖ := by
  rw [radialTrunc_eq hs hR, norm_div]
  have h1 : ‖(R : ℂ) ^ s‖ = R ^ s.re := norm_cpow_eq_rpow_re_of_pos hR s
  have h2 := norm_cpow_inv hR s
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  apply div_le_div_of_nonneg_right _ hsn.le
  rw [← h1, ← h2]
  exact abs_norm_sub_norm_le _ _

/-- **Bounded on the critical line.** If `Re s = 0`, `s ≠ 0`, then `‖radialTrunc s R‖ ≤ 2/‖s‖`. -/
theorem norm_radialTrunc_le_of_re_eq_zero {s : ℂ} (hs : s ≠ 0) (hre : s.re = 0) {R : ℝ}
    (hR : 0 < R) : ‖radialTrunc s R‖ ≤ 2 / ‖s‖ := by
  rw [radialTrunc_eq hs hR, norm_div]
  have h1 : ‖(R : ℂ) ^ s‖ = 1 := by rw [norm_cpow_eq_rpow_re_of_pos hR s, hre, Real.rpow_zero]
  have h2 : ‖((1 / R : ℝ) : ℂ) ^ s‖ = 1 := by rw [norm_cpow_inv hR s, hre, neg_zero, Real.rpow_zero]
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  apply div_le_div_of_nonneg_right _ hsn.le
  calc ‖(R : ℂ) ^ s - ((1 / R : ℝ) : ℂ) ^ s‖ ≤ ‖(R : ℂ) ^ s‖ + ‖((1 / R : ℝ) : ℂ) ^ s‖ :=
        norm_sub_le _ _
    _ = 2 := by rw [h1, h2]; norm_num

/-! ## The radial integrand is never integrable -/

/-- **(4.7) never converges as a Lebesgue integral.** For every complex `s`,
`ω ↦ ω^{s−1}` is not integrable on `(0, ∞)`. -/
theorem not_integrableOn_radial (s : ℂ) :
    ¬ IntegrableOn (fun ω : ℝ => (ω : ℂ) ^ (s - 1)) (Ioi 0) := by
  intro h
  have hn : IntegrableOn (fun ω : ℝ => ‖(ω : ℂ) ^ (s - 1)‖) (Ioi 0) := h.norm
  have hcongr : IntegrableOn (fun ω : ℝ => ω ^ (s.re - 1)) (Ioi 0) := by
    refine hn.congr_fun (fun ω hω => ?_) measurableSet_Ioi
    show ‖(ω : ℂ) ^ (s - 1)‖ = ω ^ (s.re - 1)
    rw [norm_cpow_eq_rpow_re_of_pos hω]
    simp
  exact not_integrableOn_Ioi_rpow _ hcongr

/-- In PSS variables: for every real `c`, every `d` and every `ν`,
`∫_0^∞ ω^{2c − d + iν − 1} dω` is not a Lebesgue integral, including at `c = d/2`. -/
theorem radial_not_integrable (c : ℝ) (d : ℕ) (ν : ℝ) :
    ¬ IntegrableOn (fun ω : ℝ => (ω : ℂ) ^ (((2 * c - d : ℝ) : ℂ) + ν * I - 1)) (Ioi 0) :=
  not_integrableOn_radial _

/-! ## The dichotomy -/

/-- Off-diagonal boundedness: at every `ν ≠ 0`, the truncated radial integral with exponent
`α + iν` stays bounded as `R → ∞`. -/
def OffDiagonalBounded (α : ℝ) : Prop :=
  ∀ ν : ℝ, ν ≠ 0 → ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ‖radialTrunc ((α : ℂ) + ν * I) R‖ ≤ C

theorem ne_zero_of_im_ne_zero {α ν : ℝ} (hν : ν ≠ 0) : ((α : ℂ) + ν * I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hν this

/-- **The dichotomy.** Off-diagonal boundedness holds **iff** `α = 0`. -/
theorem offDiagonalBounded_iff (α : ℝ) : OffDiagonalBounded α ↔ α = 0 := by
  constructor
  · intro h
    by_contra hα
    obtain ⟨C, hC⟩ := h 1 one_ne_zero
    set s : ℂ := (α : ℂ) + (1 : ℝ) * I with hs
    have hs0 : s ≠ 0 := ne_zero_of_im_ne_zero one_ne_zero
    have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    have hsre : s.re = α := by simp [hs]
    have ha : 0 < |α| := abs_pos.mpr hα
    -- R^{|α|} → ∞, pick R with R^{|α|} > C‖s‖ + 1
    have htend : Tendsto (fun R : ℝ => R ^ |α|) atTop atTop := tendsto_rpow_atTop ha
    obtain ⟨R, hR⟩ := ((htend.eventually_gt_atTop (C * ‖s‖ + 1)).and
      (eventually_ge_atTop 1)).exists
    have hR0 : 0 < R := by linarith [hR.2]
    have hge := norm_radialTrunc_ge hs0 hR0
    rw [hsre] at hge
    have hbig : R ^ |α| - 1 ≤ |R ^ α - R ^ (-α)| := by
      have h1 : R ^ (-|α|) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR.2 (by linarith)
      rcases le_or_gt 0 α with hpos | hneg
      · rw [abs_of_nonneg hpos] at h1 ⊢
        have : R ^ α - R ^ (-α) ≥ 0 := by
          have := Real.rpow_le_rpow_of_exponent_le hR.2 (by linarith : -α ≤ α); linarith
        rw [abs_of_nonneg this]; linarith
      · rw [abs_of_neg hneg] at h1 ⊢
        rw [neg_neg] at h1
        have : R ^ α - R ^ (-α) ≤ 0 := by
          have := Real.rpow_le_rpow_of_exponent_le hR.2 (by linarith : α ≤ -α); linarith
        rw [abs_of_nonpos this]; linarith
    have hCR := hC R hR.2
    have h3 : R ^ |α| - 1 ≤ ‖radialTrunc s R‖ * ‖s‖ := hbig.trans ((div_le_iff₀ hsn).mp hge)
    have h4 : ‖radialTrunc s R‖ * ‖s‖ ≤ C * ‖s‖ := mul_le_mul_of_nonneg_right hCR hsn.le
    linarith [hR.1]
  · rintro rfl ν hν
    refine ⟨2 / ‖((0 : ℝ) : ℂ) + ν * I‖, fun R hR => ?_⟩
    exact norm_radialTrunc_le_of_re_eq_zero (ne_zero_of_im_ne_zero hν) (by simp)
      (by linarith)

/-- **In PSS variables.** For real `c` and `d`, off-diagonal boundedness of the radial integral
with exponent `2c − d + iν − 1` holds iff `c = d/2`. -/
theorem radial_offDiagonalBounded_iff (c : ℝ) (d : ℕ) :
    OffDiagonalBounded (2 * c - d) ↔ c = d / 2 := by
  rw [offDiagonalBounded_iff]
  constructor <;> intro h <;> linarith

/-! ## The distributional identity (4.8) -/

theorem ae_ne_zero : ∀ᵐ ν : ℝ, ν ≠ 0 := by
  rw [ae_iff]
  simp [measure_singleton]

/-- On the critical line, after `ω = e^u`: `radialTrunc (iν) R = ∫_{−log R}^{log R} e^{iνu} du`
for `ν ≠ 0` and `R ≥ 1`. -/
theorem radialTrunc_imag {ν : ℝ} (hν : ν ≠ 0) {R : ℝ} (hR : 1 ≤ R) :
    radialTrunc (ν * I) R = ∫ u in (-Real.log R)..(Real.log R), cexp ((ν * I : ℂ) * u) := by
  have hR0 : 0 < R := by linarith
  have hs : (ν : ℂ) * I ≠ 0 := by simpa using ne_zero_of_im_ne_zero (α := 0) hν
  rw [radialTrunc_eq hs hR0, integral_exp_mul_complex hs]
  congr 1
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hR'ne : ((1 / R : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 1 / R := by positivity
    exact_mod_cast this.ne'
  rw [cpow_def_of_ne_zero hRne, cpow_def_of_ne_zero hR'ne, ← ofReal_log hR0.le,
    ← ofReal_log (by positivity), one_div, Real.log_inv]
  push_cast
  ring_nf

/-- **(4.8), distributional form.** For continuous integrable `ψ` with integrable Fourier
transform (every Schwartz function qualifies),
`∫ ψ(ν) · radialTrunc (iν) R dν → 2π ψ(0)` as `R → ∞`. -/
theorem tendsto_smeared_radialTrunc {ψ : ℝ → ℂ} (hc : Continuous ψ) (hi : Integrable ψ)
    (hF : Integrable (𝓕 ψ)) :
    Tendsto (fun R : ℝ => ∫ ν, ψ ν * radialTrunc (ν * I) R) atTop
      (𝓝 (2 * Real.pi * ψ 0)) := by
  set φ : ℝ → ℂ := fun u => ∫ ν, ψ ν * cexp ((ν * I : ℂ) * u) with hφ
  -- φ is the inverse Fourier transform, rescaled
  have hφeq : ∀ u, φ u = 𝓕⁻ ψ (u / (2 * Real.pi)) := by
    intro u
    rw [Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    congr 2
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  have hinvInt : Integrable (𝓕⁻ ψ) := by
    have : 𝓕⁻ ψ = fun w => 𝓕 ψ (-w) := funext (Real.fourierInv_eq_fourier_neg ψ)
    rw [this]; exact hF.comp_neg
  have hφInt : Integrable φ := by
    have : φ = fun u => 𝓕⁻ ψ (u / (2 * Real.pi)) := funext hφeq
    rw [this]; exact hinvInt.comp_div (by positivity)
  have hφtot : ∫ u, φ u = 2 * Real.pi * ψ 0 := by
    have : φ = fun u => 𝓕⁻ ψ (u / (2 * Real.pi)) := funext hφeq
    rw [this, Measure.integral_comp_div, abs_of_pos (by positivity)]
    have h0 : ∫ w, 𝓕⁻ ψ w = 𝓕 (𝓕⁻ ψ) 0 := by
      rw [Real.fourier_eq]; simp
    rw [h0, hi.fourier_fourierInv_eq hF hc.continuousAt]
    simp [Complex.real_smul]
  -- Fubini on [−L, L]
  have hstep : ∀ R : ℝ, 1 ≤ R →
      ∫ ν, ψ ν * radialTrunc (ν * I) R = ∫ u in (-Real.log R)..(Real.log R), φ u := by
    intro R hR
    set L := Real.log R with hL
    have hL0 : 0 ≤ L := Real.log_nonneg hR
    have h1 : ∫ ν, ψ ν * radialTrunc (ν * I) R =
        ∫ ν, ∫ u in Ioc (-L) L, ψ ν * cexp ((ν * I : ℂ) * u) := by
      refine integral_congr_ae (ae_ne_zero.mono fun ν hν => ?_)
      show ψ ν * radialTrunc (ν * I) R = ∫ u in Ioc (-L) L, ψ ν * cexp ((ν * I : ℂ) * u)
      rw [radialTrunc_imag hν hR, intervalIntegral.integral_of_le (show -L ≤ L by linarith),
        ← integral_const_mul]
    have hint : Integrable (Function.uncurry fun (ν u : ℝ) => ψ ν * cexp ((ν * I : ℂ) * u))
        (volume.prod (volume.restrict (Ioc (-L) L))) := by
      have hb : Integrable (fun z : ℝ × ℝ => ‖ψ z.1‖ * (1 : ℝ))
          (volume.prod (volume.restrict (Ioc (-L) L))) := by
        have : IsFiniteMeasure (volume.restrict (Ioc (-L) L)) := by
          rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
        exact hi.norm.mul_prod (integrable_const (1 : ℝ))
      refine hb.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        exact (hc.comp continuous_fst).mul (by fun_prop)
      · obtain ⟨ν, u⟩ := z
        show ‖ψ ν * cexp ((ν * I : ℂ) * u)‖ ≤ ‖ψ ν‖ * 1
        rw [norm_mul, show ((ν : ℂ) * I) * (u : ℂ) = ((ν * u : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I]
    rw [h1, integral_integral_swap hint, intervalIntegral.integral_of_le (show -L ≤ L by linarith)]
  have hlim : Tendsto (fun R : ℝ => ∫ u in (-Real.log R)..(Real.log R), φ u) atTop
      (𝓝 (∫ u, φ u)) :=
    intervalIntegral_tendsto_integral hφInt
      (tendsto_neg_atTop_atBot.comp Real.tendsto_log_atTop) Real.tendsto_log_atTop
  rw [← hφtot]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with R hR
  exact (hstep R hR).symm

/-! ## The reduction (4.7): plane-wave packets -/

/-- A superposition of the massless plane waves `e^{iω q(w̃)·X}` (File 1's `planeWave` at
`σ = 1`, `ε = 0`) with profile `F(ω, w̃)`. -/
noncomputable def wavePacket {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ) (X : Spacetime d) : ℂ :=
  ∫ ω in Ioi (0 : ℝ), ∫ w, F ω w * cexp (I * ω * mink (nullVec w) X)

/-- **Named obligation (OPEN, not asserted): the plane-wave Plancherel identity behind (4.7).**
For smooth profiles `F, G` with compact support inside `{ω > 0}`, the Klein–Gordon pairing (3.6)
of the two packets, on any slice, is

  `(2π)^{d+1} · 2^{1−d} · ∫_{ω>0} ∫ ω^{1−d} F(ω, w̃) conj G(ω, w̃) dw̃ dω`.

Derivation, for the record. On a slice the packet is a spatial Fourier integral in
`k⃗ = ω q⃗(w̃)` with energy `E = ω(1 + |w̃|²)`. The pairing gives `(E₁ + E₂)(2π)^{d+1} δ(k⃗₁ − k⃗₂)`.
The Jacobian of `(ω, w̃) ↦ k⃗` is `2^d ω^d (1 + |w̃|²)` (checked by hand at `d = 1`:
`|det| = 2ω(1 + w²)`), which leaves `2^{1−d} ω^{1−d}`. Proving it needs Fourier inversion in
`d + 1` variables and this change of variables. -/
def PSSPacketPlancherel (d : ℕ) : Prop :=
  ∀ F G : ℝ → (Fin d → ℝ) → ℂ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry G) →
    HasCompactSupport (Function.uncurry F) → HasCompactSupport (Function.uncurry G) →
    tsupport (Function.uncurry F) ⊆ Ioi 0 ×ˢ univ →
    tsupport (Function.uncurry G) ⊆ Ioi 0 ×ˢ univ →
    ∀ t : ℝ, kgPairing t (wavePacket F) (wavePacket G) =
      (2 * Real.pi) ^ (d + 1) * (2 / 2 ^ d) *
        ∫ ω in Ioi (0 : ℝ), ∫ w, (ω : ℂ) ^ (1 - (d : ℂ)) * (F ω w * starRingEnd ℂ (G ω w))

/-- For `ω > 0`, `conj (ω^z) = ω^{conj z}`. -/
theorem conj_ofReal_cpow {ω : ℝ} (hω : 0 < ω) (z : ℂ) :
    starRingEnd ℂ ((ω : ℂ) ^ z) = (ω : ℂ) ^ (starRingEnd ℂ z) := by
  have harg : (ω : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hω.le]; exact Real.pi_ne_zero.symm
  have h := conj_cpow (ω : ℂ) (starRingEnd ℂ z) harg
  rw [conj_ofReal, conj_conj] at h
  exact h.symm

/-- **The radial weight of (4.7).** For `ω > 0` and `Δ_j = c + iν_j`,
`ω^{1−d} · ω^{Δ₁−1} · conj(ω^{Δ₂−1}) = ω^{2c − d + i(ν₁ − ν₂) − 1}`. -/
theorem radial_weight {ω : ℝ} (hω : 0 < ω) (d : ℕ) (c ν₁ ν₂ : ℝ) :
    (ω : ℂ) ^ (1 - (d : ℂ)) * ((ω : ℂ) ^ ((c : ℂ) + ν₁ * I - 1) *
      starRingEnd ℂ ((ω : ℂ) ^ ((c : ℂ) + ν₂ * I - 1))) =
      (ω : ℂ) ^ (((2 * c - d : ℝ) : ℂ) + (ν₁ - ν₂ : ℝ) * I - 1) := by
  have hω0 : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  rw [conj_ofReal_cpow hω, ← cpow_add _ _ hω0, ← cpow_add _ _ hω0]
  congr 1
  apply Complex.ext <;> simp <;> ring

/-- **The reduction (4.7), conditional on `PSSPacketPlancherel`.** Take Mellin-weighted packets
`F_j(ω, w̃) = a_j(ω) f_j(w̃)` with `a_j(ω) = χ_j(ω) ω^{Δ_j − 1}` on `ω > 0`, `Δ_j = c + iν_j`,
and the regularity the obligation asks for. Then the pairing is the angular overlap times the
windowed radial integral with exponent `2c − d + i(ν₁ − ν₂) − 1`:

  `(2π)^{d+1} 2^{1−d} ⟨f₁, f₂⟩ ∫_{ω>0} χ₁ conj χ₂ ω^{2c − d + i(ν₁−ν₂) − 1} dω`.

The window `χ₁ conj χ₂` replaces the sharp cut-off `[1/R, R]` of `radialTrunc`. -/
theorem kgPairing_mellinPacket {d : ℕ} (hP : PSSPacketPlancherel d)
    {a₁ a₂ χ₁ χ₂ : ℝ → ℂ} {f₁ f₂ : (Fin d → ℝ) → ℂ} (c ν₁ ν₂ : ℝ)
    (hs₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry fun ω w => a₁ ω * f₁ w))
    (hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry fun ω w => a₂ ω * f₂ w))
    (hc₁ : HasCompactSupport (Function.uncurry fun ω w => a₁ ω * f₁ w))
    (hc₂ : HasCompactSupport (Function.uncurry fun ω w => a₂ ω * f₂ w))
    (ht₁ : tsupport (Function.uncurry fun ω w => a₁ ω * f₁ w) ⊆ Ioi 0 ×ˢ univ)
    (ht₂ : tsupport (Function.uncurry fun ω w => a₂ ω * f₂ w) ⊆ Ioi 0 ×ˢ univ)
    (ha₁ : ∀ ω : ℝ, 0 < ω → a₁ ω = χ₁ ω * (ω : ℂ) ^ ((c : ℂ) + ν₁ * I - 1))
    (ha₂ : ∀ ω : ℝ, 0 < ω → a₂ ω = χ₂ ω * (ω : ℂ) ^ ((c : ℂ) + ν₂ * I - 1)) (t : ℝ) :
    kgPairing t (wavePacket fun ω w => a₁ ω * f₁ w) (wavePacket fun ω w => a₂ ω * f₂ w) =
      (2 * Real.pi) ^ (d + 1) * (2 / 2 ^ d) * (∫ w, f₁ w * starRingEnd ℂ (f₂ w)) *
        ∫ ω in Ioi (0 : ℝ), χ₁ ω * starRingEnd ℂ (χ₂ ω) *
          (ω : ℂ) ^ (((2 * c - d : ℝ) : ℂ) + (ν₁ - ν₂ : ℝ) * I - 1) := by
  rw [hP _ _ hs₁ hs₂ hc₁ hc₂ ht₁ ht₂ t]
  have hinner : ∀ ω : ℝ, (∫ w, (ω : ℂ) ^ (1 - (d : ℂ)) *
      (a₁ ω * f₁ w * starRingEnd ℂ (a₂ ω * f₂ w))) =
      ((ω : ℂ) ^ (1 - (d : ℂ)) * (a₁ ω * starRingEnd ℂ (a₂ ω))) *
        ∫ w, f₁ w * starRingEnd ℂ (f₂ w) := by
    intro ω
    rw [← integral_const_mul]
    congr 1; funext w; rw [map_mul]; ring
  simp_rw [hinner]
  rw [integral_mul_const]
  have hrad : ∫ ω in Ioi (0 : ℝ), (ω : ℂ) ^ (1 - (d : ℂ)) * (a₁ ω * starRingEnd ℂ (a₂ ω)) =
      ∫ ω in Ioi (0 : ℝ), χ₁ ω * starRingEnd ℂ (χ₂ ω) *
        (ω : ℂ) ^ (((2 * c - d : ℝ) : ℂ) + (ν₁ - ν₂ : ℝ) * I - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun ω hω => ?_)
    have hω' : (0 : ℝ) < ω := hω
    rw [ha₁ ω hω', ha₂ ω hω', ← radial_weight hω' d c ν₁ ν₂, map_mul]
    ring
  rw [hrad]
  ring

end GppPSSRadialPairing

#print axioms GppPSSRadialPairing.radialTrunc_eq
#print axioms GppPSSRadialPairing.not_integrableOn_radial
#print axioms GppPSSRadialPairing.radial_not_integrable
#print axioms GppPSSRadialPairing.offDiagonalBounded_iff
#print axioms GppPSSRadialPairing.radial_offDiagonalBounded_iff
#print axioms GppPSSRadialPairing.tendsto_smeared_radialTrunc
#print axioms GppPSSRadialPairing.radial_weight
#print axioms GppPSSRadialPairing.kgPairing_mellinPacket
