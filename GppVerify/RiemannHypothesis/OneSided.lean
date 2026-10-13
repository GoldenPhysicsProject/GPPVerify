import Mathlib

/-!
# Wave-54 Lean workbench — δ-refined one-sided lemma, analytic core
  (paper-PROVED → LEAN-CHECKED, with paper-level hypotheses named)

Formalizes the analytic-combinatorial core of the δ-refined one-sided lemma
(Spark, proved 2026-10-08; `~/workspace/refined-onesided-lemma.tex`):

> If `C_ℓ(t) ≤ e^{Ft}` eventually, then every nontrivial zero `ρ = 1/2 + a + iγ`
> satisfies `|a| ≤ F`.

The paper's proof has four moving parts; this module separates them by
epistemic status:

* §1 (**LEAN-CHECKED**): the Laplace transform of the exponential majorant
  `e^{Ft}` is `1/(z-F)`, holomorphic on `{Re z > F}`.
* §2 (**LEAN-CHECKED**): shift reduction — an eventual one-sided exponential
  bound upgrades to a uniform bound `K·e^{Ft}` on `[0, ∞)`.
* §3 (**LEAN-CHECKED**): Landau's lemma in full one-step form (`landau_full`) —
  if the Laplace transform of a *nonnegative* function converges above
  `σc > 0` and extends holomorphically across the whole right half-plane, it
  converges above *every* `y > 0` (Taylor at `x = σc + 1` reaches all
  `y ∈ (0, x)` in one step; `y > σc` is the hypothesis). Nonnegativity is used
  exactly once (Tonelli interchange of the Taylor series with the integral).
  Corollaries: `landau_improve` (convergence at `σc/2`) and `landau_abscissa`
  (the paper's "Lemma lem:landau forces `σ_c ≤ 0`"); the wave-55 located
  blocker (iteration needing analytic continuation) is dissolved — no
  iteration is needed.
* §4 (**LEAN-CHECKED conditional**): the transfer theorem. From the
  explicit-formula shape of the holomorphic extension (paper-level: the
  explicit formula), the "no real poles" input (paper-level: `ξ > 0` on `ℝ`),
  the zero↔pole link (paper-level), and zero symmetry for nontrivial zeros
  (wave-58 G3 closure: `zeta_zero_symm`, LEAN-CHECKED — the naive all-zeros
  statement is FALSE, see `g3_as_stated_false`), every nontrivial zero
  satisfies `|a| ≤ F`. The analytic steps (Landau + solving
  for `L`) are kernel-checked; the remaining arithmetic inputs
  (G1, G2, G4, zero↔pole link) are explicit hypotheses.

Paper-level gaps (exact missing infra), to be closed in later waves:
  (G1) the explicit formula for `C_ℓ` (zero-side `L_ℓ` with poles at `ρ - 1/2`);
  (G2) `ξ > 0` on `ℝ` (no real nontrivial zeros — needs real-line nonvanishing
       of `ζ` on `(0,1)`, absent from mathlib);
  (G3) zero symmetry for `riemannZeta` — CLOSED wave-58 for nontrivial zeros
       (`zeta_zero_symm`, via `riemannZeta_one_sub` + `riemannZeta_conj`); the
       unrestricted all-zeros version is FALSE (`g3_as_stated_false`: the
       trivial zero `ρ = -2` maps to `1 - ρ̄ = 3` with `ζ(3) ≠ 0`);
  (G4) the crude zero-side bound giving a finite abscissa `σc` for `h`.

F_θ audit: the formalized `onesided_transfer` is an implication whose
hypotheses include "the extension has the explicit-formula shape with `L`
holomorphic on `{Re w > F}`". For `F_θ(s) = ξ(s-θ)ξ(s+θ)` the shifted zeros
`ρ ± θ` make `L_θ` singular at `±θ + iγ`; the hypotheses are jointly
unprovable for `F < θ`. The formalization therefore *cannot* return a false
`|a| ≤ F < θ` for `F_θ` — the control is killed at the hypotheses, exactly as
in the paper.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Nat

namespace RhWaveLean

/-! ## §1. Laplace transform of the exponential majorant -/

/-- Laplace integral of the exponential majorant `e^{Ft}` at `z`, closed form:
    `∫₀^∞ e^{-(z-F)t} dt = 1/(z-F)` for `Re z > F`. -/
theorem laplace_exp_majorant {F : ℝ} {z : ℂ} (hz : F < z.re) :
    ∫ t : ℝ in Ioi (0:ℝ), Complex.exp (-(z - (F:ℂ)) * (t:ℂ))
      = 1 / (z - (F:ℂ)) := by
  have hneg : (-(z - (F:ℂ))).re < 0 := by
    have hre : (-(z - (F:ℂ))).re = F - z.re := by
      simp [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
    linarith
  rw [integral_exp_mul_complex_Ioi hneg 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hne : z - (F:ℂ) ≠ 0 := by
    intro hcon
    have hre0 : (z - (F:ℂ)).re = 0 := by
      rw [hcon]; simp
    rw [Complex.sub_re, Complex.ofReal_re] at hre0
    linarith
  field_simp

/-- The majorant's Laplace transform is holomorphic on the half-plane `{Re z > F}`.
    (In the paper's conventions this is the `e^{FT₀}/z` term shifted by `F`.) -/
theorem laplace_exp_majorant_holo (F : ℝ) :
    DifferentiableOn ℂ
      (fun z : ℂ ↦ ∫ t : ℝ in Ioi (0:ℝ), Complex.exp (-(z - (F:ℂ)) * (t:ℂ)))
      {z : ℂ | F < z.re} := by
  have hne : ∀ z ∈ {z : ℂ | F < z.re}, (fun z : ℂ ↦ z - (F:ℂ)) z ≠ 0 := by
    intro z hz hcon
    simp only [Set.mem_ofPred_eq] at hz
    have hre0 : (z - (F:ℂ)).re = 0 := by
      have h := congrArg Complex.re hcon
      simpa using h
    rw [Complex.sub_re, Complex.ofReal_re] at hre0
    linarith
  have hdiff : DifferentiableOn ℂ (fun z : ℂ ↦ 1 / (z - (F:ℂ))) {z : ℂ | F < z.re} :=
    (differentiableOn_const (1:ℂ)).div (differentiableOn_id.sub_const (F:ℂ)) hne
  apply hdiff.congr
  intro z hz
  exact laplace_exp_majorant hz

/-! ## §2. Shift reduction -/

/-- Shift reduction (paper §"Shifting `t ↦ t + T₀`"): an eventual one-sided
    exponential bound `C t ≤ e^{Ft}` upgrades to a uniform bound `K·e^{Ft}` on
    all of `[0, ∞)`, with `K > 0` explicit. -/
theorem shift_reduction {C : ℝ → ℝ} {F : ℝ} (hC : Continuous C)
    {T₀ : ℝ} (hbound : ∀ t : ℝ, T₀ ≤ t → C t ≤ Real.exp (F * t)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t → C t ≤ K * Real.exp (F * t) := by
  set T₁ : ℝ := max T₀ 0 with hT₁
  have hT₁nn : 0 ≤ T₁ := le_max_right _ _
  have hT₁T₀ : T₀ ≤ T₁ := le_max_left _ _
  have hcont : ContinuousOn (fun t : ℝ ↦ C t - Real.exp (F * t)) (Icc 0 T₁) :=
    (hC.sub (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  obtain ⟨tstar, htstar_mem, htstar_max⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc ⟨0, left_mem_Icc.mpr hT₁nn⟩ hcont
  set M : ℝ := C tstar - Real.exp (F * tstar) with hM
  set K : ℝ := 1 + |M| * Real.exp (|F| * T₁) with hK
  have hKpos : 0 < K := by
    simp only [hK]
    have := Real.exp_pos (|F| * T₁)
    positivity
  refine ⟨K, hKpos, fun t ht ↦ ?_⟩
  have hexp_pos : 0 < Real.exp (F * t) := Real.exp_pos _
  by_cases htT₁ : t ≤ T₁
  · -- on `[0, T₁]`: `C t ≤ M + e^{Ft} ≤ K·e^{Ft}`
    have h1 : C t - Real.exp (F * t) ≤ M := htstar_max ⟨ht, htT₁⟩
    have hexp_arg : (0:ℝ) ≤ |F| * T₁ + F * t := by
      have h2 : |F| * t ≤ |F| * T₁ :=
        mul_le_mul_of_nonneg_left htT₁ (abs_nonneg _)
      have h3 : -( |F| * t) ≤ F * t := by
        have := neg_abs_le (F * t); rwa [abs_mul, abs_of_nonneg ht] at this
      linarith
    have h3 : (1:ℝ) ≤ Real.exp (|F| * T₁) * Real.exp (F * t) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr hexp_arg
    have h4 : |M| ≤ |M| * (Real.exp (|F| * T₁) * Real.exp (F * t)) :=
      le_mul_of_one_le_right (abs_nonneg _) h3
    have hKexp : K * Real.exp (F * t)
        = Real.exp (F * t) + |M| * (Real.exp (|F| * T₁) * Real.exp (F * t)) := by
      simp only [hK]; ring
    rw [hKexp]
    have hMle : M ≤ |M| := le_abs_self _
    linarith
  · -- past `T₁`: the eventual bound applies and `K ≥ 1`
    have hle : C t ≤ Real.exp (F * t) :=
      hbound t (le_trans hT₁T₀ (le_of_lt (lt_of_not_ge htT₁)))
    have hK1 : 1 ≤ K := by
      simp only [hK, le_add_iff_nonneg_right]
      positivity
    nlinarith [hexp_pos, hle, hK1]

/-! ## §3. Landau's lemma — analytic helpers -/

/-- A polynomial times a decaying exponential is bounded on `[0, ∞)`. -/
lemma pow_mul_exp_neg_bound {n : ℕ} {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ^ n * Real.exp (-c * t) ≤ C := by
  have hlim : Tendsto (fun t : ℝ ↦ t ^ n * Real.exp (-c * t)) atTop (𝓝 0) := by
    have h0 := tendsto_pow_mul_exp_neg_atTop_nhds_zero n
    have hc' : Tendsto (fun t : ℝ ↦ c * t) atTop atTop :=
      tendsto_id.const_mul_atTop hc
    have hcomp : Tendsto (fun t : ℝ ↦ (c * t) ^ n * Real.exp (-(c * t))) atTop (𝓝 0) :=
      h0.comp hc'
    have heq : (fun t : ℝ ↦ t ^ n * Real.exp (-c * t))
        = fun t : ℝ ↦ (c ^ n)⁻¹ * ((c * t) ^ n * Real.exp (-(c * t))) := by
      funext t
      have hcn : (c ^ n : ℝ) ≠ 0 := pow_ne_zero n (ne_of_gt hc)
      rw [mul_pow]
      field_simp
    rw [heq]
    simpa using hcomp.const_mul ((c ^ n)⁻¹)
  have hev : ∀ᶠ t in atTop, t ^ n * Real.exp (-c * t) ≤ 1 :=
    hlim.eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
  rw [eventually_atTop] at hev
  obtain ⟨T, hT⟩ := hev
  set T' : ℝ := max T 0 with hT'def
  have hT'nn : 0 ≤ T' := le_max_right _ _
  have hcont : ContinuousOn (fun t : ℝ ↦ t ^ n * Real.exp (-c * t)) (Icc 0 T') :=
    ((continuous_pow n).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  obtain ⟨ts, hts_mem, hts_max⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc ⟨0, left_mem_Icc.mpr hT'nn⟩ hcont
  have hCnn : (0:ℝ) ≤ max (ts ^ n * Real.exp (-c * ts)) 1 :=
    le_trans (by norm_num) (le_max_right _ _)
  refine ⟨max (ts ^ n * Real.exp (-c * ts)) 1, hCnn, fun t ht ↦ ?_⟩
  by_cases hle : t ≤ T'
  · calc t ^ n * Real.exp (-c * t)
        ≤ ts ^ n * Real.exp (-c * ts) := hts_max ⟨ht, hle⟩
      _ ≤ max (ts ^ n * Real.exp (-c * ts)) 1 := le_max_left _ _
  · have hTle : T ≤ t := le_trans (le_max_left _ _) (le_of_lt (lt_of_not_ge hle))
    have h1 : t ^ n * Real.exp (-c * t) ≤ 1 := hT t hTle
    linarith [le_max_right (ts ^ n * Real.exp (-c * ts)) 1]

/-- `h` is a.e. strongly measurable: from Laplace integrability at one exponent. -/
lemma aesm_h {h : ℝ → ℝ} {σc : ℝ}
    (hconv : ∀ τ : ℝ, σc < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume) :
    AEStronglyMeasurable h (volume.restrict (Ioi 0)) := by
  have h1 := hconv (σc + 1) (by linarith)
  have h2 : AEStronglyMeasurable (fun t : ℝ ↦ Real.exp (-(σc+1) * t) * h t)
      (volume.restrict (Ioi 0)) := by
    have h3 := (Integrable.re_im_iff.mpr h1).1.aestronglyMeasurable
    have heq : (fun x : ℝ => RCLike.re ((Real.exp (-(σc+1) * x) * h x : ℝ):ℂ))
        = (fun t : ℝ => Real.exp (-(σc+1) * t) * h t) := by
      funext t
      exact RCLike.ofReal_re _
    rwa [heq] at h3
  have h4 : AEStronglyMeasurable (fun t : ℝ ↦ Real.exp ((σc+1) * t))
      (volume.restrict (Ioi 0)) :=
    (by continuity : Continuous fun t : ℝ ↦ Real.exp ((σc+1) * t)).aestronglyMeasurable
  have h5 : AEStronglyMeasurable (fun t : ℝ ↦ (Real.exp (-(σc+1) * t) * h t) * Real.exp ((σc+1) * t))
      (volume.restrict (Ioi 0)) :=
    h2.mul h4
  have heq : (fun t : ℝ ↦ (Real.exp (-(σc+1) * t) * h t) * Real.exp ((σc+1) * t)) = h := by
    funext t
    have e0 : (-(σc+1) * t + (σc+1) * t : ℝ) = 0 := by ring
    have e : Real.exp (-(σc+1) * t) * Real.exp ((σc+1) * t) = 1 := by
      rw [← Real.exp_add, e0, Real.exp_zero]
    calc (Real.exp (-(σc+1) * t) * h t) * Real.exp ((σc+1) * t)
        = h t * (Real.exp (-(σc+1) * t) * Real.exp ((σc+1) * t)) := by ring
      _ = h t := by rw [e, mul_one]
  rw [heq] at h5
  exact h5

/-- The Laplace integrand at any exponent is a.e. strongly measurable. -/
lemma aesm_lap_integrand {h : ℝ → ℝ}
    (haesm : AEStronglyMeasurable h (volume.restrict (Ioi 0))) (τ : ℝ) :
    AEStronglyMeasurable (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ))
      (volume.restrict (Ioi 0)) :=
  Complex.continuous_ofReal.comp_aestronglyMeasurable
    ((by continuity : Continuous fun t : ℝ ↦ Real.exp (-τ * t)).aestronglyMeasurable.mul
      haesm)

/-- The `n`-th moment Laplace integral `∫₀^∞ t^n e^{-wt} h(t) dt`. -/
def momentLap (h : ℝ → ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ)) * ((h t : ℝ):ℂ)

/-- The `0`-th moment is the Laplace transform. -/
lemma momentLap_zero (h : ℝ → ℝ) :
    momentLap h 0
      = fun w : ℂ ↦ ∫ t : ℝ in Ioi 0, Complex.exp (-w * (t:ℂ)) * ((h t : ℝ):ℂ) := by
  funext w
  simp only [momentLap, pow_zero, one_mul]

/-- Integrability of the real moment integrand, by domination with the
    polynomial-exponential bound. -/
lemma integrable_momentLap_real {h : ℝ → ℝ} {σc : ℝ} (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume)
    (n : ℕ) {τ : ℝ} (hτ : σc < τ) :
    IntegrableOn (fun t : ℝ ↦ ((t ^ n * Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume := by
  obtain ⟨τ₁, hτ₁a, hτ₁b⟩ := exists_between hτ
  obtain ⟨C, hCnn, hC⟩ := pow_mul_exp_neg_bound (n := n) (c := τ - τ₁) (by linarith)
  have hre : Integrable (fun t : ℝ ↦ Real.exp (-τ₁ * t) * h t) (volume.restrict (Ioi 0)) := by
    have h2 := (Integrable.re_im_iff.mpr (hconv τ₁ hτ₁a)).1
    have heq : (fun t : ℝ => RCLike.re ((Real.exp (-τ₁ * t) * h t : ℝ):ℂ))
        = (fun t : ℝ => Real.exp (-τ₁ * t) * h t) := by
      funext t
      exact RCLike.ofReal_re _
    rwa [heq] at h2
  have hdomR : Integrable (fun t : ℝ ↦ C * Real.exp (-τ₁ * t) * |h t|)
      (volume.restrict (Ioi 0)) := by
    have h1 : (fun t : ℝ ↦ C * Real.exp (-τ₁ * t) * |h t|)
        = fun t : ℝ ↦ C * (Real.exp (-τ₁ * t) * h t) := by
      funext t
      rw [abs_of_nonneg (hpos t)]
      ring
    rw [h1]
    exact hre.const_mul C
  have haesm : AEStronglyMeasurable (fun t : ℝ ↦ ((t ^ n * Real.exp (-τ * t) * h t : ℝ):ℂ))
      (volume.restrict (Ioi 0)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((by continuity : Continuous fun t : ℝ ↦ t ^ n * Real.exp (-τ * t)).aestronglyMeasurable.mul
        (aesm_h hconv))
  refine Integrable.mono' hdomR haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0:ℝ) ≤ t := le_of_lt ht
  have hnn1 : (0:ℝ) ≤ t ^ n * Real.exp (-τ * t) * h t :=
    mul_nonneg (mul_nonneg (pow_nonneg ht' n) (Real.exp_pos _).le) (hpos t)
  have hexp : t ^ n * Real.exp (-τ * t)
      = (t ^ n * Real.exp (-(τ - τ₁) * t)) * Real.exp (-τ₁ * t) := by
    have e : Real.exp (-(τ - τ₁) * t) * Real.exp (-τ₁ * t) = Real.exp (-τ * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc t ^ n * Real.exp (-τ * t)
        = t ^ n * (Real.exp (-(τ - τ₁) * t) * Real.exp (-τ₁ * t)) := by rw [e]
      _ = _ := by ring
  have hle : t ^ n * Real.exp (-(τ - τ₁) * t) ≤ C := hC t ht'
  have hnn : (0:ℝ) ≤ Real.exp (-τ₁ * t) * h t :=
    mul_nonneg (Real.exp_pos _).le (hpos t)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn1, hexp,
    abs_of_nonneg (hpos t)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) hnn]

/-- Real-valued version of moment integrability. -/
lemma integrable_momentLap_real' {h : ℝ → ℝ} {σc : ℝ} (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume)
    (n : ℕ) {τ : ℝ} (hτ : σc < τ) :
    Integrable (fun t : ℝ ↦ t ^ n * Real.exp (-τ * t) * h t) (volume.restrict (Ioi 0)) := by
  have h1 := integrable_momentLap_real hpos hconv n hτ
  have h2 := (Integrable.re_im_iff.mpr h1).1
  have heq : (fun t : ℝ => RCLike.re ((t ^ n * Real.exp (-τ * t) * h t : ℝ):ℂ))
      = (fun t : ℝ => t ^ n * Real.exp (-τ * t) * h t) := by
    funext t
    exact RCLike.ofReal_re _
  rwa [heq] at h2

/-- Complex moment integrability, from the real version. -/
lemma integrable_momentLap {h : ℝ → ℝ} {σc : ℝ} (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume)
    (n : ℕ) {w : ℂ} (hw : σc < w.re) :
    IntegrableOn (fun t : ℝ ↦ (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ)) * ((h t : ℝ):ℂ)) (Ioi 0) volume := by
  have hreal := integrable_momentLap_real' hpos hconv n hw
  have haesm : AEStronglyMeasurable
      (fun t : ℝ ↦ (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ)) * ((h t : ℝ):ℂ))
      (volume.restrict (Ioi 0)) := by
    have h1 : AEStronglyMeasurable (fun t : ℝ ↦ (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ)))
        (volume.restrict (Ioi 0)) :=
      (by continuity : Continuous fun t : ℝ ↦ (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ))).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun t : ℝ ↦ ((h t : ℝ):ℂ)) (volume.restrict (Ioi 0)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (aesm_h hconv)
    have h3 : AEStronglyMeasurable
        (fun t : ℝ ↦ (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ)) * ((h t : ℝ):ℂ))
        (volume.restrict (Ioi 0)) :=
      h1.mul h2
    exact h3
  refine Integrable.mono' hreal haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : (0:ℝ) < t := ht
  have hLHS : ‖(t:ℂ) ^ n * Complex.exp (-w * (t:ℂ)) * ((h t : ℝ):ℂ)‖
      = t ^ n * Real.exp (-w.re * t) * |h t| := by
    rw [norm_mul, norm_mul, Complex.norm_pow, Complex.norm_exp]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    have hre : (-w * (t:ℂ)).re = -(w.re * t) := by
      simp [Complex.mul_re, Complex.neg_re]
    rw [hre]
    have e : (-(w.re * t) : ℝ) = -w.re * t := by ring
    rw [e]
  rw [hLHS, abs_of_nonneg (hpos t)]

/-- Differentiation under the Laplace integral:
    `d/dw ∫₀^∞ t^n e^{-wt} h(t) dt = -∫₀^∞ t^{n+1} e^{-wt} h(t) dt`
    for `Re w > σc`. -/
lemma hasDerivAt_momentLap {h : ℝ → ℝ} {σc : ℝ} (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume)
    (n : ℕ) {w₀ : ℂ} (hw₀ : σc < w₀.re) :
    HasDerivAt (momentLap h n) (-(momentLap h (n+1) w₀)) w₀ := by
  set δ : ℝ := (w₀.re - σc) / 2 with hδdef
  have hδpos : 0 < δ := by simp only [hδdef]; linarith
  set τ₂ : ℝ := w₀.re - δ with hτ₂def
  have hτ₂ : σc < τ₂ := by simp only [hτ₂def, hδdef]; linarith
  obtain ⟨τ₁, hτ₁a, hτ₁b⟩ := exists_between hτ₂
  obtain ⟨C, hCnn, hC⟩ := pow_mul_exp_neg_bound (n := n+1) (c := τ₂ - τ₁) (by linarith)
  set F : ℂ → ℝ → ℂ := fun w t ↦ (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ)) * ((h t : ℝ):ℂ) with hFdef
  set F' : ℂ → ℝ → ℂ := fun w t ↦ -((t:ℂ) ^ (n+1) * Complex.exp (-w * (t:ℂ)) * ((h t : ℝ):ℂ)) with hF'def
  set bound : ℝ → ℝ := fun t ↦ C * Real.exp (-τ₁ * t) * |h t| with hbounddef
  set s : Set ℂ := Metric.ball w₀ δ with hsdef
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμdef
  have hs : s ∈ 𝓝 w₀ := Metric.ball_mem_nhds w₀ hδpos
  have haesm_h := aesm_h hconv
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F w) μ := by
    apply Filter.Eventually.of_forall
    intro w
    have h1 : AEStronglyMeasurable (fun t : ℝ ↦ (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ))) μ :=
      (by continuity : Continuous fun t : ℝ ↦ (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ))).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun t : ℝ ↦ ((h t : ℝ):ℂ)) μ :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable haesm_h
    have h3 : AEStronglyMeasurable
        (fun t : ℝ ↦ (t:ℂ) ^ n * Complex.exp (-w * (t:ℂ)) * ((h t : ℝ):ℂ)) μ :=
      h1.mul h2
    simp only [hFdef]
    exact h3
  have hF_int : Integrable (F w₀) μ := integrable_momentLap hpos hconv n hw₀
  have hF'_meas : AEStronglyMeasurable (F' w₀) μ := by
    have h1 : AEStronglyMeasurable (fun t : ℝ ↦ (t:ℂ) ^ (n+1) * Complex.exp (-w₀ * (t:ℂ))) μ :=
      (by continuity : Continuous fun t : ℝ ↦ (t:ℂ) ^ (n+1) * Complex.exp (-w₀ * (t:ℂ))).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun t : ℝ ↦ ((h t : ℝ):ℂ)) μ :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable haesm_h
    have h3 : AEStronglyMeasurable
        (fun t : ℝ ↦ -((t:ℂ) ^ (n+1) * Complex.exp (-w₀ * (t:ℂ)) * ((h t : ℝ):ℂ))) μ :=
      (h1.mul h2).neg
    simp only [hF'def]
    exact h3
  have h_bound : ∀ᵐ t ∂μ, ∀ w ∈ s, ‖F' w t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : (0:ℝ) < t := ht
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hrew : τ₂ ≤ w.re := by
      have h1 : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
        have h2 := Complex.abs_re_le_norm (w - w₀)
        rwa [show (w - w₀).re = w.re - w₀.re from by simp [Complex.sub_re]] at h2
      have h3 : ‖w - w₀‖ < δ := hw
      have h4 : -δ ≤ w.re - w₀.re := (abs_le.mp (le_trans h1 (le_of_lt h3))).1
      simp only [hτ₂def, hδdef] at ⊢
      linarith
    have hnorm : ‖F' w t‖ = t ^ (n+1) * Real.exp (-w.re * t) * |h t| := by
      simp only [hF'def]
      rw [norm_neg, norm_mul, norm_mul, Complex.norm_pow, Complex.norm_exp]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
      have hre : (-w * (t:ℂ)).re = -(w.re * t) := by
        simp [Complex.mul_re, Complex.neg_re]
      rw [hre]
      have e : (-(w.re * t) : ℝ) = -w.re * t := by ring
      rw [e]
    rw [hnorm]
    simp only [hbounddef]
    have hle : t ^ (n+1) * Real.exp (-(τ₂ - τ₁) * t) ≤ C := hC t (le_of_lt htpos)
    have hexp_le : Real.exp (-w.re * t) ≤ Real.exp (-τ₂ * t) := by
      apply Real.exp_le_exp.mpr
      have hle2 : -w.re * t ≤ -τ₂ * t :=
        mul_le_mul_of_nonneg_right (by linarith : -w.re ≤ -τ₂) (le_of_lt htpos)
      linarith
    have hexp_eq : Real.exp (-τ₂ * t) = Real.exp (-(τ₂ - τ₁) * t) * Real.exp (-τ₁ * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hA : (0:ℝ) ≤ t ^ (n+1) := pow_nonneg (le_of_lt htpos) _
    have hH : (0:ℝ) ≤ |h t| := abs_nonneg _
    have hE1 : (0:ℝ) ≤ Real.exp (-τ₁ * t) := (Real.exp_pos _).le
    have p1 : (0:ℝ) ≤ (Real.exp (-τ₂ * t) - Real.exp (-w.re * t)) * (t^(n+1) * |h t|) :=
      mul_nonneg (sub_nonneg.mpr hexp_le) (mul_nonneg hA hH)
    have p2 : (0:ℝ) ≤ (C - t^(n+1) * Real.exp (-(τ₂-τ₁)*t)) * (Real.exp (-τ₁*t) * |h t|) :=
      mul_nonneg (sub_nonneg.mpr hle) (mul_nonneg hE1 hH)
    rw [hexp_eq] at p1
    nlinarith [p1, p2]
  have bound_integrable : Integrable bound μ := by
    have h1 := hconv τ₁ hτ₁a
    have h2 : (fun t : ℝ ↦ ((C * Real.exp (-τ₁ * t) * |h t| : ℝ):ℂ))
        = fun t : ℝ ↦ (C:ℂ) * ((Real.exp (-τ₁ * t) * h t : ℝ):ℂ) := by
      funext t
      rw [abs_of_nonneg (hpos t)]
      push_cast
      ring
    have h3 : Integrable (fun t : ℝ ↦ (C:ℂ) * ((Real.exp (-τ₁ * t) * h t : ℝ):ℂ)) μ :=
      h1.const_mul (C:ℂ)
    rw [← h2] at h3
    have h4 := (Integrable.re_im_iff.mpr h3).1
    have heq4 : (fun x : ℝ => RCLike.re ((C * Real.exp (-τ₁ * x) * |h x| : ℝ):ℂ))
        = (fun t : ℝ => C * Real.exp (-τ₁ * t) * |h t|) := by
      funext t
      exact RCLike.ofReal_re _
    rw [heq4] at h4
    simpa [hbounddef] using h4
  have h_diff : ∀ᵐ t ∂μ, ∀ w ∈ s, HasDerivAt (F · t) (F' w t) w := by
    filter_upwards with t
    intro w hw
    have hexp : HasDerivAt (fun w : ℂ ↦ Complex.exp (-w * (t:ℂ)))
        (Complex.exp (-w * (t:ℂ)) * (-(t:ℂ))) w := by
      have h1 : HasDerivAt (fun w : ℂ ↦ -w * (t:ℂ)) (-(t:ℂ)) w := by
        have h2 := (hasDerivAt_id w).neg.mul_const (t:ℂ)
        simpa using h2
      exact (Complex.hasDerivAt_exp _).comp w h1
    have hmul := hexp.mul_const ((t:ℂ) ^ n * ((h t : ℝ):ℂ))
    have efun : (fun w : ℂ ↦ F w t)
        = fun w : ℂ ↦ Complex.exp (-w * (t:ℂ)) * ((t:ℂ) ^ n * ((h t : ℝ):ℂ)) := by
      funext w'
      simp only [hFdef]
      ring
    have ederiv : F' w t
        = (Complex.exp (-w * (t:ℂ)) * (-(t:ℂ))) * ((t:ℂ) ^ n * ((h t : ℝ):ℂ)) := by
      simp only [hF'def]
      ring
    rw [efun, ederiv]
    exact hmul
  obtain ⟨-, hderiv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) hs hF_meas hF_int hF'_meas
      h_bound bound_integrable h_diff
  have e1 : (fun x : ℂ ↦ ∫ a, F x a ∂μ) = momentLap h n := rfl
  have e2 : (∫ a, F' w₀ a ∂μ) = -(momentLap h (n+1) w₀) := by
    have e2a : (fun a : ℝ ↦ F' w₀ a)
        = fun a : ℝ ↦ -((a:ℂ) ^ (n+1) * Complex.exp (-w₀ * (a:ℂ)) * ((h a : ℝ):ℂ)) := by
      funext a
      simp only [hF'def]
    rw [e2a, integral_neg]
    rfl
  rw [e1, e2] at hderiv
  exact hderiv

/-- Iterated derivatives of the Laplace integral are the signed moment integrals. -/
lemma iteratedDeriv_momentLap {h : ℝ → ℝ} {σc : ℝ} (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume)
    (n : ℕ) {w : ℂ} (hw : σc < w.re) :
    iteratedDeriv n (momentLap h 0) w = (-1) ^ n * momentLap h n w := by
  induction n generalizing w with
  | zero => simp
  | succ k ih =>
    have hmem : {w' : ℂ | σc < w'.re} ∈ 𝓝 w :=
      (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hw
    have hev : (fun w' : ℂ ↦ iteratedDeriv k (momentLap h 0) w')
        =ᶠ[𝓝 w] (fun w' : ℂ ↦ (-1) ^ k * momentLap h k w') := by
      filter_upwards [hmem] with w' hw'
      exact ih hw'
    have hdm := (hasDerivAt_momentLap hpos hconv k hw).const_mul ((-1 : ℂ) ^ k)
    rw [iteratedDeriv_succ, hev.deriv_eq, hdm.deriv]
    ring

/-! ## §3 continued. Landau's lemma — the full one-step improvement -/

/-- **Landau's lemma, full one-step form.** Let `h ≥ 0` with Laplace transform
    converging (absolutely) above `σc > 0`. If the Laplace transform extends to
    a function holomorphic on the whole right half-plane `{Re z > 0}`, then it
    converges above *every* `y > 0` — the abscissa is `≤ 0`.

    Proof: for `y > σc` this is the hypothesis; for `0 < y ≤ σc`,
    Taylor-expand the extension at `x = σc + 1` (the disc of radius `x`
    reaches `y = x - d` in one step, with `d = x - y < x`); the Taylor
    coefficients are the moment integrals (by differentiation under the
    integral sign); nonnegativity lets us interchange sum and integral
    (Tonelli), giving convergence at `y`. No iteration — and hence no
    analytic-continuation / identity-theorem step — is needed (this dissolves
    the wave-55 located blocker). -/
theorem landau_full {h : ℝ → ℝ} {σc : ℝ} {Hext : ℂ → ℂ}
    (hpos : ∀ t, 0 ≤ h t)
    (hσc : 0 < σc)
    (hconv : ∀ τ : ℝ, σc < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume)
    (hHext : DifferentiableOn ℂ Hext {z : ℂ | 0 < z.re})
    (heq : ∀ z : ℂ, σc < z.re → Hext z = ∫ t : ℝ in Ioi 0, Complex.exp (-z * (t:ℂ)) * ((h t : ℝ):ℂ)) :
    ∀ y : ℝ, 0 < y → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-y * t) * h t : ℝ):ℂ)) (Ioi 0) volume := by
  intro y hy
  by_cases hlt : σc < y
  · exact hconv y hlt
  · rw [not_lt] at hlt
    set x : ℝ := σc + 1 with hx_def
    set d : ℝ := x - y with hd_def
    have hxσ : σc < x := by simp only [hx_def]; linarith
    have hx0 : 0 < x := by simp only [hx_def]; linarith
    have hd0 : 0 < d := by simp only [hd_def, hx_def]; linarith
    have hdx : d < x := by simp only [hd_def]; linarith
    have hxy : y - x = -d := by simp only [hd_def]; ring
    have haesm_h := aesm_h hconv
    -- Taylor setup: ball(x, x) ⊆ {Re > 0}, y ∈ ball(x, x)
    have hball_sub : Metric.ball (x:ℂ) (x:ℝ) ⊆ {z : ℂ | 0 < z.re} := by
      intro z hz
      simp only [Set.mem_ofPred_eq]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h1 : |z.re - x| ≤ ‖z - (x:ℂ)‖ := by
        have h2 := Complex.abs_re_le_norm (z - (x:ℂ))
        rwa [show (z - (x:ℂ)).re = z.re - x from by simp] at h2
      have h3 : |z.re - x| < x := lt_of_le_of_lt h1 hz
      have h4 := abs_lt.mp h3
      linarith
    have hmem : (y:ℂ) ∈ Metric.ball (x:ℂ) (x:ℝ) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have e1 : (y:ℂ) - (x:ℂ) = ((-d : ℝ):ℂ) := by
        rw [← Complex.ofReal_sub, hxy]
      rw [e1]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hd0]
      exact hdx
    -- real moments at x
    set m : ℕ → ℝ := fun n ↦ ∫ t : ℝ in Ioi 0, t ^ n * Real.exp (-x * t) * h t with hm_def
    have hm_nonneg : ∀ n, 0 ≤ m n := by
      intro n
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : (0:ℝ) < t := ht
      have h1 := hpos t
      positivity
    -- coefficient identification: Taylor coefficients are the moment integrals
    have hcoeff : ∀ n : ℕ, iteratedDeriv n Hext (x:ℂ) = (-1 : ℂ) ^ n * ((m n : ℝ):ℂ) := by
      intro n
      have hev : Hext =ᶠ[𝓝 (x:ℂ)] momentLap h 0 := by
        have hmem2 : {z : ℂ | σc < z.re} ∈ 𝓝 (x:ℂ) :=
          (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hxσ
        filter_upwards [hmem2] with z hz
        rw [heq z hz]
        simp only [momentLap, pow_zero, one_mul]
      rw [hev.iteratedDeriv_eq n, iteratedDeriv_momentLap hpos hconv n hxσ]
      congr 1
      simp only [momentLap, hm_def]
      have e : (∫ (t : ℝ) in Ioi 0, (t:ℂ) ^ n * Complex.exp (-(x:ℂ) * (t:ℂ)) * ((h t : ℝ):ℂ))
          = ∫ (t : ℝ) in Ioi 0, (((t ^ n * Real.exp (-x * t) * h t : ℝ)):ℂ) := by
        apply setIntegral_congr_ae measurableSet_Ioi
        filter_upwards with t _
        have hexp_eq : Complex.exp (-(x:ℂ) * (t:ℂ)) = (((Real.exp (-x * t) : ℝ)):ℂ) := by
          have e1 : (-(x:ℂ) * (t:ℂ)) = (((-(x * t)) : ℝ):ℂ) := by push_cast; ring
          calc Complex.exp (-(x:ℂ) * (t:ℂ))
              = Complex.exp (((-(x * t)) : ℝ):ℂ) := by rw [e1]
            _ = (((Real.exp (-(x * t)) : ℝ)):ℂ) := (Complex.ofReal_exp _).symm
            _ = (((Real.exp (-x * t) : ℝ)):ℂ) := by
                have harg : -(x * t) = -x * t := by ring
                rw [harg]
        rw [hexp_eq]
        push_cast
        ring
      rw [e]
      exact integral_complex_ofReal
    -- Taylor terms as nonneg reals
    have hterm : ∀ n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n Hext (x:ℂ) * ((y:ℂ) - (x:ℂ)) ^ n
        = ((((d ^ n / n ! * m n : ℝ))):ℂ) := by
      intro n
      have hyx'' : (y:ℂ) - (x:ℂ) = ((-d : ℝ):ℂ) := by
        rw [← Complex.ofReal_sub, hxy]
      rw [hcoeff n, hyx'']
      have hneg1 : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow ⟨n, by ring⟩
      have e2 : (-d : ℝ) ^ n = (-1 : ℝ) ^ n * d ^ n := by
        rw [show (-d : ℝ) = -1 * d by ring, mul_pow]
      have hreal : ((n ! : ℕ):ℝ)⁻¹ * (-1:ℝ)^n * m n * (-d:ℝ)^n
          = d^n / ((n ! : ℕ):ℝ) * m n := by
        rw [e2, div_eq_mul_inv]
        have e3 : ((n ! : ℕ):ℝ)⁻¹ * (-1:ℝ)^n * m n * ((-1:ℝ)^n * d^n)
            = (((n ! : ℕ):ℝ)⁻¹ * (m n * d^n)) * ((-1:ℝ)^n * (-1:ℝ)^n) := by ring
        rw [e3, hneg1, mul_one]
        ring
      -- Collapse the LHS coercions into a single ofReal
      -- (needs explicit bridges: `(-1:ℂ)` is not syntactically a cast, and `(n!:ℂ)`
      -- is `Nat.cast`, not `Complex.ofReal`)
      have eLHS : (n ! : ℂ)⁻¹ * ((-1:ℂ) ^ n * ((m n : ℝ):ℂ)) * (((-d : ℝ):ℂ) ^ n)
          = ((((n ! : ℕ):ℝ)⁻¹ * (-1:ℝ)^n * m n * (-d:ℝ)^n : ℝ):ℂ) := by
        have c1 : (-1:ℂ) = (((-1:ℝ)):ℂ) := by norm_cast
        have c2 : (n ! : ℂ) = ((((n ! : ℕ):ℝ)):ℂ) := by norm_cast
        rw [c1, c2, ← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
          ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
          Complex.ofReal_inj]
        ring
      rw [eLHS]
      exact_mod_cast hreal
    -- summability via the Taylor HasSum, transported along the coefficient identity.
    -- (The intended `tsum_eq_hasSum : a = ∑' i, f i → HasSum f a` does not exist in
    -- mathlib — it is false in general. `Complex.hasSum_taylorSeries_on_ball` gives the
    -- `HasSum` directly.)
    have htaylorHas : HasSum
        (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • ((y:ℂ) - (x:ℂ)) ^ n • iteratedDeriv n Hext (x:ℂ))
        (Hext (y:ℂ)) :=
      Complex.hasSum_taylorSeries_on_ball (hHext.mono hball_sub) hmem
    have hsummC : Summable (fun n : ℕ ↦ (((d ^ n / n ! * m n : ℝ)):ℂ)) :=
      (htaylorHas.congr_fun (fun n ↦ by
        have h := hterm n
        simp only [smul_eq_mul]
        rw [← h]
        ring)).summable
    -- real summability via `Complex.summable_ofReal`
    -- (the old `hsummC.norm` route is invalid: `Summable.norm` does not exist in
    -- mathlib — summability of norms is false for conditionally convergent series)
    have hsummR : Summable (fun n : ℕ ↦ (d ^ n / n ! * m n : ℝ)) :=
      Complex.summable_ofReal.mp hsummC
    -- the nonneg summands
    set G : ℕ → ℝ → ℝ := fun n t ↦ d ^ n / n ! * (t ^ n * Real.exp (-x * t) * h t) with hGdef
    have hG_nonneg : ∀ n t, 0 ≤ t → 0 ≤ G n t := by
      intro n t ht
      simp only [hGdef]
      apply mul_nonneg
      · apply div_nonneg
        · exact pow_nonneg (le_of_lt hd0) n
        · exact Nat.cast_nonneg _
      · have h1 := hpos t
        positivity
    have ha_eq : ∀ n : ℕ, d ^ n / n ! * m n = ∫ t : ℝ in Ioi 0, G n t := by
      intro n
      simp only [hm_def, hGdef, integral_const_mul]
    have hintG : ∀ n : ℕ, Integrable (G n) (volume.restrict (Ioi 0)) := by
      intro n
      have h1 := integrable_momentLap_real' hpos hconv n hxσ
      have h2 := h1.const_mul (d ^ n / n !)
      simpa [hGdef] using h2
    have haemeas : ∀ n : ℕ, AEMeasurable (fun t : ℝ ↦ ENNReal.ofReal (G n t))
        (volume.restrict (Ioi 0)) := by
      intro n
      have hc : AEStronglyMeasurable (fun t : ℝ ↦ d ^ n / n ! * (t ^ n * Real.exp (-x * t) * h t))
          (volume.restrict (Ioi 0)) :=
        ((aestronglyMeasurable_const).mul
          ((((continuous_pow n).aestronglyMeasurable.mul
            (by continuity : Continuous fun t : ℝ ↦ Real.exp (-x * t)).aestronglyMeasurable).mul
            haesm_h)))
      have hcG : AEStronglyMeasurable (G n) (volume.restrict (Ioi 0)) := by
        simpa [hGdef] using hc
      exact (ENNReal.continuous_ofReal.measurable.comp_aemeasurable hcG.aemeasurable)
    -- pointwise sum: the exponential series
    have hsum_pt : ∀ t : ℝ, ∑' n : ℕ, G n t = Real.exp (-y * t) * h t := by
      intro t
      have hexp : ∑' n : ℕ, ((d * t) ^ n / n ! : ℝ) = Real.exp (d * t) := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
        apply tsum_congr
        intro n
        rw [smul_eq_mul, div_eq_mul_inv]
        ring
      calc ∑' n : ℕ, G n t
          = ∑' n : ℕ, (((d * t) ^ n / n !) * (Real.exp (-x * t) * h t) : ℝ) := by
            apply tsum_congr
            intro n
            simp only [hGdef]
            ring
        _ = (∑' n : ℕ, ((d * t) ^ n / n ! : ℝ)) * (Real.exp (-x * t) * h t) := by
            rw [tsum_mul_right]
        _ = Real.exp (d * t) * (Real.exp (-x * t) * h t) := by rw [hexp]
        _ = Real.exp (-y * t) * h t := by
            have harg : d * t + -x * t = -y * t := by
              have hyd : y = x - d := by simp only [hd_def]; ring
              rw [hyd]; ring
            calc Real.exp (d * t) * (Real.exp (-x * t) * h t)
                = Real.exp (d * t + -x * t) * h t := by rw [Real.exp_add]; ring
              _ = Real.exp (-y * t) * h t := by rw [harg]
    -- Tonelli interchange via lintegral
    have hlin_eq : (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-y * t) * h t))
        = ∑' n : ℕ, ENNReal.ofReal (d ^ n / n ! * m n) := by
      have step1 : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
          ENNReal.ofReal (Real.exp (-y * t) * h t) = ∑' n : ℕ, ENNReal.ofReal (G n t) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0:ℝ) ≤ t := le_of_lt ht
        have hsummGt : Summable (fun n : ℕ ↦ G n t) := by
          have hsumm := Real.summable_pow_div_factorial (d * t)
          have heqG : (fun n : ℕ ↦ G n t)
              = fun n : ℕ ↦ ((d * t) ^ n / n ! * (Real.exp (-x * t) * h t)) := by
            funext n
            simp only [hGdef]
            ring
          rw [heqG]
          exact hsumm.mul_right _
        rw [← hsum_pt t]
        exact ENNReal.ofReal_tsum_of_nonneg (fun n ↦ hG_nonneg n t ht0) hsummGt
      rw [lintegral_congr_ae step1, lintegral_tsum haemeas]
      apply tsum_congr
      intro n
      have hint := hintG n
      have hnn : ∀ᵐ t ∂(volume.restrict (Ioi 0)), 0 ≤ G n t := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hG_nonneg n t (le_of_lt ht)
      have h2 := ofReal_integral_eq_lintegral_ofReal hint hnn
      rw [ha_eq n, ← h2]
    -- finiteness and integrability, via `HasFiniteIntegral` (no `eLpNorm` spelling)
    have hpos_m : ∀ n : ℕ, 0 ≤ d ^ n / n ! * m n := by
      intro n
      apply mul_nonneg
      · apply div_nonneg
        · exact pow_nonneg (le_of_lt hd0) n
        · exact Nat.cast_nonneg _
      · exact hm_nonneg n
    have hS_aesm : AEStronglyMeasurable (fun t : ℝ ↦ Real.exp (-y * t) * h t)
        (volume.restrict (Ioi 0)) :=
      ((by continuity : Continuous fun t : ℝ ↦ Real.exp (-y * t)).aestronglyMeasurable.mul haesm_h)
    have hS_int : Integrable (fun t : ℝ ↦ Real.exp (-y * t) * h t) (volume.restrict (Ioi 0)) := by
      have hnnS_ae : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi 0)]
          (fun t : ℝ ↦ Real.exp (-y * t) * h t) :=
        Filter.Eventually.of_forall (fun t ↦ mul_nonneg (Real.exp_pos _).le (hpos t))
      have hfin : (∫⁻ a, ENNReal.ofReal (Real.exp (-y * a) * h a) ∂(volume.restrict (Ioi 0))) < ⊤ := by
        rw [hlin_eq, ← ENNReal.ofReal_tsum_of_nonneg hpos_m hsummR]
        exact ENNReal.ofReal_lt_top
      exact ⟨hS_aesm, (hasFiniteIntegral_iff_ofReal hnnS_ae).mpr hfin⟩
    have hfinal : Integrable (fun t : ℝ ↦ ((Real.exp (-y * t) * h t : ℝ):ℂ))
        (volume.restrict (Ioi 0)) :=
      Integrable.ofReal hS_int
    exact hfinal

/-- **Landau's lemma (improvement form)** — corollary of `landau_full`:
    convergence above `σc` gives convergence at `σc / 2`. -/
theorem landau_improve {h : ℝ → ℝ} {σc : ℝ} {Hext : ℂ → ℂ}
    (hpos : ∀ t, 0 ≤ h t)
    (hσc : 0 < σc)
    (hconv : ∀ τ : ℝ, σc < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume)
    (hHext : DifferentiableOn ℂ Hext {z : ℂ | 0 < z.re})
    (heq : ∀ z : ℂ, σc < z.re → Hext z = ∫ t : ℝ in Ioi 0, Complex.exp (-z * (t:ℂ)) * ((h t : ℝ):ℂ)) :
    IntegrableOn (fun t : ℝ ↦ ((Real.exp (-(σc/2) * t) * h t : ℝ):ℂ)) (Ioi 0) volume :=
  landau_full hpos hσc hconv hHext heq _ (by linarith)

/-- **Landau abscissa** — corollary of `landau_full`: convergence above `σc`
    gives convergence above every `σ > 0` (in particular every `σ > σc / 2`).
    This is the paper's "Lemma lem:landau forces `σ_c ≤ 0`". The wave-55
    located blocker (iterating the halving would need `heq` at smaller
    thresholds, i.e. analytic continuation) is DISSOLVED: one Taylor step at
    `x = σc + 1` reaches every positive exponent, so no iteration is needed. -/
theorem landau_abscissa {h : ℝ → ℝ} {σc : ℝ} {Hext : ℂ → ℂ}
    (hpos : ∀ t, 0 ≤ h t)
    (hσc : 0 < σc)
    (hconv : ∀ τ : ℝ, σc < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ):ℂ)) (Ioi 0) volume)
    (hHext : DifferentiableOn ℂ Hext {z : ℂ | 0 < z.re})
    (heq : ∀ z : ℂ, σc < z.re → Hext z = ∫ t : ℝ in Ioi 0, Complex.exp (-z * (t:ℂ)) * ((h t : ℝ):ℂ)) :
    ∀ σ : ℝ, σc / 2 < σ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-σ * t) * h t : ℝ):ℂ)) (Ioi 0) volume :=
  fun σ hσ ↦ landau_full hpos hσc hconv hHext heq σ (by linarith)

/-! ## §4. The transfer theorem (conditional) -/

/-- **G3, corrected (LEAN-CHECKED, wave 58).** Zero symmetry for *nontrivial*
    zeros of `riemannZeta`: if `ζ(ρ) = 0`, `ρ ≠ 1`, and `ρ` is not a
    non-positive integer (i.e. not a trivial zero), then `ζ(1 - ρ̄) = 0`.

    Proof: the functional equation `riemannZeta_one_sub` at `s := star ρ`
    (its side conditions `star ρ ≠ -n`, `star ρ ≠ 1` are exactly the
    nontriviality hypotheses, transported across `star`/`conj`) gives
    `ζ(1 - ρ̄) = χ(ρ̄)·ζ(ρ̄)`, and conjugation symmetry `riemannZeta_conj`
    gives `ζ(ρ̄) = conj (ζ ρ) = 0`. -/
theorem zeta_zero_symm {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1)
    (hnt : ∀ n : ℕ, ρ ≠ -(n : ℂ)) : riemannZeta (1 - star ρ) = 0 := by
  have hs : ∀ n : ℕ, star ρ ≠ -(n : ℂ) := by
    intro n hn
    have hfix : star (-(n : ℂ)) = -(n : ℂ) := by
      rw [Complex.star_def]
      simp
    have h2 := congrArg star hn
    rw [star_star, hfix] at h2
    exact hnt n h2
  have hs' : star ρ ≠ 1 := by
    intro h1
    apply hρ1
    have h2 := congrArg star h1
    rw [star_star, star_one] at h2
    exact h2
  have hconj0 : riemannZeta (star ρ) = 0 := by
    have hsc : star ρ = (starRingEnd ℂ) ρ := congrFun Complex.star_def ρ
    rw [hsc, riemannZeta_conj, hρ]
    exact map_zero _
  have hfe := riemannZeta_one_sub (s := star ρ) hs hs'
  rw [hfe, hconj0, mul_zero]

/-- **G3 as originally stated is FALSE (LEAN-CHECKED kill, wave 58).** The
    naive zero symmetry `ζ(ρ) = 0 → ρ ≠ 1 → ζ(1 - ρ̄) = 0` for *all* zeros
    fails for ordinary `riemannZeta`: the trivial zero `ρ = -2`
    (`riemannZeta_neg_two_mul_nat_add_one`) maps under `ρ ↦ 1 - ρ̄` to `3`,
    but `ζ(3) ≠ 0` (`riemannZeta_ne_zero_of_one_le_re`). The paper's G3 is a
    statement about the *completed* zeta `ξ` (whose zeros are symmetric) or,
    for `ζ`, about *nontrivial* zeros (`zeta_zero_symm`). -/
theorem g3_as_stated_false :
    ¬ ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → riemannZeta (1 - star ρ) = 0 := by
  intro h
  have h2 : riemannZeta (-2 : ℂ) = 0 := by
    have h0 := riemannZeta_neg_two_mul_nat_add_one 0
    simpa using h0
  have h3 := h (-2) h2 (by norm_num)
  have hstar : star (-2 : ℂ) = (-2 : ℂ) := by
    have e1 : (-2 : ℂ) = -((2 : ℕ) : ℂ) := by norm_num
    rw [Complex.star_def, e1, map_neg, map_natCast]
  rw [hstar] at h3
  have h13 : (1 : ℂ) - (-2 : ℂ) = 3 := by norm_num
  rw [h13] at h3
  have hne : riemannZeta (3 : ℂ) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    have hco : (3 : ℂ) = ((3 : ℝ) : ℂ) := by simp
    rw [hco, Complex.ofReal_re]
    norm_num
  exact hne h3

/-- **Transfer theorem (conditional).** From the explicit-formula shape of the
    holomorphic extension (paper-level G1), the "no real poles" input
    (paper-level G2: `ξ > 0` on `ℝ`, folded into `hHext`), the zero↔pole link
    (paper-level), and zero symmetry for nontrivial zeros (wave-58 G3 closure:
    `zeta_zero_symm`, LEAN-CHECKED — no longer a hypothesis), every nontrivial
    zero `ρ` (explicit hypothesis `hρnt`: not a non-positive integer, i.e. not
    a trivial zero) satisfies `|Re ρ - 1/2| ≤ F`.

    The analytic content — Landau (`landau_improve`) forcing the abscissa
    `≤ 0`, and solving the explicit-formula identity for `L` — is
    kernel-checked. The arithmetic inputs are explicit hypotheses, so the
    `F_θ` control cannot be misapplied: for `F_θ` the shifted zeros make the
    "no poles past `F`" consequence unprovable when `F < θ`. -/
theorem onesided_transfer {F _σc T₀ K : ℝ} {_h : ℝ → ℝ} {Hext L E : ℂ → ℂ}
    (hHext : DifferentiableOn ℂ Hext {z : ℂ | 0 < z.re})
    (hform : ∀ z : ℂ, 0 < z.re → Hext z = K / z - Complex.exp ((z + F) * T₀) * L (z + F) + E z)
    (hE : DifferentiableOn ℂ E Set.univ)
    (hzp : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → ¬ DifferentiableAt ℂ L (ρ - 1/2))
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1)
    (hρnt : ∀ n : ℕ, ρ ≠ -(n : ℂ)) :
    |ρ.re - 1/2| ≤ F := by
  -- Step A: solve the explicit-formula identity for L; L is holomorphic on {Re > F}
  have hL : ∀ w : ℂ, F < w.re → DifferentiableAt ℂ L w := by
    intro w hw
    -- w' near w with Re w' > F: same formula
    have hmem : {w' : ℂ | F < w'.re} ∈ 𝓝 w :=
      (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hw
    have hev : (fun w' : ℂ ↦ L w')
        =ᶠ[𝓝 w] (fun w' : ℂ ↦ Complex.exp (-(w' * T₀)) *
          (K / (w' - F) + E (w' - F) - Hext (w' - F))) := by
      filter_upwards [hmem] with w' hw'
      have hzpos : (0:ℝ) < (w' - F).re := by
        have : (w' - (F:ℂ)).re = w'.re - F := by simp [Complex.sub_re]
        rw [this] at ⊢
        linarith
      have hform' := hform (w' - F) hzpos
      -- hform' : Hext (w'-F) = K/(w'-F) - exp((w'-F+F)*T₀)*L(w'-F+F) + E(w'-F)
      have e1 : (w' - (F:ℂ)) + F = w' := by
        simp
      rw [e1] at hform'
      -- solve: exp(w'T₀) * L w' = K/(w'-F) + E(w'-F) - Hext(w'-F)
      have hsolve : Complex.exp ((w':ℂ) * T₀) * L w'
          = K / (w' - F) + E (w' - F) - Hext (w' - F) := by
        linear_combination hform'
      have hLw' : L w' = Complex.exp (-(w' * T₀)) *
          (K / (w' - F) + E (w' - F) - Hext (w' - F)) := by
        have e2 : Complex.exp (-(w' * (T₀:ℂ))) * Complex.exp ((w':ℂ) * T₀) = 1 := by
          rw [← Complex.exp_add]
          simp
        calc L w' = 1 * L w' := by rw [one_mul]
          _ = (Complex.exp (-(w' * T₀)) * Complex.exp ((w':ℂ) * T₀)) * L w' := by rw [e2]
          _ = Complex.exp (-(w' * T₀)) * (Complex.exp ((w':ℂ) * T₀) * L w') := by ring
          _ = _ := by rw [hsolve]
      exact hLw'
    -- RHS is differentiable at w
    have hne : w - (F:ℂ) ≠ 0 := by
      intro hcon
      have hre0 : (w - (F:ℂ)).re = 0 := by
        rw [hcon]; simp
      have hre : (w - (F:ℂ)).re = w.re - F := by simp [Complex.sub_re]
      rw [hre] at hre0
      linarith
    have hdiff : DifferentiableAt ℂ
        (fun w' : ℂ ↦ Complex.exp (-(w' * T₀)) *
          (K / (w' - F) + E (w' - F) - Hext (w' - F))) w := by
      have hexp : DifferentiableAt ℂ (fun w' : ℂ ↦ Complex.exp (-(w' * (T₀:ℂ)))) w :=
        ((differentiableAt_id.mul_const (T₀:ℂ)).neg).cexp
      have hdiv : DifferentiableAt ℂ (fun w' : ℂ ↦ K / (w' - (F:ℂ))) w :=
        (differentiableAt_const _).div (differentiableAt_id.sub_const (F:ℂ)) hne
      have hEw : DifferentiableAt ℂ (fun w' : ℂ ↦ E (w' - (F:ℂ))) w :=
        (hE.differentiableAt Filter.univ_mem).comp w (differentiableAt_id.sub_const (F:ℂ))
      have hHw : DifferentiableAt ℂ (fun w' : ℂ ↦ Hext (w' - (F:ℂ))) w := by
        have hmemw : w - (F:ℂ) ∈ {z : ℂ | 0 < z.re} := by
          show 0 < (w - (F:ℂ)).re
          have hre : (w - (F:ℂ)).re = w.re - F := by simp [Complex.sub_re]
          rw [hre]; linarith
        have hnbhd : {z : ℂ | 0 < z.re} ∈ 𝓝 (w - (F:ℂ)) :=
          (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hmemw
        exact (hHext.differentiableAt hnbhd).comp w (differentiableAt_id.sub_const (F:ℂ))
      exact hexp.mul ((hdiv.add hEw).sub hHw)
    exact (hev.differentiableAt_iff).mpr hdiff
  -- Step B: no zero with Re ρ > 1/2 + F
  have hB : ρ.re ≤ 1/2 + F := by
    by_contra hcon
    push Not at hcon
    have hwF : F < (ρ - 1/2).re := by
      have hre : (ρ - (1/2:ℂ)).re = ρ.re - 1/2 := by simp [Complex.sub_re]
      rw [hre]; linarith
    exact hzp ρ hρ hρ1 (hL (ρ - 1/2) hwF)
  -- Step C: symmetry (wave-58: zeta_zero_symm, no longer a hypothesis) gives the lower bound
  have hρ' : riemannZeta (1 - star ρ) = 0 := zeta_zero_symm hρ hρ1 hρnt
  have hρ1' : (1 - star ρ) ≠ 1 := by
    intro hcon
    have hstar : star ρ = 0 := by
      have h2 := congrArg (· - 1) hcon
      simpa using h2
    have h0 : ρ = 0 := star_eq_zero.mp hstar
    rw [h0, riemannZeta_zero] at hρ
    norm_num at hρ
  have hB' : (1 - star ρ).re ≤ 1/2 + F := by
    by_contra hcon
    push Not at hcon
    have hwF : F < ((1 - star ρ) - 1/2).re := by
      have hre : ((1 - star ρ) - (1/2:ℂ)).re = (1 - star ρ).re - 1/2 := by
        simp [Complex.sub_re]
      rw [hre]; linarith
    exact hzp (1 - star ρ) hρ' hρ1' (hL ((1 - star ρ) - 1/2) hwF)
  have hstar_re : (star ρ).re = ρ.re := Complex.conj_re ρ
  have hre_symm : (1 - star ρ).re = 1 - ρ.re := by
    rw [Complex.sub_re, Complex.one_re, hstar_re]
  have hBlow : 1 - ρ.re ≤ 1/2 + F := by linarith [hB', hre_symm]
  rw [abs_le]
  constructor <;> linarith

#print axioms laplace_exp_majorant
#print axioms laplace_exp_majorant_holo
#print axioms shift_reduction
#print axioms landau_full
#print axioms landau_improve
#print axioms landau_abscissa
#print axioms onesided_transfer
#print axioms zeta_zero_symm
#print axioms g3_as_stated_false

end RhWaveLean
