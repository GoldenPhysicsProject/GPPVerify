import GppVerify.RiemannHypothesis.OneSidedPsiRH
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# No bound states: Nyman–Beurling density implies the Riemann Hypothesis

The Hilbert space is `L²(0,1]`, the scale half-line, with the dilation structure of the Mellin
transform. The primes enter through the Beurling functions `ρ_θ(x) = {θ/x} - θ{1/x}`,
`0 < θ ≤ 1`, whose Mellin transforms carry `ζ` as a factor. A zero `ρ` of `ζ` with
`1/2 < re ρ < 1` is a *bound state*: the vector `x^{ρ-1}` is square-integrable on `(0,1]`, it is
orthogonal to every `ρ_θ`, and its pairing with the constant `1` is `1/ρ ≠ 0`. A zero on the line
gives the same vector without square-integrability: a scattering state of the continuum.

* `zeta_eq_fracInt`: `ζ(s) = s/(s-1) - s ∫_{(1,∞)} {t} t^{-s-1} dt` for `1 < re s` (Abel summation,
  Mathlib's `LSeries_eq_mul_integral_of_nonneg`).
* `mul_fracInt_eq`: `s ∫_{(1,∞)} {t} t^{-s-1} dt = 1 - ζ₀(s)` for `0 < re s`, where
  `ζ(s) = 1/(s-1) + ζ₀(s)`: the continuation into the critical strip, by the identity theorem on
  the half-plane, with differentiability from Mellin-transform theory.
* `mellin_fracInv`: `∫_{(0,∞)} {1/x} x^{s-1} dx = -ζ(s)/s` for `0 < re s < 1`.
* `mellin_beurling`: the Mellin transform of `ρ_θ` is `(θ^s - θ)(-ζ(s)/s)`; `beurling_eq_zero`:
  `ρ_θ` vanishes on `(1,∞)`; `beurling_orthogonal`: at a zero in the strip, `x^{ρ-1}` is
  orthogonal to every `ρ_θ` on `(0,1]`.
* `NymanBeurlingDense`: the constant `1` is an `L²(0,1]`-limit of finite combinations of the `ρ_θ`.
* `zeta_ne_zero_of_nymanBeurling`: density forbids zeros with `1/2 < re ρ < 1` (the bound state
  would pair with `1` to `1/ρ`, while the pairing is bounded by `δ(1+B)/2` for every `δ`).
* `riemannHypothesis_of_nymanBeurling : NymanBeurlingDense → RiemannHypothesis`.

The converse (the Riemann Hypothesis gives density) is Beurling's theorem and is the harder
direction; this module carries the direction that turns density into the Riemann Hypothesis.
-/

open Complex MeasureTheory Set Filter Topology

namespace GppNymanBeurling

/-- `∫_{(1,∞)} {t} t^{-s-1} dt`. -/
noncomputable def fracInt (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

theorem integrableOn_fract_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hI : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  refine Integrable.mono' hI.norm ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact (Complex.measurable_ofReal.comp measurable_fract).mul (by fun_prop)
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    rw [norm_mul]
    have h1 : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    calc ‖((Int.fract t : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖ ≤ 1 * ‖(t : ℂ) ^ (-(s + 1))‖ := by
          gcongr
      _ = ‖(t : ℂ) ^ (-(s + 1))‖ := one_mul _

theorem zeta_eq_fracInt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * fracInt s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.isBigO_of_le _ fun n => ?_
    simp
  have h := LSeries_eq_mul_integral_of_nonneg (fun _ => (1 : ℝ)) zero_le_one hs hO (fun _ => zero_le_one)
  rw [← LSeries_one_eq_riemannZeta hs]
  have hL : LSeries (fun n => (((fun _ : ℕ => (1 : ℝ)) n : ℝ) : ℂ)) s = LSeries 1 s := by
    congr 1
  rw [← hL, h]
  have hsum : ∀ t : ℝ, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (((fun _ : ℕ => (1 : ℝ)) k : ℝ) : ℂ)) =
      ((⌊t⌋₊ : ℕ) : ℂ) := by
    intro t; simp
  simp_rw [hsum]
  have hpt : ∀ t ∈ Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := by have := mem_Ioi.1 ht; linarith
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [Int.fract, natCast_floor_eq_intCast_floor ht0]; ring
    have htc : (t : ℂ) ≠ 0 := by
      have := mem_Ioi.1 ht; exact_mod_cast (by linarith : t ≠ 0)
    have hcp : (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
      have e : (t : ℂ) ^ (-s) = (t : ℂ) ^ ((1 : ℂ) + (-(s + 1))) := by ring_nf
      rw [e, cpow_add _ _ htc, cpow_one]
    have : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      rw [show ((⌊t⌋₊ : ℕ) : ℂ) = (((⌊t⌋₊ : ℕ) : ℝ) : ℂ) by norm_cast, hfl]; push_cast; ring
    rw [this, sub_mul, hcp]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  rw [integral_sub hI1 (integrableOn_fract_cpow (by linarith)),
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  unfold fracInt
  have hs1 : s - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hs1' : -s + 1 ≠ 0 := by
    intro h0; apply hs1; linear_combination -h0
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

/-- The fractional part on `(1, ∞)`, zero elsewhere. -/
noncomputable def fracTail (t : ℝ) : ℂ := (Ioi (1 : ℝ)).indicator (fun t => ((Int.fract t : ℝ) : ℂ)) t

theorem fracInt_eq_mellin (s : ℂ) : fracInt s = mellin fracTail (-s) := by
  unfold fracInt mellin fracTail
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · have ht0 : t ∈ Ioi (0 : ℝ) := mem_Ioi.2 (lt_trans one_pos ht)
    simp only [indicator_of_mem ht, indicator_of_mem ht0, smul_eq_mul]
    ring_nf
  · simp only [indicator_of_notMem ht, smul_eq_mul]
    by_cases ht0 : t ∈ Ioi (0 : ℝ)
    · simp [indicator_of_mem ht0, indicator_of_notMem ht]
    · simp [indicator_of_notMem ht0]

theorem differentiableAt_fracInt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ fracInt s := by
  have hm : DifferentiableAt ℂ (mellin fracTail) (-s) := by
    have hb : ∀ t, ‖fracTail t‖ ≤ 1 := by
      intro t; unfold fracTail
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · rw [indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Int.fract_nonneg t)]
        exact (Int.fract_lt_one t).le
      · rw [indicator_of_notMem ht]; simp
    have hmeas : Measurable fracTail := by
      unfold fracTail
      exact (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ioi
    apply mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    · rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
      intro k _ hk
      exact IntegrableOn.of_bound hk.measure_lt_top hmeas.aestronglyMeasurable 1
        (Eventually.of_forall hb)
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [neg_zero, Real.rpow_zero, norm_one, one_mul]
      exact hb t
    · simp; linarith
    · refine Asymptotics.IsBigO.of_bound 0 ?_
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (one_pos : (0 : ℝ) < 1))] with t ht
      have : t ∉ Ioi (1 : ℝ) := fun h => absurd (mem_Ioi.1 h) (not_lt.2 (le_of_lt ht))
      unfold fracTail
      rw [indicator_of_notMem this]; simp
    · simp
  have : fracInt = fun s => mellin fracTail (-s) := funext fracInt_eq_mellin
  rw [this]
  exact hm.comp s differentiableAt_id.neg

/-- The fractional-part integral continued into the critical strip:
`s ∫_{(1,∞)} {t} t^{-s-1} dt = 1 - ζ₀(s)` for `0 < re s`, where `ζ(s) = 1/(s-1) + ζ₀(s)`. -/
theorem mul_fracInt_eq {s : ℂ} (hs : 0 < s.re) : s * fracInt s = 1 - riemannZeta₀ s := by
  set U : Set ℂ := {z | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := by
    have : Convex ℝ U := by
      intro x hx y hy a b ha hb hab
      simp only [hU, Set.mem_ofPred_eq, add_re, smul_re, smul_eq_mul] at hx hy ⊢
      rcases ha.eq_or_lt with h | h
      · subst h; simp at hab; subst hab; simp [hy]
      · nlinarith [mul_pos h hx, mul_nonneg hb hy.le]
    exact this.isPreconnected
  have hf : AnalyticOnNhd ℂ (fun z => z * fracInt z) U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_id.mul
      (differentiableAt_fracInt hz)).differentiableWithinAt) hUo
  have hg : AnalyticOnNhd ℂ (fun z => 1 - riemannZeta₀ z) U :=
    DifferentiableOn.analyticOnNhd (fun z _ => ((differentiable_riemannZeta₀ z).const_sub
      1).differentiableWithinAt) hUo
  have h2 : (2 : ℂ) ∈ U := by simp [hU]
  have hev : (fun z => z * fracInt z) =ᶠ[𝓝 (2 : ℂ)] fun z => 1 - riemannZeta₀ z := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
    have e1 := zeta_eq_fracInt hz
    have e2 := riemannZeta_eq_inv_sub_add hz1
    rw [e2] at e1
    have : z * fracInt z = z / (z - 1) - ((z - 1)⁻¹ + riemannZeta₀ z) := by
      linear_combination e1
    rw [this]
    field_simp
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h2 hev hs

/-- `x ↦ {1/x}` as a complex function. -/
noncomputable def fracInv (x : ℝ) : ℂ := ((Int.fract x⁻¹ : ℝ) : ℂ)

theorem integral_Ioc_cpow_neg {s : ℂ} (h1 : s.re < 1) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-s) = 1 / (1 - s) := by
  rw [← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by simp; linarith))]
  have hs : -s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [ofReal_one, one_cpow, ofReal_zero, zero_cpow hs]
  have h2 : (1 : ℂ) - s ≠ 0 := by intro h; apply hs; linear_combination h
  field_simp
  ring

theorem mellin_fracInv {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin fracInv s = -riemannZeta s / s := by
  have hcomp : mellin fracInv s = mellin (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)) (-s) :=
    mellin_comp_inv (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)) s
  rw [hcomp]
  unfold mellin
  simp only [smul_eq_mul]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) = (t : ℂ) ^ (-s) := by
    intro t ht
    have hf : Int.fract t = t := Int.fract_eq_self.2 ⟨ht.1.le, ht.2⟩
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    rw [hf]
    have e : (t : ℂ) ^ (-s) = (t : ℂ) ^ ((-s - 1) + 1) := by ring_nf
    rw [e, cpow_add _ _ htc, cpow_one]
  have hIoc : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    have hI : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_cpow_iff zero_lt_one).2 (by simp; linarith)
    exact hI.congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioo
  have hIoi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) (Ioi 1) := by
    have := integrableOn_fract_cpow h0
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    ring_nf
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hIoi]
  have hA : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) = 1 / (1 - s) := by
    rw [integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hpt,
      ← integral_Ioc_eq_integral_Ioo, integral_Ioc_cpow_neg h1]
  have hB : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) = fracInt s := by
    unfold fracInt
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    ring_nf
  rw [hA, hB]
  have hs0 : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hs1'' : 1 - s ≠ 0 := by intro h; apply hs1'; linear_combination -h
  have e1 := mul_fracInt_eq h0
  have e2 := riemannZeta_eq_inv_sub_add hs1
  rw [e2]
  have : fracInt s = (1 - riemannZeta₀ s) / s := by field_simp; linear_combination e1
  rw [this]
  field_simp
  ring

theorem mellinConvergent_fract {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    MellinConvergent (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)) (-s) := by
  unfold MellinConvergent
  simp only [smul_eq_mul]
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) = (t : ℂ) ^ (-s) := by
    intro t ht
    have hf : Int.fract t = t := Int.fract_eq_self.2 ⟨ht.1.le, ht.2⟩
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    rw [hf]
    have e : (t : ℂ) ^ (-s) = (t : ℂ) ^ ((-s - 1) + 1) := by ring_nf
    rw [e, cpow_add _ _ htc, cpow_one]
  have hIoc : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    have hI : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_cpow_iff zero_lt_one).2 (by simp; linarith)
    exact hI.congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioo
  have hIoi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) (Ioi 1) := by
    have := integrableOn_fract_cpow h0
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    ring_nf
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  exact hIoc.union hIoi

theorem mellinConvergent_fracInv {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    MellinConvergent fracInv s := by
  have h := (MellinConvergent.comp_rpow (f := fun t : ℝ => ((Int.fract t : ℝ) : ℂ)) (s := s)
    (a := -1) (by norm_num)).2 (by simpa [div_neg, div_one] using mellinConvergent_fract h0 h1)
  unfold MellinConvergent at h ⊢
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [fracInv, Real.rpow_neg_one]

/-- The Beurling function `ρ_θ(x) = {θ/x} - θ {1/x}`. -/
noncomputable def beurling (θ : ℝ) (x : ℝ) : ℂ := fracInv (θ⁻¹ * x) - (θ : ℂ) * fracInv x

theorem mellin_beurling {θ : ℝ} (hθ : 0 < θ) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (beurling θ) s = ((θ : ℂ) ^ s - θ) * (-riemannZeta s / s) := by
  have hA : MellinConvergent (fun t => fracInv (θ⁻¹ * t)) s :=
    (MellinConvergent.comp_mul_left (inv_pos.2 hθ)).2 (mellinConvergent_fracInv h0 h1)
  have hB : MellinConvergent (fun t => (θ : ℂ) * fracInv t) s := by
    have := (mellinConvergent_fracInv h0 h1).const_smul (θ : ℂ)
    simpa [smul_eq_mul] using this
  have hsub : mellin (beurling θ) s = mellin (fun t => fracInv (θ⁻¹ * t)) s -
      mellin (fun t => (θ : ℂ) * fracInv t) s := by
    unfold mellin beurling
    rw [← integral_sub hA hB]
    congr 1; funext t; simp only [smul_eq_mul]; ring
  rw [hsub, mellin_comp_mul_left _ _ (inv_pos.2 hθ)]
  have hc : mellin (fun t => (θ : ℂ) * fracInv t) s = (θ : ℂ) * mellin fracInv s := by
    have := mellin_const_smul fracInv s (θ : ℂ)
    simpa [smul_eq_mul] using this
  rw [hc, mellin_fracInv h0 h1, smul_eq_mul]
  have hinv : ((θ⁻¹ : ℝ) : ℂ) ^ (-s) = (θ : ℂ) ^ s := by
    rw [ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hθ.le]; exact Real.pi_ne_zero.symm),
      cpow_neg, inv_inv]
  rw [hinv]
  ring

theorem beurling_eq_zero {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) {x : ℝ} (hx : 1 < x) :
    beurling θ x = 0 := by
  have hx0 : 0 < x := by linarith
  unfold beurling fracInv
  have h1 : Int.fract (θ⁻¹ * x)⁻¹ = θ / x := by
    rw [mul_inv, inv_inv, ← div_eq_mul_inv]
    exact Int.fract_eq_self.2 ⟨by positivity, by rw [div_lt_one hx0]; linarith⟩
  have h2 : Int.fract x⁻¹ = 1 / x := by
    rw [← one_div]
    exact Int.fract_eq_self.2 ⟨by positivity, by rw [div_lt_one hx0]; linarith⟩
  rw [h1, h2]
  push_cast
  field_simp
  ring

/-- **A zero is orthogonal to the Beurling functions.** If `ζ ρ = 0` with `0 < re ρ < 1`, then for
every `0 < θ ≤ 1`, `∫_{(0,1]} x^{ρ-1} ρ_θ(x) dx = 0`. -/
theorem beurling_orthogonal {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) {ρ : ℂ} (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * beurling θ x = 0 := by
  have hm := mellin_beurling hθ h0 h1
  rw [hz, neg_zero, zero_div, mul_zero] at hm
  have hconv : MellinConvergent (beurling θ) ρ := by
    have hA : MellinConvergent (fun t => fracInv (θ⁻¹ * t)) ρ :=
      (MellinConvergent.comp_mul_left (inv_pos.2 hθ)).2 (mellinConvergent_fracInv h0 h1)
    have hB : MellinConvergent (fun t => (θ : ℂ) * fracInv t) ρ := by
      have := (mellinConvergent_fracInv h0 h1).const_smul (θ : ℂ)
      simpa [smul_eq_mul] using this
    unfold MellinConvergent at hA hB ⊢
    refine (hA.sub hB).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [beurling, smul_eq_mul, Pi.sub_apply]; ring
  unfold mellin at hm
  unfold MellinConvergent at hconv
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hconv.mono_set (by rw [hsplit]; exact subset_union_left))
    (hconv.mono_set (by rw [hsplit]; exact subset_union_right))] at hm
  have hz2 : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (ρ - 1) • beurling θ t = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℂ))
      (fun t ht => by simp [beurling_eq_zero hθ hθ1 ht])]
    simp
  rw [hz2, add_zero] at hm
  simpa [smul_eq_mul] using hm

theorem measurable_fracInv : Measurable fracInv := by
  unfold fracInv
  exact Complex.measurable_ofReal.comp (measurable_fract.comp measurable_inv)

theorem norm_fracInv_le (x : ℝ) : ‖fracInv x‖ ≤ 1 := by
  unfold fracInv
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

theorem measurable_beurling (θ : ℝ) : Measurable (beurling θ) := by
  unfold beurling
  exact (measurable_fracInv.comp (measurable_const.mul measurable_id)).sub
    (measurable_const.mul measurable_fracInv)

theorem norm_beurling_le {θ : ℝ} (hθ : 0 < θ) (x : ℝ) : ‖beurling θ x‖ ≤ 1 + θ := by
  unfold beurling
  calc ‖fracInv (θ⁻¹ * x) - (θ : ℂ) * fracInv x‖ ≤ ‖fracInv (θ⁻¹ * x)‖ + ‖(θ : ℂ) * fracInv x‖ :=
        norm_sub_le _ _
    _ ≤ 1 + θ * 1 := by
        gcongr
        · exact norm_fracInv_le _
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ]
          exact mul_le_mul_of_nonneg_left (norm_fracInv_le _) hθ.le
    _ = 1 + θ := by ring

/-- **Nyman–Beurling density.** The constant `1` is in the `L²(0,1]`-closure of the span of the
Beurling functions `ρ_θ`, `0 < θ ≤ 1`: every tolerance `ε > 0` is met by a finite combination. -/
def NymanBeurlingDense : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℂ) (θ : Fin n → ℝ), (∀ k, 0 < θ k ∧ θ k ≤ 1) ∧
    ∫ x in Ioc (0 : ℝ) 1, ‖1 - ∑ k, c k * beurling (θ k) x‖ ^ 2 ≤ ε

theorem integral_Ioc_cpow_sub_one {ρ : ℂ} (h0 : 0 < ρ.re) :
    ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) = 1 / ρ := by
  rw [← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by simp; linarith))]
  have hρ : ρ ≠ 0 := by intro h; rw [h] at h0; simp at h0
  rw [ofReal_one, one_cpow, ofReal_zero, sub_add_cancel, zero_cpow hρ]
  simp

theorem integrableOn_cpow_sub_one {ρ : ℂ} (h0 : 0 < ρ.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (ρ - 1)) (Ioc 0 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  exact (intervalIntegral.integrableOn_Ioo_cpow_iff zero_lt_one).2 (by simp; linarith)

theorem integrableOn_norm_cpow_sq {ρ : ℂ} (h : 1 / 2 < ρ.re) :
    IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (ρ - 1)‖ ^ 2) (Ioc 0 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hI : IntegrableOn (fun x : ℝ => x ^ (2 * ρ.re - 2)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  refine hI.congr_fun (fun x hx => ?_) measurableSet_Ioo
  rw [norm_cpow_eq_rpow_re_of_pos hx.1, ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
  simp; ring_nf

/-- **Bound states are forbidden by density.** If the Beurling functions are dense (in the sense of
`NymanBeurlingDense`), `ζ` has no zero with `1/2 < re ρ < 1`: such a zero would give the vector
`x^{ρ-1}`, square-integrable on `(0,1]`, orthogonal to every Beurling function but not to `1`. -/
theorem zeta_ne_zero_of_nymanBeurling (h : NymanBeurlingDense) {ρ : ℂ} (h1 : 1 / 2 < ρ.re)
    (h2 : ρ.re < 1) : riemannZeta ρ ≠ 0 := by
  intro hz
  have h0 : 0 < ρ.re := by linarith
  set B : ℝ := ∫ x in Ioc (0 : ℝ) 1, ‖(x : ℂ) ^ (ρ - 1)‖ ^ 2 with hBdef
  have hB : 0 ≤ B := setIntegral_nonneg measurableSet_Ioc (fun _ _ => by positivity)
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  set δ : ℝ := 1 / (‖ρ‖ * (1 + B)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨n, c, θ, hθ, hint⟩ := h (δ ^ 2) (by positivity)
  set F : ℝ → ℂ := fun x => 1 - ∑ k, c k * beurling (θ k) x with hFdef
  set C : ℝ := 1 + ∑ k, ‖c k‖ * (1 + θ k) with hCdef
  have hFb : ∀ x, ‖F x‖ ≤ C := by
    intro x
    calc ‖F x‖ ≤ ‖(1 : ℂ)‖ + ‖∑ k, c k * beurling (θ k) x‖ := norm_sub_le _ _
      _ ≤ 1 + ∑ k, ‖c k * beurling (θ k) x‖ := by
          rw [norm_one]; gcongr; exact norm_sum_le _ _
      _ ≤ C := by
          rw [hCdef]; gcongr with k
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_beurling_le (hθ k).1 x) (norm_nonneg _)
  have hFm : Measurable F := by
    rw [hFdef]
    exact measurable_const.sub (Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (measurable_beurling (θ k)))
  have hgi := integrableOn_cpow_sub_one h0
  have hgF : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (ρ - 1) * F x) (Ioc 0 1) :=
    Integrable.mul_bdd hgi hFm.aestronglyMeasurable (Eventually.of_forall hFb)
  have hgb : ∀ k, IntegrableOn (fun x : ℝ => (x : ℂ) ^ (ρ - 1) * beurling (θ k) x) (Ioc 0 1) :=
    fun k => Integrable.mul_bdd hgi (measurable_beurling (θ k)).aestronglyMeasurable
      (Eventually.of_forall (norm_beurling_le (hθ k).1))
  -- the pairing of `F` with the bound state is `1/ρ`
  have hP : ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * F x = 1 / ρ := by
    have hpt : (fun x : ℝ => (x : ℂ) ^ (ρ - 1) * F x) =
        fun x : ℝ => (x : ℂ) ^ (ρ - 1) - ∑ k, c k * ((x : ℂ) ^ (ρ - 1) * beurling (θ k) x) := by
      funext x; rw [hFdef]; simp only [mul_sub, mul_one, Finset.mul_sum]; congr 1
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hpt, integral_sub hgi (integrable_finsetSum _ fun k _ => (hgb k).const_mul (c k)),
      integral_finsetSum _ fun k _ => (hgb k).const_mul (c k), integral_Ioc_cpow_sub_one h0]
    have hz0 : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        ∫ x in Ioc (0 : ℝ) 1, c k * (((x : ℝ) : ℂ) ^ (ρ - 1) * beurling (θ k) x) = 0 := by
      intro k _
      rw [integral_const_mul, beurling_orthogonal (hθ k).1 (hθ k).2 h0 h2 hz, mul_zero]
    rw [Finset.sum_eq_zero hz0, sub_zero]
  -- the Cauchy–Schwarz-type bound
  have hF2 : IntegrableOn (fun x : ℝ => ‖F x‖ ^ 2) (Ioc 0 1) :=
    IntegrableOn.of_bound measure_Ioc_lt_top (hFm.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFb x) 2)
  have hg2 := integrableOn_norm_cpow_sq h1
  have hbound : ‖∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * F x‖ ≤ δ * (1 + B) / 2 := by
    calc ‖∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * F x‖
        ≤ ∫ x in Ioc (0 : ℝ) 1, ‖(x : ℂ) ^ (ρ - 1) * F x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in Ioc (0 : ℝ) 1, (δ⁻¹ * ‖F x‖ ^ 2 + δ * ‖(x : ℂ) ^ (ρ - 1)‖ ^ 2) / 2 := by
          refine setIntegral_mono_on hgF.norm
            (((hF2.const_mul δ⁻¹).add (hg2.const_mul δ)).div_const 2) measurableSet_Ioc
            (fun x _ => ?_)
          rw [norm_mul]
          have key : 0 ≤ (‖F x‖ - δ * ‖(x : ℂ) ^ (ρ - 1)‖) ^ 2 := sq_nonneg _
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
          have : ‖(x : ℂ) ^ (ρ - 1)‖ * ‖F x‖ * 2 ≤ δ⁻¹ * ‖F x‖ ^ 2 + δ * ‖(x : ℂ) ^ (ρ - 1)‖ ^ 2 := by
            have hd : δ * (δ⁻¹ * ‖F x‖ ^ 2 + δ * ‖(x : ℂ) ^ (ρ - 1)‖ ^ 2) =
                ‖F x‖ ^ 2 + δ ^ 2 * ‖(x : ℂ) ^ (ρ - 1)‖ ^ 2 := by field_simp
            nlinarith [key, hd, mul_pos hδ hδ]
          linarith
      _ = (δ⁻¹ * ∫ x in Ioc (0 : ℝ) 1, ‖F x‖ ^ 2) / 2 + δ * B / 2 := by
          rw [integral_div, integral_add (hF2.const_mul δ⁻¹) (hg2.const_mul δ), integral_const_mul,
            integral_const_mul]
          ring
      _ ≤ (δ⁻¹ * δ ^ 2) / 2 + δ * B / 2 := by gcongr
      _ = δ * (1 + B) / 2 := by field_simp
  rw [hP] at hbound
  have : ‖(1 : ℂ) / ρ‖ = 1 / ‖ρ‖ := by rw [norm_div, norm_one]
  rw [this, hδdef] at hbound
  have hpos : 0 < 1 + B := by linarith
  have : 1 / (‖ρ‖ * (1 + B)) * (1 + B) / 2 = 1 / (2 * ‖ρ‖) := by field_simp
  rw [this] at hbound
  have : 1 / (2 * ‖ρ‖) < 1 / ‖ρ‖ := by
    apply one_div_lt_one_div_of_lt hn; linarith
  linarith

/-- **Nyman–Beurling density implies the Riemann Hypothesis.** No bound states, no off-line
zeros: the half-plane `re ρ ≥ 1` is zero-free by Mathlib, the strip `1/2 < re ρ < 1` by
`zeta_ne_zero_of_nymanBeurling`, and the functional equation does the rest. -/
theorem riemannHypothesis_of_nymanBeurling (h : NymanBeurlingDense) : RiemannHypothesis := by
  apply GppOneSidedRH.riemannHypothesis_of_ne_zero
  intro s hs
  rcases lt_or_ge s.re 1 with h1 | h1
  · exact zeta_ne_zero_of_nymanBeurling h hs h1
  · exact riemannZeta_ne_zero_of_one_le_re h1

#print axioms zeta_eq_fracInt
#print axioms mul_fracInt_eq
#print axioms mellin_fracInv
#print axioms beurling_orthogonal
#print axioms zeta_ne_zero_of_nymanBeurling
#print axioms riemannHypothesis_of_nymanBeurling

end GppNymanBeurling
