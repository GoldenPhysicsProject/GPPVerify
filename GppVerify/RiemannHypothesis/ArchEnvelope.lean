import GppVerify.Upstream.DigammaVerticalBounds
import GppVerify.RiemannHypothesis.DigammaGaussSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The archimedean factor of `Kψ`: continuity and an integrable envelope

On `flint/workbench`, `KreinKpsiContinuous.lean` proves continuity of `Kψ` modulo two named
obligations about the archimedean factor

  `archFactor t = Re (logDeriv Γ)(1/4 + i t/2) - log π`

weighted by `bigPsi t = (sin(t/2)/(t/2))²` (and `1` at `t = 0`):

* `ArchGammaFactorContinuous : ContinuousOn archFactor (Ioi 0)`;
* `ArchEnvelopeIntegrable : IntegrableOn (fun t => bigPsi t ^ 2 * |archFactor t|) (Ioi 0)`.

This file proves both, with the two functions written out explicitly (`archFactor'`, `bigPsi'`),
because their in-tree definitions live on branches that are not on `main`. The definitions here
agree with those clause for clause, so the obligations are discharged by `exact` once the
branches meet (`logDeriv Γ = digamma` holds by definition, `Complex.digamma_def`).

* `continuous_archFactor'`: `archFactor'` is continuous on all of `ℝ`. Analyticity of `ψ` off
  the poles (`GppDigammaGaussSeries.analyticAt_digamma`); `1/4 + i t/2` is never an integer.
* `abs_archFactor'_le`: `|archFactor' t| ≤ 12 + t²`, from the two-sided vertical enclosure
  `Complex.re_digamma_mem_Icc` at `M = 0`.
* `bigPsi'_le`: `0 ≤ bigPsi' t ≤ 8/(1 + t²)`.
* `integrable_envelope`: `bigPsi'² · |archFactor'|` is integrable on `ℝ`, dominated by
  `768/(1 + t²)`. Hence `integrableOn_envelope` on `(0, ∞)`.

No named premises. No `sorry`. Standard axioms only.
-/

namespace GppArchEnvelope

open MeasureTheory Set Filter Topology Complex

/-- `archFactor t = Re ψ(1/4 + i t/2) - log π`, written with `logDeriv Γ` exactly as on
`flint/workbench`. -/
noncomputable def archFactor' (t : ℝ) : ℝ :=
  (logDeriv Complex.Gamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re - Real.log Real.pi

/-- `bigPsi t = (sin(t/2)/(t/2))²`, `bigPsi 0 = 1`, exactly as in `GppKreinHPsi.bigPsi`. -/
noncomputable def bigPsi' (t : ℝ) : ℝ := if t = 0 then 1 else (Real.sin (t / 2) / (t / 2)) ^ 2

theorem archFactor'_eq (t : ℝ) :
    archFactor' t = (Complex.digamma ⟨1 / 4, t / 2⟩).re - Real.log Real.pi := by
  unfold archFactor'
  rw [← Complex.digamma_def]
  congr 3
  apply Complex.ext <;> simp

theorem mem_integerComplement (t : ℝ) :
    ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have h := congrArg Complex.re hn
  simp at h
  have h1 : (0 : ℝ) < n := by rw [h]; norm_num
  have h2 : (n : ℝ) < 1 := by rw [h]; norm_num
  have h1' : (0 : ℤ) < n := by exact_mod_cast h1
  have h2' : n < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- **`ArchGammaFactorContinuous`, in a stronger form**: `archFactor'` is continuous on `ℝ`. -/
theorem continuous_archFactor' : Continuous archFactor' := by
  unfold archFactor'
  rw [← Complex.digamma_def]
  have hpath : Continuous fun t : ℝ => (1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    fun_prop
  have hd : Continuous fun t : ℝ => Complex.digamma ((1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (g := Complex.digamma)
        (f := fun t : ℝ => (1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)
        (GppDigammaGaussSeries.analyticAt_digamma (mem_integerComplement t)).continuousAt
        hpath.continuousAt
  exact (Complex.continuous_re.comp hd).sub continuous_const

theorem continuousOn_archFactor' : ContinuousOn archFactor' (Ioi 0) :=
  continuous_archFactor'.continuousOn

/-- `|archFactor' t| ≤ 12 + t²`. -/
theorem abs_archFactor'_le (t : ℝ) : |archFactor' t| ≤ 12 + t ^ 2 := by
  have h := Complex.re_digamma_mem_Icc (a := 1 / 4) (by norm_num) (t / 2) 0
  simp only [CharP.cast_eq_zero, add_zero, Finset.range_zero, Finset.sum_empty, sub_zero] at h
  obtain ⟨hlo, hhi⟩ := h
  rw [archFactor'_eq]
  set b : ℝ := t / 2 with hb
  set y : ℝ := (1 / 4 + 1 / 2) ^ 2 + b ^ 2 with hy
  have hy0 : 0 < y := by positivity
  -- log y bounds
  have hlog_up : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
  have hlog_lo : -1 ≤ Real.log y := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hy0)
    rw [Real.log_inv] at this
    have hyinv : y⁻¹ ≤ 16 / 9 := by
      rw [inv_le_comm₀ hy0 (by norm_num)]; rw [hy]; nlinarith [sq_nonneg b]
    linarith
  have hq0 : 0 ≤ (1 / 4 : ℝ) / ((1 / 4) ^ 2 + b ^ 2) := by positivity
  have hq1 : (1 / 4 : ℝ) / ((1 / 4) ^ 2 + b ^ 2) ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg b]
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpi1 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_d2]
  have hb2 : b ^ 2 = t ^ 2 / 4 := by rw [hb]; ring
  rw [abs_le]
  constructor
  · -- lower: Re ψ ≥ log y/2 - 4 - 4 ≥ -9
    have : (Complex.digamma ⟨1 / 4, b⟩).re ≥ -1 / 2 - 4 - 4 := by
      have e : (1 : ℝ) / (4 * (1 / 4) ^ 2) = 4 := by norm_num
      rw [e] at hlo; linarith
    nlinarith [sq_nonneg t]
  · have e : (1 : ℝ) / (2 * (1 / 4) ^ 2) = 8 := by norm_num
    rw [e] at hhi
    have : y - 1 ≤ t ^ 2 / 4 := by rw [hy, hb2]; linarith
    nlinarith [sq_nonneg t]

/-- `0 ≤ bigPsi' t`. -/
theorem bigPsi'_nonneg (t : ℝ) : 0 ≤ bigPsi' t := by
  unfold bigPsi'; split_ifs <;> positivity

/-- `bigPsi' t ≤ 8 / (1 + t²)`. -/
theorem bigPsi'_le (t : ℝ) : bigPsi' t ≤ 8 / (1 + t ^ 2) := by
  unfold bigPsi'
  split_ifs with ht
  · subst ht; norm_num
  · set x : ℝ := t / 2 with hx
    have hx0 : x ≠ 0 := by rw [hx]; exact div_ne_zero ht two_ne_zero
    have hsq : (Real.sin x / x) ^ 2 = Real.sin x ^ 2 / x ^ 2 := by rw [div_pow]
    have hs1 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
    have hs2 : Real.sin x ^ 2 ≤ x ^ 2 := by
      have := Real.abs_sin_le_abs (x := x)
      nlinarith [abs_nonneg (Real.sin x), sq_abs (Real.sin x), sq_abs x]
    have hxpos : 0 < x ^ 2 := by positivity
    rw [hsq]
    have h1 : Real.sin x ^ 2 / x ^ 2 ≤ 1 := by rw [div_le_one hxpos]; exact hs2
    have h2 : Real.sin x ^ 2 / x ^ 2 ≤ 4 / t ^ 2 := by
      have ht2 : x ^ 2 = t ^ 2 / 4 := by rw [hx]; ring
      rw [ht2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rcases le_total (t ^ 2) 1 with hle | hge
    · calc Real.sin x ^ 2 / x ^ 2 ≤ 1 := h1
        _ ≤ 8 / (1 + t ^ 2) := by rw [le_div_iff₀ (by positivity)]; linarith
    · calc Real.sin x ^ 2 / x ^ 2 ≤ 4 / t ^ 2 := h2
        _ ≤ 8 / (1 + t ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

/-- The envelope is dominated by `768/(1 + t²)`. -/
theorem envelope_le (t : ℝ) :
    bigPsi' t ^ 2 * |archFactor' t| ≤ 768 * (1 + t ^ 2)⁻¹ := by
  have h0 := bigPsi'_nonneg t
  have h1 := bigPsi'_le t
  have h2 := abs_archFactor'_le t
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hsq : bigPsi' t ^ 2 ≤ 64 / (1 + t ^ 2) ^ 2 := by
    calc bigPsi' t ^ 2 ≤ (8 / (1 + t ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 64 / (1 + t ^ 2) ^ 2 := by rw [div_pow]; norm_num
  calc bigPsi' t ^ 2 * |archFactor' t| ≤ 64 / (1 + t ^ 2) ^ 2 * (12 * (1 + t ^ 2)) := by
        apply mul_le_mul hsq _ (abs_nonneg _) (by positivity)
        nlinarith [sq_nonneg t]
    _ = 768 * (1 + t ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv]; field_simp; ring

theorem continuousOn_bigPsi' : ContinuousOn bigPsi' (Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => (Real.sin (t / 2) / (t / 2)) ^ 2) (Ioi 0) := by
    refine ContinuousOn.pow (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) 2
    intro t ht; exact div_ne_zero (ne_of_gt ht) two_ne_zero
  refine h.congr fun t ht => ?_
  have : t ≠ 0 := ne_of_gt ht
  simp [bigPsi', this]

/-- **`ArchEnvelopeIntegrable`**: the envelope is integrable on `(0, ∞)`. -/
theorem integrableOn_envelope :
    IntegrableOn (fun t => bigPsi' t ^ 2 * |archFactor' t|) (Ioi 0) volume := by
  have hdom : IntegrableOn (fun t : ℝ => 768 * (1 + t ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul 768).integrableOn
  refine hdom.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (continuousOn_bigPsi'.pow 2).mul (continuous_archFactor'.continuousOn.abs)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t _ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))]
    exact envelope_le t

end GppArchEnvelope
