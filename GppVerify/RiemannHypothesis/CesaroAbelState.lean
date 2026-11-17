/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Flint (D3 seat). Routed task: Turbo to Flint, 2026-11-12 (Heart of the Cosmos via
PR #11 comment 6832868926; Daniel's direction). Items 1–2 of the routed task.

# The Abel–Cesàro state on finite character sums

For `ε > 0`, the Abel–Cesàro state of the Cesàro papers (rh_cesaro_v2, ONON Pathway 1)
is the positive functional
  `ω_ε(F) = ε ∫ e^{−ε|u|} F(u) du`
on finite sums `F(u) = Σᵢ cᵢ e^{αᵢ u}` of scaling characters in the logarithmic
coordinate `u = log t` (so `αᵢ = sᵢ − 1/2`; the critical line is `Re αᵢ = 0`).
The sesquilinear form is `⟨F, G⟩_ε = ω_ε(F̄ · G)`. Note the normalisation is
`ε ∫` (Heart's routed statement), so `ω_ε(1) = 2`.

Labels:
* `integral_abel_char` (**PROVED**): the character formula
  `ω_ε(e^{β·}) = 2ε²/(ε² − β²)`, by a convergent positive integral **only in the
  strip** `|Re β| < ε` (the two half-line integrals are exactly Mathlib's
  `integral_exp_mul_complex_Ioi` / `integral_exp_mul_complex_Iic`).
* `abelState_eq_integral`, `abelForm_eq_integral` (**PROVED**): the state and the
  form are the stated integrals, under the strip hypotheses `|Re αᵢ| < ε`
  (state) resp. `|Re αᵢ| < ε/2` (form: the cross exponents `ᾱᵢ + αⱼ` must
  satisfy `|Re (ᾱᵢ + αⱼ)| < ε`).
* `abelForm_self_nonneg` (**PROVED**): `⟨F, F⟩_ε` is a nonnegative real number
  for every `ε > 0` in the strip: it is the integral of `ε e^{−ε|u|} |F(u)|² ≥ 0`.
* `tendsto_abelForm` (**PROVED**): for **every** finite exponent family (no strip
  hypothesis — this is the rational formula, not the integral), the termwise
  `ε → 0⁺` limit of the form is the diagonal/shadow selection
  `2 · Σ_{i,j : ᾱᵢ + αⱼ = 0} c̄ᵢ dⱼ`.
* `abelForm_limit_self_nonneg_onLine` (**PROVED**): on the critical line
  (`Re αᵢ = 0` for all `i`) the limit of `⟨F, F⟩_ε` is a nonnegative real:
  there it is the limit of the in-strip positive integrals.

Located boundary (Turbo's guardrail; Astra's Abel-domain obstruction, on record in
the 2026-10-20 Cesàro note): outside the strip the formula `2ε²/(ε² − β²)` is an
analytic continuation, **not** a positive integral, and no positivity is claimed
for it there. The pole characters of `Kψ` sit at `Re α = ±1/2`, outside the strip
for every `ε < 1`; see `CesaroWeilGram.lean` for what this does to item 4.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace GppCesaroAbel

open MeasureTheory Complex Filter Topology Finset ComplexConjugate

/-- The Abel–Cesàro kernel value `ω_ε(e^{β·}) = 2ε²/(ε² − β²)`. As a formula this
is defined for all `β` (junk value at the poles); as a convergent positive integral
it is valid only for `|Re β| < ε` (`integral_abel_char`). -/
noncomputable def abelValue (ε : ℝ) (β : ℂ) : ℂ := 2 * (ε : ℂ) ^ 2 / ((ε : ℂ) ^ 2 - β ^ 2)

/-- Evaluation of the finite character sum `F(u) = Σᵢ cᵢ e^{αᵢ u}`. -/
noncomputable def evalSum {n : ℕ} (α : Fin n → ℂ) (c : Fin n → ℂ) (u : ℝ) : ℂ :=
  ∑ i, c i * Complex.exp (α i * u)

/-- The Abel–Cesàro state of a finite character sum, by its character formula:
`ω_ε(F) = Σᵢ cᵢ · 2ε²/(ε² − αᵢ²)`. -/
noncomputable def abelState (ε : ℝ) {n : ℕ} (α : Fin n → ℂ) (c : Fin n → ℂ) : ℂ :=
  ∑ i, c i * abelValue ε (α i)

/-- The Abel–Cesàro sesquilinear form, by its character formula:
`⟨F, G⟩_ε = Σᵢⱼ c̄ᵢ dⱼ · 2ε²/(ε² − (ᾱᵢ + αⱼ)²)`. -/
noncomputable def abelForm (ε : ℝ) {n : ℕ} (α : Fin n → ℂ) (c d : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (c i) * d j * abelValue ε (conj (α i) + α j)

/-! ## The character integral -/

private theorem abel_integrand_Ioi {ε : ℝ} {β : ℂ} (u : ℝ) (hu : 0 ≤ u) :
    (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
      = (ε : ℂ) * Complex.exp ((β - ε) * u) := by
  rw [abs_of_nonneg hu, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem abel_integrand_Iic {ε : ℝ} {β : ℂ} (u : ℝ) (hu : u ≤ 0) :
    (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
      = (ε : ℂ) * Complex.exp ((β + ε) * u) := by
  rw [abs_of_nonpos hu, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Integrability of one Abel–Cesàro character integrand on the whole line,
in the strip `|Re β| < ε`. -/
theorem integrable_abel_char {ε : ℝ} (hε : 0 < ε) {β : ℂ} (hβ : |β.re| < ε) (w : ℂ) :
    Integrable (fun u : ℝ => w * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)) := by
  have hβ' := abs_lt.mp hβ
  have hIoi : IntegrableOn (fun u : ℝ => w * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u))
      (Set.Ioi 0) := by
    have hbase : Integrable (fun u : ℝ => Complex.exp ((β - ε) * u))
        (volume.restrict (Set.Ioi 0)) :=
      integrableOn_exp_mul_complex_Ioi (a := β - ε)
        (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith) 0
    have h := hbase.const_mul w
    refine IntegrableOn.congr_fun h (fun u hu => ?_) measurableSet_Ioi
    have h2 := abel_integrand_Ioi (ε := ε) (β := β) u (le_of_lt hu)
    have hεℂ : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have h3 : Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
        = Complex.exp ((β - ε) * u) := by
      have h4 := congrArg (fun z : ℂ => (ε : ℂ)⁻¹ * z) h2
      simpa [mul_assoc, inv_mul_cancel_left₀ hεℂ] using h4
    have h5 : w * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
        = w * Complex.exp ((β - ε) * u) := by
      rw [mul_assoc, h3]
    rw [h5]
  have hIic : IntegrableOn (fun u : ℝ => w * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u))
      (Set.Iic 0) := by
    have hbase : Integrable (fun u : ℝ => Complex.exp ((β + ε) * u))
        (volume.restrict (Set.Iic 0)) :=
      integrableOn_exp_mul_complex_Iic (a := β + ε)
        (by simp only [Complex.add_re, Complex.ofReal_re]; linarith) 0
    have h := hbase.const_mul w
    refine IntegrableOn.congr_fun h (fun u hu => ?_) measurableSet_Iic
    have h2 := abel_integrand_Iic (ε := ε) (β := β) u hu
    have hεℂ : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have h3 : Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
        = Complex.exp ((β + ε) * u) := by
      have h4 := congrArg (fun z : ℂ => (ε : ℂ)⁻¹ * z) h2
      simpa [mul_assoc, inv_mul_cancel_left₀ hεℂ] using h4
    have h5 : w * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
        = w * Complex.exp ((β + ε) * u) := by
      rw [mul_assoc, h3]
    rw [h5]
  have hunion := hIic.union hIoi
  rwa [Set.Iic_union_Ioi_of_le le_rfl, integrableOn_univ] at hunion

/-- **The character formula (PROVED)**: for `|Re β| < ε`,
`ω_ε(e^{β·}) = ε ∫ e^{−ε|u|} e^{βu} du = 2ε²/(ε² − β²)`, the integral being
absolutely convergent. -/
theorem integral_abel_char {ε : ℝ} (hε : 0 < ε) {β : ℂ} (hβ : |β.re| < ε) :
    ∫ u : ℝ, (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
      = abelValue ε β := by
  have hβ' := abs_lt.mp hβ
  have hβ1 : β - (ε : ℂ) ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at h2
    linarith
  have hβ2 : β + (ε : ℂ) ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h2
    linarith
  have hεβ1 : (ε : ℂ) - β ≠ 0 := by
    intro h
    apply hβ1
    have h2 : β - (ε : ℂ) = -((ε : ℂ) - β) := by ring
    rw [h2, h, neg_zero]
  have hεβ2 : (ε : ℂ) + β ≠ 0 := by rwa [add_comm] at hβ2
  have hsq : (ε : ℂ) ^ 2 - β ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hεβ2 hεβ1
  have hInt := integrable_abel_char hε hβ (ε : ℂ)
  have hsplit : ∫ u : ℝ, (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
      = (∫ u in Set.Iic (0 : ℝ), (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u))
        + ∫ u in Set.Ioi (0 : ℝ), (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u) := by
    have h := integral_add_compl (μ := volume) (s := Set.Iic (0 : ℝ))
      (f := fun u : ℝ => (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u))
      measurableSet_Iic hInt
    rw [Set.compl_Iic] at h
    exact h.symm
  rw [hsplit]
  have hIoi : ∫ u in Set.Ioi (0 : ℝ), (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
      = (ε : ℂ) / (ε - β) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => abel_integrand_Ioi u (le_of_lt hu)),
      integral_const_mul,
      integral_exp_mul_complex_Ioi (a := β - ε)
        (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith) 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
    ring
  have hIic : ∫ u in Set.Iic (0 : ℝ), (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
      = (ε : ℂ) / (ε + β) := by
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun u hu => abel_integrand_Iic u hu),
      integral_const_mul,
      integral_exp_mul_complex_Iic (a := β + ε)
        (by simp only [Complex.add_re, Complex.ofReal_re]; linarith) 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
    ring
  rw [hIoi, hIic]
  unfold abelValue
  field_simp
  ring

/-- The character integral with an arbitrary constant in front. -/
theorem integral_abel_char_mul {ε : ℝ} (hε : 0 < ε) {β : ℂ} (hβ : |β.re| < ε) (w : ℂ) :
    ∫ u : ℝ, w * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)
      = w * (ε : ℂ)⁻¹ * abelValue ε β := by
  have hεℂ : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hpt : (fun u : ℝ => w * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u))
      = fun u : ℝ => (w * (ε : ℂ)⁻¹) * ((ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (β * u)) := by
    funext u
    field_simp
  rw [hpt, integral_const_mul, integral_abel_char hε hβ]

/-! ## Pointwise decomposition of the integrands -/

private theorem state_integrand_decomp {n : ℕ} (α : Fin n → ℂ) (c : Fin n → ℂ)
    (ε : ℝ) (u : ℝ) :
    (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * evalSum α c u
      = ∑ i, ((ε : ℂ) * c i) * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp (α i * u) := by
  rw [evalSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem form_integrand_decomp {n : ℕ} (α : Fin n → ℂ) (c d : Fin n → ℂ)
    (ε : ℝ) (u : ℝ) :
    (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * conj (evalSum α c u) * evalSum α d u
      = ∑ i, ∑ j, ((ε : ℂ) * (conj (c i) * d j)) * Complex.exp (-(ε : ℂ) * |u|)
          * Complex.exp ((conj (α i) + α j) * u) := by
  have hconj : conj (evalSum α c u)
      = ∑ i, conj (c i) * Complex.exp (conj (α i) * u) := by
    rw [evalSum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal]
  have hexp : ∀ i j : Fin n, Complex.exp (conj (α i) * u) * Complex.exp (α j * u)
      = Complex.exp ((conj (α i) + α j) * u) := by
    intro i j
    rw [← Complex.exp_add, add_mul]
  rw [hconj, evalSum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hexp]
  ring

/-! ## The state and the form as integrals -/

/-- **PROVED**: in the strip `|Re αᵢ| < ε` for all `i`, the Abel–Cesàro state is
the integral `ω_ε(F) = ε ∫ e^{−ε|u|} F(u) du`. -/
theorem abelState_eq_integral {ε : ℝ} (hε : 0 < ε) {n : ℕ} {α : Fin n → ℂ} {c : Fin n → ℂ}
    (hα : ∀ i, |(α i).re| < ε) :
    abelState ε α c = ∫ u : ℝ, (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * evalSum α c u := by
  have hεℂ : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  rw [integral_congr_ae (Filter.Eventually.of_forall fun u => state_integrand_decomp α c ε u),
    integral_finsetSum _ (fun i _ => integrable_abel_char hε (hα i) _)]
  unfold abelState
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_abel_char_mul hε (hα i) ((ε : ℂ) * c i)]
  show c i * abelValue ε (α i) = (↑ε * c i) * (↑ε)⁻¹ * abelValue ε (α i)
  field_simp

/-- **PROVED**: in the strip `|Re αᵢ| < ε/2` for all `i`, the Abel–Cesàro form is
the integral `⟨F, G⟩_ε = ε ∫ e^{−ε|u|} F(u)̄ G(u) du`. -/
theorem abelForm_eq_integral {ε : ℝ} (hε : 0 < ε) {n : ℕ} {α : Fin n → ℂ}
    {c d : Fin n → ℂ} (hα : ∀ i, |(α i).re| < ε / 2) :
    abelForm ε α c d
      = ∫ u : ℝ, (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * conj (evalSum α c u) * evalSum α d u := by
  have hεℂ : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hβ : ∀ i j, |(conj (α i) + α j).re| < ε := by
    intro i j
    simp only [Complex.add_re, Complex.conj_re]
    have h1 := abs_lt.mp (hα i)
    have h2 := abs_lt.mp (hα j)
    rw [abs_lt]
    constructor <;> linarith
  rw [integral_congr_ae (Filter.Eventually.of_forall fun u => form_integrand_decomp α c d ε u),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => integrable_abel_char hε (hβ i j) _))]
  unfold abelForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => integrable_abel_char hε (hβ i j) _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_abel_char_mul hε (hβ i j) ((ε : ℂ) * (conj (c i) * d j))]
  show conj (c i) * d j * abelValue ε (conj (α i) + α j)
    = (↑ε * (conj (c i) * d j)) * (↑ε)⁻¹ * abelValue ε (conj (α i) + α j)
  field_simp

/-! ## Positivity in the strip -/

/-- **PROVED (positivity)**: in the strip, `⟨F, F⟩_ε` is a nonnegative real
number for every `ε > 0`: it equals `∫ ε e^{−ε|u|} |F(u)|² du ≥ 0`. -/
theorem abelForm_self_nonneg {ε : ℝ} (hε : 0 < ε) {n : ℕ} {α : Fin n → ℂ}
    {c : Fin n → ℂ} (hα : ∀ i, |(α i).re| < ε / 2) :
    (abelForm ε α c c).im = 0 ∧ 0 ≤ (abelForm ε α c c).re := by
  have hβ : ∀ i j, |(conj (α i) + α j).re| < ε := by
    intro i j
    simp only [Complex.add_re, Complex.conj_re]
    have h1 := abs_lt.mp (hα i)
    have h2 := abs_lt.mp (hα j)
    rw [abs_lt]
    constructor <;> linarith
  have hInt : Integrable (fun u : ℝ => (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|)
      * conj (evalSum α c u) * evalSum α c u) := by
    have hInt0 : Integrable (fun u : ℝ => ∑ i, ∑ j, ((ε : ℂ) * (conj (c i) * c j))
        * Complex.exp (-(ε : ℂ) * |u|) * Complex.exp ((conj (α i) + α j) * u)) :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => integrable_abel_char hε (hβ i j) _))
    exact Integrable.congr hInt0
      (Filter.Eventually.of_forall fun u => (form_integrand_decomp α c c ε u).symm)
  have hform : ∀ u : ℝ, (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|)
        * conj (evalSum α c u) * evalSum α c u
      = ((ε * Real.exp (-ε * |u|) * ‖evalSum α c u‖ ^ 2 : ℝ) : ℂ) := by
    intro u
    rw [show (ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) = ((ε * Real.exp (-ε * |u|) : ℝ) : ℂ) by
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      congr 2
      push_cast
      ring]
    rw [mul_assoc, Complex.conj_mul']
    push_cast
    ring
  have hg : Integrable (fun u : ℝ => ε * Real.exp (-ε * |u|) * ‖evalSum α c u‖ ^ 2) := by
    have h := hInt.re
    refine Integrable.congr h (Filter.Eventually.of_forall fun u => ?_)
    show RCLike.re ((ε : ℂ) * Complex.exp (-(ε : ℂ) * |u|) * conj (evalSum α c u)
        * evalSum α c u) = ε * Real.exp (-ε * |u|) * ‖evalSum α c u‖ ^ 2
    rw [hform u]
    exact Complex.ofReal_re _
  rw [abelForm_eq_integral hε hα,
    integral_congr_ae (Filter.Eventually.of_forall hform),
    integral_complex_ofReal]
  constructor
  · simp
  · simp only [Complex.ofReal_re]
    exact integral_nonneg fun u =>
      mul_nonneg (mul_nonneg hε.le (Real.exp_nonneg _)) (sq_nonneg _)

/-! ## The `ε → 0⁺` limit of the formula (diagonal / shadow selection) -/

/-- For `β ≠ 0`, the kernel value tends to `0` as `ε → 0⁺`. (Formula-level
statement; no strip hypothesis.) -/
theorem tendsto_abelValue {β : ℂ} (hβ : β ≠ 0) :
    Tendsto (fun ε : ℝ => abelValue ε β) (𝓝[>] 0) (𝓝 0) := by
  have htend : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h
  have h1 : Tendsto (fun ε : ℝ => (2 : ℂ) * (ε : ℂ) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (htend.pow 2).const_mul (2 : ℂ)
  have h2 : Tendsto (fun ε : ℝ => (ε : ℂ) ^ 2 - β ^ 2) (𝓝[>] 0) (𝓝 (- β ^ 2)) := by
    simpa using (htend.pow 2).sub tendsto_const_nhds
  have hβ2 : (- β ^ 2) ≠ 0 := by
    simp only [neg_ne_zero, ne_eq, sq_eq_zero_iff]
    exact hβ
  have := h1.div h2 hβ2
  simpa only [Pi.div_def, zero_div, abelValue] using this

/-- At `β = 0` the kernel value is constantly `2` (for `ε ≠ 0`). -/
theorem abelValue_zero (ε : ℝ) (hε : ε ≠ 0) : abelValue ε 0 = 2 := by
  have hεℂ : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have h2 : (ε : ℂ) ^ 2 - (0 : ℂ) ^ 2 = (ε : ℂ) ^ 2 := by ring
  unfold abelValue
  rw [h2]
  field_simp

/-- **PROVED (the selection limit)**: for every finite exponent family, the
Abel–Cesàro form tends, as `ε → 0⁺`, to the diagonal/shadow pairing
`2 · Σ_{i,j : ᾱᵢ + αⱼ = 0} c̄ᵢ dⱼ`. No strip hypothesis: this is a statement
about the rational formula. -/
theorem tendsto_abelForm {n : ℕ} (α : Fin n → ℂ) (c d : Fin n → ℂ) :
    Tendsto (fun ε : ℝ => abelForm ε α c d) (𝓝[>] 0)
      (𝓝 (2 * ∑ i, ∑ j, if conj (α i) + α j = 0 then conj (c i) * d j else 0)) := by
  unfold abelForm
  rw [show (2 * ∑ i, ∑ j, if conj (α i) + α j = 0 then conj (c i) * d j else 0)
      = ∑ i, ∑ j, (2 : ℂ) * (if conj (α i) + α j = 0 then conj (c i) * d j else 0) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  by_cases h : conj (α i) + α j = 0
  · rw [if_pos h]
    have h2 : Tendsto (fun ε : ℝ => abelValue ε (conj (α i) + α j)) (𝓝[>] 0) (𝓝 2) := by
      rw [h]
      exact (tendsto_congr'
        (eventually_nhdsWithin_of_forall fun ε hε => (abelValue_zero ε (ne_of_gt hε)).symm)).mp
        tendsto_const_nhds
    have h3 := h2.const_mul (conj (c i) * d j)
    rwa [show conj (c i) * d j * 2 = 2 * (conj (c i) * d j) by ring] at h3
  · rw [if_neg h]
    have h3 := (tendsto_abelValue h).const_mul (conj (c i) * d j)
    simpa using h3

/-- **PROVED**: on the critical line, the `ε → 0⁺` limit of `⟨F, F⟩_ε` is a
nonnegative real number (it is the limit of the in-strip positive integrals). -/
theorem abelForm_limit_self_nonneg_onLine {n : ℕ} {α : Fin n → ℂ} (c : Fin n → ℂ)
    (hα : ∀ i, (α i).re = 0) :
    (2 * ∑ i, ∑ j, if conj (α i) + α j = 0 then conj (c i) * c j else 0).im = 0 ∧
    0 ≤ (2 * ∑ i, ∑ j, if conj (α i) + α j = 0 then conj (c i) * c j else 0).re := by
  have hlim := tendsto_abelForm α c c
  have hmem : ∀ ε ∈ Set.Ioi (0 : ℝ),
      (abelForm ε α c c).im = 0 ∧ 0 ≤ (abelForm ε α c c).re := by
    intro ε hε
    have hε' : 0 < ε := hε
    refine abelForm_self_nonneg hε' fun i => ?_
    rw [hα i]
    simp only [abs_zero]
    linarith
  have him : Tendsto (fun ε : ℝ => (abelForm ε α c c).im) (𝓝[>] 0)
      (𝓝 (2 * ∑ i, ∑ j, if conj (α i) + α j = 0 then conj (c i) * c j else 0).im) :=
    (Complex.continuous_im.tendsto _).comp hlim
  have hre : Tendsto (fun ε : ℝ => (abelForm ε α c c).re) (𝓝[>] 0)
      (𝓝 (2 * ∑ i, ∑ j, if conj (α i) + α j = 0 then conj (c i) * c j else 0).re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  constructor
  · have him0 : Tendsto (fun ε : ℝ => (abelForm ε α c c).im) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_congr' (eventually_nhdsWithin_of_forall
        (fun ε hε => ((hmem ε hε).1).symm))).mp tendsto_const_nhds
    exact tendsto_nhds_unique him him0
  · exact ge_of_tendsto hre (eventually_nhdsWithin_of_forall fun ε hε => (hmem ε hε).2)

end GppCesaroAbel

#print axioms GppCesaroAbel.integral_abel_char
#print axioms GppCesaroAbel.abelState_eq_integral
#print axioms GppCesaroAbel.abelForm_eq_integral
#print axioms GppCesaroAbel.abelForm_self_nonneg
#print axioms GppCesaroAbel.tendsto_abelForm
#print axioms GppCesaroAbel.abelForm_limit_self_nonneg_onLine
