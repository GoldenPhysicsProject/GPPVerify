import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The Abel regularization of the Cesàro invariant mean

Formalizes Theorem 3.2 of Toupin, *Haar Measure Self-Duality, Abel Regularization of the
Cesàro Mean, and the Riemann Hypothesis* (`rh_cesaro_v2.tex`): the regularized state
`ω_ε(f) = (ε/2) ∫₀^∞ e^{-ε|log t|} f(t) dt/t`, written in the logarithmic variable
`u = log t` where it becomes `(ε/2) ∫_ℝ e^{-ε|u|} g(u) du`, satisfies

* **(i) positivity**: `ω_ε(f²) ≥ 0` — the integrand is pointwise nonnegative
  (`abel_state_sq_nonneg`);
* **(ii) the character formula**: `ω_ε(t^α) = ε²/(ε²-α²)` for `|α| < ε`
  (`abel_character_formula`) — the paper's eq. (char-calc), computed exactly as there by
  splitting the line at `u = 0` into two convergent exponential integrals;
* **(iii) the critical-line limit**: `ω_ε(1) = 1` exactly for every `ε > 0`
  (`abel_state_one`), while for `γ ≠ 0` the formula value `ε²/(ε²+γ²)` (the specialization
  of (ii) to the purely-imaginary exponent `α = iγ` relevant on the critical line) tends
  to `0` as `ε → 0` (`tendsto_abel_formula_zero`) — the δ-selection of `γ = 0`.

The integrals are stated in the log variable as the sum of their two half-line pieces
(`Iic 0` and `Ioi 0`), which is exactly how the paper's proof of (ii) evaluates them; each
piece is a genuinely convergent improper exponential integral
(`integral_exp_mul_Ioi`/`integral_comp_neg_Ioi`, Mathlib). Property (iii)'s vanishing
limit is where the paper's identification gets its δ_{ρ', 1-ρ̄} selection: only the
self-dual pairing `α = 0` survives `ε → 0⁺`.

Together with `CesaroMeanDivergence.lean` (the unregularized mean diverges off the
critical line) and `born_rule_cesaro` (`RHProofStructure.lean`, the unregularized mean is
exactly 1 on it), this completes the elementary-analysis layer of the paper; the
operator-theoretic layer (Yakaboylu's Riemann operator, biorthogonal system, and
intertwining operator, arXiv:2408.15135) is genuinely deeper functional analysis and is
not attempted here.
-/

namespace GppAbelCesaro

open MeasureTheory Filter

/-- The negative-half-line exponential integral: `∫_{u ≤ 0} e^{b·u} du = 1/b` for `b > 0`.
    Obtained from Mathlib's positive-half-line `integral_exp_mul_Ioi` by the reflection
    `u ↦ -u` (`integral_comp_neg_Ioi`). -/
theorem integral_exp_mul_Iic_zero {b : ℝ} (hb : 0 < b) :
    ∫ u in Set.Iic (0 : ℝ), Real.exp (b * u) = 1 / b := by
  have hrefl := integral_comp_neg_Ioi (0 : ℝ) (fun u => Real.exp (b * u))
  rw [neg_zero] at hrefl
  rw [← hrefl]
  have heq : ∀ x ∈ Set.Ioi (0 : ℝ), Real.exp (b * -x) = Real.exp (-b * x) := by
    intro x _
    rw [mul_neg, neg_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
      integral_exp_mul_Ioi (by linarith : -b < 0) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]

/-- **Positivity of the regularized state** (Theorem 3.2 (i)): `ω_ε(f²) ≥ 0`, since the
    integrand `e^{-ε|u|} f(u)²` is pointwise nonnegative. Stated for each half-line piece
    summed, matching the evaluation form used throughout this file. -/
theorem abel_state_sq_nonneg {ε : ℝ} (hε : 0 ≤ ε) (f : ℝ → ℝ) :
    0 ≤ ε / 2 * ((∫ u in Set.Iic (0 : ℝ), Real.exp (-ε * |u|) * f u ^ 2) +
      ∫ u in Set.Ioi (0 : ℝ), Real.exp (-ε * |u|) * f u ^ 2) := by
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · exact setIntegral_nonneg measurableSet_Iic fun u _ => by positivity
  · exact setIntegral_nonneg measurableSet_Ioi fun u _ => by positivity

/-- **The character formula** (Theorem 3.2 (ii), the paper's eq. (char-calc)): in the
    logarithmic variable, `ω_ε(t^α) = (ε/2) ∫_ℝ e^{-ε|u|} e^{α·u} du = ε²/(ε²-α²)` for
    `|α| < ε`. The line integral is evaluated as the paper does: split at `u = 0`, where
    `|u|` resolves to `-u` resp. `u`, leaving two convergent exponential integrals with
    values `1/(ε+α)` and `1/(ε-α)`. -/
theorem abel_character_formula {ε α : ℝ} (hα : |α| < ε) :
    ε / 2 * ((∫ u in Set.Iic (0 : ℝ), Real.exp (-ε * |u|) * Real.exp (α * u)) +
      ∫ u in Set.Ioi (0 : ℝ), Real.exp (-ε * |u|) * Real.exp (α * u)) =
    ε ^ 2 / (ε ^ 2 - α ^ 2) := by
  obtain ⟨hα1, hα2⟩ := abs_lt.mp hα
  have hεα : 0 < ε + α := by linarith
  have hαε : α - ε < 0 := by linarith
  have hL : (∫ u in Set.Iic (0 : ℝ), Real.exp (-ε * |u|) * Real.exp (α * u)) =
      1 / (ε + α) := by
    have heq : ∀ u ∈ Set.Iic (0 : ℝ),
        Real.exp (-ε * |u|) * Real.exp (α * u) = Real.exp ((ε + α) * u) := by
      intro u hu
      rw [abs_of_nonpos hu, ← Real.exp_add]
      congr 1
      ring
    rw [setIntegral_congr_fun measurableSet_Iic heq, integral_exp_mul_Iic_zero hεα]
  have hR : (∫ u in Set.Ioi (0 : ℝ), Real.exp (-ε * |u|) * Real.exp (α * u)) =
      1 / (ε - α) := by
    have heq : ∀ u ∈ Set.Ioi (0 : ℝ),
        Real.exp (-ε * |u|) * Real.exp (α * u) = Real.exp ((α - ε) * u) := by
      intro u hu
      rw [abs_of_pos hu, ← Real.exp_add]
      congr 1
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq,
        integral_exp_mul_Ioi hαε 0, mul_zero, Real.exp_zero,
        show α - ε = -(ε - α) by ring, div_neg, neg_div, neg_neg]
  rw [hL, hR]
  have h1 : ε + α ≠ 0 := ne_of_gt hεα
  have h2 : ε - α ≠ 0 := ne_of_gt (by linarith)
  have h3 : ε ^ 2 - α ^ 2 ≠ 0 := by
    rw [show ε ^ 2 - α ^ 2 = (ε + α) * (ε - α) by ring]
    exact mul_ne_zero h1 h2
  field_simp
  ring

/-- **`ω_ε(1) = 1` exactly, for every `ε > 0`** (Theorem 3.2 (iii), `γ = 0` case): the
    `α = 0` specialization of the character formula. The regularized mean of the constant
    function is exactly `1` — not merely in the limit — mirroring how the unregularized
    Cesàro mean is exactly `1` at `σ = 1/2` (`born_rule_cesaro`). -/
theorem abel_state_one {ε : ℝ} (hε : 0 < ε) :
    ε / 2 * ((∫ u in Set.Iic (0 : ℝ), Real.exp (-ε * |u|)) +
      ∫ u in Set.Ioi (0 : ℝ), Real.exp (-ε * |u|)) = 1 := by
  have h := abel_character_formula (ε := ε) (α := 0) (by rwa [abs_zero])
  have hsimp : ∀ u : ℝ, Real.exp (-ε * |u|) * Real.exp ((0 : ℝ) * u) =
      Real.exp (-ε * |u|) := by
    intro u
    rw [zero_mul, Real.exp_zero, mul_one]
  simp_rw [hsimp] at h
  rw [h, show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero]
  exact div_self (pow_ne_zero 2 (ne_of_gt hε))

/-- **The critical-line δ-selection** (Theorem 3.2 (iii), `γ ≠ 0` case): the character
    formula's value at a purely imaginary exponent `α = iγ` is `ε²/(ε²+γ²)`, and this
    tends to `0` as `ε → 0` whenever `γ ≠ 0`. Combined with `abel_state_one` (the value is
    identically `1` at `γ = 0`), the family `ω_ε` selects exactly the self-dual pairing
    `γ = 0` in the limit — the mechanism behind the `δ_{ρ', 1-ρ̄}` matrix-element limit in
    the paper. -/
theorem tendsto_abel_formula_zero {γ : ℝ} (hγ : γ ≠ 0) :
    Tendsto (fun ε : ℝ => ε ^ 2 / (ε ^ 2 + γ ^ 2)) (nhds 0) (nhds 0) := by
  have hnum : Tendsto (fun ε : ℝ => ε ^ 2) (nhds 0) (nhds 0) := by
    have := (continuous_pow 2 (M := ℝ)).tendsto 0
    simpa using this
  have hden : Tendsto (fun ε : ℝ => ε ^ 2 + γ ^ 2) (nhds 0) (nhds (γ ^ 2)) := by
    have := hnum.add (tendsto_const_nhds (x := γ ^ 2) (f := nhds (0 : ℝ)))
    simpa using this
  have hγ2 : γ ^ 2 ≠ 0 := pow_ne_zero 2 hγ
  have := hnum.div hden hγ2
  simpa [Pi.div_def] using this

/-! ## The full-line form

The pieces above state the character formula as the sum of its two half-line integrals —
exactly how the paper evaluates it. The theorems below glue the halves into the literal
full-line statement `(ε/2) ∫_ℝ e^{-ε|u|} e^{αu} du = ε²/(ε²-α²)`, which requires knowing
each half is genuinely integrable (`exp_neg_integrableOn_Ioi` on the right;
reflection via `IntegrableOn.comp_neg_Iic` on the left). -/

/-- The Abel-weighted character is integrable on the right half-line: on `Ioi 0` it equals
    the decaying exponential `e^{-(ε-α)u}`. -/
theorem integrableOn_abel_char_Ioi {ε α : ℝ} (hα : |α| < ε) :
    IntegrableOn (fun u => Real.exp (-ε * |u|) * Real.exp (α * u)) (Set.Ioi (0 : ℝ)) := by
  obtain ⟨hα1, hα2⟩ := abs_lt.mp hα
  have hbase : IntegrableOn (fun u => Real.exp (-(ε - α) * u)) (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro u hu
  show Real.exp (-(ε - α) * u) = Real.exp (-ε * |u|) * Real.exp (α * u)
  rw [abs_of_pos hu, ← Real.exp_add]
  congr 1
  ring

/-- The Abel-weighted character is integrable on the left half-line: reflected through
    `u ↦ -u` it becomes the right-half-line decaying exponential `e^{-(ε+α)u}`. -/
theorem integrableOn_abel_char_Iic {ε α : ℝ} (hα : |α| < ε) :
    IntegrableOn (fun u => Real.exp (-ε * |u|) * Real.exp (α * u)) (Set.Iic (0 : ℝ)) := by
  obtain ⟨hα1, hα2⟩ := abs_lt.mp hα
  have hIci : IntegrableOn (fun u => Real.exp (-(ε + α) * u)) (Set.Ici (-(0 : ℝ))) := by
    rw [neg_zero, integrableOn_Ici_iff_integrableOn_Ioi]
    exact exp_neg_integrableOn_Ioi 0 (by linarith)
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-(ε + α) * -x)) (Set.Iic (0 : ℝ)) :=
    hIci.comp_neg_Iic
  refine hneg.congr_fun ?_ measurableSet_Iic
  intro u hu
  show Real.exp (-(ε + α) * -u) = Real.exp (-ε * |u|) * Real.exp (α * u)
  rw [abs_of_nonpos hu, ← Real.exp_add]
  congr 1
  ring

/-- **Character formula, full-line form** (Theorem 3.2 (ii) as literally stated):
    `(ε/2) ∫_ℝ e^{-ε|u|} e^{αu} du = ε²/(ε²-α²)` for `|α| < ε` — the two-piece version
    glued at `u = 0`, now that both halves are known integrable. -/
theorem abel_character_formula_integral {ε α : ℝ} (hα : |α| < ε) :
    ε / 2 * ∫ u : ℝ, Real.exp (-ε * |u|) * Real.exp (α * u) = ε ^ 2 / (ε ^ 2 - α ^ 2) := by
  have hsplit : (∫ u : ℝ, Real.exp (-ε * |u|) * Real.exp (α * u)) =
      (∫ u in Set.Iic (0 : ℝ), Real.exp (-ε * |u|) * Real.exp (α * u)) +
        ∫ u in Set.Ioi (0 : ℝ), Real.exp (-ε * |u|) * Real.exp (α * u) := by
    rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        (integrableOn_abel_char_Iic hα) (integrableOn_abel_char_Ioi hα)]
  rw [hsplit]
  exact abel_character_formula hα

/-- **`ω_ε(1) = 1`, full-line form**: the Abel weight `e^{-ε|u|}` integrates to `2/ε` over
    the whole line, so the normalized state assigns the constant function exactly `1`. -/
theorem abel_state_one_integral {ε : ℝ} (hε : 0 < ε) :
    ε / 2 * ∫ u : ℝ, Real.exp (-ε * |u|) = 1 := by
  have h := abel_character_formula_integral (ε := ε) (α := 0) (by rwa [abs_zero])
  have hsimp : ∀ u : ℝ, Real.exp (-ε * |u|) * Real.exp ((0 : ℝ) * u) =
      Real.exp (-ε * |u|) := by
    intro u
    rw [zero_mul, Real.exp_zero, mul_one]
  simp_rw [hsimp] at h
  rw [h, show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero]
  exact div_self (pow_ne_zero 2 (ne_of_gt hε))

end GppAbelCesaro
