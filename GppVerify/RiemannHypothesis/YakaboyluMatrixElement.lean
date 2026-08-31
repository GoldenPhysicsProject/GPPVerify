import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Yakaboylu's regularized matrix element (Lemma 4.3, eq. (49))

Formalizes the central calculation of Lemma 4.3 of Yakaboylu, *Nontrivial Riemann Zeros as
Spectrum* (arXiv:2408.15135v14), in its real-exponent form: the ε-regularized matrix
element of the intertwining operator between eigenstates evaluates, in the multiplicative
variable, to

  `(ε/2) (∫₀¹ t^{σ-2+ε} dt + ∫₁^∞ t^{σ-2-ε} dt) = ε²/(ε² - (σ-1)²)`

for `1 - ε < σ < 1 + ε` (the paper's convergence strip, with `σ` playing the role of
`Re(s̄ + s')`). The weight `e^{-ε|log t|}` resolves to `t^{ε}` on `(0,1)` and `t^{-ε}` on
`(1,∞)`, which is why the two half-integrals carry shifted exponents — this is the same
Abel regularization formalized in the logarithmic variable in
`AbelCesaroRegularization.lean` (`rh_cesaro_v2.tex` proves the two are the same state; the
substitution `u = log t` maps one formula to the other).

Also included: the two limit facts that make eq. (49) act as the Kronecker delta
`δ_{s̄+s',1}` of the paper's eq. (47) — the value is identically `1` at `σ = 1`
(`matrix_element_at_one`) and tends to `0` as `ε → 0` for every `σ ≠ 1`
(`tendsto_matrix_element_zero`). This δ-selection is what forces `ρ' = 1 - ρ̄` pairings in
the intertwining operator `Ŵ`, the engine of the paper's positivity argument.
-/

namespace GppYakaboylu

open MeasureTheory

/-- The `(0,1]` piece: `∫₀¹ t^{σ-2+ε} dt = 1/(σ-1+ε)`, convergent since the exponent
    exceeds `-1` exactly when `σ > 1 - ε`. -/
theorem integral_unit_interval_rpow {σ ε : ℝ} (h : 1 - ε < σ) :
    ∫ t in (0 : ℝ)..1, t ^ (σ - 2 + ε) = 1 / (σ - 1 + ε) := by
  have ha : (-1 : ℝ) < σ - 2 + ε := by linarith
  rw [integral_rpow (Or.inl ha), show σ - 2 + ε + 1 = σ - 1 + ε by ring, Real.one_rpow,
    Real.zero_rpow (by linarith : σ - 1 + ε ≠ 0), sub_zero]

/-- The `[1,∞)` piece: `∫₁^∞ t^{σ-2-ε} dt = 1/(1+ε-σ)`, convergent since the exponent is
    below `-1` exactly when `σ < 1 + ε`. -/
theorem integral_Ioi_one_rpow {σ ε : ℝ} (h : σ < 1 + ε) :
    ∫ t in Set.Ioi (1 : ℝ), t ^ (σ - 2 - ε) = 1 / (1 + ε - σ) := by
  have ha : σ - 2 - ε < -1 := by linarith
  rw [integral_Ioi_rpow_of_lt ha one_pos, Real.one_rpow,
    show σ - 2 - ε + 1 = -(1 + ε - σ) by ring, neg_div_neg_eq]

/-- **Yakaboylu Lemma 4.3, eq. (49)** (real-exponent form): the regularized matrix
    element evaluates to `ε²/(ε² - (σ-1)²)` on the convergence strip `1-ε < σ < 1+ε`. -/
theorem regularized_matrix_element {σ ε : ℝ} (h1 : 1 - ε < σ) (h2 : σ < 1 + ε) :
    ε / 2 * ((∫ t in (0 : ℝ)..1, t ^ (σ - 2 + ε)) +
      ∫ t in Set.Ioi (1 : ℝ), t ^ (σ - 2 - ε)) =
    ε ^ 2 / (ε ^ 2 - (σ - 1) ^ 2) := by
  rw [integral_unit_interval_rpow h1, integral_Ioi_one_rpow h2]
  have ha : σ - 1 + ε ≠ 0 := ne_of_gt (by linarith)
  have hb : (1 : ℝ) + ε - σ ≠ 0 := ne_of_gt (by linarith)
  have hc : ε ^ 2 - (σ - 1) ^ 2 ≠ 0 := by
    rw [show ε ^ 2 - (σ - 1) ^ 2 = (σ - 1 + ε) * (1 + ε - σ) by ring]
    exact mul_ne_zero ha hb
  field_simp
  ring

/-- At the self-dual point `σ = 1` the matrix element is exactly `1`, for every `ε ≠ 0` —
    the surviving diagonal of the paper's `δ_{s̄+s',1}` limit (eq. (47)). -/
theorem matrix_element_at_one {ε : ℝ} (hε : ε ≠ 0) :
    ε ^ 2 / (ε ^ 2 - ((1 : ℝ) - 1) ^ 2) = 1 := by
  rw [show ((1 : ℝ) - 1) ^ 2 = 0 by norm_num, sub_zero]
  exact div_self (pow_ne_zero 2 hε)

/-- Away from the self-dual point the matrix element vanishes in the `ε → 0` limit — the
    off-diagonal of the `δ_{s̄+s',1}` selection: only `ρ' = 1 - ρ̄` pairings survive in the
    intertwining operator `Ŵ`. -/
theorem tendsto_matrix_element_zero {σ : ℝ} (hσ : σ ≠ 1) :
    Filter.Tendsto (fun ε : ℝ => ε ^ 2 / (ε ^ 2 - (σ - 1) ^ 2)) (nhds 0) (nhds 0) := by
  have hnum : Filter.Tendsto (fun ε : ℝ => ε ^ 2) (nhds 0) (nhds 0) := by
    have := (continuous_pow 2 (M := ℝ)).tendsto 0
    simpa using this
  have hden : Filter.Tendsto (fun ε : ℝ => ε ^ 2 - (σ - 1) ^ 2) (nhds 0)
      (nhds (-(σ - 1) ^ 2)) := by
    have := hnum.sub (tendsto_const_nhds (x := ((σ - 1) ^ 2 : ℝ)) (f := nhds (0 : ℝ)))
    simpa using this
  have hne : -((σ - 1) ^ 2) ≠ 0 := by
    simp only [neg_ne_zero]
    exact pow_ne_zero 2 (sub_ne_zero.mpr hσ)
  have := hnum.div hden hne
  simpa using this

end GppYakaboylu
