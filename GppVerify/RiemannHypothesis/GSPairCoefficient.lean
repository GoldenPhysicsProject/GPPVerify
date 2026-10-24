import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The (GS)-pair coefficient: finite identity and Cauchy–Schwarz bound

Source: Turbo, `MuseResearch/agent1-pair-statements.md` (GPP-bridge `695e7f4`; Wave 274 §5,
deposited in Wave 275). This is the finite core of the (GS)-pair variant of
`GppGroundStateDetector` (#418).
Daniel Toupin / Golden Physics Project, with AI assistance from Turbo (statements) and Claude Code
(formalization and one correction).

* `inner_isometry_le`: for any linear isometry `U`, `‖⟨x, U y⟩‖ ≤ ‖x‖ ‖y‖`. This is the free-pair
  bound (Turbo's Gap 2); no positivity is used.
* In coordinates `ℂ^{2N}` with basis `e_{j,±}`, `U_t e_{j,±} = e^{±iγ_j t} e_{j,±}` and the
  antilinear twist `J(c, d) = (conj d, conj c)`, the pair coefficient `C(t) = ⟨Ψ_L, U_t J Ψ_L⟩` for
  `Ψ_L = (c, d)` expands to `pairCoeff`, the sum of `conj c_j conj d_j (e^{iγ_j t} + e^{−iγ_j t})`.
* `pairCoeff_eq`: `C(t) = ∑_j 2 conj(c_j d_j) cos(γ_j t)`.
  **Correction to the deposit's §2.1.** The deposit writes
  `C(t) = 2 Re ∑_j conj(c_j d_j) e^{iγ_j t}`. That agrees with the line above only when every
  `c_j d_j` is real. The deposit's own code (`pair273b.py`) computes the form proved here.
* `pairCoeff_bound`: `‖C(t)‖ ≤ ∑_j (‖c_j‖² + ‖d_j‖²) = ‖Ψ_L‖² = ‖Ψ_L‖ ‖JΨ_L‖` for every `t`.

**Scope.** Finite `N`. The continuous (GS)-pair implication, the off-diagonal dilation identity,
and (PAIR-NORM), (P2) and (P3) are not formalized. By Turbo's Wave 276–279 classification,
(PAIR-NORM) via `S₀`-boundedness is strictly stronger than RH. No claim about RH.
-/

open Complex Finset

namespace GppGSPair

/-- **Free-pair bound**: `‖⟨x, U y⟩‖ ≤ ‖x‖ ‖y‖` for a linear isometry `U`. -/
theorem inner_isometry_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →ₗᵢ[ℂ] E) (x y : E) : ‖@inner ℂ E _ x (U y)‖ ≤ ‖x‖ * ‖y‖ := by
  calc ‖@inner ℂ E _ x (U y)‖ ≤ ‖x‖ * ‖U y‖ := norm_inner_le_norm x (U y)
    _ = ‖x‖ * ‖y‖ := by rw [U.norm_map]

/-- The pair coefficient `⟨Ψ_L, U_t J Ψ_L⟩` for `Ψ_L = (c, d)`, written in coordinates. -/
noncomputable def pairCoeff {N : ℕ} (c d : Fin N → ℂ) (γ : Fin N → ℝ) (t : ℝ) : ℂ :=
  ∑ j, ((starRingEnd ℂ) (c j) * (starRingEnd ℂ) (d j) * exp (γ j * t * I) +
    (starRingEnd ℂ) (d j) * (starRingEnd ℂ) (c j) * exp (-(γ j * t * I)))

/-- **The pair coefficient is a cosine sum**: `C(t) = ∑_j 2 conj(c_j d_j) cos(γ_j t)`. -/
theorem pairCoeff_eq {N : ℕ} (c d : Fin N → ℂ) (γ : Fin N → ℝ) (t : ℝ) :
    pairCoeff c d γ t = ∑ j, 2 * (starRingEnd ℂ) (c j * d j) * Real.cos (γ j * t) := by
  unfold pairCoeff
  refine sum_congr rfl fun j _ => ?_
  rw [map_mul, ofReal_cos, ofReal_mul, Complex.cos]
  rw [show -((γ j : ℂ) * t * I) = -((γ j * t : ℂ) * I) by ring]
  field_simp

/-- **The pair coefficient is bounded** by `‖Ψ_L‖² = ∑_j (‖c_j‖² + ‖d_j‖²)`, uniformly in `t`. -/
theorem pairCoeff_bound {N : ℕ} (c d : Fin N → ℂ) (γ : Fin N → ℝ) (t : ℝ) :
    ‖pairCoeff c d γ t‖ ≤ ∑ j, (‖c j‖ ^ 2 + ‖d j‖ ^ 2) := by
  rw [pairCoeff_eq]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, map_mul, norm_mul, Complex.norm_conj, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_two]
  have hcos := Real.abs_cos_le_one (γ j * t)
  have h1 : 0 ≤ ‖c j‖ * ‖d j‖ := by positivity
  nlinarith [sq_nonneg (‖c j‖ - ‖d j‖), abs_nonneg (Real.cos (γ j * t))]

end GppGSPair
