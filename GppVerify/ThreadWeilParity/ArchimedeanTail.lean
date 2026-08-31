import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Thread Weil-Parity — the exact Archimedean renormalization tail

New thread, opened this session from `arithmetic_principal_series_RH_program34.tex`,
section "The exact semilocal Weil form" (around line 6414). That section defines, for
`λ > 1` and `N ≥ 0`, the exact finite prime–Archimedean Gram matrix

  `(Q_{λ,N})_{mn} = Ψ♯(F_{mn})`, `Ψ♯ = W₀,₂♯ − W_ℝ♯ − Σ_p Wₚ♯`,

where the Archimedean piece is

  `W_ℝ♯(F) = (1/2)(log4π+γ)·F(1) + ∫₁^∞ [u^{1/2}F(u) − F(1)] / (u − u⁻¹) · du/u`.

`F_{mn}` is compactly supported in `[1, λ²]`, and the diagonal case has `F_{mn}(1) = 2`
(from `q_{mn}(0) = 2` in the paper's kernel formula). A numerical implementation of this
construction was checkpointed to `lean_results` this session (rows `02a84cc3…`,
`079ca52f…`): a naive truncation of the integral at `u = λ²` silently drops the
"`−F(1)`" subtraction's tail beyond the support cutoff, producing a spurious negative
scalar offset in the raw eigenvalues. The correction (`079ca52f…`) identified the
omitted tail in closed form: for the diagonal case (`F(1) = 2`, `F(u) = 0` for `u > c`,
`c = λ²`), the missing piece is

  `−2 ∫_c^∞ du/(u² − 1) = −log((c+1)/(c−1))`.

That correction was stated and used numerically but never proved. This file promotes it
to an actual theorem: `archimedean_diagonal_tail` below is exactly that closed-form
identity, proved from Mathlib's elementary calculus + improper-integral machinery, with
no custom axiom and no `sorry`.

## What this does NOT do

This is a single self-contained calculus fact used inside the `W_ℝ♯` construction — it
says nothing about the actual eigenvalues of `Q_{λ,N}`, the observed odd/even parity
ratios (`δ₋/δ₊`), or any Weil-positivity statement. The checkpoints' larger research
questions (a "double-defect factorization" theorem transferring the parity separation
from the pure-prolate asymptotic to the actual semilocal Weil operator at the correct
error order, and any inequality this would feed into) are **not proved and not attempted
here** — they depend on an operator-comparison theorem that does not yet exist even
on paper (see `lean_results` row `02a84cc3…`: "Required new theorem: a second-cancellation
/double-defect factorization... Next source target: Connes-Consani archimedean
Weil/prolate Selecta construction"). No RH claim, no claim about `Q_{λ,N}`'s spectrum.
-/

open MeasureTheory Set Filter Topology

namespace GppWeilParity

/-- The antiderivative of `(u² − 1)⁻¹` on `(1, ∞)`: `(1/2)·log((u−1)/(u+1))`. -/
noncomputable def archTailAntideriv (u : ℝ) : ℝ := (1 / 2) * Real.log ((u - 1) / (u + 1))

theorem archTailAntideriv_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt archTailAntideriv ((u ^ 2 - 1)⁻¹) u := by
  have h1 : u - 1 ≠ 0 := by linarith
  have h2 : u + 1 ≠ 0 := by linarith
  have hquot : HasDerivAt (fun u : ℝ => (u - 1) / (u + 1))
      (((u + 1) - (u - 1)) / (u + 1) ^ 2) u := by
    have hd1 : HasDerivAt (fun u : ℝ => u - 1) 1 u := (hasDerivAt_id u).sub_const 1
    have hd2 : HasDerivAt (fun u : ℝ => u + 1) 1 u := (hasDerivAt_id u).add_const 1
    have := hd1.div hd2 h2
    simpa [Pi.div_def] using this
  have hlog : HasDerivAt (fun u : ℝ => Real.log ((u - 1) / (u + 1)))
      ((((u + 1) - (u - 1)) / (u + 1) ^ 2) * ((u - 1) / (u + 1))⁻¹) u := by
    apply HasDerivAt.log hquot
    exact div_ne_zero h1 h2
  have := hlog.const_mul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * ((((u + 1) - (u - 1)) / (u + 1) ^ 2) * ((u - 1) / (u + 1))⁻¹)
      = (u ^ 2 - 1)⁻¹ := by
    rw [show (u ^ 2 - 1) = (u - 1) * (u + 1) from by ring]
    field_simp
    ring
  rw [← hval]
  exact this

theorem archTailAntideriv_tendsto_atTop : Tendsto archTailAntideriv atTop (𝓝 0) := by
  have hden : Tendsto (fun u : ℝ => u + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hratio : Tendsto (fun u : ℝ => (u - 1) / (u + 1)) atTop (𝓝 1) := by
    have heq : ∀ u : ℝ, u + 1 ≠ 0 → (u - 1) / (u + 1) = 1 - 2 / (u + 1) := by
      intro u hu
      field_simp
      ring
    have hsmall : Tendsto (fun u : ℝ => (2 : ℝ) / (u + 1)) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop hden 2
    have hlim := Tendsto.const_sub (1 : ℝ) hsmall
    simp only [sub_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (-1 : ℝ)] with u hu
    rw [heq u (by linarith)]
  have hlog : Tendsto (fun u : ℝ => Real.log ((u - 1) / (u + 1))) atTop (𝓝 (Real.log 1)) :=
    (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  rw [Real.log_one] at hlog
  have hfin := hlog.const_mul (1 / 2 : ℝ)
  rw [mul_zero] at hfin
  exact hfin

/-- `∫_c^∞ (u²−1)⁻¹ du = −archTailAntideriv c`, for `c > 1`, via Mathlib's FTC-2 on
`(a, ∞)` (`integral_Ioi_of_hasDerivAt_of_nonneg'`). -/
theorem tail_integral {c : ℝ} (hc : 1 < c) :
    ∫ u : ℝ in Ioi c, (u ^ 2 - 1)⁻¹ = -archTailAntideriv c := by
  have hderiv : ∀ x ∈ Ici c, HasDerivAt archTailAntideriv ((x ^ 2 - 1)⁻¹) x := fun x hx =>
    archTailAntideriv_hasDerivAt (lt_of_lt_of_le hc hx)
  have hpos : ∀ x ∈ Ioi c, (0 : ℝ) ≤ (x ^ 2 - 1)⁻¹ := by
    intro x hx
    have hx1 : 1 < x := lt_trans hc hx
    have hx2 : (1 : ℝ) < x ^ 2 := by nlinarith
    exact inv_nonneg.mpr (by linarith)
  have := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos archTailAntideriv_tendsto_atTop
  rw [this]
  ring

/-- Closed form matching the paper's convention: `∫_c^∞ (u²−1)⁻¹ du = (1/2)·log((c+1)/(c−1))`. -/
theorem tail_integral_closed_form {c : ℝ} (hc : 1 < c) :
    ∫ u : ℝ in Ioi c, (u ^ 2 - 1)⁻¹ = (1 / 2) * Real.log ((c + 1) / (c - 1)) := by
  rw [tail_integral hc, archTailAntideriv]
  rw [show (c + 1) / (c - 1) = ((c - 1) / (c + 1))⁻¹ from (inv_div _ _).symm,
      Real.log_inv]
  ring

/-- **The exact omitted-tail identity** used in the `lean_results` correction
(`079ca52f…`). For the diagonal case `F(1) = 2` of the paper's `W_ℝ♯`, with `F`
supported in `[1, c]`, the tail dropped by truncating the defining integral at `u = c`
instead of continuing to `∞` is exactly `−log((c+1)/(c−1))`. Restoring it shifts the
truncated computation upward by exactly this amount, matching the correction that
reconciled the raw numerical output with Connes–Consani's published tiny positive
minima. This is the closed-form justification of that numerical fix — not a new
numerical claim. -/
theorem archimedean_diagonal_tail {c : ℝ} (hc : 1 < c) :
    -2 * ∫ u : ℝ in Ioi c, (u ^ 2 - 1)⁻¹ = -Real.log ((c + 1) / (c - 1)) := by
  rw [tail_integral_closed_form hc]
  ring

end GppWeilParity
