import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Parity, charge conjugation, and the two half-planes on the log-scale line

On the log-scale line `u = log x`, a test function `g : ℝ → ℂ` has bilateral Laplace transform
`ĝ(z) = ∫ g(u) e^{z u} du`, `z = s − 1/2`. The functional equation `s ↦ 1 − s` is `z ↦ −z`, and complex
conjugation is `z ↦ z̄`; their product is the complete reversal `𝒟 z = −z̄` (reflection in the critical
line `Re z = 0`).

* `laplace_comp_neg`: `L(g ∘ (−·))(z) = L g (−z)` — parity `u ↦ −u` acts on the transform as the
  functional-equation flip `z ↦ −z` (it exchanges the two half-planes);
* `laplace_conj`: for real-valued `g`, `L g (z̄) = conj (L g z)` — reality is charge conjugation;
* `laplace_odd`, `laplace_even`: for odd (even) `g`, `ĝ(−z) = −ĝ(z)` (`+ĝ(z)`);
* `laplace_odd_real_reversal`: for odd real `g`, `ĝ(𝒟 z) = −conj(ĝ(z))`, hence on the critical line
  (`𝒟 z = z`) `Re ĝ = 0` (`laplace_odd_real_line`): the transform is purely imaginary there;
* `laplace_even_real_line`: for even real `g`, `ĝ` is real on the critical line.

## Checks and scope

Exact and unconditional (no integrability hypotheses are needed: the change of variables and complex
conjugation commute with the Bochner integral, which is `0` on non-integrable functions). This is the
precise sense in which the *odd, real* test functions are antisymmetric under the half-plane swap and
symmetric under conjugation — the sector of the odd Weil form. It makes no claim about the Weil
distribution, its positivity, or zeros. No RH claim.
-/

open MeasureTheory ComplexConjugate

namespace GppLogScaleParity

/-- The bilateral Laplace transform `ĝ(z) = ∫ g(u) e^{z u} du` on the log-scale line. -/
noncomputable def laplace (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u : ℝ, g u * Complex.exp (z * u)

/-- **Parity `u ↦ −u` is the functional-equation flip `z ↦ −z`.** -/
theorem laplace_comp_neg (g : ℝ → ℂ) (z : ℂ) :
    laplace (fun u => g (-u)) z = laplace g (-z) := by
  unfold laplace
  rw [← integral_neg_eq_self (fun u : ℝ => g u * Complex.exp (-z * u))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]

/-- **Reality is charge conjugation.** -/
theorem laplace_conj (g : ℝ → ℝ) (z : ℂ) :
    laplace (fun u => (g u : ℂ)) (conj z) = conj (laplace (fun u => (g u : ℂ)) z) := by
  unfold laplace
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]

theorem laplace_odd (g : ℝ → ℂ) (hg : ∀ u, g (-u) = -g u) (z : ℂ) :
    laplace g (-z) = -laplace g z := by
  rw [← laplace_comp_neg]
  unfold laplace
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [hg, neg_mul]

theorem laplace_even (g : ℝ → ℂ) (hg : ∀ u, g (-u) = g u) (z : ℂ) :
    laplace g (-z) = laplace g z := by
  rw [← laplace_comp_neg]
  unfold laplace
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [hg]

/-- **Odd real test functions are antisymmetric under the complete reversal `𝒟 z = −z̄`.** -/
theorem laplace_odd_real_reversal (g : ℝ → ℝ) (hg : ∀ u, g (-u) = -g u) (z : ℂ) :
    laplace (fun u => (g u : ℂ)) (-conj z) = -conj (laplace (fun u => (g u : ℂ)) z) := by
  have hodd : ∀ u, (fun u => (g u : ℂ)) (-u) = -(fun u => (g u : ℂ)) u := by
    intro u; simp [hg]
  rw [laplace_odd _ hodd, laplace_conj]

/-- On the critical line (`𝒟 z = z`, i.e. `Re z = 0`) the transform of an odd real function is purely
imaginary. -/
theorem laplace_odd_real_line (g : ℝ → ℝ) (hg : ∀ u, g (-u) = -g u) (z : ℂ) (hz : z.re = 0) :
    (laplace (fun u => (g u : ℂ)) z).re = 0 := by
  have hD : -conj z = z := by
    apply Complex.ext <;> simp [hz]
  have h := laplace_odd_real_reversal g hg z
  rw [hD] at h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- On the critical line the transform of an even real function is real. -/
theorem laplace_even_real_line (g : ℝ → ℝ) (hg : ∀ u, g (-u) = g u) (z : ℂ) (hz : z.re = 0) :
    (laplace (fun u => (g u : ℂ)) z).im = 0 := by
  have hD : -conj z = z := by
    apply Complex.ext <;> simp [hz]
  have hev : ∀ u, (fun u => (g u : ℂ)) (-u) = (fun u => (g u : ℂ)) u := by
    intro u; simp [hg]
  have h : laplace (fun u => (g u : ℂ)) (-conj z) = conj (laplace (fun u => (g u : ℂ)) z) := by
    rw [laplace_even _ hev, laplace_conj]
  rw [hD] at h
  have := congrArg Complex.im h
  simp at this
  linarith

end GppLogScaleParity
