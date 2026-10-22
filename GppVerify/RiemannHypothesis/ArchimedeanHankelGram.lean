import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The archimedean Hankel kernel: Gram expansion and the odd companion

Sources: Astra, `work/2026-10-22_astra_archimedean_hankel_realisation.md` §1 and
`work/2026-10-22_astra_cayley_nested_spectral_audit.md` §4 (GPP-bridge), both about the kernel
`k_arch(v) = −e^{−v/2}/(1 − e^{−2v})` that Turbo reported (PR11, Wave 233). Daniel Toupin / Golden
Physics Project, with AI assistance from Astra (statements) and Claude Code (formalization).

* `hasSum_phi_mul`: `∑_j φ_j(u) φ_j(v) = e^{−(u+v)/2}/(1 − e^{−2(u+v)}) = −k_arch(u + v)` for
  `u + v > 0`, with `φ_j(u) = e^{−(2j+1/2)u}`, so the negated kernel is a Gram (`T* T`) form.
* `integral_phi_mul`: the Gram matrix `⟨φ_j, φ_k⟩_{L²(0,∞)} = 1/(2j + 2k + 1)`.
* `arch_add_companion`: with `A(v) = e^{−v/2}/(1 − e^{−2v})` and its companion
  `B(v) = e^{−3v/2}/(1 − e^{−2v})`, `A + B = 1/(2 sinh(v/2))`.

**Scope.** Not formalized here: Astra's Schur-weight bound `∑ z̄ G z ≤ (π/2)∑|z|²` (it needs the
central-binomial convolution `∑ C(2i,i) C(2n−2i,n−i) = 4ⁿ`, which is not in Mathlib), the sharp tail
norm `π/2`, the Mellin identity `(2^s − 1) ζ(s)`, and the continuous/discrete intertwiner no-go.
These are identities about one reported kernel. They say nothing about whether that kernel is the
right archimedean piece of the Weil form, about the full sewing operator, or about RH.
-/

open Real MeasureTheory Set

namespace GppArchimedeanHankelGram

/-- The synthesis functions `φ_j(u) = e^{−(2j+1/2)u}`. -/
noncomputable def phi (j : ℕ) (u : ℝ) : ℝ := Real.exp (-(2 * j + 1 / 2) * u)

/-- **Gram expansion of the archimedean Hankel kernel.** For `u + v > 0`,
`∑_j φ_j(u) φ_j(v) = e^{−(u+v)/2} / (1 − e^{−2(u+v)}) = −k_arch(u + v)`. -/
theorem hasSum_phi_mul {u v : ℝ} (huv : 0 < u + v) :
    HasSum (fun j : ℕ => phi j u * phi j v)
      (Real.exp (-(u + v) / 2) / (1 - Real.exp (-2 * (u + v)))) := by
  have hr0 : 0 ≤ Real.exp (-2 * (u + v)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2 * (u + v)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-(u + v) / 2))
  rw [div_eq_mul_inv]
  refine h.congr_fun fun j => ?_
  simp only [phi]
  rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; ring

/-- **The Gram entries.** `⟨φ_j, φ_k⟩_{L²(0,∞)} = 1/(2j + 2k + 1)`. -/
theorem integral_phi_mul (j k : ℕ) :
    ∫ u in Ioi (0 : ℝ), phi j u * phi k u = 1 / (2 * j + 2 * k + 1) := by
  have hpos : (0 : ℝ) < 2 * j + 2 * k + 1 := by positivity
  have h : ∀ u : ℝ, phi j u * phi k u = Real.exp (-(2 * j + 2 * k + 1) * u) := fun u => by
    simp only [phi]; rw [← Real.exp_add]; congr 1; ring
  simp_rw [h]
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- **The odd companion.** With `A(v) = e^{−v/2}/(1 − e^{−2v})` and
`B(v) = e^{−3v/2}/(1 − e^{−2v})`,
`A + B = 1/(2 sinh(v/2))` for `v > 0`. -/
theorem arch_add_companion {v : ℝ} (hv : 0 < v) :
    Real.exp (-v / 2) / (1 - Real.exp (-2 * v)) + Real.exp (-3 * v / 2) / (1 - Real.exp (-2 * v))
      = 1 / (2 * Real.sinh (v / 2)) := by
  rw [Real.sinh_eq]
  have e1 : Real.exp (-2 * v) = Real.exp (-(v / 2)) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-v / 2) = Real.exp (-(v / 2)) := by congr 1; ring
  have e3 : Real.exp (-3 * v / 2) = Real.exp (-(v / 2)) ^ 3 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e4 : Real.exp (v / 2) = (Real.exp (-(v / 2)))⁻¹ := by
    rw [← Real.exp_neg, neg_neg]
  set x := Real.exp (-(v / 2)) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [e1, e2, e3, e4]
  have hx2 : 1 - x ^ 2 ≠ 0 := by
    have : x ^ 2 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
    linarith
  have hd : x⁻¹ - x = (1 - x ^ 2) / x := by field_simp
  rw [hd]
  have h4 : 1 - x ^ 4 = (1 - x ^ 2) * (1 + x ^ 2) := by ring
  rw [h4]
  have hp : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp

end GppArchimedeanHankelGram
