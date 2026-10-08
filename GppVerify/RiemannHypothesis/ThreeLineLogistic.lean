import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The three-line logistic Poisson form: exact bookkeeping

Source: Codex's note `research/codex/2026-10-01_three_line_logistic_poisson.md`. With the logistic weight
`p(x)⁻¹ = 4 cosh²(x/2) = e^x + 2 + e^{-x}` and `‖h‖_σ² = ∫ h² e^{σx}`, this file proves the exact
parts of the note:

* `weight_split`: `4 cosh²(x/2) = e^x + 2 + e^{-x}` and, for integrable pieces,
  `‖h‖²_𝓗 = ‖h‖₊₁² + 2‖h‖₀² + ‖h‖₋₁²`;
* `normSq_translate`: `‖T_t h‖_σ² = e^{-σt} ‖h‖_σ²` (so the three boundary pieces scale by `e^{-t}, 1, e^{t}`);
* `normSq_swap`: reflection exchanges the `±1` pieces;
* `W_translate`: after the unitary `W h = 2cosh(x/2) h`, translation becomes the cocycle
  `cosh(x/2)/cosh((x+t)/2) · F(x+t)`, and `tendsto_cocycle`: the cocycle tends to `e^{-t/2}` at `+∞`;
* `W_kernel`: `2cosh(x/2) e^{x/2} = 1 + e^x` (the factor in `(1+u) Σ f(nu)`), and
  `poisson_reflection_factor`: given the Poisson relation `S₁ = u⁻¹ S₂`, `(1+u)S₁ = (1+u⁻¹)S₂`.

## Scope

Exact elementary identities only. The target (TV) — the simultaneous two-endpoint estimate on the
arithmetic subspace `𝓡` — is the open core of the note; the Poisson summation formula itself and the
Plancherel/vertical-line reading are not formalized here. No RH claim.
-/

open MeasureTheory Filter Topology

namespace GppThreeLineLogistic

/-- The logistic inverse weight. -/
noncomputable def wInv (x : ℝ) : ℝ := 4 * Real.cosh (x / 2) ^ 2

theorem wInv_eq (x : ℝ) : wInv x = Real.exp x + 2 + Real.exp (-x) := by
  unfold wInv
  have h1 : Real.cosh (x / 2) = (Real.exp (x / 2) + Real.exp (-(x / 2))) / 2 := Real.cosh_eq _
  have e1 : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by rw [← Real.exp_add]; simp
  rw [h1, e1, e2]; nlinarith [e3]

/-- `‖h‖_σ² = ∫ h² e^{σx}`. -/
noncomputable def normSq (σ : ℝ) (h : ℝ → ℝ) : ℝ := ∫ x, h x ^ 2 * Real.exp (σ * x)

/-- **Three-boundary decomposition of the logistic norm.** -/
theorem weight_split (h : ℝ → ℝ)
    (h1 : Integrable fun x => h x ^ 2 * Real.exp (1 * x))
    (h0 : Integrable fun x => h x ^ 2 * Real.exp (0 * x))
    (hm : Integrable fun x => h x ^ 2 * Real.exp ((-1) * x)) :
    ∫ x, h x ^ 2 * wInv x = normSq 1 h + 2 * normSq 0 h + normSq (-1) h := by
  unfold normSq
  have e : (fun x => h x ^ 2 * wInv x) = fun x =>
      (h x ^ 2 * Real.exp (1 * x) + 2 * (h x ^ 2 * Real.exp (0 * x))) + h x ^ 2 * Real.exp ((-1) * x) := by
    funext x; rw [wInv_eq]; simp; ring
  have hm' : Integrable fun x => h x ^ 2 * Real.exp (-1 * x) := hm
  rw [e]
  have hA : Integrable fun x => h x ^ 2 * Real.exp (1 * x) + 2 * (h x ^ 2 * Real.exp (0 * x)) :=
    h1.add (h0.const_mul 2)
  rw [integral_add hA hm', integral_add h1 (h0.const_mul 2), integral_const_mul]

/-- **Translation scales the σ-norm:** `‖T_t h‖_σ² = e^{−σt}‖h‖_σ²`. -/
theorem normSq_translate (σ t : ℝ) (h : ℝ → ℝ) :
    normSq σ (fun x => h (x + t)) = Real.exp (-σ * t) * normSq σ h := by
  unfold normSq
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => h y ^ 2 * Real.exp (σ * (y - t))) t
  have e : (fun x => h (x + t) ^ 2 * Real.exp (σ * x)) =
      fun x => (fun y => h y ^ 2 * Real.exp (σ * (y - t))) (x + t) := by
    funext x; simp
  rw [e, this]
  have e2 : (fun y => h y ^ 2 * Real.exp (σ * (y - t))) =
      fun y => (h y ^ 2 * Real.exp (σ * y)) * Real.exp (-σ * t) := by
    funext y; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [e2, integral_mul_const, mul_comm]

/-- **Reflection exchanges the endpoint lines:** `‖h(−·)‖_σ² = ‖h‖_{−σ}²`. -/
theorem normSq_swap (σ : ℝ) (h : ℝ → ℝ) : normSq σ (fun x => h (-x)) = normSq (-σ) h := by
  unfold normSq
  have := integral_neg_eq_self (μ := (volume : Measure ℝ)) (fun y => h y ^ 2 * Real.exp (-σ * y))
  rw [← this]
  congr 1; funext x; simp

/-- The unitary `W h = 2 cosh(x/2) h`, as a pointwise multiplier. -/
noncomputable def W (h : ℝ → ℝ) : ℝ → ℝ := fun x => 2 * Real.cosh (x / 2) * h x

/-- **Conjugated translation is the cocycle** `cosh(x/2)/cosh((x+t)/2) · F(x+t)`: with `F = W h`,
`W (T_t h) = cocycle · (T_t F)`. -/
theorem W_translate (t : ℝ) (h : ℝ → ℝ) (x : ℝ) :
    W (fun y => h (y + t)) x =
      (Real.cosh (x / 2) / Real.cosh ((x + t) / 2)) * W h (x + t) := by
  unfold W
  have : Real.cosh ((x + t) / 2) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp

/-- The cocycle tends to `e^{−t/2}` as `x → +∞`. -/
theorem tendsto_cocycle (t : ℝ) :
    Tendsto (fun x : ℝ => Real.cosh (x / 2) / Real.cosh ((x + t) / 2)) atTop
      (𝓝 (Real.exp (-t / 2))) := by
  have key : ∀ x : ℝ, Real.cosh (x / 2) / Real.cosh ((x + t) / 2) =
      (1 + Real.exp (-x)) / (Real.exp (t / 2) * (1 + Real.exp (-(x + t)))) := by
    intro x
    have c1 : Real.cosh (x / 2) = Real.exp (x / 2) * (1 + Real.exp (-x)) / 2 := by
      rw [Real.cosh_eq, mul_add, mul_one, ← Real.exp_add]; congr 2 <;> ring_nf
    have c2 : Real.cosh ((x + t) / 2) =
        Real.exp ((x + t) / 2) * (1 + Real.exp (-(x + t))) / 2 := by
      rw [Real.cosh_eq, mul_add, mul_one, ← Real.exp_add]; congr 2 <;> ring_nf
    have e : Real.exp ((x + t) / 2) = Real.exp (x / 2) * Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [c1, c2, e]
    have : Real.exp (x / 2) ≠ 0 := (Real.exp_pos _).ne'
    have : 0 < 1 + Real.exp (-(x + t)) := by positivity
    field_simp
  simp_rw [key]
  have hx : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hxt : Tendsto (fun x : ℝ => Real.exp (-(x + t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_atTop_add_const_right _ t tendsto_id)
  have hnum : Tendsto (fun x : ℝ => 1 + Real.exp (-x)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hx
  have hden : Tendsto (fun x : ℝ => Real.exp (t / 2) * (1 + Real.exp (-(x + t)))) atTop
      (𝓝 (Real.exp (t / 2) * (1 + 0))) := tendsto_const_nhds.mul (tendsto_const_nhds.add hxt)
  have := hnum.div hden (by simp [Real.exp_ne_zero])
  have e : (1 + 0 : ℝ) / (Real.exp (t / 2) * (1 + 0)) = Real.exp (-t / 2) := by
    have : -t / 2 = -(t / 2) := by ring
    rw [this, Real.exp_neg]; simp
  rwa [e] at this

/-- `2 cosh(x/2) e^{x/2} = 1 + e^x`. -/
theorem W_kernel (x : ℝ) : 2 * Real.cosh (x / 2) * Real.exp (x / 2) = 1 + Real.exp x := by
  rw [Real.cosh_eq]
  have e : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [e, e3]

/-- Given the Poisson relation `S₁ = u⁻¹ S₂` (with `S₁ = Σ f(nu)`, `S₂ = Σ f̂(n/u)`),
`(1 + u) S₁ = (1 + u⁻¹) S₂`: the weighted seed is reflected by `x ↦ −x`. -/
theorem poisson_reflection_factor {u S₁ S₂ : ℝ} (hu : u ≠ 0) (h : S₁ = u⁻¹ * S₂) :
    (1 + u) * S₁ = (1 + u⁻¹) * S₂ := by
  rw [h]; field_simp; ring

end GppThreeLineLogistic
