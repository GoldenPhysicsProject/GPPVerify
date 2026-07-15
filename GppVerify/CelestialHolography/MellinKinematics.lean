import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Mellin kinematics: power laws, the scale shadow, and the Δ = 2s bridge

Thread M of `docs/FORMALIZATION_PLAN.md`, from `mellin_kinematics.tex` — the elementary
harmonic-analysis layer of the celestial–arithmetic dictionary:

* `power_law_classification` (the paper's Lemma "power laws are the continuous group
  homomorphisms of `(ℝ⁺,×)`"): every continuous multiplicative self-map of the positive
  reals is `ω ↦ ω^α` for a **unique** `α : ℝ`. Proof: conjugate by `log`/`exp` to a
  continuous additive endomorphism of `ℝ`, which is linear
  (`AddMonoidHom.toRealLinearMap`). *Honesty note*: the paper asserts a unique `α > 0`,
  but the constant map (`α = 0`) and inversion (`α = −1`) are continuous homomorphisms
  too — the correct classification has `α : ℝ`, as proved here; positivity of `α` needs
  (and only needs) the extra hypothesis that `φ` is somewhere `> 1` on `(1,∞)`, which we
  do not assume.
* `scale_shadow_involutive` / `scale_shadow_norm_sq` (the paper's Definition
  "half-density scale shadow" and its unitarity): `(Sf)(x) = x⁻¹·f(x⁻¹)` is an involution
  on functions on `(0,∞)` and preserves the squared `L²(dx)`-mass — the substitution
  `u = x⁻¹` executed by Mathlib's `integral_comp_rpow_Ioi` at `p = −1`.
* `mellin_kernel_transport` / `quadratic_transport_axis` (the paper's Theorem "uniqueness
  of the quadratic scale transport"): under the homogeneous transport `x = ω^α` the
  arithmetic Mellin kernel `x^{s−1}dx` becomes `α·ω^{αs−1}dω` (the `Δ = αs` dictionary),
  and matching the arithmetic unitary axis `Re s = 1/2` to the celestial one `Re Δ = 1`
  forces `α = 2` — the origin of `Δ = 2s`.
-/

namespace GppMellin

open MeasureTheory Set

/-! ## M1: power laws are the continuous homomorphisms of `(ℝ⁺,×)` -/

/-- **Classification of continuous multiplicative self-maps of `(0,∞)`**: there is a
    unique real `α` with `φ(x) = x^α` on `(0,∞)`. -/
theorem power_law_classification (φ : ℝ → ℝ)
    (hpos : ∀ x, 0 < x → 0 < φ x)
    (hmul : ∀ x y, 0 < x → 0 < y → φ (x * y) = φ x * φ y)
    (hcont : ContinuousOn φ (Ioi 0)) :
    ∃! α : ℝ, ∀ x, 0 < x → φ x = x ^ α := by
  -- φ(1) = 1
  have hφ1 : φ 1 = 1 := by
    have h := hmul 1 1 one_pos one_pos
    rw [one_mul] at h
    have hp := hpos 1 one_pos
    nlinarith [h, hp, sq_nonneg (φ 1 - 1)]
  -- the log-conjugated map is a continuous additive endomorphism of ℝ
  have hψadd : ∀ s t : ℝ, Real.log (φ (Real.exp (s + t))) =
      Real.log (φ (Real.exp s)) + Real.log (φ (Real.exp t)) := by
    intro s t
    rw [Real.exp_add, hmul _ _ (Real.exp_pos s) (Real.exp_pos t),
      Real.log_mul (hpos _ (Real.exp_pos s)).ne' (hpos _ (Real.exp_pos t)).ne']
  set ψ : ℝ →+ ℝ :=
    { toFun := fun t => Real.log (φ (Real.exp t))
      map_zero' := by rw [Real.exp_zero, hφ1, Real.log_one]
      map_add' := hψadd } with hψ
  have hψcont : Continuous ψ := by
    show Continuous fun t => Real.log (φ (Real.exp t))
    have hφexp : Continuous fun t => φ (Real.exp t) :=
      hcont.comp_continuous Real.continuous_exp fun t => Real.exp_pos t
    exact hφexp.log fun t => (hpos _ (Real.exp_pos t)).ne'
  -- linearity: ψ t = t * ψ 1
  have hlin : ∀ t : ℝ, ψ t = t * ψ 1 := by
    intro t
    have hcoe := AddMonoidHom.coe_toRealLinearMap ψ hψcont
    have h := (ψ.toRealLinearMap hψcont).map_smul t (1:ℝ)
    rw [hcoe] at h
    rw [smul_eq_mul, mul_one, smul_eq_mul] at h
    exact h
  refine ⟨ψ 1, fun x hx => ?_, fun β hβ => ?_⟩
  · -- φ x = x ^ ψ 1
    have hx' : φ x = Real.exp (ψ (Real.log x)) := by
      show φ x = Real.exp (Real.log (φ (Real.exp (Real.log x))))
      rw [Real.exp_log hx, Real.exp_log (hpos x hx)]
    rw [hx', hlin, Real.rpow_def_of_pos hx]
  · -- uniqueness: evaluate at x = e
    have he := hβ (Real.exp 1) (Real.exp_pos 1)
    have hd' : Real.exp 1 ^ β = Real.exp β := by
      rw [Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp, one_mul]
    have hφe : φ (Real.exp 1) = Real.exp (ψ 1) := by
      have hψ1 : (ψ 1 : ℝ) = Real.log (φ (Real.exp 1)) := rfl
      rw [hψ1, Real.exp_log (hpos _ (Real.exp_pos 1))]
    rw [hd', hφe] at he
    -- he : Real.exp (ψ 1) = Real.exp β
    exact (Real.exp_eq_exp.mp he).symm

/-! ## M2: the half-density scale shadow -/

/-- The half-density scale shadow `(Sf)(x) = x⁻¹·f(x⁻¹)`. -/
noncomputable def scaleShadow (f : ℝ → ℝ) : ℝ → ℝ := fun x => x⁻¹ * f x⁻¹

/-- The scale shadow is an involution on `(0,∞)`. -/
theorem scale_shadow_involutive (f : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    scaleShadow (scaleShadow f) x = f x := by
  show x⁻¹ * ((x⁻¹)⁻¹ * f (x⁻¹)⁻¹) = f x
  rw [inv_inv]
  field_simp

/-- **Unitarity of the scale shadow** (squared-mass form): the substitution `u = x⁻¹`
    carries the `L²(dx)` mass of `Sf` to that of `f` exactly —
    `∫₀^∞ (x⁻¹·f(x⁻¹))² dx = ∫₀^∞ f² dx`. -/
theorem scale_shadow_norm_sq (f : ℝ → ℝ) :
    ∫ x in Ioi (0:ℝ), scaleShadow f x ^ 2 = ∫ x in Ioi (0:ℝ), f x ^ 2 := by
  have h := MeasureTheory.integral_comp_rpow_Ioi (fun u : ℝ => f u ^ 2)
    (p := (-1:ℝ)) (by norm_num)
  have heq : ∀ x ∈ Ioi (0:ℝ),
      (|(-1:ℝ)| * x ^ ((-1:ℝ) - 1)) • (fun u : ℝ => f u ^ 2) (x ^ (-1:ℝ)) =
        scaleShadow f x ^ 2 := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    show (|(-1:ℝ)| * x ^ ((-1:ℝ) - 1)) * f (x ^ (-1:ℝ)) ^ 2 = (x⁻¹ * f x⁻¹) ^ 2
    rw [Real.rpow_neg_one, show ((-1:ℝ) - 1) = -((2:ℕ):ℝ) by norm_num,
      Real.rpow_neg hx'.le, Real.rpow_natCast, abs_neg, abs_one]
    ring
  rw [← setIntegral_congr_fun measurableSet_Ioi heq]
  exact h

/-! ## M3: the quadratic scale transport and `Δ = 2s` -/

/-- **Mellin kernel transport** (the `Δ = αs` dictionary): under `x = ω^α` (`α ≠ 0`,
    `ω > 0`), the arithmetic Mellin kernel transports as
    `∫₀^∞ f(x)·x^{s−1} dx = ∫₀^∞ |α|·f(ω^α)·ω^{αs−1} dω` — the celestial kernel at
    dimension `Δ = αs`. -/
theorem mellin_kernel_transport (f : ℝ → ℝ) {α : ℝ} (hα : α ≠ 0) (s : ℝ) :
    ∫ x in Ioi (0:ℝ), f x * x ^ (s - 1) =
      ∫ ω in Ioi (0:ℝ), |α| * (f (ω ^ α) * ω ^ (α * s - 1)) := by
  have h := MeasureTheory.integral_comp_rpow_Ioi
    (fun x : ℝ => f x * x ^ (s - 1)) (p := α) hα
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ω hω
  have hω' : (0:ℝ) < ω := hω
  show (|α| * ω ^ (α - 1)) • (f (ω ^ α) * (ω ^ α) ^ (s - 1)) =
    |α| * (f (ω ^ α) * ω ^ (α * s - 1))
  rw [smul_eq_mul, ← Real.rpow_mul hω'.le α (s - 1),
    show α * s - 1 = (α - 1) + α * (s - 1) by ring, Real.rpow_add hω']
  ring

/-- **The unitary-axis match forces `α = 2`** — the arithmetic critical axis
    `Re s = 1/2` maps to the celestial unitarity axis `Re Δ = 1` under `Δ = αs` iff
    `α = 2`: the origin of the `Δ = 2s` dictionary. -/
theorem quadratic_transport_axis (α : ℝ) :
    α * (1/2) = 1 ↔ α = 2 := by
  constructor <;> intro h <;> linarith

end GppMellin
