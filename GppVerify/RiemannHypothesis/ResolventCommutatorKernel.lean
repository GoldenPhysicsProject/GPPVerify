import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Dirichlet half-line resolvent commutes with translation up to a rank-one kernel

Source: Codex, bridge `research/codex/2026-10-02_rank_one_resolvent_feshbach_collapse.md`, §§1–2
(the kernel computation; the Feshbach/AFT consequences in §3 are not formalized).

On `L²(ℝ₊)` the Dirichlet resolvent `G_κ = (−∂² + κ²)^{-1}` has kernel
`G_κ(x,y) = (e^{-κ|x−y|} − e^{-κ(x+y)}) / (2κ)`, and `V_a` is the unilateral right translation.

* `commutator_kernel`: for `κ, a > 0` and `x, y` the kernel of `G_κ V_a − V_a G_κ` is
  `G_κ(x, y + a) − 1_{x ≥ a} G_κ(x − a, y) = u_{a,κ}(x) e^{-κ y}`, a rank-one kernel with the
  **same right vector `e_κ(y) = e^{-κ y}`** for every `a`, and with
  `u_{a,κ}(x) = κ^{-1} e^{-κ a} sinh(κ x)` for `x < a`, `κ^{-1} sinh(κ a) e^{-κ x}` for `x ≥ a`;
* `norm_sq_expVec`: `‖e_κ‖² = ∫₀^∞ e^{-2κ y} dy = 1/(2κ)`.

## Checks and scope

The kernel identity is checked pointwise (the `x ≥ a` branch needs no case split on the sign of
`x − y − a`, because the two absolute values coincide). **Not formalized:** the operator-level
statements (that the integral operators with these kernels are the resolvent and translation on
`L²`), the trace `Tr[G_κ, V_a] = a e^{-κa}/(2κ)`, the contact limit as `a → 0`, and the rank-one
collapse of the completed cutoff connection (§3), which needs the AFT operator package. No RH
claim.
-/

open Real MeasureTheory Set

namespace GppResolventCommutator

/-- The Dirichlet resolvent kernel on the half-line. -/
noncomputable def G (κ x y : ℝ) : ℝ :=
  (1 / (2 * κ)) * (Real.exp (-(κ * |x - y|)) - Real.exp (-(κ * (x + y))))

/-- The boundary vector `u_{a,κ}`. -/
noncomputable def u (κ a x : ℝ) : ℝ :=
  (1 / κ) * (if x < a then Real.exp (-(κ * a)) * Real.sinh (κ * x)
    else Real.sinh (κ * a) * Real.exp (-(κ * x)))

/-- The kernel of `G_κ V_a − V_a G_κ`: `G(x, y+a) − 1_{x ≥ a} G(x−a, y)`. -/
noncomputable def commKernel (κ a x y : ℝ) : ℝ :=
  G κ x (y + a) - (if a ≤ x then G κ (x - a) y else 0)

/-- **The commutator is rank one with right vector `e^{-κ y}`.** -/
theorem commutator_kernel (κ a x y : ℝ) (hκ : 0 < κ) (hy : 0 < y) :
    commKernel κ a x y = u κ a x * Real.exp (-(κ * y)) := by
  unfold commKernel G u
  by_cases hax : a ≤ x
  · rw [if_pos hax, if_neg (not_lt.mpr hax)]
    have habs : |x - (y + a)| = |x - a - y| := by rw [show x - (y + a) = x - a - y by ring]
    have e1 : Real.exp (-(κ * (x + (y + a)))) =
        Real.exp (-(κ * x)) * Real.exp (-(κ * y)) * (Real.exp (κ * a))⁻¹ := by
      rw [← Real.exp_neg (κ * a), ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(κ * (x - a + y))) =
        Real.exp (-(κ * x)) * Real.exp (-(κ * y)) * Real.exp (κ * a) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [habs, e1, e2, Real.sinh_eq, Real.exp_neg (κ * a)]
    field_simp
    ring
  · rw [if_neg hax, if_pos (not_le.mp hax)]
    have habs : |x - (y + a)| = y + a - x := by
      rw [abs_of_neg (by linarith [not_le.mp hax])]; ring
    have e1 : Real.exp (-(κ * (y + a - x))) =
        Real.exp (-(κ * y)) * Real.exp (-(κ * a)) * Real.exp (κ * x) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(κ * (x + (y + a)))) =
        (Real.exp (κ * x))⁻¹ * Real.exp (-(κ * y)) * Real.exp (-(κ * a)) := by
      rw [← Real.exp_neg (κ * x), ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [habs, e1, e2, Real.sinh_eq, Real.exp_neg (κ * x)]
    field_simp
    ring

/-- **`‖e_κ‖² = 1/(2κ)`.** -/
theorem norm_sq_expVec (κ : ℝ) (hκ : 0 < κ) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-(κ * y)) ^ 2 = 1 / (2 * κ) := by
  have h : ∀ y : ℝ, Real.exp (-(κ * y)) ^ 2 = Real.exp ((-(2 * κ)) * y) := by
    intro y
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_exp_mul_Ioi (by linarith)]
  simp only [mul_zero, Real.exp_zero]
  field_simp

end GppResolventCommutator
