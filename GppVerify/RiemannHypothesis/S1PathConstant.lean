import Mathlib.Tactic

/-!
# The sharp S1 constant `c₀* = ½(c₃ + √(c₃² + 4c₂²))`: top eigenvalue of the weighted 4-path

Source: Grok sub-team handoff `work/grok/HANDOFF_RH_TEAM_2026-11-03.md` §3.3 and §6(d)
(GPPDiscovery5 `derivation/ARP.md` §P P.16: "sharp joint S1 constant ... from a fibre
decomposition into weighted 4-paths"). Daniel Toupin / Golden Physics Project, with AI assistance
from Grok (statement) and Claude Code (formalization).

For `c₂, c₃ > 0` let `c₀* = (c₃ + √(c₃² + 4c₂²))/2` and
`Q(x) = 2c₂x₁x₂ + 2c₃x₂x₃ + 2c₂x₃x₄`, the quadratic form of the path with edge weights
`(c₂, c₃, c₂)`.

* `c0star_sq`: `c₀*² = c₃ c₀* + c₂²`.
* `path_form_le`: `Q(x) ≤ c₀* · ‖x‖²` for every `x ∈ ℝ⁴`, via the exact identity
  `c₀*‖x‖² − Q(x) = (c₀*x₁ − c₂x₂)²/c₀* + c₃(x₂ − x₃)² + (c₀*x₄ − c₂x₃)²/c₀*`.
* `path_form_witness`: equality at the positive vector `v = (c₂, c₀*, c₀*, c₂)`, so the constant is
  sharp (it is the Perron eigenvalue; `v` is an eigenvector).

**Scope.** Only this finite quadratic-form fact. That the S1 constant of the Weil form on the
`{2,3}` window equals this eigenvalue (the fibre decomposition), the numerical value `0.90093` for
`c₂ = log 2/√2`, `c₃ = log 3/√3`, and every Arb/Schur step are NOT formalized. No claim about RH.
-/

set_option autoImplicit false

namespace GppS1PathConstant

/-- The sharp S1 constant. -/
noncomputable def c0star (c2 c3 : ℝ) : ℝ := (c3 + Real.sqrt (c3 ^ 2 + 4 * c2 ^ 2)) / 2

/-- The path quadratic form with edge weights `(c₂, c₃, c₂)`. -/
def pathForm (c2 c3 x1 x2 x3 x4 : ℝ) : ℝ := 2 * c2 * x1 * x2 + 2 * c3 * x2 * x3 + 2 * c2 * x3 * x4

theorem c0star_sq {c2 c3 : ℝ} (hc2 : 0 < c2) (hc3 : 0 < c3) :
    c0star c2 c3 ^ 2 = c3 * c0star c2 c3 + c2 ^ 2 := by
  unfold c0star
  have h : Real.sqrt (c3 ^ 2 + 4 * c2 ^ 2) ^ 2 = c3 ^ 2 + 4 * c2 ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [h]

theorem c0star_pos {c2 c3 : ℝ} (hc2 : 0 < c2) (hc3 : 0 < c3) : 0 < c0star c2 c3 := by
  unfold c0star
  have : 0 < Real.sqrt (c3 ^ 2 + 4 * c2 ^ 2) := Real.sqrt_pos.2 (by positivity)
  linarith

/-- The exact sum-of-squares identity. -/
theorem path_identity {c2 c3 : ℝ} (hc2 : 0 < c2) (hc3 : 0 < c3) (x1 x2 x3 x4 : ℝ) :
    c0star c2 c3 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) - pathForm c2 c3 x1 x2 x3 x4
      = (c0star c2 c3 * x1 - c2 * x2) ^ 2 / c0star c2 c3 + c3 * (x2 - x3) ^ 2
        + (c0star c2 c3 * x4 - c2 * x3) ^ 2 / c0star c2 c3 := by
  have hl := c0star_pos hc2 hc3
  have hs := c0star_sq hc2 hc3
  set l := c0star c2 c3
  unfold pathForm
  field_simp
  linear_combination (x2 ^ 2 + x3 ^ 2) * hs

theorem path_form_le {c2 c3 : ℝ} (hc2 : 0 < c2) (hc3 : 0 < c3) (x1 x2 x3 x4 : ℝ) :
    pathForm c2 c3 x1 x2 x3 x4 ≤ c0star c2 c3 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
  have h := path_identity hc2 hc3 x1 x2 x3 x4
  have hl := c0star_pos hc2 hc3
  have : 0 ≤ (c0star c2 c3 * x1 - c2 * x2) ^ 2 / c0star c2 c3 + c3 * (x2 - x3) ^ 2
        + (c0star c2 c3 * x4 - c2 * x3) ^ 2 / c0star c2 c3 := by positivity
  linarith

/-- Equality at the positive eigenvector `(c₂, c₀*, c₀*, c₂)`: the constant is sharp. -/
theorem path_form_witness {c2 c3 : ℝ} (hc2 : 0 < c2) (hc3 : 0 < c3) :
    pathForm c2 c3 c2 (c0star c2 c3) (c0star c2 c3) c2
      = c0star c2 c3 * (c2 ^ 2 + c0star c2 c3 ^ 2 + c0star c2 c3 ^ 2 + c2 ^ 2) := by
  have h := path_identity hc2 hc3 c2 (c0star c2 c3) (c0star c2 c3) c2
  have hl := c0star_pos hc2 hc3
  have hs := c0star_sq hc2 hc3
  set l := c0star c2 c3
  have e1 : (l * c2 - c2 * l) = 0 := by ring
  rw [e1] at h
  simp at h
  linarith

end GppS1PathConstant
