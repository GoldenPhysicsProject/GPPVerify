import Mathlib.Tactic

/-!
# Confluent real-node Pick matrices: the exact third-order jet obstruction

Let f(x) be analytic at a real x>0, and form the Pick kernel
K(u,v)=(f(u)+f(v))/(u+v). When sample nodes coalesce at x,
the 3x3 divided-difference limit is the symmetric matrix of Taylor
coefficients of K(x+u,x+v) for u^i v^j, 0 <= i,j <= 2.

The formulas below use f0=f(x), f1=f'(x), f2=f''(x). No assumption
about zeta or RH is made here. Positivity of the full original Pick
kernel makes the confluent matrix positive semidefinite, so its
determinant must be nonnegative. Proving that implication analytically
and proving positivity for the completed xi function are separate
open formalization tasks.

Provenance: written by Codex (draft PR #282, head `8ef63216`), ported
unchanged into the root import graph by Claude Code at Codex's request.
-/

namespace GppConfluentPickThirdOrder

noncomputable section

def c00 (a f₀ : ℝ) : ℝ := f₀ / a
def c01 (a f₀ f₁ : ℝ) : ℝ := (a*f₁-f₀)/(2*a^2)
def c02 (a f₀ f₁ f₂ : ℝ) : ℝ :=
  (a^2*f₂-a*f₁+f₀)/(4*a^3)
def c11 (a f₀ f₁ : ℝ) : ℝ := (f₀-a*f₁)/(2*a^3)
def c12 (a f₀ f₁ f₂ : ℝ) : ℝ :=
  (-a^2*f₂+3*a*f₁-3*f₀)/(8*a^4)
def c22 (a f₀ f₁ f₂ : ℝ) : ℝ :=
  (a^2*f₂-3*a*f₁+3*f₀)/(8*a^5)

/-- This equals the determinant of the first two confluent Pick jets. -/
def det2 (a f₀ f₁ : ℝ) : ℝ :=
  c00 a f₀ * c11 a f₀ f₁ - (c01 a f₀ f₁)^2

/-- This equals the determinant of the first three confluent Pick jets. -/
def det3 (a f₀ f₁ f₂ : ℝ) : ℝ :=
  c00 a f₀ * c11 a f₀ f₁ * c22 a f₀ f₁ f₂
  + 2*c01 a f₀ f₁*c02 a f₀ f₁ f₂*c12 a f₀ f₁ f₂
  - c00 a f₀*(c12 a f₀ f₁ f₂)^2
  - c11 a f₀ f₁*(c02 a f₀ f₁ f₂)^2
  - c22 a f₀ f₁ f₂*(c01 a f₀ f₁)^2

/-- Exact 2-jet factorization; necessary positivity gives |a f'| <= f
    if f(a) >= 0. -/
theorem det2_factor (a f₀ f₁ : ℝ) (ha : a ≠ 0) :
    det2 a f₀ f₁ = (f₀^2-a^2*f₁^2)/(4*a^4) := by
  unfold det2 c00 c01 c11
  field_simp
  ring

/-- Exact 3-jet factorization. The derivative form of the obstruction is:
  -(a² f''+a f'-f) * (a² f f''-2a² f'²+a f f'+f²) /(64a⁹).

  Both factors need to be controlled in the actual arithmetic problem. -/
theorem det3_factor (a f₀ f₁ f₂ : ℝ) (ha : a ≠ 0) :
    det3 a f₀ f₁ f₂ =
      - (a^2*f₂+a*f₁-f₀) *
        (a^2*f₀*f₂-2*a^2*f₁^2+a*f₀*f₁+f₀^2) /
        (64*a^9) := by
  unfold det3 c00 c01 c02 c11 c12 c22
  field_simp
  ring

end

end GppConfluentPickThirdOrder
