import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Shifted resolvent ratios of a finite real spectrum are unimodular with positive phase density

Source: Codex / Discovery2, `research/2026-09-28_poisson_resolvent_inner_closure.md` §§1–2
(`GPPDiscovery2`, `codex/discovery-workbench`). Daniel Toupin / Golden Physics Project, with AI
assistance from Codex (statements) and Claude Code (formalization).

For real eigenvalues `γ_k` and `ω > 0` the shifted ratio is
`Θ_{ω}(z) = ∏_k (γ_k − z + iω)/(γ_k − z − iω)`. Factor by factor, with `θ_γ(x) = (γ−x+iω)/(γ−x−iω)`:

* `norm_theta`: `‖θ_γ(x)‖ = 1` for real `x` (so `‖Θ‖ = 1` on the real line: `norm_prod_theta`).
* `theta_hasDerivAt`: `θ_γ'(x) = θ_γ(x) · 2iω/((γ−x)² + ω²)`, i.e. `(1/i) d/dx log θ_γ = 2ω/((x−γ)²+ω²)`.
* `phase_density_pos`: the phase derivative of the product, `P(x) = 2ω Σ_k 1/((x−γ_k)²+ω²)`, is
  strictly positive for a nonempty finite spectrum.

**Scope.** The finite algebra and calculus of the shifted ratio on the real axis. That `Θ` is a
Schur/inner function in the upper half-plane, the comparison with `ξ(½ ∓ ω − iz)` and Suzuki's
criterion, the CCM finite triples, and the closure theorem (locally uniform convergence of `Θ_{j,ω}`)
in §§3–4 are not formalized. No claim about RH.
-/

set_option autoImplicit false

open Complex Finset

namespace GppPoissonResolventInner

/-- One factor `θ_γ(x) = (γ − x + iω)/(γ − x − iω)`. -/
noncomputable def theta (ω γ x : ℝ) : ℂ :=
  (((γ - x : ℝ) : ℂ) + (ω : ℂ) * I) / (((γ - x : ℝ) : ℂ) - (ω : ℂ) * I)

/-- `‖θ_γ(x)‖ = 1` for real `x` and `ω > 0`. -/
theorem norm_theta (ω γ x : ℝ) (hω : 0 < ω) : ‖theta ω γ x‖ = 1 := by
  unfold theta
  have hden : (((γ - x : ℝ) : ℂ) - (ω : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [norm_div, div_eq_one_iff_eq (by simpa using hden)]
  have : (((γ - x : ℝ) : ℂ) - (ω : ℂ) * I) = (starRingEnd ℂ) (((γ - x : ℝ) : ℂ) + (ω : ℂ) * I) := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [this, Complex.norm_conj]

/-- Product of the factors over a finite spectrum has modulus `1`. -/
theorem norm_prod_theta {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (ω x : ℝ) (hω : 0 < ω) :
    ‖∏ k ∈ s, theta ω (γ k) x‖ = 1 := by
  rw [norm_prod]
  exact Finset.prod_eq_one (fun k _ => norm_theta ω (γ k) x hω)

/-- Derivative of one factor: `θ' = θ · 2iω/((γ−x)² + ω²)`. -/
theorem theta_hasDerivAt (ω γ x : ℝ) (hω : 0 < ω) :
    HasDerivAt (theta ω γ)
      (theta ω γ x * (2 * I * (ω : ℂ) / (((γ - x : ℝ) : ℂ) ^ 2 + (ω : ℂ) ^ 2))) x := by
  have hr : HasDerivAt (fun y : ℝ => γ - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub γ
  have h1 : HasDerivAt (fun y : ℝ => ((γ - y : ℝ) : ℂ)) (-1) x := by
    simpa using hr.ofReal_comp
  have hn : HasDerivAt (fun y : ℝ => ((γ - y : ℝ) : ℂ) + (ω : ℂ) * I) (-1) x := h1.add_const _
  have hd : HasDerivAt (fun y : ℝ => ((γ - y : ℝ) : ℂ) - (ω : ℂ) * I) (-1) x := h1.sub_const _
  have hden : (((γ - x : ℝ) : ℂ) - (ω : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hnum : (((γ - x : ℝ) : ℂ) + (ω : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h := hn.div hd hden
  unfold theta
  refine h.congr_deriv ?_
  generalize ((γ - x : ℝ) : ℂ) = a at *
  have hnd : a ^ 2 + (ω : ℂ) ^ 2 = (a + (ω : ℂ) * I) * (a - (ω : ℂ) * I) := by
    have : I ^ 2 = -1 := Complex.I_sq
    linear_combination ((ω : ℂ) ^ 2) * this
  rw [hnd]
  field_simp
  ring

/-- Positivity of the phase density `2ω Σ_k 1/((x − γ_k)² + ω²)`. -/
theorem phase_density_pos {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (γ : ι → ℝ)
    (ω x : ℝ) (hω : 0 < ω) :
    0 < 2 * ω * ∑ k ∈ s, 1 / ((x - γ k) ^ 2 + ω ^ 2) := by
  have : 0 < ∑ k ∈ s, 1 / ((x - γ k) ^ 2 + ω ^ 2) :=
    Finset.sum_pos (fun k _ => by positivity) hs
  positivity

end GppPoissonResolventInner
