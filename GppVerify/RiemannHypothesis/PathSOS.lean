import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# The exact path sum-of-squares identity for the short-support Weil positivity tower

Source: Codex, GPP-bridge PR #11 comment 6539964860 (2026-10-31), "disintegrate zero-extended f into
`k`-point fibers `a_j`"; written up in `discovery/short_support_nilpotent_tower.md`
(GPPDiscovery2, `codex/discovery-workbench`). Daniel Toupin / Golden Physics Project, with AI
assistance from Codex (statement) and Claude Code (formalization).

For `k = m + 1 ≥ 1`, `θ = π/(k+1)`, `w_j = sin(jθ)` and complex `a_1,…,a_k`:

`2cos θ · Σ_{j=1}^{k} |a_j|² − 2 Re Σ_{j=1}^{k−1} conj(a_j) a_{j+1}
   = Σ_{j=1}^{k−1} w_j w_{j+1} · |a_j/w_j − a_{j+1}/w_{j+1}|²`.

The right side is nonnegative, so `Σ_j 2 Re conj(a_j)a_{j+1} ≤ 2cos θ · Σ|a_j|²`: the path Laplacian's
Dirichlet ground-state transform, with ground state `w`.

* `term_identity`: `w₁ w₂ |x/w₁ − y/w₂|² = (w₂/w₁)|x|² + (w₁/w₂)|y|² − 2 Re conj(x) y`.
* `path_sos`: the identity above (indices shifted so the sums run over `range`).
* `path_sos_nonneg`: the right side is `≥ 0`, hence the one-sided bound.

**Scope.** This is only the finite algebraic identity. The analytic content of Codex's theorem
(`Q_L[f] > ‖f‖²/200` for `L ≤ 5/32`, the Arb certificate `B_40(5/32) > 1/200`, the disintegration of
`f` into fibers, the gamma-tilt discount) is not formalized. No claim about RH.
-/

set_option autoImplicit false

open Finset

namespace GppPathSOS

/-- `w_j w_{j+1} |x/w_j − y/w_{j+1}|² = (w_{j+1}/w_j)|x|² + (w_j/w_{j+1})|y|² − 2Re(x̄ y)`. -/
theorem term_identity (x y : ℂ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    u * v * ‖x / (u : ℂ) - y / (v : ℂ)‖ ^ 2 =
      v / u * ‖x‖ ^ 2 + u / v * ‖y‖ ^ 2 - 2 * ((starRingEnd ℂ) x * y).re := by
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_div, Complex.normSq_div,
    Complex.normSq_ofReal, Complex.normSq_ofReal, Complex.sq_norm, Complex.sq_norm]
  have h3 : (x / (u : ℂ) * (starRingEnd ℂ) (y / (v : ℂ))).re =
      (x * (starRingEnd ℂ) y).re / (u * v) := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, ← Complex.ofReal_mul,
      Complex.div_ofReal_re]
  have h4 : (x * (starRingEnd ℂ) y).re = ((starRingEnd ℂ) x * y).re := by
    simp [Complex.mul_re]
  rw [h3, h4]
  field_simp

open Real in
/-- **The exact path sum-of-squares identity** (indices shifted: `a (j+1)` is `a_{j+1}`, `j < k`
with `k = m + 1`, and `w_j = sin(jπ/(m+2))`). -/
theorem path_sos (m : ℕ) (a : ℕ → ℂ) :
    2 * Real.cos (π / (m + 2)) * ∑ j ∈ range (m + 1), ‖a (j + 1)‖ ^ 2 -
        2 * (∑ j ∈ range m, (starRingEnd ℂ) (a (j + 1)) * a (j + 2)).re =
      ∑ j ∈ range m, Real.sin (((j + 1 : ℕ) : ℝ) * (π / (m + 2))) *
        Real.sin (((j + 2 : ℕ) : ℝ) * (π / (m + 2))) *
        ‖a (j + 1) / (Real.sin (((j + 1 : ℕ) : ℝ) * (π / (m + 2))) : ℂ) -
          a (j + 2) / (Real.sin (((j + 2 : ℕ) : ℝ) * (π / (m + 2))) : ℂ)‖ ^ 2 := by
  set θ : ℝ := π / (m + 2) with hθ
  set W : ℕ → ℝ := fun j => Real.sin ((j : ℝ) * θ) with hW
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hθpos : 0 < θ := div_pos Real.pi_pos hm2
  have hWpos : ∀ j, 1 ≤ j → j ≤ m + 1 → 0 < W j := by
    intro j h1 h2
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < j := by exact_mod_cast h1
      positivity
    · have hj : (j : ℝ) ≤ m + 1 := by exact_mod_cast h2
      calc (j : ℝ) * θ ≤ (m + 1) * θ := by gcongr
        _ < π := by
          rw [hθ, ← mul_div_assoc, div_lt_iff₀ hm2]; nlinarith [Real.pi_pos]
  have hW0 : W 0 = 0 := by simp [hW]
  have hWend : W (m + 2) = 0 := by
    simp only [hW]
    have : ((m + 2 : ℕ) : ℝ) * θ = π := by
      rw [hθ]; push_cast; field_simp
    rw [this, Real.sin_pi]
  have hrec : ∀ j, W (j + 2) + W j = 2 * Real.cos θ * W (j + 1) := by
    intro j
    simp only [hW]
    have e1 : ((j + 2 : ℕ) : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
    have e2 : ((j : ℕ) : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]; ring
  -- termwise
  have hterm : ∀ j ∈ range m,
      W (j + 1) * W (j + 2) * ‖a (j + 1) / (W (j + 1) : ℂ) - a (j + 2) / (W (j + 2) : ℂ)‖ ^ 2 =
        W (j + 2) / W (j + 1) * ‖a (j + 1)‖ ^ 2 + W (j + 1) / W (j + 2) * ‖a (j + 2)‖ ^ 2 -
          2 * ((starRingEnd ℂ) (a (j + 1)) * a (j + 2)).re := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact term_identity _ _ (hWpos (j + 1) (by omega) (by omega))
      (hWpos (j + 2) (by omega) (by omega))
  show _ = ∑ j ∈ range m, W (j + 1) * W (j + 2) *
    ‖a (j + 1) / (W (j + 1) : ℂ) - a (j + 2) / (W (j + 2) : ℂ)‖ ^ 2
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Complex.re_sum]
  set P : ℕ → ℝ := fun j => W (j + 2) / W (j + 1) * ‖a (j + 1)‖ ^ 2 with hP
  set Q : ℕ → ℝ := fun j => W j / W (j + 1) * ‖a (j + 1)‖ ^ 2 with hQ
  have hPm : ∑ j ∈ range m, P j = ∑ j ∈ range (m + 1), P j := by
    rw [Finset.sum_range_succ, hP]
    simp [hWend]
  have hQm : ∑ j ∈ range m, W (j + 1) / W (j + 2) * ‖a (j + 2)‖ ^ 2 =
      ∑ j ∈ range (m + 1), Q j := by
    rw [Finset.sum_range_succ' _ m, hQ]
    simp [hW0]
  have hdiag : ∑ j ∈ range (m + 1), (P j + Q j) =
      2 * Real.cos θ * ∑ j ∈ range (m + 1), ‖a (j + 1)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.mem_range.mp hj
    have hpos := (hWpos (j + 1) (by omega) (by omega)).ne'
    have := hrec j
    simp only [hP, hQ]
    field_simp
    linear_combination (‖a (j + 1)‖ ^ 2) * this
  have hPQ : ∑ j ∈ range m, P j +
      ∑ j ∈ range m, W (j + 1) / W (j + 2) * ‖a (j + 2)‖ ^ 2 =
      2 * Real.cos θ * ∑ j ∈ range (m + 1), ‖a (j + 1)‖ ^ 2 := by
    rw [hPm, hQm, ← Finset.sum_add_distrib, hdiag]
  simpa [hP] using by linarith [hPQ]

open Real in
/-- `w_j = sin(jπ/(m+2)) > 0` for `1 ≤ j ≤ m + 1`. -/
theorem sin_pos_idx (m j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ m + 1) :
    0 < Real.sin ((j : ℝ) * (π / (m + 2))) := by
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  apply Real.sin_pos_of_pos_of_lt_pi
  · have : (0 : ℝ) < j := by exact_mod_cast h1
    have : 0 < π / ((m : ℝ) + 2) := div_pos Real.pi_pos hm2
    positivity
  · have hj : (j : ℝ) ≤ m + 1 := by exact_mod_cast h2
    calc (j : ℝ) * (π / (m + 2)) ≤ (m + 1) * (π / (m + 2)) := by
          have : 0 < π / ((m : ℝ) + 2) := div_pos Real.pi_pos hm2
          gcongr
      _ < π := by
          rw [← mul_div_assoc, div_lt_iff₀ hm2]; nlinarith [Real.pi_pos]

open Real in
/-- **Consequence.** `2 Re Σ conj(a_j) a_{j+1} ≤ 2cos(π/(m+2)) Σ |a_j|²`. -/
theorem path_sos_nonneg (m : ℕ) (a : ℕ → ℂ) :
    2 * (∑ j ∈ range m, (starRingEnd ℂ) (a (j + 1)) * a (j + 2)).re ≤
      2 * Real.cos (π / (m + 2)) * ∑ j ∈ range (m + 1), ‖a (j + 1)‖ ^ 2 := by
  have h := path_sos m a
  have hnn : 0 ≤ ∑ j ∈ range m, Real.sin (((j + 1 : ℕ) : ℝ) * (π / (m + 2))) *
        Real.sin (((j + 2 : ℕ) : ℝ) * (π / (m + 2))) *
        ‖a (j + 1) / (Real.sin (((j + 1 : ℕ) : ℝ) * (π / (m + 2))) : ℂ) -
          a (j + 2) / (Real.sin (((j + 2 : ℕ) : ℝ) * (π / (m + 2))) : ℂ)‖ ^ 2 := by
    refine Finset.sum_nonneg (fun j hj => ?_)
    have hj' := Finset.mem_range.mp hj
    have h1 := sin_pos_idx m (j + 1) (by omega) (by omega)
    have h2 := sin_pos_idx m (j + 2) (by omega) (by omega)
    push_cast at h1 h2 ⊢
    positivity
  linarith

/-- **Weighted edge AM–GM** (the graph SOS of Codex's Hardy–Schur absorption, PR #11 comments
6540017178 / 6540047604, for one edge): for positive weights `u, v`,
`2 Re(x̄ y) ≤ (v/u)|x|² + (u/v)|y|²`. -/
theorem edge_amgm (x y : ℂ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    2 * ((starRingEnd ℂ) x * y).re ≤ v / u * ‖x‖ ^ 2 + u / v * ‖y‖ ^ 2 := by
  have h := term_identity x y hu hv
  have hnn : 0 ≤ u * v * ‖x / (u : ℂ) - y / (v : ℂ)‖ ^ 2 := by positivity
  linarith

/-- **Finite weighted edge sum.** For nonnegative edge weights `w_e` and positive comparison weights
`h`, `Σ_e w_e · 2 Re(conj f(s e) · f(t e)) ≤ Σ_e w_e ((h(t e)/h(s e))|f(s e)|² + (h(s e)/h(t e))|f(t e)|²)`
for any edge list with endpoints `s, t`. -/
theorem edge_sum_le {ε ι : Type*} (E : Finset ε) (s t : ε → ι) (w : ε → ℝ) (h : ι → ℝ)
    (f : ι → ℂ) (hw : ∀ e ∈ E, 0 ≤ w e) (hh : ∀ i, 0 < h i) :
    ∑ e ∈ E, w e * (2 * ((starRingEnd ℂ) (f (s e)) * f (t e)).re) ≤
      ∑ e ∈ E, w e * (h (t e) / h (s e) * ‖f (s e)‖ ^ 2 + h (s e) / h (t e) * ‖f (t e)‖ ^ 2) := by
  refine Finset.sum_le_sum (fun e he => ?_)
  exact mul_le_mul_of_nonneg_left (edge_amgm _ _ (hh (s e)) (hh (t e))) (hw e he)

end GppPathSOS
