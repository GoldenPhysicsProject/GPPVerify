import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# No-go: a bare Euler pole plus any bounded correction is never Pick-positive near `s = 1`

**Strategy refuted.** "Approximate `F = ξ'/ξ` by a finite Euler truncation
`F_N(s) = B(s) − ∑_{n ≤ N} Λ(n) n^{−s}` and prove the real-node Pick matrices of `F_N` are PSD, then
pass to the limit." (Codex, GPP-bridge PR #11, 2026-10-10; Astra's Pick criterion.)

Near `s = 1`, `F_N(s) = 1/(s−1) + H_N(s)` with `H_N` bounded (the `1/s`, `ψ(s/2)` and finite prime
terms are all bounded there). For the two real nodes `s = 1 + ε`, `t = 1 + 2ε` the 2×2 Pick matrix
`P = [[F(s)/(s−½), (F(s)+F(t))/(s+t−1)], [·, F(t)/(t−½)]]` has determinant `det` with

**Theorem (`eps_sq_det_tendsto`).** `ε² · det → −1/4` as `ε → 0⁺`, for **every** bounded correction.
Hence (`det_eventually_neg`) the determinant is negative for all small `ε`: no finite truncation, and
no bounded perturbation of the pole, gives a PSD Pick kernel.

**What the no-go leaves open (the hint).** The pole must be cancelled by an *unbounded*, signed
arithmetic tail — the infinite prime sum near `s = 1` — so any positive approximation scheme must
renormalise the pole jointly with the primes, not truncate the primes.

Independent confirmation of Codex's asymptotic (his statement: "determinant × ε² tends to −1/4
regardless of bounded H_N").
-/

namespace GppNoGo.EulerPole

open Filter Topology

/-- The 2×2 Pick determinant at centred nodes `a = s−½`, `b = t−½` with `u = F(s)`, `v = F(t)`:
    entries `(F_i + F_j)/(s_i + s_j − 1)`, so the diagonal is `2u/(2a) = u/a`. -/
noncomputable def pickDet (a b u v : ℝ) : ℝ := u / a * (v / b) - ((u + v) / (a + b)) ^ 2

/-- The value at `s = 1 + ε` (centred `a = ½ + ε`) of `1/(s−1) + h`. -/
noncomputable def det2 (h₁ h₂ : ℝ → ℝ) (ε : ℝ) : ℝ :=
  pickDet (1 / 2 + ε) (1 / 2 + 2 * ε) (1 / ε + h₁ ε) (1 / (2 * ε) + h₂ ε)

theorem eps_sq_det_eq (h₁ h₂ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ε ^ 2 * det2 h₁ h₂ ε
      = (1 + ε * h₁ ε) * (1 / 2 + ε * h₂ ε) / ((1 / 2 + ε) * (1 / 2 + 2 * ε))
        - ((3 / 2 + ε * (h₁ ε + h₂ ε)) / (1 + 3 * ε)) ^ 2 := by
  unfold det2 pickDet
  have h1 : (1 / 2 : ℝ) + ε ≠ 0 := by positivity
  have h2 : (1 / 2 : ℝ) + 2 * ε ≠ 0 := by positivity
  have h3 : (1 : ℝ) + 3 * ε ≠ 0 := by positivity
  field_simp
  ring

/-- `ε · h(ε) → 0` for bounded `h`. -/
theorem eps_mul_bounded_tendsto (h : ℝ → ℝ) {M : ℝ} (hM : ∀ x, |h x| ≤ M) :
    Tendsto (fun ε => ε * h ε) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  refine squeeze_zero_norm' ?_ (by simpa using (h0.abs.mul_const M))
  refine Eventually.of_forall (fun ε => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hM ε) (abs_nonneg ε)

/-- **No-go.** For every bounded correction, `ε² · det → −1/4`. -/
theorem eps_sq_det_tendsto (h₁ h₂ : ℝ → ℝ) {M : ℝ} (hM₁ : ∀ x, |h₁ x| ≤ M) (hM₂ : ∀ x, |h₂ x| ≤ M) :
    Tendsto (fun ε => ε ^ 2 * det2 h₁ h₂ ε) (𝓝[>] 0) (𝓝 (-1 / 4)) := by
  have e1 := eps_mul_bounded_tendsto h₁ hM₁
  have e2 := eps_mul_bounded_tendsto h₂ hM₂
  have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  let G : ℝ × ℝ × ℝ → ℝ := fun q =>
    (1 + q.2.1) * (1 / 2 + q.2.2) / ((1 / 2 + q.1) * (1 / 2 + 2 * q.1))
      - ((3 / 2 + (q.2.1 + q.2.2)) / (1 + 3 * q.1)) ^ 2
  have hG : ContinuousAt G (0, 0, 0) := by
    simp only [G]
    apply ContinuousAt.sub
    · apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    · apply ContinuousAt.pow
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
  have hG0 : G (0, 0, 0) = -1 / 4 := by simp only [G]; norm_num
  have hpath : Tendsto (fun ε => ((ε : ℝ), ε * h₁ ε, ε * h₂ ε)) (𝓝[>] 0) (𝓝 ((0 : ℝ), (0 : ℝ), (0 : ℝ))) :=
    h0.prodMk_nhds (e1.prodMk_nhds e2)
  have hlim : Tendsto (fun ε => G (ε, ε * h₁ ε, ε * h₂ ε)) (𝓝[>] 0) (𝓝 (-1 / 4)) := by
    rw [← hG0]; exact hG.tendsto.comp hpath
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  rw [eps_sq_det_eq h₁ h₂ hε']
  simp only [G]
  ring

/-- Corollary: the 2-node Pick determinant is negative for all small `ε > 0`. -/
theorem det_eventually_neg (h₁ h₂ : ℝ → ℝ) {M : ℝ} (hM₁ : ∀ x, |h₁ x| ≤ M) (hM₂ : ∀ x, |h₂ x| ≤ M) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), det2 h₁ h₂ ε < 0 := by
  have ht := eps_sq_det_tendsto h₁ h₂ hM₁ hM₂
  have hneg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 2 * det2 h₁ h₂ ε < 0 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hneg, self_mem_nhdsWithin] with ε h hε
  have hε' : (0 : ℝ) < ε := hε
  have hε2 : 0 < ε ^ 2 := by positivity
  by_contra hc
  push Not at hc
  have := mul_nonneg hε2.le hc
  linarith

end GppNoGo.EulerPole
