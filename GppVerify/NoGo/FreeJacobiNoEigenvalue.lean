import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# No-go: the free half-line Jacobi operator has no `ℓ²` eigenvector at any real energy

**Strategy refuted.** "Encode each zeta zero (or each local Euler channel) as an *eigenvalue* of the
free Hecke/Jacobi operator `(Jf)₀ = f₁`, `(Jf)ₙ = fₙ₋₁ + fₙ₊₁` on `ℓ²(ℕ)`."

**Theorem (`no_l2_eigenvector`).** For every real `E`, the only square-summable solution of `Jf = Ef`
is `f = 0`. (Complex non-real `E` are excluded anyway because `J` is symmetric.)

**Proof idea.** Every solution is `f₀ · Uₙ(E)` with `U` the Chebyshev-type recurrence
`U₀ = 1, U₁ = E, Uₙ₊₂ = E Uₙ₊₁ − Uₙ`, and the Casoratian invariant
`Uₙ₊₁² − E Uₙ₊₁ Uₙ + Uₙ² = 1` forces `Uₙ₊₁² + Uₙ² ≥ 1/(1 + |E|/2)` for all `n`, so `Uₙ ↛ 0`.

**What the no-go leaves open (the hint).** A zero can appear only as *boundary/scattering data* — a
boundary value of the Weyl function `m₀`, a resonance, or an eigenvalue of a *perturbed* operator
(e.g. `J + τ|0⟩⟨0|` has one at `τ + 1/τ` iff `|τ| > 1`, outside the band). Any spectral encoding of the
zeros must therefore go through a perturbation or a boundary condition, not the free `J`.

Sources: Claude Code audit of Codex's Jacobi-boundary note, CONVERSATION.md 2026-10-09 (Remark B).
-/

namespace GppNoGo.FreeJacobi

/-- The Chebyshev-type solution `U₀ = 1, U₁ = E, Uₙ₊₂ = E Uₙ₊₁ − Uₙ`. -/
noncomputable def U (E : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => E
  | (n + 2) => E * U E (n + 1) - U E n

/-- Casoratian invariant. -/
theorem casorati (E : ℝ) (n : ℕ) :
    U E (n + 1) ^ 2 - E * U E (n + 1) * U E n + U E n ^ 2 = 1 := by
  induction n with
  | zero => simp [U]; ring
  | succ n ih =>
    have h : U E (n + 2) = E * U E (n + 1) - U E n := rfl
    rw [h]
    linear_combination ih

/-- Consecutive values never get small: `Uₙ₊₁² + Uₙ² ≥ 1 / (1 + |E|/2)`. -/
theorem pair_lower (E : ℝ) (n : ℕ) :
    1 / (1 + |E| / 2) ≤ U E (n + 1) ^ 2 + U E n ^ 2 := by
  set x := U E (n + 1)
  set y := U E n
  have hc := casorati E n
  have hxy : |E * x * y| ≤ |E| / 2 * (x ^ 2 + y ^ 2) := by
    rw [abs_mul, abs_mul]
    have : |x| * |y| ≤ (x ^ 2 + y ^ 2) / 2 := by
      nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
    nlinarith [abs_nonneg E]
  have h1 : 1 ≤ (1 + |E| / 2) * (x ^ 2 + y ^ 2) := by
    have := neg_abs_le (E * x * y)
    nlinarith
  have hpos : 0 < 1 + |E| / 2 := by positivity
  rw [div_le_iff₀ hpos]
  linarith

/-- `U` is not square-summable, for every real `E`. -/
theorem not_summable_sq (E : ℝ) : ¬ Summable (fun n => U E n ^ 2) := by
  intro hs
  have ht := hs.tendsto_atTop_zero
  have ht1 : Filter.Tendsto (fun n => U E (n + 1) ^ 2 + U E n ^ 2) Filter.atTop (nhds 0) := by
    simpa using (ht.comp (Filter.tendsto_add_atTop_nat 1)).add ht
  have hpos : (0 : ℝ) < 1 / (1 + |E| / 2) := by positivity
  have hev := ht1.eventually (gt_mem_nhds hpos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have := hN N le_rfl
  linarith [pair_lower E N]

/-- Every solution of the eigen-recurrence is `f₀ · U`. -/
theorem solution_eq (E : ℝ) (f : ℕ → ℂ) (h1 : f 1 = (E : ℂ) * f 0)
    (hrec : ∀ n, f (n + 2) = (E : ℂ) * f (n + 1) - f n) : ∀ n, f n = f 0 * (U E n : ℂ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [U]
    | 1, _ => simp [U, h1, mul_comm]
    | (k + 2), ih =>
      rw [hrec k, ih (k + 1) (by omega), ih k (by omega)]
      simp only [U]
      push_cast
      ring

/-- **No-go.** The free half-line Jacobi operator has no nonzero square-summable eigenvector at any
real energy `E`: if `f₁ = E f₀`, `fₙ₋₁ + fₙ₊₁ = E fₙ` and `∑ ‖fₙ‖² < ∞` then `f = 0`. -/
theorem no_l2_eigenvector (E : ℝ) (f : ℕ → ℂ) (h1 : f 1 = (E : ℂ) * f 0)
    (hrec : ∀ n, f n + f (n + 2) = (E : ℂ) * f (n + 1))
    (hsum : Summable (fun n => ‖f n‖ ^ 2)) : f = 0 := by
  have hrec' : ∀ n, f (n + 2) = (E : ℂ) * f (n + 1) - f n := fun n => by
    linear_combination hrec n
  have hsol := solution_eq E f h1 hrec'
  by_cases h0 : f 0 = 0
  · funext n; rw [hsol n, h0, zero_mul]; rfl
  · exfalso
    have hc : 0 < ‖f 0‖ ^ 2 := by positivity
    have : Summable (fun n => U E n ^ 2) := by
      have hs2 : Summable (fun n => (‖f 0‖ ^ 2)⁻¹ * ‖f n‖ ^ 2) := hsum.mul_left _
      refine hs2.congr (fun n => ?_)
      rw [hsol n, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      field_simp
    exact not_summable_sq E this

end GppNoGo.FreeJacobi
