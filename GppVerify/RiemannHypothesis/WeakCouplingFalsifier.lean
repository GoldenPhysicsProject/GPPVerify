import GppVerify.RiemannHypothesis.RungConvexity

/-!
# The weak-coupling falsifier: the exact rational core

GPP's all-prime graph / Suzuki rung-flow filing (Turbo relay `b64da14`, §7) uses *fake weights*
`ṽ_n = (log n)/√n` for every `n ≥ 2`. They keep the first-rung entrant bound `g̃_n < 1` with `g̃_n → 0`,
yet `H̃(log 200) < 0`: no all-rung induction that only uses local `g_n < 1` can supply the global
Lyapunov invariant. The certificate of `H̃(log 200) < 0` is a rational inequality:

`Σ_{k=2}^{50} (69/100)² ⌊log₂ k⌋ ⌊log₂ ⌊200/k⌋⌋ / ⌈√k⌉ = 1091856/21875 > 1711/35 = 4(283/20 + 1/14 − 2)`,

with margin exactly `22481/21875`.

This file proves **only that rational statement**, kernel-checked over ℚ, with `⌊log₂ k⌋` and `⌈√k⌉`
written as explicit counts (`flog2`, `csqrt`). The chain from `H̃(log 200)` to this sum — `log 2 > 69/100`,
`14 < √200 < 283/20`, nonnegativity of the omitted `k > 50` terms, the `⌊log₂⌋` structure of the
prime-power count — is an analytic obligation and is **not** formalised here.

No `sorry`, no axiom.
-/

noncomputable section

namespace GppFalsifier

/-- `⌊log₂ k⌋` for `k ≥ 1`, as the number of `i < 12` with `2^(i+1) ≤ k`. -/
def flog2 (k : ℕ) : ℕ := ((List.range 12).filter fun i => 2 ^ (i + 1) ≤ k).length

/-- `⌈√k⌉` for `1 ≤ k ≤ 200`, as the number of `j < 15` with `j² < k`. -/
def csqrt (k : ℕ) : ℕ := ((List.range 15).filter fun j => j * j < k).length

theorem flog2_spec : ∀ k ∈ Finset.Icc 1 200, 2 ^ flog2 k ≤ k ∧ k < 2 ^ (flog2 k + 1) := by
  decide +kernel

theorem csqrt_spec : ∀ k ∈ Finset.Icc 1 200, k ≤ csqrt k ^ 2 ∧ (csqrt k - 1) ^ 2 < k := by
  decide +kernel

/-- The falsifier sum `Σ_{k=2}^{50} (69/100)² ⌊log₂ k⌋ ⌊log₂ ⌊200/k⌋⌋ / ⌈√k⌉` over ℚ. -/
def falsifierSum : ℚ :=
  ∑ i ∈ Finset.range 49,
    (69 / 100 : ℚ) ^ 2 * (flog2 (i + 2) : ℚ) * (flog2 (200 / (i + 2)) : ℚ) / (csqrt (i + 2) : ℚ)

theorem falsifierSum_eq : falsifierSum = 1091856 / 21875 := by
  unfold falsifierSum; decide +kernel

theorem rhs_eq : 4 * ((283 : ℚ) / 20 + 1 / 14 - 2) = 1711 / 35 := by norm_num

/-- **The falsifier inequality:** `Σ > 1711/35 = 4(283/20 + 1/14 − 2)`, margin exactly `22481/21875`. -/
theorem falsifier_gt : (1711 / 35 : ℚ) < falsifierSum := by
  rw [falsifierSum_eq]; norm_num

theorem falsifier_margin : falsifierSum - 1711 / 35 = 22481 / 21875 := by
  rw [falsifierSum_eq]; norm_num

end GppFalsifier

#print axioms GppFalsifier.falsifier_gt
#print axioms GppFalsifier.falsifier_margin
